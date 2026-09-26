// The Go side of the differential test: github.com/transparency-dev/merkle,
// the reference implementation, acts as the oracle for ocaml-merkle.
//
//	go run . corpus FILE   write a corpus of roots, proofs and verification
//	                       queries, each query with this implementation's
//	                       verdict, for compat/ocaml/replay.exe to replay
//	go run . vectors       print test/reference_vectors.ml
//
// See ../README.md.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"strings"

	"github.com/transparency-dev/merkle/proof"
	"github.com/transparency-dev/merkle/rfc6962"
	"github.com/transparency-dev/merkle/testonly"
)

var hasher = rfc6962.DefaultHasher

func main() {
	switch {
	case len(os.Args) == 3 && os.Args[1] == "corpus":
		corpus(os.Args[2])
	case len(os.Args) == 2 && os.Args[1] == "vectors":
		vectors()
	default:
		fmt.Fprintln(os.Stderr, "usage: go run . corpus FILE | go run . vectors")
		os.Exit(2)
	}
}

func env(name string, def int) int {
	if v, err := strconv.Atoi(os.Getenv(name)); err == nil {
		return v
	}
	return def
}

// ---------------------------------------------------------------- corpus
//
// Line formats, space separated; hashes and leaf data are hex, "-" is the
// empty string or the empty proof, proofs are comma separated:
//
//	L data                              a leaf, in log order
//	R size root                         root of the first size leaves
//	P index size proof                  inclusion proof
//	Q size1 size2 proof                 consistency proof
//	I index size leaf root proof 0|1    VerifyInclusion and its verdict
//	C size1 size2 root1 root2 proof 0|1 VerifyConsistency and its verdict

var (
	out    *bufio.Writer
	rng    *rand.Rand
	nI, nC int
)

func hx(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

func px(p [][]byte) string {
	if len(p) == 0 {
		return "-"
	}
	s := make([]string, len(p))
	for i, e := range p {
		s[i] = hex.EncodeToString(e)
	}
	return strings.Join(s, ",")
}

func verdict(err error) int {
	if err == nil {
		return 1
	}
	return 0
}

func randHash() []byte {
	b := make([]byte, 32)
	rng.Read(b)
	return b
}

func flip(b []byte) []byte {
	c := append([]byte{}, b...)
	c[rng.Intn(len(c))] ^= 1 << uint(rng.Intn(8))
	return c
}

func clone(p [][]byte) [][]byte { return append([][]byte{}, p...) }

// OCaml ints have 63 bits: keep every query representable on both sides.
const maxSize = 1 << 62

func qi(index, size uint64, leaf []byte, p [][]byte, root []byte) {
	if index >= maxSize || size >= maxSize {
		return
	}
	err := proof.VerifyInclusion(hasher, index, size, leaf, p, root)
	fmt.Fprintf(out, "I %d %d %s %s %s %d\n", index, size, hx(leaf), hx(root), px(p), verdict(err))
	nI++
}

func qc(size1, size2 uint64, root1, root2 []byte, p [][]byte) {
	if size1 >= maxSize || size2 >= maxSize {
		return
	}
	err := proof.VerifyConsistency(hasher, size1, size2, p, root1, root2)
	fmt.Fprintf(out, "C %d %d %s %s %s %d\n", size1, size2, hx(root1), hx(root2), px(p), verdict(err))
	nC++
}

// One honest inclusion query and the ways it can be wrong: every argument
// off by a little or by a lot, and the path damaged structurally.
func inclusionQueries(t *testonly.Tree, index, size uint64) {
	leaf := t.LeafHash(index)
	root := t.HashAt(size)
	p, err := t.InclusionProof(index, size)
	if err != nil {
		panic(err)
	}
	qi(index, size, leaf, p, root)
	qi(index, size, flip(leaf), p, root)
	qi(index, size, leaf, p, flip(root))
	for _, d := range []int64{-2, -1, 1, 2} {
		if i := int64(index) + d; i >= 0 {
			qi(uint64(i), size, leaf, p, root)
		}
		if s := int64(size) + d; s >= 0 {
			qi(index, uint64(s), leaf, p, root)
		}
	}
	qi(index, size*2, leaf, p, root)
	qi(index, size*2+1, leaf, p, root)
	qi(index, (size+1)/2, leaf, p, root)
	qi(index, 0, leaf, p, root)
	qi(size, size, leaf, p, root)
	qi(index+(1<<40), size+(1<<40), leaf, p, root)
	qi(index, size+(1<<40), leaf, p, root)
	if len(p) > 0 {
		qi(index, size, leaf, p[:len(p)-1], root)
		qi(index, size, leaf, p[1:], root)
		m := clone(p)
		j := rng.Intn(len(m))
		m[j] = flip(m[j])
		qi(index, size, leaf, m, root)
	}
	if len(p) > 1 {
		m := clone(p)
		m[0], m[len(m)-1] = m[len(m)-1], m[0]
		qi(index, size, leaf, m, root)
		r := clone(p)
		for a, b := 0, len(r)-1; a < b; a, b = a+1, b-1 {
			r[a], r[b] = r[b], r[a]
		}
		qi(index, size, leaf, r, root)
	}
	qi(index, size, leaf, append(clone(p), randHash()), root)
	qi(index, size, leaf, append([][]byte{randHash()}, p...), root)
	qi(index, size, leaf, append(clone(p), root), root)
	qi(index, size, leaf, [][]byte{}, root)
	qi(index, size, root, [][]byte{}, root)
}

func consistencyQueries(t *testonly.Tree, size1, size2 uint64) {
	root1, root2 := t.HashAt(size1), t.HashAt(size2)
	p, err := t.ConsistencyProof(size1, size2)
	if err != nil {
		panic(err)
	}
	qc(size1, size2, root1, root2, p)
	qc(size1, size2, flip(root1), root2, p)
	qc(size1, size2, root1, flip(root2), p)
	qc(size1, size2, root2, root1, p)
	qc(size2, size1, root2, root1, p)
	qc(size2, size1, root1, root2, p)
	// Equal sizes and equal roots, but not the roots of the tree: from
	// size 0 this is the documented difference (only H("") is a root).
	bogus := randHash()
	qc(size1, size1, bogus, bogus, [][]byte{})
	qc(size2, size2, bogus, bogus, [][]byte{})
	for _, d := range []int64{-2, -1, 1, 2} {
		if s := int64(size1) + d; s >= 0 {
			qc(uint64(s), size2, root1, root2, p)
		}
		if s := int64(size2) + d; s >= 0 {
			qc(size1, uint64(s), root1, root2, p)
		}
	}
	qc(size1, size2*2, root1, root2, p)
	qc(size1*2, size2*2, root1, root2, p)
	qc(size1, size2+(1<<40), root1, root2, p)
	qc(size1+(1<<40), size2+(1<<40), root1, root2, p)
	qc(size1, size2, root1, root2, [][]byte{})
	// Some logs send the old root first even when size1 is a power of two.
	qc(size1, size2, root1, root2, append([][]byte{root1}, p...))
	qc(size1, size2, root1, root2, append(clone(p), randHash()))
	qc(size1, size2, root1, root2, append(clone(p), root2))
	qc(size1, size2, root1, root2, append([][]byte{randHash()}, p...))
	if len(p) > 0 {
		qc(size1, size2, root1, root2, p[:len(p)-1])
		qc(size1, size2, root1, root2, p[1:])
		m := clone(p)
		j := rng.Intn(len(m))
		m[j] = flip(m[j])
		qc(size1, size2, root1, root2, m)
	}
	if len(p) > 1 {
		m := clone(p)
		m[0], m[len(m)-1] = m[len(m)-1], m[0]
		qc(size1, size2, root1, root2, m)
	}
}

func corpus(path string) {
	seed := int64(env("SEED", 20260917))
	leaves := env("LEAVES", 1500)       // size of the log
	exhaustive := env("EXHAUSTIVE", 64) // every proof up to this tree size
	queried := env("QUERIED", 40)       // every query up to this tree size
	samples := env("SAMPLES", 1500)     // random draws from the whole log
	rng = rand.New(rand.NewSource(seed))

	f, err := os.Create(path)
	if err != nil {
		panic(err)
	}
	defer f.Close()
	out = bufio.NewWriterSize(f, 1<<20)
	defer out.Flush()

	t := testonly.New(hasher)
	for i := 0; i < leaves; i++ {
		var d []byte
		switch {
		case i == 0: // the empty leaf
		case i%7 == 0:
			d = []byte(fmt.Sprintf("leaf-%d", i))
		default:
			d = make([]byte, rng.Intn(48))
			rng.Read(d)
		}
		t.AppendData(d)
		fmt.Fprintf(out, "L %s\n", hx(d))
	}
	for s := 0; s <= leaves; s++ {
		fmt.Fprintf(out, "R %d %s\n", s, hx(t.HashAt(uint64(s))))
	}

	emitP := func(i, s uint64) {
		p, err := t.InclusionProof(i, s)
		if err != nil {
			panic(err)
		}
		fmt.Fprintf(out, "P %d %d %s\n", i, s, px(p))
	}
	emitQ := func(s1, s2 uint64) {
		p, err := t.ConsistencyProof(s1, s2)
		if err != nil {
			panic(err)
		}
		fmt.Fprintf(out, "Q %d %d %s\n", s1, s2, px(p))
	}
	for s := uint64(1); s <= uint64(exhaustive); s++ {
		for i := uint64(0); i < s; i++ {
			emitP(i, s)
		}
	}
	for s2 := uint64(0); s2 <= uint64(exhaustive); s2++ {
		for s1 := uint64(0); s1 <= s2; s1++ {
			emitQ(s1, s2)
		}
	}
	for s := uint64(1); s <= uint64(queried); s++ {
		for i := uint64(0); i < s; i++ {
			inclusionQueries(t, i, s)
		}
	}
	for s2 := uint64(0); s2 <= uint64(queried); s2++ {
		for s1 := uint64(0); s1 <= s2; s1++ {
			consistencyQueries(t, s1, s2)
		}
	}
	for k := 0; k < samples; k++ {
		s := uint64(1 + rng.Intn(leaves))
		i := uint64(rng.Intn(int(s)))
		s1 := uint64(rng.Intn(int(s) + 1))
		emitP(i, s)
		emitQ(s1, s)
		inclusionQueries(t, i, s)
		consistencyQueries(t, s1, s)
	}
	fmt.Fprintf(os.Stderr, "%d leaves, %d inclusion queries, %d consistency queries (seed %d)\n",
		leaves, nI, nC, seed)
}

// --------------------------------------------------------------- vectors

func ocamlList(p [][]byte, indent string) string {
	if len(p) == 0 {
		return "[]"
	}
	s := "[\n"
	for _, e := range p {
		s += indent + "  \"" + hex.EncodeToString(e) + "\";\n"
	}
	return s + indent + "]"
}

func vectors() {
	t := testonly.New(hasher)
	for i := 0; i < 1000; i++ {
		t.AppendData([]byte(fmt.Sprintf("leaf-%d", i)))
	}
	fmt.Print(`(* Known answers computed by the Go reference implementation,
   github.com/transparency-dev/merkle v0.0.2 (rfc6962.DefaultHasher, i.e.
   SHA-256), for the log whose i-th leaf is the ASCII string "leaf-<i>".

   They complement the 8-leaf Certificate Transparency vectors with
   larger and irregular tree shapes: sizes either side of a power of two,
   a log that outgrows its initial storage, and proofs up to ten hashes
   long.

   Generated by compat/go ("go run . vectors"); compat/run.sh checks that
   this file is current. Do not edit. *)

`)
	fmt.Println("(* (size, root) *)")
	fmt.Println("let roots =\n  [")
	for _, s := range []uint64{1, 2, 3, 9, 13, 16, 17, 100, 127, 128, 129, 255, 256, 257, 1000} {
		fmt.Printf("    (%d, \"%s\");\n", s, hex.EncodeToString(t.HashAt(s)))
	}
	fmt.Println("  ]")
	fmt.Println()
	fmt.Println("(* (index, size, audit path) *)")
	fmt.Println("let inclusion =\n  [")
	for _, c := range [][2]uint64{{0, 13}, {12, 13}, {5, 13}, {16, 17}, {77, 100}, {128, 129}, {0, 129}, {255, 257}, {500, 1000}, {999, 1000}} {
		p, err := t.InclusionProof(c[0], c[1])
		if err != nil {
			panic(err)
		}
		fmt.Printf("    ( %d,\n      %d,\n      %s );\n", c[0], c[1], ocamlList(p, "      "))
	}
	fmt.Println("  ]")
	fmt.Println()
	fmt.Println("(* (old_size, new_size, consistency proof) *)")
	fmt.Println("let consistency =\n  [")
	for _, c := range [][2]uint64{{1, 2}, {4, 13}, {7, 13}, {12, 13}, {16, 17}, {64, 100}, {99, 100}, {128, 129}, {129, 1000}, {512, 1000}, {999, 1000}} {
		p, err := t.ConsistencyProof(c[0], c[1])
		if err != nil {
			panic(err)
		}
		fmt.Printf("    ( %d,\n      %d,\n      %s );\n", c[0], c[1], ocamlList(p, "      "))
	}
	fmt.Println("  ]")
}
