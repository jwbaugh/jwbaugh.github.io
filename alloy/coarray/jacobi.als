
module jacobi

/*
 * Verification of a parallel Laplace equation solver on a rectangular
 * domain from an implementation in Coarray Fortran
 *
 * Authors: Juan Benavides, John Baugh, and Ganesh Gopalakrishnan
 * Date: October 13, 2022
 * Alloy Analyzer 6.1.0
 *
 * For a detailed description, see:
 *
 * An HPC practitioner's workbench for formal refinement checking
 *
 * LCPC 2022: 35th International Workshop on Languages and Compilers
 *   for Parallel Computing (to appear)
 */

// Abstract level: start with original matrix structure from Dyer et al.

sig Value {}
one sig Zero, One extends Value {}

-- Dense matrices of symbolic (atomic) values, zero and non-zeros

sig Matrix {
  rows, cols: Int,
  vals: Int->Int->lone Value
}

fact AbstractInv { all m: Matrix | Inv[m] }

-- abstract invariant: enforce as a fact
pred Inv [m: Matrix] {
  m.rows >= 0
  m.cols >= 0
  m.rows = 0 <=> m.cols = 0  -- just one shape for an empty matrix (both 0)
  m.vals.univ = range[m.rows]->range[m.cols]
}

-- the set [0, n-1]
fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}

-- two matrices have the same dimensions
pred sameShape [a, b: Matrix] {
  a.rows = b.rows
  a.cols = b.cols
}

-- two matrices are equivalent
pred equivalent [a, b: Matrix] {
  a.rows = b.rows
  a.cols = b.cols
  a.vals = b.vals
}

-- index of last column of a matrix
fun lastCol [m: Matrix]: one Int {
  { i: Int | i = minus[m.cols, 1] }
}

-- index of last row of a matrix
fun lastRow [m: Matrix]: one Int {
  { i: Int | i = minus[m.rows, 1] }
}

// Adding expressions

// Instead of building up and comparing general arithmetic
// expressions, provide a way to record values of the four neighbors
// in a matrix that are used to compute an average (the only type of
// arithmetic computation being performed in a Jacobi iteration).

sig Neighbors extends Value {
  up, down, left, right: Value
}

fun neighbors [m: Matrix, i: Int, j: Int]: one Neighbors {
  { n: Neighbors |
      n.up = m.vals[plus[i, 1], j] and
      n.down = m.vals[minus[i, 1], j] and
      n.left = m.vals[i, minus[j, 1]] and
      n.right = m.vals[i, plus[j, 1]]
  }
}

-- no extraneous neighbors: keep only those that appear somewhere in a matrix
fact { all n: Neighbors | n in Matrix.vals[Int][Int] }

-- A step in a Jacobi iteration (abstract)
pred JacobiStep [U, V: Matrix] {
  sameShape[U, V]
  V.vals.univ = range[V.rows]->range[V.cols] -- populate elements (neighbors)
  V.vals =
    { i: range[U.rows], j: range[U.cols], x: Value |
        let boundary = (j = 0 or j = minus[U.cols, 1] or
                          i = 0 or i = minus[U.rows, 1]) |
          x = (boundary => U.vals[i, j] else neighbors[U, i, j]) }
}

// Generate some instances to look at

pred show {
  some a, b: Matrix |
    relevant[a] and simpleMatrix[a] and JacobiStep[a, b]
}

run show for 5 but 2 Matrix, 0 Coarray

-- show only "interesting" matrices
pred relevant [m: Matrix] {
  m.rows >= 3
  m.cols >= 3
}

-- a matrix with only "atomic" values for elements (no Neighbors)
pred simpleMatrix [m: Matrix] {
  no m.vals[Int][Int] & Neighbors
}

// Concrete level: a coarray is a sequence of matrix images

sig Coarray {
  mseq: seq Matrix
}

-- coarrays have at least one image, and they all have the same
-- the number of images (basic Coarray Fortran semantics)
fact numImages {
  all a: Coarray | #a.mseq > 0 and all b: Coarray | #a.mseq = #b.mseq
}

fact ConcreteInv { all c: Coarray | Inv[c] }

-- concrete invariant: enforce uniform shape of all images and
-- overlapping columns at the interfaces for border exchanges.
pred Inv [c: Coarray] {
  all disj a, b: c.mseq.elems | sameShape[a, b]
  all i: allRows[c], q, p: c.mseq.inds |
    let Lc = lastCol[c] {
      -- if q is left of p, last column of q is the second column of p
      q = minus[p, 1] =>
        c.mseq[q].vals[i, Lc] = c.mseq[p].vals[i, 1]
      -- if q is right of p, first column of q is next to last column of p
      q = plus[p, 1] =>
        c.mseq[q].vals[i, 0] = c.mseq[p].vals[i, minus[Lc, 1]]
    }
}

-- abstraction relation (alpha)
pred alpha [c: Coarray, m: Matrix] {
  totRows[c, m.rows]
  totCols[c, m.cols]
  all i: range[m.rows], j: range[m.cols] {
    -- 1st column of m is the 1st column of the 1st image of c
    j = 0 => m.vals[i, j] = c.mseq[0].vals[i, 0]

    -- last column of m is the last column of the last image of c
    j = lastCol[m] =>
      let mi = sub[#c.mseq, 1],      -- matrix index
          ci = lastCol[c.mseq[mi]] | -- column index
        m.vals[i, j] = c.mseq[mi].vals[i, ci]

    -- mapping of middle image columns
    j != 0 and j != lastCol[m] =>
      let mi = div[sub[j, 1], sub[c.mseq[0].cols, 2]],
          ci = add[1, rem[sub[j, 1], sub[c.mseq[0].cols, 2]]] |
        m.vals[i, j] = c.mseq[mi].vals[i, ci] }
}

-- number of rows (every image has the same number of rows)
pred totRows [c: Coarray, r: Int] {
  r = c.mseq[0].rows
}

-- number of matrix columns when coarray images are combined
pred totCols [c: Coarray, m: Int] {
  rel[m, c.mseq[0].cols, #c.mseq]
}

// rel: relationship between the number of abstract matrix columns,
//      coarray matrix columns, and images

// a: number of columns in the abstract matrix
// c: number of columns in EACH coarray matrix
// i: number of images

pred rel [a, c, i: Int] {
  a >= 0 and c >= 0 and i > 0
  a < 4 => c = a and i = 1
  a >= 4 => a = add[mul[i, sub[c, 2]], 2] // arranged to minimize int size
}

-- A step in a Jacobi iteration (concrete, predicate 2 from Martin)
pred JacobiStep [u, v: Coarray] {
  sameShape[u, v]
  all i: allRows[u], j: allCols[u], q, p: u.mseq.inds |
    let Lc = lastCol[u], Lr = lastRow[u] {
      -- start with simple matrices for now
      simpleMatrix[u.mseq[q]]

      -- COMPUTATION PHASE
      -- internal region: set non-boundary elements in v to neighbors in u
      -- top and bottom rows (except first and last cols):
      --   copy into v the elements from u
      q = p and j != 0 and j != Lc =>
       	 (i != 0 and i != Lr =>
	          v.mseq[q].vals[i, j] = neighbors[u.mseq[q], i, j]
	            else v.mseq[q].vals[i, j] = u.mseq[q].vals[i, j])
      -- first column of first image: copy into v the elements from u
      v.mseq[0].vals[i, 0] = u.mseq[0].vals[i, 0]
      -- last column of last image: copy into v the elements from u
      q = u.mseq.lastIdx => v.mseq[q].vals[i, Lc] = u.mseq[q].vals[i, Lc]

      -- COMMUNICATION PHASE
      -- if q is left of p, set last column of q to the second column of p
      q = minus[p, 1] and j = Lc =>
        v.mseq[q].vals[i, j] = v.mseq[p].vals[i, 1]
      -- if q is right of p, set first column of q to next to last column of p
      q = plus[p, 1] and j = 0 =>
        v.mseq[q].vals[i, j] = v.mseq[p].vals[i, minus[Lc, 1]]
    }
}

-- for iterating over columns of a coarray image
fun allCols [c: Coarray]: set Int {
  range[c.mseq[0].cols]
}

-- for iterating over rows of a coarray image
fun allRows [c: Coarray]: set Int {
  range[c.mseq[0].rows]
}

-- two coarrays have the same dimensions
pred sameShape [u, v: Coarray] {
  all i: range[#u.mseq] |
    u.mseq[i].rows = v.mseq[i].rows and u.mseq[i].cols = v.mseq[i].cols
}

-- two coarrays are equivalent
pred equivalent [u, v: Coarray] {
  sameShape[u, v]
  all i: u.mseq.inds | equivalent[u.mseq[i], v.mseq[i]]
}

-- index of last column of a coarray image
fun lastCol [c: Coarray]: one Int {
  { i: Int | i = minus[c.mseq[0].cols, 1] }
}

-- index of last row of a coarray image
fun lastRow [c:Coarray]: one Int {
  { i: Int | i = minus[c.mseq[0].rows, 1] }
}

// Generate some instances to look at

pred show2 {
  some U, V: Matrix, u, v: Coarray |
    relevant[v, V] and alpha[u, U] and alpha[v, V] and
      simpleMatrix[U] and JacobiStep[u, v] and JacobiStep[U, V]
}

run show2 for 2 Coarray, 7 Matrix, 4 Value

-- show only "interesting" coarray-matrix combinations
pred relevant [c: Coarray, m: Matrix] {
  #c.mseq >= 2
  m.cols >= 3
  m.rows >= 3
}

/*
default scope is 3 (except for integers, which have a default bitwidth of 4)

max integer for "n Int" = 2^(n-1) - 1

  n   max   min
 --   ---   ---
 10   511  -512
  9   255  -256
  8   127  -128
  7    63   -64
  6    31   -32
  5    15   -16
  4     7    -8   <- default
  3     3    -4
  2     1    -2
*/


