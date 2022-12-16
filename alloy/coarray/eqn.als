
// eqn.als -- a predicate relating matrix, coarray, and image sizes

one sig Eqn {
  na, nc, ni: Int
}{
  rel[na, nc, ni]
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

pred show {
  Eqn.na = 11
}

run show for 3 but 5 Int

/*
  a    (i, c) possibilities
 ---  ----------------------
  0    (1, 0)
  1    (1, 1)
  2    (1, 2)
  3    (1, 3)
  4    (1, 4) (2, 3)
  5    (1, 5) (3, 3)
  6    (1, 6) (2, 4) (4, 3)
  7    (1, 7) (5, 3)
  8    (1, 8) (2, 5) (3, 4) (6, 3)
  9    (1, 9) (7, 3)
 10    (1, 10) (2, 6) (4, 4) (8, 3)
 11    (1, 11) (3, 5) (9, 3)
*/

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

