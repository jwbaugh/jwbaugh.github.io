
-- adequacy: every abstract state must have a concrete counterpart

open jacobi

sig P {
  con: lone Coarray,
  abs: Matrix
}{
  (some con and abs.cols >= 4) => #con.mseq > 1  // multiple images
}

// the trivial case (with just one image that is identical to the
// abstract matrix) is uninteresting, so check abstract matrices that
// are large enough to have multiple images (above)

assert isAdequate { all p: P | alpha[p.con, p.abs] => some p.con }

check isAdequate for 7 but 1 P, 4 Int

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
