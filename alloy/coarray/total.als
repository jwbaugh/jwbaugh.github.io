
-- total: show that alpha is total

open jacobi

sig P {
  con: Coarray,
  abs: lone Matrix
}

assert isTotal { all p: P | alpha[p.con, p.abs] => some p.abs }

check isTotal for 7 but 1 P, 4 Int

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
