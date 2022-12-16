
-- functional: show that alpha is functional

open jacobi

-- restrict coarray sizes to prevent overflow
fun CoarraySmall : set Coarray {	
  { c: Coarray | some m: Int | rel[m, c.mseq[0].cols, #c.mseq] }
}

assert isFunctional {
  all a1, a2: Matrix, c: CoarraySmall |
    (alpha[c, a1] and alpha [c, a2]) => equivalent[a1, a2]
}

check isFunctional for 7 but 4 Int

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




