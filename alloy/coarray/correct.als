
-- correct: show that the refinement is correct (a safety check)

open jacobi

-- restrict coarray sizes to prevent overflow
fun CoarraySmall : set Coarray {	
  { c: Coarray | some m: Int | rel[m, c.mseq[0].cols, #c.mseq] }
}

assert correct {
  all c, c2: CoarraySmall, a, a2: Matrix |
    (alpha[c, a] and alpha[c2, a2] and JacobiStep[c, c2]) => JacobiStep[a, a2]
}

check correct for 7 but 4 Int

// using Lingeling on an M1 MacBook Air takes about 36 minutes

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
