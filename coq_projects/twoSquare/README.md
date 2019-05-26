# Two Square

A proof of Fermat's theorem on sum of two squares.
It is the proof that uses gaussian integers. This is done in ssreflect.
It contains two file :

================================

gauss_int.v : the definition of gaussian integers

fermar2.v : the proof of Fermat's theorem

================================

The final statement reads:

From mathcomp.contrib.sum_of_two_square
Require Import fermat2.

Check sum2stest.

sum2stest :

  reflect
  (forall p,  prime p -> odd p -> p %| n -> odd (logn p n) -> p %% 4 = 1)
  (n \is a sum_of_two_square).



