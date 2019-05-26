From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import List.

Inductive Bar :=
| Bar0 : Bar
| Bar1 : nat -> Bar
| Bar2 : Bar -> Bar -> Bar.

Derive (Show, Arbitrary, Sized) for Bar.
Derive CanonicalSized for Bar.

Derive SizeMonotonic for Bar using GenSizedBar.
Derive SizedMonotonic for Bar using GenSizedBar.
Derive SizedCorrect for Bar using GenSizedBar and SizeMonotonicBar.


