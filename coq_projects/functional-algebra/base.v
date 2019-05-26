(**
  This module defines functions and notations shared by all of the
  modules in this package.

  Copyright (C) 2018 Larry D. Lee Jr. <llee454@gmail.com>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

(**
  The following notations are introduced here
  to simplify sequences of algebraic rewrites
  which would otherwise be expressed as long
  sequences of eq_ind*.
*)

Notation "A || B @ X 'by' E"
  := (eq_ind_r (fun X => B) A E) (at level 40, left associativity).

Notation "A || B @ X 'by' <- H"
  := (eq_ind_r (fun X => B) A (eq_sym H)) (at level 40, left associativity).

(**
  The following notation can be used to define
  equality assertions. These are like unittests
  in that they check that a given expression
  reduces to a given value.
*)
Notation "A =:= B"
  := (eq_refl A : A = B) (at level 90).

(**
  Proves that every boolean value is either true
  or false.
*)
Definition bool_dec0
  :  forall b : bool, {b = true}+{b = false}
  := bool_rect
      (fun b => {b = true}+{b = false})
         (left (true = false) (eq_refl true))
         (right (false = true) (eq_refl false)).
