(**
  This module defines basic properties for functions.

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

(** Defines the injective predicate. *)
Definition is_injective (A B : Type) (f : A -> B) : Prop
  := forall x y : A, f x = f y -> x = y.

(** Defines the onto predicate. *)
Definition is_onto (A B : Type) (f : A -> B) : Prop
  := forall y : B, exists x : A, f x = y.

(** Defines the bijective predicate. *)
Definition is_bijective (A B : Type) (f : A -> B) : Prop
  := is_injective A B f /\ is_onto A B f.
