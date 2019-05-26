(* Copyright (C) 2005-2008 Sebastien Briais *)
(* http://lamp.epfl.ch/~sbriais/ *)

(* This library is free software; you can redistribute it and/or modify *)
(* it under the terms of the GNU Lesser General Public License as *)
(* published by the Free Software Foundation; either version 2.1 of the *)
(* License, or (at your option) any later version. *)

(* This library is distributed in the hope that it will be useful, but *)
(* WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA *)
(* 02110-1301 USA *)

Require Import Bool.

Ltac and_elim :=
match goal with
  | [H:_ /\ _ |- _ ] => elim H;clear H;intro H;intro;and_elim
  | _ => idtac
end.

Ltac andb_elim :=
match goal with
  | [H:andb _ _ = true |- _ ] => elim (andb_prop _ _ H);clear H;intro H;intro;and_elim
  | _ => idtac
end.

Ltac ex_elim H x := elim H;clear H;intro x;intro H;and_elim.

Ltac or_elim H := (case H;clear H;intro H;[idtac | or_elim H]) || idtac.

Ltac clear_all := 
  match goal with
    | [id:_ |- _] => clear id;clear_all
    | [ |- _] => idtac
  end.

Require Import Arith.
Require Import Omega.

Ltac try_absurd_arith := try (elim (lt_irrefl 0);omega).
