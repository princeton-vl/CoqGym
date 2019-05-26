(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

Set Asymmetric Patterns.

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                               compile_ml.v                               *)
(****************************************************************************)

Variable OP : Set.

Definition Pat := nat.

Inductive MLexp : Set :=
  | Bool : bool -> MLexp
  | Num : nat -> MLexp
  | op : OP -> MLexp
  | id : Pat -> MLexp
  | appl : MLexp -> MLexp -> MLexp
  | mlpair : MLexp -> MLexp -> MLexp
  | lambda : Pat -> MLexp -> MLexp
  | let' : Pat -> MLexp -> MLexp -> MLexp
  | letrec : Pat -> Pat -> MLexp -> MLexp -> MLexp
  | ite : MLexp -> MLexp -> MLexp -> MLexp.

Inductive Value : Set :=
  | null : Value
  | elem : bool -> Value
  | int : nat -> Value
  | def_op : OP -> Value.

Inductive Commande : Set :=
  | quote : Value -> Commande
  | car : Commande
  | cdr : Commande
  | cons : Commande
  | push : Commande
  | swap : Commande
  | branch : Commande -> Commande -> Commande
  | cur : Commande -> Commande
  | cur_rec : Commande -> Commande
  | app : Commande
  | o : Commande -> Commande -> Commande.

Inductive Squelette : Set :=
  | nil_squelette : Squelette
  | cons_squelette : Pat -> Squelette -> Squelette.

Inductive Access : Pat -> Squelette -> Commande -> Prop :=
  | Rule1 :
      forall (P : Pat) (s : Squelette), Access P (cons_squelette P s) cdr
  | Rule2 :
      forall (P T : Pat) (s : Squelette) (C : Commande),
      P <> T :>Pat -> Access P s C -> Access P (cons_squelette T s) (o car C).

Inductive Traduction : Squelette -> MLexp -> Commande -> Prop :=
  | Bool_Trad :
      forall (b : bool) (S : Squelette),
      Traduction S (Bool b) (quote (elem b))
  | Trad_num :
      forall (n : nat) (S : Squelette), Traduction S (Num n) (quote (int n))
  | Trad_clos :
      forall (c : OP) (S : Squelette), Traduction S (op c) (quote (def_op c))
  | Trad_var :
      forall (p : Pat) (S : Squelette) (C : Commande),
      Access p S C -> Traduction S (id p) C
  | Trad_ite :
      forall (S : Squelette) (E1 E2 E3 : MLexp) (C1 C2 C3 : Commande),
      Traduction S E1 C1 ->
      Traduction S E2 C2 ->
      Traduction S E3 C3 ->
      Traduction S (ite E1 E2 E3) (o push (o C1 (branch C2 C3)))
  | Trad_pair :
      forall (S : Squelette) (E1 E2 : MLexp) (C1 C2 : Commande),
      Traduction S E1 C1 ->
      Traduction S E2 C2 ->
      Traduction S (mlpair E1 E2) (o push (o C1 (o swap (o C2 cons))))
  | Trad_app :
      forall (S : Squelette) (E1 E2 : MLexp) (C1 C2 : Commande),
      Traduction S E1 C1 ->
      Traduction S E2 C2 ->
      Traduction S (appl E1 E2) (o push (o C1 (o swap (o C2 (o cons app)))))
  | Trad_let :
      forall (p : Pat) (S : Squelette) (E1 E2 : MLexp) (C1 C2 : Commande),
      Traduction S E1 C1 ->
      Traduction (cons_squelette p S) E2 C2 ->
      Traduction S (let' p E1 E2) (o push (o C1 (o cons C2)))
  | Trad_let_rec :
      forall (p x : Pat) (S : Squelette) (E E2 : MLexp) (C C2 : Commande),
      Traduction (cons_squelette x (cons_squelette p S)) E C ->
      Traduction (cons_squelette p S) E2 C2 ->
      Traduction S (letrec p x E E2) (o push (o (cur_rec C) (o cons C2)))
  | Trad_lambda :
      forall (S : Squelette) (p : Pat) (E : MLexp) (C : Commande),
      Traduction (cons_squelette p S) E C ->
      Traduction S (lambda p E) (cur C). 

Definition two := lambda 0 (lambda 1 (appl (id 1) (appl (id 1) (id 0)))).

Definition compile_two : {c : Commande | Traduction nil_squelette two c}.
Proof.
unfold two in |- *.
eapply exist.
prolog
 [ Bool_Trad Trad_num Trad_clos Trad_var Trad_ite Trad_pair Trad_app Trad_let
  Trad_let_rec Trad_lambda Rule1 Rule2 cons_squelette nil_squelette O_S ] 10. 
Defined.
(* Transparent compile_two. ne fonctionne pas a la compilation *)

(*
Compute (<Commande>Case compile_two
                       of [c:Commande][h:(Traduction nil_squelette two c)]c end).
*)


Eval compute in match compile_two with
                | exist c _ => c
                end.