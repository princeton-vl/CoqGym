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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ----                          machine.v                        ----- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(* 
   This file describes the implementation of our powering algorithm:
*)
Require Import monoid.
Require Import Constants.

(*  Let us imagine an abstract machine for computing on the monoid (M,o,u)
  (see "monoid.v").
    This machine has a register X and a stack S.
*)


Inductive Instr : Set :=
  | MUL : Instr
  | SQR : Instr
  | PUSH : Instr
  | SWAP : Instr.       


(* sequences of instructions *)

Inductive Code : Set :=
  | End : Code
  | seq : Instr -> Code -> Code.


(* code appending *)

(*Recursive Definition app:Code->Code->Code:=
    End c' => c'
  | (seq i  c) c' => (seq i ( app c  c')).
*)

Fixpoint app (c : Code) : Code -> Code :=
  fun c' : Code => match c with
                   | End => c'
                   | seq i c => seq i (app c c')
                   end.

(* semantics *)
(*************)

Section Monoid.
 Variable M : Set.
 Variable MO : monoid M.
 Let uM := u _ MO.
 Let oM := o _ MO.


 Inductive Stack : Set :=
   | emptystack : Stack
   | push : M -> Stack -> Stack.

 Definition top (s : Stack) :=
   match s return M with
   | emptystack => uM
   | push m _ => m
   end.
 Definition pop (s : Stack) :=
   match s return Stack with
   | emptystack => emptystack
   | push _ r => r
   end.


(* configurations of the abstract machine *)
(******************************************)


 Record Config : Set := config {config_X : M; config_S : Stack}.


 Lemma Config_inv :
  forall (a a' : M) (s s' : Stack),
  a = a' -> s = s' -> config a s = config a' s'.
 (****************************************************************************)
 Proof.
  intros. rewrite H; rewrite H0; auto.
 Qed.
 
 Hint Resolve Config_inv: arith.




(* Operational semantics of the elementary instructions *)

 Definition Exec1 (c : Instr) (v : Config) : Config :=
   let (m, s) := v in
   match c with
   | MUL => config (oM m (top s)) (pop s) 
   | SQR => config (oM m m) s
   | PUSH => config m (push m s)
   | SWAP => config m (push (top (pop s)) (push (top s) (pop (pop s))))
   end.
 (****************************************************************)



(* Execution of a compound instruction *)


Fixpoint Exec (c : Code) : Config -> Config :=
  fun v : Config =>
  match c with
  | End => v
  | seq i c => Exec c (Exec1 i v)
  end.

 (****************************************)

 (* Semantics of code   appending *)
 (*********************************)

 Lemma Exec_app :
  forall (c c' : Code) (v : Config), Exec (app c c') v = Exec c' (Exec c v).
 (*******************************************************)
 Proof.
  simple induction c; simpl in |- *.
  auto.
  intros; rewrite H; auto. 
 Qed.

End Monoid.

