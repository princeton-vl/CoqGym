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

(* ---                           develop.v                              --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* 

  This file contains some important lemmas used in the "generation" module.
  It tells how to compose abstract machine code (with append) to build
  code for Call_M, Call_C and Call_K calls (see the module "spec")
*)

Require Import Constants.
Require Import monoid.
Require Import spec.
Require Import machine.
Require Import Wf_compl.
Require Import Plus.
Require Import Mult.
Require Import Lt.
Require Import Mult_compl.
Require Import euclid.
Require Import two_power.


(* A sequence for computing the cube of some m in M *)
Lemma M3 : gencode (Call_M three).
(******************************)
Proof.
 refine (gencode_intro _ (seq PUSH (seq SQR (seq MUL End))) _).
(*
 Realizer (seq PUSH (seq SQR (seq MUL End))).
 Program_all. 
*)
 constructor 1.
 simpl in |- *; unfold power, three in |- *; intros.
 rewrite (u_neutral_r M MO).
 rewrite <- (point_assoc M MO); auto with arith.
 Qed.




(* A sequence for computing the (2^q)-th power of some m in M;
 this is a sequence of q SQRs  *)



Lemma M2q : forall q : nat, gencode (Call_M (two_power q)).
(**********************************************)
Proof.
 refine
  (let t := fun q : nat => gencode (Call_M (two_power q)) in
   (fix M2q (q : nat) : t q :=
      match q as x return (t x) with
      | O => gencode_intro _ End _
      | S p =>
          match M2q p with
          | gencode_intro c s => gencode_intro _ (seq SQR c) _
          end
      end)).
(* 
 Realizer [q:nat]<Code>Match q with End
                                    ([_,c:?](seq SQR c))
                                    end.
 Program_all.
*)
 constructor 1.
 unfold power in |- *; simpl in |- *.
 intros; rewrite (u_neutral_r M MO); auto with arith.
 constructor 1; auto with arith.
 intros; simpl in |- *.
 inversion_clear s.
 rewrite H.
 apply Config_inv; auto with arith.
 rewrite <- plus_n_O.
 apply a2x; auto with arith.
Qed.


(* code generation  for (Call_M p) from the code for (Call_C p q) 
   (it's the same!) *)

Lemma C2M : forall p q : nat, gencode (Call_C p q) -> gencode (Call_M p).
(****************************************)
Proof.
 refine
  (fun p q g => match g with
                | gencode_intro c s => gencode_intro _ c _
                end).
(*
 Realizer [p,q:nat][c:Code]c.
 Program_all.
*)
 constructor 1.
 inversion_clear s.
 auto with arith.
Qed.



(*  code generation for  (Call_C qp p) from the codes for (Call_M p) and (Call_M q)
    just append !                                                          *)
Lemma MMC :
 forall p q : nat,
 gencode (Call_M p) -> gencode (Call_M q) -> gencode (Call_C (q * p) p).
(***********************************************)
Proof.
 refine
  (fun p q g g' =>
   match g with
   | gencode_intro c s =>
       match g' with
       | gencode_intro c' s0 => gencode_intro _ (app c c') _
       end
   end).
(*
 Realizer [p,q:nat][c,c':Code](app c  c').
 Program_all.
*)
 constructor 2.
 intros; rewrite Exec_app.
 inversion_clear s.
 rewrite H.
 inversion_clear s0.
 rewrite (H0 M MO).
 rewrite power_mult; auto with arith.
Qed.


(* code generation for  (Call_C qp+r p) from cpr (code for (Call_K p r))
                                      and cq (code for (Call_M q))   
 (it's cpr, followed by cq then a MUL statement                       *)

Lemma KMC :
 forall p q r : nat,
 gencode (Call_K p r) -> gencode (Call_M q) -> gencode (Call_C (q * p + r) p).
(***********************************************************)
Proof.
 refine
  (fun p q r g g' =>
   match g with
   | gencode_intro cpr s =>
       match g' with
       | gencode_intro cq s0 =>
           gencode_intro _ (app cpr (app cq (seq MUL End))) _
       end
   end).
(*
 Realizer [p,q,r:nat][cpr,cq:Code](app cpr (app  cq (seq MUL   End))).
 Program_all.
*)
 inversion_clear s; inversion_clear s0.
 constructor 2.
 intros; rewrite Exec_app.
 rewrite (H M MO a).
 rewrite (Exec_app M MO); simpl in |- *; rewrite H0.
 simpl in |- *.
 apply Config_inv.
 rewrite power_eucl; auto with arith.
 auto with arith.
Qed.


(* Code generation for (Call_K qp p) from cp (code for (Call_M p))
                                   and cq (code for (Call_M q))
   It's cp, followed by a PUSH, then cq                       *)

Lemma MMK :
 forall p q : nat,
 gencode (Call_M p) -> gencode (Call_M q) -> gencode (Call_K (q * p) p).
(**************************************************)
Proof.
 refine
  (fun p q g g' =>
   match g with
   | gencode_intro cp s =>
       match g' with
       | gencode_intro cq s0 => gencode_intro _ (app cp (seq PUSH cq)) _
       end
   end).
(* 
 Realizer [p,q:nat][cp,cq:Code](app cp  (seq PUSH  cq)).
 Program_all. 
*)
 inversion_clear s; inversion_clear s0.
 constructor 3.
 intros; rewrite Exec_app. 
 rewrite H; simpl in |- *.
 rewrite H0; simpl in |- *.
 apply Config_inv; auto with arith.
 rewrite <- power_mult; auto with arith.
Qed.


(* Code generation for (Call_K qp+r p) from kpr (code for (Call_K p r))
                                     and mq (code for (Call_M q))
  it's kpr, followed by a sequence (PUSH;SWAP), then mq and a MUL statement *)

Lemma KMK :
 forall p q r : nat,
 gencode (Call_K p r) -> gencode (Call_M q) -> gencode (Call_K (q * p + r) p).
(***********************************************************)
Proof.
  refine
   (fun p q r g g' =>
    match g with
    | gencode_intro kpr s =>
        match g' with
        | gencode_intro mq s0 =>
            gencode_intro _
              (app kpr (seq PUSH (seq SWAP (app mq (seq MUL End))))) _
        end
    end).
(*
 Realizer [p,q,r:nat][kpr,mq:Code]
    (app kpr  (seq PUSH (seq  SWAP  ( app mq  (seq MUL  End))))).
 Program_all.
*)
 inversion_clear s; inversion_clear s0.
 constructor 3.
 intros; rewrite Exec_app.
 rewrite H; simpl in |- *.
 rewrite Exec_app.
 rewrite H0; simpl in |- *. auto with arith.
 rewrite power_eucl; auto with arith.
Qed.







