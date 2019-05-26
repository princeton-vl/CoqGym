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

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  Mini_ML.v                                                               *)
(*                                                                          *)
(*  This file contains the definitions of the Mini-ML and the               *)
(*  Categorical Abstract Machine (C.A.M) natural semantics                  *)
(*  It also contains the definition of the translation from                 *)
(*  Mini-ML to the CAM and the proof that this translation is               *)
(*  correct                                                                 *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  December  1994                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                Mini_ML.v                                 *)
(****************************************************************************)

(*****************************************************************************)
(*                CORRECTNESS PROOF OF A MINI_ML COMPILER                    *)
(*                             Samuel Boutin                                 *)
(*                             December 1994                                 *)
(*                              Coql  V5.10                                  *)
(*****************************************************************************)

(*****************************************************************************)
(* First we define a Set "OP" of variable which is a representation of the   *)
(* arithmetic functions *,+,-... that we will not describe explicitely       *)
(* We take the natural numbers to code the variables (but of course it has no*)
(* relation with the De bruijn indexes)                                      *)
(*****************************************************************************)

Parameter OP : Set.

Parameter eval_op : OP -> nat -> nat -> nat.

Definition Pat := nat.

(*****************************************************************************)
(*              Defining the syntax of ML expressions                        *)
(*****************************************************************************)

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

(*****************************************************************************)
(*     ML values and environment are defined with the following mutual       *)
(*     recursive definition                                                  *)
(*****************************************************************************)

Inductive MLval : Set :=
  | num : nat -> MLval
  | boolean : bool -> MLval
  | valpair : MLval -> MLval -> MLval
  | OP_clos : OP -> MLval
  | Clos : Pat -> MLexp -> MLenv -> MLval
  | Clos_rec : Pat -> MLexp -> Pat -> MLenv -> MLval
with MLenv : Set :=
  | Enil : MLenv
  | Econs : Pat -> MLval -> MLenv -> MLenv.


(*****************************************************************************)
(* Definition of VAL_OF which decide if a variable belongs to an environment *)
(*****************************************************************************)

Inductive VAL_OF : MLenv -> Pat -> MLval -> Prop :=
  | ELT : forall (e : MLenv) (I : Pat) (a : MLval), VAL_OF (Econs I a e) I a
  | CHG :
      forall (e : MLenv) (X I : Pat) (a b : MLval),
      VAL_OF e I a -> X <> I :>Pat -> VAL_OF (Econs X b e) I a.

(*****************************************************************************)
(*         The following lemma shows us that VAL_OF is deterministic         *)
(*****************************************************************************)

Lemma determ_VAL_OF :
 forall (e : MLenv) (i : Pat) (V V' : MLval),
 VAL_OF e i V' -> VAL_OF e i V -> V = V' :>MLval.

simple induction 1.
intros.
inversion_clear H0; auto.
elim H2; auto.
intros.
apply H1.
inversion H3.
elim H2.

exact H4.
auto.
(*
Injection H4.
Intros.
Try Rewrite <- H5.
Elim H9;Auto.
Intros;Auto.
*)
Qed.

(*****************************************************************************)
(*                   We define now the Mini-ML semantics                     *)
(*In this semantics we want to distinguish the places where application is   *)
(*used in a recursive scheme from the other places.                          *)
(*That's why we have a special rule for application in the case where the    *)
(*function applied has as value a recursive closure (this correspond in fact *)
(*to a test during application                                               *)
(*****************************************************************************)

Inductive ML_DS : MLenv -> MLexp -> MLval -> Prop :=
  | BOOL : forall (b : bool) (e : MLenv), ML_DS e (Bool b) (boolean b)
  | NUM : forall (n : nat) (e : MLenv), ML_DS e (Num n) (num n)
  | Sem_OP : forall (c : OP) (e : MLenv), ML_DS e (op c) (OP_clos c)
  | LAMBDA :
      forall (e : MLenv) (P : Pat) (E : MLexp),
      ML_DS e (lambda P E) (Clos P E e)
  | IDENT :
      forall (e : MLenv) (v : MLval) (I : Pat),
      VAL_OF e I v -> ML_DS e (id I) v
  | ITE1 :
      forall (e : MLenv) (E1 E2 E3 : MLexp) (v : MLval),
      ML_DS e E1 (boolean true) -> ML_DS e E2 v -> ML_DS e (ite E1 E2 E3) v
  | ITE2 :
      forall (e : MLenv) (E1 E2 E3 : MLexp) (v : MLval),
      ML_DS e E1 (boolean false) -> ML_DS e E3 v -> ML_DS e (ite E1 E2 E3) v
  | MLPAIR :
      forall (e : MLenv) (E1 E2 : MLexp) (u v : MLval),
      ML_DS e E1 u -> ML_DS e E2 v -> ML_DS e (mlpair E1 E2) (valpair u v)
  | APPml1 :
      forall (e e1 : MLenv) (P : Pat) (E E1 E2 : MLexp) (u v : MLval),
      ML_DS e E1 (Clos P E e1) ->
      ML_DS e E2 u -> ML_DS (Econs P u e1) E v -> ML_DS e (appl E1 E2) v
  | APPml2 :
      forall (e e1 : MLenv) (x P : Pat) (E E1 E2 : MLexp) (u v : MLval),
      ML_DS e E1 (Clos_rec x E P e1) ->
      ML_DS e E2 u ->
      ML_DS (Econs x u (Econs P (Clos_rec x E P e1) e1)) E v ->
      ML_DS e (appl E1 E2) v
  | APPml_op :
      forall (e : MLenv) (E1 E2 : MLexp) (n m : nat) (c : OP),
      ML_DS e E1 (OP_clos c) ->
      ML_DS e E2 (valpair (num n) (num m)) ->
      ML_DS e (appl E1 E2) (num (eval_op c n m))
  | Sem_let :
      forall (e : MLenv) (P : Pat) (E1 E2 : MLexp) (u v : MLval),
      ML_DS e E2 u -> ML_DS (Econs P u e) E1 v -> ML_DS e (let' P E2 E1) v
  | Sem_letrec :
      forall (e : MLenv) (P x : Pat) (E E2 : MLexp) (u : MLval),
      ML_DS (Econs P (Clos_rec x E P e) e) E2 u ->
      ML_DS e (letrec P x E E2) u.   


(*****************************************************************************)
(* This predicate can be seen as an injective partial function associating a *)
(*  value to an environment and an expression:                               *)
(*****************************************************************************)


Lemma ML_DS_determ :
 forall (e : MLenv) (E : MLexp) (V : MLval),
 ML_DS e E V -> forall V' : MLval, ML_DS e E V' -> V = V' :>MLval.


simple induction 1; intros.

inversion_clear H0; auto.
inversion_clear H0; auto.
inversion_clear H0; auto.
inversion_clear H0; auto.
inversion_clear H1; auto. apply (determ_VAL_OF e0 I); auto.

inversion_clear H4. exact (H3 V' H6).
cut (boolean true = boolean false).
intro HH; discriminate HH.
exact (H1 (boolean false) H5).

inversion_clear H4.
cut (boolean false = boolean true).
intro HH; discriminate HH.
exact (H1 (boolean true) H5).
exact (H3 V' H6).

inversion_clear H4.
elim (H1 u0 H5); elim (H3 v0 H6); trivial.

inversion_clear H6.
cut (Clos P E0 e1 = Clos P0 E3 e3).
intro HH; injection HH.
intros.
cut (u = u0).
intro.
apply H5.
try rewrite H6; try rewrite H10; try rewrite H11; try rewrite H12.
exact H9.
exact (H3 u0 H8).
exact (H1 (Clos P0 E3 e3) H7).
cut (Clos P E0 e1 = Clos_rec x E3 P0 e3).
intro HH; discriminate HH.
exact (H1 (Clos_rec x E3 P0 e3) H7).
cut (Clos P E0 e1 = OP_clos c).
intro HH; discriminate HH.
exact (H1 (OP_clos c) H7).

inversion_clear H6.
cut (Clos_rec x E0 P e1 = Clos P0 E3 e3).
intro HH; discriminate HH.
exact (H1 (Clos P0 E3 e3) H7).
cut (Clos_rec x E0 P e1 = Clos_rec x0 E3 P0 e3).
intro HH; injection HH.
cut (u = u0).
intros.
apply H5.
try rewrite H6; try rewrite H10; try rewrite H11; try rewrite H12;
 try rewrite H13.
exact H9.
exact (H3 u0 H8).
exact (H1 (Clos_rec x0 E3 P0 e3) H7).
cut (Clos_rec x E0 P e1 = OP_clos c).
intro HH; discriminate HH.
exact (H1 (OP_clos c) H7).

inversion_clear H4.
cut (OP_clos c = Clos P E0 e2).
intro HH; discriminate HH.
exact (H1 (Clos P E0 e2) H5).
cut (OP_clos c = Clos_rec x E0 P e2).
intro HH; discriminate HH.
exact (H1 (Clos_rec x E0 P e2) H5).
cut (valpair (num n) (num m) = valpair (num n0) (num m0)).
intro HH; injection HH.
intros.
cut (OP_clos c = OP_clos c0).
intro HH1; injection HH1.
intro.
try rewrite H4; try rewrite H7; try rewrite H8.
trivial.
exact (H1 (OP_clos c0) H5).
exact (H3 (valpair (num n0) (num m0)) H6).

inversion_clear H4.
cut (u = u0).
intro.
apply H3.
try rewrite H4.
exact H6.
exact (H1 u0 H5).

inversion_clear H2.
apply H1.
exact H3.

Qed.

(*****************************************************************************)
(*We present now the definitions that concerns the Categorical Abstract      *)
(*Machine. The Set Commande defines its syntax                               *)
(*****************************************************************************)

Inductive Value : Set :=
  | null : Value
  | elem : bool -> Value
  | int : nat -> Value
  | def_op : OP -> Value.

(*****************************************************************************)

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

(*****************************************************************************)

Inductive CSem_val : Set :=
  | val : Value -> CSem_val
  | Cam_pair : CSem_val -> CSem_val -> CSem_val
  | Cam_clos : Commande -> CSem_val -> CSem_val
  | Cam_clos_rec : Commande -> CSem_val -> CSem_val
  | Cam_nil : CSem_val.

(*****************************************************************************)

Inductive Etat : Set :=
  | nil : Etat
  | ETcons : CSem_val -> Etat -> Etat.
           
(*****************************************************************************)
(*               We provide now the Semantics of the CAM                     *)
(*****************************************************************************)


Inductive CAM_DS : Etat -> Commande -> Etat -> Prop :=
  | QUO :
      forall (s : Etat) (a : CSem_val) (b : Value),
      CAM_DS (ETcons a s) (quote b) (ETcons (val b) s)
  | CAR :
      forall (s : Etat) (a b : CSem_val),
      CAM_DS (ETcons (Cam_pair a b) s) car (ETcons a s)
  | CDR :
      forall (s : Etat) (a b : CSem_val),
      CAM_DS (ETcons (Cam_pair a b) s) cdr (ETcons b s)
  | CONS :
      forall (s : Etat) (a b : CSem_val),
      CAM_DS (ETcons b (ETcons a s)) cons (ETcons (Cam_pair a b) s)
  | PUSH :
      forall (s : Etat) (a : CSem_val),
      CAM_DS (ETcons a s) push (ETcons a (ETcons a s))
  | SWAP :
      forall (s : Etat) (a b : CSem_val),
      CAM_DS (ETcons a (ETcons b s)) swap (ETcons b (ETcons a s))
  | BRANCHT :
      forall (s s1 : Etat) (c1 c2 : Commande),
      CAM_DS s c1 s1 -> CAM_DS (ETcons (val (elem true)) s) (branch c1 c2) s1
  | BRANCHF :
      forall (s s2 : Etat) (c1 c2 : Commande),
      CAM_DS s c2 s2 ->
      CAM_DS (ETcons (val (elem false)) s) (branch c1 c2) s2
  | CUR :
      forall (s : Etat) (a : CSem_val) (c : Commande),
      CAM_DS (ETcons a s) (cur c) (ETcons (Cam_clos c a) s)
  | APPcam1 :
      forall (s s1 : Etat) (a b : CSem_val) (c : Commande),
      CAM_DS (ETcons (Cam_pair a b) s) c s1 ->
      CAM_DS (ETcons (Cam_pair (Cam_clos c a) b) s) app s1
  | APPcam2 :
      forall (s s1 : Etat) (a b : CSem_val) (c : Commande),
      CAM_DS (ETcons (Cam_pair (Cam_pair b (Cam_clos_rec c b)) a) s) c s1 ->
      CAM_DS (ETcons (Cam_pair (Cam_clos_rec c b) a) s) app s1
  | APPcam_op :
      forall (s : Etat) (n m : nat) (oper : OP),
      CAM_DS
        (ETcons
           (Cam_pair (val (def_op oper))
              (Cam_pair (val (int n)) (val (int m)))) s) app
        (ETcons (val (int (eval_op oper n m))) s)
  | CUR_REC :
      forall (s : Etat) (a : CSem_val) (c : Commande),
      CAM_DS (ETcons a s) (cur_rec c) (ETcons (Cam_clos_rec c a) s)
  | o_DS :
      forall (s s1 s2 : Etat) (c1 c2 : Commande),
      CAM_DS s c1 s1 -> CAM_DS s1 c2 s2 -> CAM_DS s (o c1 c2) s2.
             

(*****************************************************************************)
(*We now define the "Squelette"of an environment which is the intuitive      *)
(*corresponding list of Debruijn indexes of an environment                   *)
(*****************************************************************************)


Inductive Squelette : Set :=
  | nil_squelette : Squelette
  | cons_squelette : Pat -> Squelette -> Squelette.

(*****************************************************************************)

Inductive Habite : MLenv -> Squelette -> Prop :=
  | triv_habite : Habite Enil nil_squelette
  | cons_habite :
      forall (x : Pat) (u : MLval) (e : MLenv) (s : Squelette),
      Habite e s -> Habite (Econs x u e) (cons_squelette x s).

(*****************************************************************************)
(*                Habite is an injective w.r.t the Squelette argument        *)
(*****************************************************************************)

Lemma Habite_inject :
 forall (e : MLenv) (s1 s2 : Squelette),
 Habite e s1 -> Habite e s2 -> s1 = s2.

simple induction e.
intros.
inversion_clear H; inversion_clear H0; trivial.
intros.
inversion_clear H0; inversion_clear H1.
elim (H s s0 H2 H0); trivial.
Qed.

(*****************************************************************************)
(*  The Acces predicate is defined using the notion of Squelette             *)
(* It describes how to reach an identifier in an environment                 *)
(*****************************************************************************)

Inductive Access : Pat -> Squelette -> Commande -> Prop :=
  | Rule1 :
      forall (P : Pat) (s : Squelette), Access P (cons_squelette P s) cdr
  | Rule2 :
      forall (P T : Pat) (s : Squelette) (C : Commande),
      P <> T -> Access P s C -> Access P (cons_squelette T s) (o car C).

(*****************************************************************************)
(*   The following small lemma shows that Access is injective                *)
(*****************************************************************************)

Lemma Access_inject :
 forall (x : Pat) (s : Squelette) (C C' : Commande),
 Access x s C' -> Access x s C -> C = C' :>Commande.

intro.
simple induction s; intros.
inversion_clear H0.
simple inversion H0.
simple inversion H1.
elim H4; elim H7; trivial.
injection H8; injection H3.
intros.
elim H12.
try rewrite H7; try rewrite <- H2; try rewrite H6; try rewrite <- H11; auto.
try rewrite H4.
simple inversion H1.
intros.
elim H8.
injection H5; injection H3; intros.
try rewrite <- H2; try rewrite H11; try rewrite <- H13; auto.
try rewrite H7.
injection H8; injection H5.
intros HH1 HH2 HH3.
try rewrite HH1; try rewrite HH3.
try rewrite <- H6; try rewrite <- H9.
intros.
elim (H C1 C0 H12 H10).
trivial.
Qed.


(*****************************************************************************)

Lemma Squelet : forall e : MLenv, exists s : Squelette, Habite e s.

intro.
pattern e in |- *.
apply MLenv_ind.
exists nil_squelette.
exact triv_habite.
intros.
elim H; intro s; intro.
exists (cons_squelette p s).
exact (cons_habite p m m0 s H0).
Qed.

(*****************************************************************************)
(*It's now time to define the translation of ML code onto CAM code           *)
(*****************************************************************************)


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


(*****************************************************************************)
(* The Traduction Predicate can be seen as a partial injective function      *)
(* that given a state and an ML expression yields a CAM sentence:            *)
(*****************************************************************************)

Lemma Traduction_inject :
 forall (E : MLexp) (C C' : Commande) (s : Squelette),
 Traduction s E C -> Traduction s E C' -> C = C' :>Commande.



simple induction E; intros.

inversion_clear H.
inversion_clear H0.
trivial.

inversion_clear H.
inversion_clear H0.
trivial.

inversion_clear H.
inversion_clear H0.
trivial.

inversion_clear H.
inversion_clear H0.
exact (Access_inject p s C C' H H1).

inversion_clear H1.
inversion_clear H2.
elim (H C1 C0 s H3 H1).
elim (H0 C2 C3 s H4 H5).
trivial.

inversion_clear H1.
inversion_clear H2.
elim (H C1 C0 s H3 H1).
elim (H0 C2 C3 s H4 H5).
trivial.

inversion_clear H0.
inversion_clear H1.
elim (H C0 C1 (cons_squelette p s) H2 H0).
trivial.

inversion_clear H1.
inversion_clear H2.
elim (H C1 C0 s H3 H1).
elim (H0 C2 C3 (cons_squelette p s) H4 H5).
trivial.

inversion_clear H1.
inversion_clear H2.
elim (H C0 C1 (cons_squelette p0 (cons_squelette p s)) H3 H1).
elim (H0 C2 C3 (cons_squelette p s) H4 H5).
trivial.

inversion_clear H2.
inversion_clear H3.
elim (H C1 C0 s H4 H2).
elim (H0 C2 C4 s H5 H7).
elim (H1 C3 C5 s H6 H8).
trivial.

Qed.


(*****************************************************************************)
(*We can now define an equivalence between ML values and CAM values with the *)
(*the help of the predicate Traduction                                       *)
(*****************************************************************************)


Inductive Equiv_val : MLval -> CSem_val -> Prop :=
  | Eqbool : forall b : bool, Equiv_val (boolean b) (val (elem b))
  | Eqnum : forall n : nat, Equiv_val (num n) (val (int n))
  | Eq_op : forall c : OP, Equiv_val (OP_clos c) (val (def_op c))
  | Eqpair :
      forall (V1 V2 : MLval) (Cval1 Cval2 : CSem_val),
      Equiv_val V1 Cval1 ->
      Equiv_val V2 Cval2 -> Equiv_val (valpair V1 V2) (Cam_pair Cval1 Cval2)
  | Eqclos :
      forall (p : Pat) (E : MLexp) (C : Commande) (e : MLenv) 
        (CV : CSem_val) (s : Squelette),
      Equiv_env e CV ->
      Habite e s ->
      Traduction (cons_squelette p s) E C ->
      Equiv_val (Clos p E e) (Cam_clos C CV)
  | Eqclos_rec :
      forall (p x : Pat) (E : MLexp) (e : MLenv) (C : Commande)
        (CV : CSem_val) (s : Squelette),
      Equiv_env e CV ->
      Habite e s ->
      Traduction (cons_squelette x (cons_squelette p s)) E C ->
      Equiv_val (Clos_rec x E p e) (Cam_clos_rec C CV)
with Equiv_env : MLenv -> CSem_val -> Prop :=
  | Eqenv1 : Equiv_env Enil Cam_nil
  | Eqenv2 :
      forall (p : Pat) (E : MLenv) (CV0 : CSem_val),
      Equiv_env E CV0 ->
      forall (V : MLval) (CV : CSem_val),
      Equiv_val V CV -> Equiv_env (Econs p V E) (Cam_pair CV0 CV).



(*****************************************************************************)
(*                 We can now give a formulation of the proof                *)
(*****************************************************************************)

Inductive compilation (E : MLexp) : Prop :=
    preuve_compilation :
      (forall (e : MLenv) (V : MLval),
       ML_DS e E V ->
       forall (s : Squelette) (C : Commande),
       Traduction s E C ->
       Habite e s ->
       forall CV : CSem_val,
       Equiv_env e CV ->
       exists CV1 : CSem_val,
         Equiv_val V CV1 /\
         (forall s : Etat, CAM_DS (ETcons CV s) C (ETcons CV1 s))) ->
      compilation E.
                 



(*****************************************************************************)
(*This formulation permits us to make the proof for the different cases      *)
(*       where we don't need induction assumptions.                          *)
(*****************************************************************************)


(*****************************************************************************)
(*                  Case where E is a boolean                                *)
(*****************************************************************************)

Lemma Proof_bool : forall b : bool, compilation (Bool b).


intro b.
apply preuve_compilation.
intros e V ML_b s C Trad_b hab CV Eq.
inversion_clear ML_b.
exists (val (elem b)).
split.
exact (Eqbool b).
inversion_clear Trad_b.
intro s0.
exact (QUO s0 CV (elem b)).
Qed.

(*****************************************************************************)
(*                  Case where E is an integer                               *)
(*****************************************************************************)

Lemma Proof_int : forall n : nat, compilation (Num n).

intro n.
apply preuve_compilation.
intros e V ML_n s C Trad_n hab CV Eq.
inversion_clear ML_n.
exists (val (int n)).
split.
exact (Eqnum n).
inversion_clear Trad_n.
intro s0.
exact (QUO s0 CV (int n)).
Qed.

(*****************************************************************************)
(*               Case where E is a predefinite operator                      *)
(*****************************************************************************)


Lemma Proof_op : forall c : OP, compilation (op c).


intro c.
apply preuve_compilation.
intros e V ML_c s C Trad_c hab CV Eq.
inversion_clear ML_c.
exists (val (def_op c)).
split.
exact (Eq_op c).
inversion_clear Trad_c.
intro s0.
exact (QUO s0 CV (def_op c)).
Qed.

(*****************************************************************************)
(*                    Case where E is an identifier                          *)
(* This case is special in the sens that we cannot use the predicate         *)
(*compilation because the variables of the formulation must be introduced    *)
(* in a very precise order.                                                  *)
(* Of course we could avoid a new definition using a the Cut tactic          *)
(* The point is that in this case only we must first do an induction on the  *)
(* ML environment in which we evaluate our expression (an identifier!)       *)
(*****************************************************************************)


Inductive compilation_id (E : MLexp) : Prop :=
    preuve_compilation_id :
      (forall (e : MLenv) (s : Squelette),
       Habite e s ->
       forall V : MLval,
       ML_DS e E V ->
       forall C : Commande,
       Traduction s E C ->
       forall CV : CSem_val,
       Equiv_env e CV ->
       exists CV1 : CSem_val,
         Equiv_val V CV1 /\
         (forall s : Etat, CAM_DS (ETcons CV s) C (ETcons CV1 s))) ->
      compilation_id E.


Lemma Proof_ident : forall x : Pat, compilation_id (id x).

intro.
apply preuve_compilation_id.
simple induction e.
intros.
inversion_clear H0.
inversion_clear H3.
do 6 intro.
inversion_clear H0.
intro; intro.
inversion_clear H0.
simple inversion H2.
injection H0; do 3 intro.
try rewrite <- H3; try rewrite H7.
do 2 intro.
inversion_clear H8.
inversion_clear H9.
do 2 intro.
inversion_clear H8.
try rewrite <- H4; try rewrite H6.
exists CV1.
split.
exact H10.
intro; apply CDR.

elim H8; trivial.
injection H4; do 3 intro.
try rewrite H5; try rewrite H7; try rewrite H6; try rewrite H0.
do 4 intro.
inversion_clear H10.

simple inversion H11.
injection H12; try rewrite H10; do 2 intro.
elim H9; elim H15; auto.

try rewrite H13; injection H14; do 2 intro; try rewrite H12; try rewrite H10.
try rewrite <- H15.
do 4 intro.
inversion_clear H18.
cut (ML_DS m0 (id x) V).
cut (Traduction s0 (id x) C0).
intros Hyp_Trad Hyp_ML.
elim (H s0 H1 V Hyp_ML C0 Hyp_Trad CV0 H19).
do 2 intro.
elim H18; do 2 intro.
exists x0.
split.
exact H21.
intro.
apply
 (o_DS (ETcons (Cam_pair CV0 CV1) s2) (ETcons CV0 s2) (ETcons x0 s2) car C0).
apply CAR.
exact (H22 s2).
apply Trad_var.
exact H17.
apply IDENT.
exact H8.

Qed.




(*****************************************************************************)
(*                     Case where E is an abstraction                        *)
(*****************************************************************************)


Lemma Proof_abstraction :
 forall (E : MLexp) (p : Pat), compilation (lambda p E).

intros E p.
apply preuve_compilation.
intros e V ML_lambda.
inversion_clear ML_lambda.
intros s C Trad_lam.
inversion_clear Trad_lam.
intros hab CV Eq_e_CV.
exists (Cam_clos C0 CV).
split.
apply (Eqclos p E C0 e CV s Eq_e_CV hab H).
intro.
apply CUR.

Qed.

(*****************************************************************************)
(*          We have now all the tools we need to make the proof              *)
(* We want to prove that the following diagram commutes:                     *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                           "Traduction"                                    *)
(*         Mini_ML terms ---------------------> CAM terms                    *)
(*             |                                  |                          *)
(*             |                                  |                          *)
(*             |                                  |                          *)
(*             |                                  |                          *)
(*      "ML_DS"|                                  |"CAM_DS"                  *)
(*             |                                  |                          *)
(*             |                                  |                          *)
(*             |                                  |                          *)
(*             V              "Equiv"             V                          *)
(*      Mini_ML values ---------------------> CAM values                     *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* This means that having an MLexp E its ML value and its translation onto   *)
(*CAM code we can find a  CAM value such that the diagram commutes           *)
(*                                                                           *)
(*      The proof is made by induction on the Predicate ML_DS.               *)
(*****************************************************************************)
    
Lemma final_proof :
 forall (E : MLexp) (e : MLenv) (V : MLval),
 ML_DS e E V ->
 forall (s : Squelette) (C : Commande),
 Traduction s E C ->
 Habite e s ->
 forall V : MLval,
 ML_DS e E V ->
 forall CV : CSem_val,
 Equiv_env e CV ->
 exists CV1 : CSem_val,
   Equiv_val V CV1 /\
   (forall s : Etat, CAM_DS (ETcons CV s) C (ETcons CV1 s)).

intros E e V.
simple induction 1.

(*****************************************************************************)
(*                Simple cases have already been treated                     *)
(*****************************************************************************)

intros b e0 s C Trad_b hab V0 ML_b CV Eq.
cut (compilation (Bool b)).
2: exact (Proof_bool b).
intro comp.
elim comp; intro hyp.
exact (hyp e0 V0 ML_b s C Trad_b hab CV Eq).

intros n e0 s C Trad_int hab V0 ML_int CV Eq.
cut (compilation (Num n)).
2: exact (Proof_int n).
intro comp.
elim comp; intro hyp.
exact (hyp e0 V0 ML_int s C Trad_int hab CV Eq).

intros c e0 s C Trad_op hab V0 ML_op CV Eq.
cut (compilation (op c)).
2: exact (Proof_op c).
intro comp.
elim comp; intro hyp.
exact (hyp e0 V0 ML_op s C Trad_op hab CV Eq).

intros e0 P E0 s C Trad_lam hab V0 ML_lambda CV Eq.
cut (compilation (lambda P E0)).
2: exact (Proof_abstraction E0 P).
intro comp.
elim comp; intro hyp.
exact (hyp e0 V0 ML_lambda s C Trad_lam hab CV Eq).

intros e0 v I VAL_I s C Trad_pat hab V0 ML_pat CV Eq.
cut (compilation_id (id I)).
2: exact (Proof_ident I).
intro comp.
elim comp; intro hyp.
exact (hyp e0 s hab V0 ML_pat C Trad_pat CV Eq).


(*****************************************************************************)
(*We have now to treat the cases where "compilation" cannot be used          *)
(*****************************************************************************)


(*****************************************************************************)
(*                       Case of the " if then else"                         *)
(*****************************************************************************)


                     (*   Case where E1 evaluates to true    *)


intros e0 E1 E2 E3 v ML_E1 hyp_E1 ML_E2 hyp_E2 s C Trad_if.
inversion_clear Trad_if.
intros hab V_final ML_DS_if. 
inversion_clear ML_DS_if.
intros CV0 eq_e0_CV0.
elim (hyp_E2 s C2 H1 hab V_final H4 CV0 eq_e0_CV0).
intros CV_final HH; elim HH.
intros Eq_Vf_CVf CAM_C2.
exists CV_final.
split.
exact Eq_Vf_CVf.
intro s0.
cut
 (CAM_DS (ETcons CV0 (ETcons CV0 s0)) (o C1 (branch C2 C3))
    (ETcons CV_final s0)).
cut (CAM_DS (ETcons CV0 s0) push (ETcons CV0 (ETcons CV0 s0))).
exact
 (o_DS (ETcons CV0 s0) (ETcons CV0 (ETcons CV0 s0)) 
    (ETcons CV_final s0) push (o C1 (branch C2 C3))).
exact (PUSH s0 CV0).
elim (hyp_E1 s C1 H0 hab (boolean true) ML_E1 CV0 eq_e0_CV0).
intros CV1 HH'; elim HH'.
intro Eq_1; inversion_clear Eq_1.
intro CAM_C1.
apply
 (o_DS (ETcons CV0 (ETcons CV0 s0))
    (ETcons (val (elem true)) (ETcons CV0 s0)) (ETcons CV_final s0) C1
    (branch C2 C3)).
exact (CAM_C1 (ETcons CV0 s0)).
apply (BRANCHT (ETcons CV0 s0) (ETcons CV_final s0) C2 C3).
exact (CAM_C2 s0).
cut (boolean false = boolean true).
intro HH.
discriminate HH.
exact (ML_DS_determ e0 E1 (boolean false) H3 (boolean true) ML_E1).


               (*   Case where E1 evaluates to false    *)


intros e0 E1 E2 E3 v ML_E1 hyp_E1 ML_E3 hyp_E3 s C Trad_if.
inversion_clear Trad_if.
intros hab V_final ML_DS_if. 
inversion_clear ML_DS_if.
cut (boolean false = boolean true).
intro HH.
discriminate HH.
exact (ML_DS_determ e0 E1 (boolean false) ML_E1 (boolean true) H3).
intros CV0 eq_e0_CV0.
elim (hyp_E3 s C3 H2 hab V_final H4 CV0 eq_e0_CV0).
intros CV_final HH; elim HH.
intros Eq_Vf_CVf CAM_C3.
exists CV_final.
split.
exact Eq_Vf_CVf.
intro s0.
cut
 (CAM_DS (ETcons CV0 (ETcons CV0 s0)) (o C1 (branch C2 C3))
    (ETcons CV_final s0)).
cut (CAM_DS (ETcons CV0 s0) push (ETcons CV0 (ETcons CV0 s0))).
exact
 (o_DS (ETcons CV0 s0) (ETcons CV0 (ETcons CV0 s0)) 
    (ETcons CV_final s0) push (o C1 (branch C2 C3))).
exact (PUSH s0 CV0).
elim (hyp_E1 s C1 H0 hab (boolean false) ML_E1 CV0 eq_e0_CV0).
intros CV1 HH'; elim HH'.
intro Eq_1; inversion_clear Eq_1.
intro CAM_C1.
apply
 (o_DS (ETcons CV0 (ETcons CV0 s0))
    (ETcons (val (elem false)) (ETcons CV0 s0)) (ETcons CV_final s0) C1
    (branch C2 C3)).
exact (CAM_C1 (ETcons CV0 s0)).
apply (BRANCHF (ETcons CV0 s0) (ETcons CV_final s0) C2 C3).
exact (CAM_C3 s0).


(*****************************************************************************)
(*                            the pair case                                  *)
(*****************************************************************************)


intros e0 E1 E2 u v ML_E1 hyp_E1 ML_E2 hyp_E2 s C Trad_p.
inversion_clear Trad_p.
intros hab V_final ML_DS_pair.
inversion_clear ML_DS_pair.
intros CV0 eq_e0_CV0.
elim (hyp_E1 s C1 H0 hab u0 H2 CV0 eq_e0_CV0).
intros CV_E1 HH; elim HH.
intros eq_u0_CV_E1 CAM_C1.
elim (hyp_E2 s C2 H1 hab v0 H3 CV0 eq_e0_CV0).
intros CV_E2 HH'; elim HH'.
intros eq_v0_CV_E2 CAM_C2.
exists (Cam_pair CV_E1 CV_E2).
split.
apply (Eqpair u0 v0 CV_E1 CV_E2 eq_u0_CV_E1 eq_v0_CV_E2).
intro s0.
apply
 (o_DS (ETcons CV0 s0) (ETcons CV0 (ETcons CV0 s0))
    (ETcons (Cam_pair CV_E1 CV_E2) s0) push (o C1 (o swap (o C2 cons)))).
apply (PUSH s0 CV0).
apply
 (o_DS (ETcons CV0 (ETcons CV0 s0)) (ETcons CV_E1 (ETcons CV0 s0))
    (ETcons (Cam_pair CV_E1 CV_E2) s0) C1 (o swap (o C2 cons))).
apply CAM_C1.
apply
 (o_DS (ETcons CV_E1 (ETcons CV0 s0)) (ETcons CV0 (ETcons CV_E1 s0))
    (ETcons (Cam_pair CV_E1 CV_E2) s0) swap (o C2 cons)).
apply SWAP.
apply
 (o_DS (ETcons CV0 (ETcons CV_E1 s0)) (ETcons CV_E2 (ETcons CV_E1 s0))
    (ETcons (Cam_pair CV_E1 CV_E2) s0) C2 cons).
apply CAM_C2.
apply CONS.

(*****************************************************************************)
(*We have now to solve the case of the application (It is important to notice*)
(*that we were not able to make the proof on induction on E because of the   *)
(*application case                                                           *)
(*****************************************************************************)


intros e0 e1 P E0 E1 E2 u v ML_E1 hyp_E1 ML_E2 hyp_E2 ML_E0 hyp_E0 s C
 Trad_appl.
inversion_clear Trad_appl.
intros hab V0 ML_appl.
inversion_clear ML_appl.
cut (Clos P E0 e1 = Clos P0 E3 e3).
intro HH1; injection HH1.
intros eq1 eq2 eq3.
cut (u = u0).
intro eq4.
cut (ML_DS (Econs P0 u0 e3) E3 V0).
try rewrite <- eq1; try rewrite <- eq2; try rewrite <- eq3;
 try rewrite <- eq4.
intro HH2; cut (v = V0).
intro eq5; try rewrite <- eq5.
intros CV0 eq_e0_CV0.
elim (hyp_E2 s C2 H1 hab u ML_E2 CV0 eq_e0_CV0).
intros CVal_E2 HH3; elim HH3.
intros Eq_u_Cval_E2 CAM_C2.
elim (hyp_E1 s C1 H0 hab (Clos P E0 e1) ML_E1 CV0 eq_e0_CV0).
intros Closure HH4; elim HH4.
intro eq_clos.
inversion_clear eq_clos.
intro CAM_C1.
cut (Habite (Econs P u e1) (cons_squelette P s0)).
intro hab_P_e1.
cut (Equiv_env (Econs P u e1) (Cam_pair CV CVal_E2)).
intro eq_env_closure.
elim
 (hyp_E0 (cons_squelette P s0) C0 H7 hab_P_e1 v ML_E0 
    (Cam_pair CV CVal_E2) eq_env_closure).
intros CV_final HH5; elim HH5.
intros eq_v_CV_final CAM_C0.
exists CV_final.
split.
exact eq_v_CV_final. 
intro sq.
apply
 (o_DS (ETcons CV0 sq) (ETcons CV0 (ETcons CV0 sq)) 
    (ETcons CV_final sq) push (o C1 (o swap (o C2 (o cons app))))).
apply PUSH.
apply
 (o_DS (ETcons CV0 (ETcons CV0 sq)) (ETcons (Cam_clos C0 CV) (ETcons CV0 sq))
    (ETcons CV_final sq) C1 (o swap (o C2 (o cons app)))).
apply CAM_C1.
apply
 (o_DS (ETcons (Cam_clos C0 CV) (ETcons CV0 sq))
    (ETcons CV0 (ETcons (Cam_clos C0 CV) sq)) (ETcons CV_final sq) swap
    (o C2 (o cons app))).
apply SWAP.
apply
 (o_DS (ETcons CV0 (ETcons (Cam_clos C0 CV) sq))
    (ETcons CVal_E2 (ETcons (Cam_clos C0 CV) sq)) (ETcons CV_final sq) C2
    (o cons app)).
apply CAM_C2.
apply
 (o_DS (ETcons CVal_E2 (ETcons (Cam_clos C0 CV) sq))
    (ETcons (Cam_pair (Cam_clos C0 CV) CVal_E2) sq) 
    (ETcons CV_final sq) cons app).
apply CONS.
apply (APPcam1 sq (ETcons CV_final sq) CV CVal_E2 C0).
apply CAM_C0.
apply (Eqenv2 P e1 CV H5 u CVal_E2 Eq_u_Cval_E2).
apply (cons_habite P u e1 s0 H6).
apply (ML_DS_determ (Econs P u e1) E0 v ML_E0 V0 HH2).
exact H4.
apply (ML_DS_determ e0 E2 u ML_E2 u0 H3).
apply (ML_DS_determ e0 E1 (Clos P E0 e1) ML_E1 (Clos P0 E3 e3) H2).
cut (Clos P E0 e1 = Clos_rec x E3 P0 e3).
intro hyp_not; discriminate hyp_not.
apply (ML_DS_determ e0 E1 (Clos P E0 e1) ML_E1 (Clos_rec x E3 P0 e3) H2).
cut (Clos P E0 e1 = OP_clos c).
intro hyp_not; discriminate hyp_not.
apply (ML_DS_determ e0 E1 (Clos P E0 e1) ML_E1 (OP_clos c) H2).


(*****************************************************************************)
(*                         Case of a recursive closure                       *)
(*****************************************************************************)


intros e0 e1 x P E0 E1 E2 u v ML_E1 hyp_E1 ML_E2 hyp_E2 ML_E0 hyp_E0 s C
 Trad_appl.
inversion_clear Trad_appl.
intros hab V0 ML_app.
inversion_clear ML_app.
cut (Clos_rec x E0 P e1 = Clos P0 E3 e3). 
intro HH1; discriminate HH1.
apply (ML_DS_determ e0 E1 (Clos_rec x E0 P e1) ML_E1 (Clos P0 E3 e3) H2).
intros CV0 eq_e0_CV0.
cut (Clos_rec x E0 P e1 = Clos_rec x0 E3 P0 e3).
intro HH1; injection HH1.
intros eq1 eq2 eq3 eq4.
cut (ML_DS (Econs x0 u0 (Econs P0 (Clos_rec x0 E3 P0 e3) e3)) E3 V0).
try rewrite <- eq1; try rewrite <- eq2; try rewrite <- eq3;
 try rewrite <- eq4.
cut (u = u0).
intro eq5; try rewrite <- eq5.
intro ML_E0'.
cut (v = V0).
intro eq6; try rewrite <- eq6.
elim (hyp_E2 s C2 H1 hab u ML_E2 CV0 eq_e0_CV0).
intros CV_E2 HH3; elim HH3.
intros eq_u_CV_E2 CAM_C2.
elim (hyp_E1 s C1 H0 hab (Clos_rec x E0 P e1) ML_E1 CV0 eq_e0_CV0).
intros CV_E1 HH2; elim HH2.
intros eq_V1_CV_E1 CAM_C1.
simple inversion eq_V1_CV_E1.
discriminate H5.
discriminate H5.
discriminate H5.
discriminate H7.
discriminate H8.
injection H8.
intros eq7 eq8 eq9 eq10.
try rewrite eq7; try rewrite eq8; try rewrite eq9; try rewrite eq10.
intros.
cut
 (Habite (Econs x u (Econs P (Clos_rec x E0 P e1) e1))
    (cons_squelette x (cons_squelette P s0))).
intro hab0.
cut
 (Equiv_env (Econs x u (Econs P (Clos_rec x E0 P e1) e1))
    (Cam_pair (Cam_pair CV CV_E1) CV_E2)).
intro Eq_env0.
elim
 (hyp_E0 (cons_squelette x (cons_squelette P s0)) C0 H7 hab0 v ML_E0
    (Cam_pair (Cam_pair CV CV_E1) CV_E2) Eq_env0).

intros CV_E0 HH4; elim HH4.
intros eq_v_CV_E0 CAM_C0.
exists CV_E0.
split.
exact eq_v_CV_E0.
intro S.
apply
 (o_DS (ETcons CV0 S) (ETcons CV0 (ETcons CV0 S)) (ETcons CV_E0 S) push
    (o C1 (o swap (o C2 (o cons app))))).
apply PUSH.
apply
 (o_DS (ETcons CV0 (ETcons CV0 S)) (ETcons CV_E1 (ETcons CV0 S))
    (ETcons CV_E0 S) C1 (o swap (o C2 (o cons app)))).
apply CAM_C1.
apply
 (o_DS (ETcons CV_E1 (ETcons CV0 S)) (ETcons CV0 (ETcons CV_E1 S))
    (ETcons CV_E0 S) swap (o C2 (o cons app))).
apply SWAP.
apply
 (o_DS (ETcons CV0 (ETcons CV_E1 S)) (ETcons CV_E2 (ETcons CV_E1 S))
    (ETcons CV_E0 S) C2 (o cons app)).
apply CAM_C2.
apply
 (o_DS (ETcons CV_E2 (ETcons CV_E1 S)) (ETcons (Cam_pair CV_E1 CV_E2) S)
    (ETcons CV_E0 S) cons app).
apply CONS.
cut
 (forall s : Etat,
  CAM_DS (ETcons (Cam_pair (Cam_pair CV CV_E1) CV_E2) s) C0 (ETcons CV_E0 s)).
2: auto.
try rewrite <- H9.
intro Good_CAM_C0.
apply (APPcam2 S (ETcons CV_E0 S) CV_E2 CV C0 (Good_CAM_C0 S)).
apply Eqenv2; auto.
apply Eqenv2; auto.
apply cons_habite; auto.
apply cons_habite; auto.
apply
 (ML_DS_determ (Econs x u (Econs P (Clos_rec x E0 P e1) e1)) E0 v ML_E0 V0
    ML_E0').
apply (ML_DS_determ e0 E2 u ML_E2 u0 H3).
auto.
apply
 (ML_DS_determ e0 E1 (Clos_rec x E0 P e1) ML_E1 (Clos_rec x0 E3 P0 e3) H2).
cut (OP_clos c = Clos_rec x E0 P e1).
intro Hyp_false; discriminate Hyp_false.
apply (ML_DS_determ e0 E1 (OP_clos c) H2 (Clos_rec x E0 P e1) ML_E1). 

                             

(*****************************************************************************)
(*            Case where we apply a predefined operator                      *)
(*****************************************************************************)



intros e0 E1 E2 n m c ML_E1 hyp_E1 ML_E2 hyp_E2 s C Trad_appl.
inversion_clear Trad_appl.
intros hab V0 ML_appl.
inversion_clear ML_appl.
intros CV0 eq_e0_CV0.
cut (OP_clos c = Clos P E0 e2).
2: exact (ML_DS_determ e0 E1 (OP_clos c) ML_E1 (Clos P E0 e2) H2). 
intro HH; discriminate HH.
cut (OP_clos c = Clos_rec x E0 P e2).
2: exact (ML_DS_determ e0 E1 (OP_clos c) ML_E1 (Clos_rec x E0 P e2) H2). 
intro HH; discriminate HH.
cut (valpair (num n) (num m) = valpair (num n0) (num m0)).
2: exact
    (ML_DS_determ e0 E2 (valpair (num n) (num m)) ML_E2
       (valpair (num n0) (num m0)) H3).
intro HH; injection HH.
intros eq1 eq2.
cut (OP_clos c = OP_clos c0).
intro HH1; injection HH1.
intro eq3.
try rewrite <- eq1; try rewrite <- eq2; try rewrite <- eq3.
intros CV0 eq_e0_CV0.
elim (hyp_E1 s C1 H0 hab (OP_clos c) ML_E1 CV0 eq_e0_CV0).
intro HH2; elim HH2.
intros CV_c HH3.
elim HH3.
intros eq_c_CV_c CAM_C1.
elim (hyp_E2 s C2 H1 hab (valpair (num n) (num m)) ML_E2 CV0 eq_e0_CV0).
intros CV_nm HH4.
elim HH4.
intro eq_nm_CV_nm.
inversion_clear eq_nm_CV_nm.
inversion_clear H4.
inversion_clear H5.
intro CAM_C2.
exists (val (int (eval_op c n m))).
split.
exact (Eqnum (eval_op c n m)).
intro S.
apply
 (o_DS (ETcons CV0 S) (ETcons CV0 (ETcons CV0 S))
    (ETcons (val (int (eval_op c n m))) S) push
    (o C1 (o swap (o C2 (o cons app))))).
apply PUSH.
apply
 (o_DS (ETcons CV0 (ETcons CV0 S)) (ETcons (val CV_c) (ETcons CV0 S))
    (ETcons (val (int (eval_op c n m))) S) C1 (o swap (o C2 (o cons app)))).
apply CAM_C1.
apply
 (o_DS (ETcons (val CV_c) (ETcons CV0 S)) (ETcons CV0 (ETcons (val CV_c) S))
    (ETcons (val (int (eval_op c n m))) S) swap (o C2 (o cons app))).
apply SWAP.
apply
 (o_DS (ETcons CV0 (ETcons (val CV_c) S))
    (ETcons (Cam_pair (val (int n)) (val (int m))) (ETcons (val CV_c) S))
    (ETcons (val (int (eval_op c n m))) S) C2 (o cons app)).
apply CAM_C2.
cut (forall s : Etat, CAM_DS (ETcons CV0 s) C1 (ETcons (val CV_c) s)).
2: auto.
inversion_clear eq_c_CV_c.
intro U_CAM_C1.
apply
 (o_DS
    (ETcons (Cam_pair (val (int n)) (val (int m)))
       (ETcons (val (def_op c)) S))
    (ETcons
       (Cam_pair (val (def_op c)) (Cam_pair (val (int n)) (val (int m)))) S)
    (ETcons (val (int (eval_op c n m))) S) cons app).
apply CONS.
apply (APPcam_op S n m c).  
intros.
elim H6.
intro HH5; inversion_clear HH5.
intros.
elim H5.
intro HH5; inversion_clear HH5.
intros.
elim H5.
intro HH5; inversion_clear HH5.
intros.
elim H4.
intro HH4; inversion_clear HH4.
exact (ML_DS_determ e0 E1 (OP_clos c) ML_E1 (OP_clos c0) H2).


(*****************************************************************************)
(*                        Case where E is a let'                             *)
(*****************************************************************************)


intros e0 P E1 E2 u v ML_E2 hyp_E2 ML_E1 hyp_E1 s C Trad_let'.
inversion_clear Trad_let'.
intros hab V0 ML_let.
inversion_clear ML_let.
intros CV0 eq_e0_CV0.
cut (u = u0); cut (v = V0).
intros eq1 eq2.
try rewrite <- eq1; try rewrite <- eq2.
elim (hyp_E2 s C1 H0 hab u ML_E2 CV0 eq_e0_CV0).
intros CV_u HH.
elim HH.
intros eq_u_CV_u CAM_C1.
elim
 (hyp_E1 (cons_squelette P s) C2 H1 (cons_habite P u e0 s hab) v ML_E1
    (Cam_pair CV0 CV_u) (Eqenv2 P e0 CV0 eq_e0_CV0 u CV_u eq_u_CV_u)).
intros CV_v HH2.        
elim HH2.
intros eq_v_CV_v CAM_C2.
exists CV_v.
split.
exact eq_v_CV_v.
intro S.
apply
 (o_DS (ETcons CV0 S) (ETcons CV0 (ETcons CV0 S)) (ETcons CV_v S) push
    (o C1 (o cons C2))).
apply PUSH.      
apply
 (o_DS (ETcons CV0 (ETcons CV0 S)) (ETcons CV_u (ETcons CV0 S))
    (ETcons CV_v S) C1 (o cons C2)).
apply CAM_C1.        
apply
 (o_DS (ETcons CV_u (ETcons CV0 S)) (ETcons (Cam_pair CV0 CV_u) S)
    (ETcons CV_v S) cons C2).
apply CONS.
apply CAM_C2.
cut (u = u0).
intro eq3.
cut (ML_DS (Econs P u0 e0) E1 V0).
2: exact H3.
try rewrite <- eq3.
intro ML_E1'.
apply (ML_DS_determ (Econs P u e0) E1 v ML_E1 V0 ML_E1').
apply (ML_DS_determ e0 E2 u ML_E2 u0 H2).
intro; apply (ML_DS_determ e0 E2 u ML_E2 u0 H2).
cut (u = u0).
intro eq3.
cut (ML_DS (Econs P u0 e0) E1 V0).
2: exact H3.
try rewrite <- eq3.
intro ML_E1'.
apply (ML_DS_determ (Econs P u e0) E1 v ML_E1 V0 ML_E1').
apply (ML_DS_determ e0 E2 u ML_E2 u0 H2).


(*****************************************************************************)
(*                     Case where E is a let_rec                             *)
(*****************************************************************************)

intros e0 P x E0 E2 u ML_E2 hyp_E2 s C Trad_letrec.
inversion_clear Trad_letrec.
intros hab V0 ML_letrec.
inversion_clear ML_letrec.
intros CV0 eq_e0_CV0.
cut (u = V0).
intro eq1.
try rewrite <- eq1.
elim
 (hyp_E2 (cons_squelette P s) C2 H1
    (cons_habite P (Clos_rec x E0 P e0) e0 s hab) u ML_E2
    (Cam_pair CV0 (Cam_clos_rec C0 CV0))
    (Eqenv2 P e0 CV0 eq_e0_CV0 (Clos_rec x E0 P e0) 
       (Cam_clos_rec C0 CV0) (Eqclos_rec P x E0 e0 C0 CV0 s eq_e0_CV0 hab H0))).   
intros CV_u HH.
elim HH. intros eq_u_CV_u CAM_C2.
exists CV_u.
split.
exact eq_u_CV_u.
intro S.
apply
 (o_DS (ETcons CV0 S) (ETcons CV0 (ETcons CV0 S)) (ETcons CV_u S) push
    (o (cur_rec C0) (o cons C2))).
apply PUSH.
apply
 (o_DS (ETcons CV0 (ETcons CV0 S))
    (ETcons (Cam_clos_rec C0 CV0) (ETcons CV0 S)) (ETcons CV_u S)
    (cur_rec C0) (o cons C2)).
apply CUR_REC.
apply
 (o_DS (ETcons (Cam_clos_rec C0 CV0) (ETcons CV0 S))
    (ETcons (Cam_pair CV0 (Cam_clos_rec C0 CV0)) S) 
    (ETcons CV_u S) cons C2).
apply CONS.
apply CAM_C2.
apply (ML_DS_determ (Econs P (Clos_rec x E0 P e0) e0) E2 u ML_E2 V0 H2). 


Qed.



(*****************************************************************************)
