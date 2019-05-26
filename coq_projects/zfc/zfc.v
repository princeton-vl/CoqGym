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
(************************************************************************)
(*                      Zermolo Set Theory                              *)
(*                                                                      *)
(*                        Benjamin Werner                               *)
(************************************************************************)




(* This is an encoding of usual Set Theory, simillar to Peter Aczel's work *)
(* in the early 80's. The main difference is that the propositions here    *)
(* live in the impredicative world of "Prop". Thus, priority is given to   *)
(* expressivity against constructivity.                                    *)

(* Since the definition of Sets is the same for both approaches, I added   *) 
(* most  of Aczel's encoding of CZF at the end of the file. Many           *)
(* definitions are common to both aproaches.                               *)

Set Asymmetric Patterns.
(* The type representing sets  (Ensemble = french for set) *)

Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.

(* Existential quantification *)

Inductive EXType (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei : forall x : P, Q x -> EXType P Q.

(* Cartesian product in Type *)

Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.


(* Existential on the Type level *)

Inductive depprod (A : Type) (P : A -> Type) : Type :=
    dep_i : forall x : A, P x -> depprod A P.


(* Recursive Definition of the extentional equality on sets *)

Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.

(* Membership on sets *)

Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => EXType _ (fun y : A => EQ E1 (f y))
  end.


(* INCLUSION *)

Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
exact (forall E : Ens, IN E E1 -> IN E E2).
Defined.


(* EQ is an equivalence relation  *)

Theorem EQ_refl : forall E : Ens, EQ E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto.

exists y; auto.
Qed.

Theorem EQ_tran : forall E1 E2 E3 : Ens, EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simple induction E3; intros A3 f3 r3; simpl in |- *; 
 intros e1 e2.
split; (elim e1; intros I1 I2; elim e2; intros I3 I4).
intros a1; elim (I1 a1); intros a2.
elim (I3 a2); intros a3.
exists a3.
apply r1 with (f2 a2); auto.
intros a3; elim (I4 a3); intros a2; elim (I2 a2); intros a1; exists a1.
apply r1 with (f2 a2); auto.
Qed.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
intros a1; elim (e1 a1); intros a2 H2; exists a2; auto.
Qed.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 simpl in |- *; simple induction 1; intros e1 e2; unfold INC in |- *;
 simpl in |- *.
intros C; simple induction 1; intros a ea; elim (e1 a); intros a' ea';
 exists a'.
apply EQ_tran with (f a); assumption.
Qed.

Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.

(* easy lemma *)

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 unfold INC in |- *; simpl in |- *; intros I1 I2; split.
intros a; apply I1.
exists a; auto with zfc.
intros a'; cut (EXType A (fun x : A => EQ (f' a') (f x))).
simple induction 1; intros a ea; exists a; auto with zfc.
apply I2; exists a'; auto with zfc.
Qed.

Hint Resolve INC_EQ: zfc.


(* Membership is extentional (i.e. is stable w.r.t. EQ)   *)

Theorem IN_sound_left :
 forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
simple induction E''; intros A'' f'' r'' e; simpl in |- *; simple induction 1;
 intros a'' p; exists a''; apply EQ_tran with E; auto with zfc.
Qed.

Theorem IN_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
simple induction E'; intros A' f' r'; simple induction E'';
 intros A'' f'' r''; simpl in |- *; simple induction 1; 
 intros e1 e2; simple induction 1; intros a' e'; elim (e1 a'); 
 intros a'' e''; exists a''; apply EQ_tran with (f' a'); 
 assumption.

Qed.

(* Inclusion is reflexive, transitive, extentional *)

Theorem INC_refl : forall E : Ens, INC E E.
unfold INC in |- *; auto with zfc.
Qed.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
unfold INC in |- *; auto with zfc.
Qed.


Theorem INC_sound_left :
 forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
simple induction E''; unfold INC in |- *; simpl in |- *;
 intros A f HR e H1 E0 i; apply H1.
apply IN_sound_right with E'; auto with zfc.
Qed.

Theorem INC_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
simple induction E'; simple induction E''; unfold INC in |- *; simpl in |- *;
 intros.
elim (H2 E0); try assumption; intros.
elim H1; intros HA HB; elim (HA x); intros.
exists x0; apply EQ_tran with (e x); auto with zfc.
Qed.


(* Useful types (actually top and bottom)   *)

Inductive Un : Set :=
    void : Un.

Inductive F : Set :=.

(* The empty set  (vide = french for empty)   *)

Definition Vide : Ens := sup F (fun f : F => match f return Ens with
                                             end).

(* The axioms of the empty set *)

Theorem Vide_est_vide : forall E : Ens, IN E Vide -> F.
unfold Vide in |- *; simpl in |- *; intros E H; cut False.
simple induction 1.
elim H; intros x; elim x.
Qed.


Theorem tout_vide_est_Vide :
 forall E : Ens, (forall E' : Ens, IN E' E -> F) -> EQ E Vide.
 unfold Vide in |- *; simple induction E; simpl in |- *; intros A e H H0;
  split.
intros; elim (H0 (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.
Qed.

(* Pair *)

Definition Paire : forall E E' : Ens, Ens.
intros.
apply (sup bool).
simple induction 1.
exact E.
exact E'.
Defined.

(* The pair construction is extentional *)

Theorem Paire_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.
Qed.

Theorem Paire_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
exists false; auto with zfc.
Qed.

Hint Resolve Paire_sound_right Paire_sound_left: zfc.

(* The axioms of the pair *)

Theorem IN_Paire_left : forall E E' : Ens, IN E (Paire E E').
unfold Paire in |- *; simpl in |- *; exists true; simpl in |- *;
 auto with zfc.
Qed.

Theorem IN_Paire_right : forall E E' : Ens, IN E' (Paire E E').
unfold Paire in |- *; simpl in |- *; exists false; simpl in |- *;
 auto with zfc.
Qed.

Theorem Paire_IN :
 forall E E' A : Ens, IN A (Paire E E') -> EQ A E \/ EQ A E'.
unfold Paire in |- *; simpl in |- *.
simple induction 1; intros b; elim b; simpl in |- *; auto with zfc.
Qed.

Hint Resolve IN_Paire_left IN_Paire_right Vide_est_vide: zfc.

(* The singleton set  *)
(* Note that we could define it directly using the base type Un *)

Definition Sing (E : Ens) := Paire E E.

(* The axioms  *)

Theorem IN_Sing : forall E : Ens, IN E (Sing E).
unfold Sing in |- *; auto with zfc.
Qed.

Theorem IN_Sing_EQ : forall E E' : Ens, IN E (Sing E') -> EQ E E'.
unfold Sing in |- *; intros E E' H; elim (Paire_IN E' E' E);
 auto with zfc.
Qed.



Hint Resolve IN_Sing IN_Sing_EQ: zfc.

Theorem Sing_sound : forall A A' : Ens, EQ A A' -> EQ (Sing A) (Sing A').
unfold Sing in |- *; intros; apply EQ_tran with (Paire A A');
 auto with zfc.
Qed.

Hint Resolve Sing_sound: zfc.

Theorem EQ_Sing_EQ : forall E1 E2 : Ens, EQ (Sing E1) (Sing E2) -> EQ E1 E2.
intros; cut (IN E1 (Sing E2)).
intros; auto with zfc.
apply IN_sound_right with (Sing E1); auto with zfc.
Qed.

Hint Resolve EQ_Sing_EQ: zfc.



(* We here need sigma types -- i.e. computational existentials *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig A P.


(* The set obtained by the comprehension (or separation) axiom *)

Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.

(* The comprehension/separation axioms *)

Theorem Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
unfold Comp, INC in |- *; simple induction E; simpl in |- *; intros.
elim H0; simple induction x; intros; exists x0; auto with zfc.
Qed.

Theorem IN_Comp_P :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A (Comp E P) -> P A.
simple induction E; simpl in |- *; intros B f Hr A P H i; elim i; intros c;
 elim c; simpl in |- *; intros x q e; apply H with (f x); 
 auto with zfc.
Qed.

Theorem IN_P_Comp :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
 IN A E -> P A -> IN A (Comp E P).
simple induction E; simpl in |- *; intros B f HR A P H i; elim i;
 simpl in |- *; intros.
cut (P (f x)).
intros Pf.
exists (exist B (fun x : B => P (f x)) x Pf); simpl in |- *;
 auto with zfc.
apply H with A; auto with zfc.
Qed.

(* Again, extentionality is not stated, but easy *)


(* Projections of a set: *)
(*  1: its base type     *)

Definition pi1 : Ens -> Type.
simple induction 1.
intros A f r.
exact A.
Defined.

(*  2: the function      *)

Definition pi2 : forall E : Ens, pi1 E -> Ens.
simple induction E.
intros A f r.
exact f.
Defined.

(* The Union set   *)

Definition Union : forall E : Ens, Ens.
simple induction 1; intros A f r.
apply (sup (depprod A (fun x : A => pi1 (f x)))).
simple induction 1; intros a b.
exact (pi2 (f a) b).
Defined.

Theorem EQ_EXType :
 forall E E' : Ens,
 EQ E E' ->
 forall a : pi1 E,
 EXType (pi1 E') (fun b : pi1 E' => EQ (pi2 E a) (pi2 E' b)).
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 simpl in |- *; simple induction 1; intros e1 e2 a.
apply e1.
Defined.

Theorem IN_EXType :
 forall E E' : Ens,
 IN E' E -> EXType (pi1 E) (fun a : pi1 E => EQ E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
exists x; auto with zfc.
Qed.

(* The union axioms *)

Theorem IN_Union :
 forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).

simple induction E; intros A f r.
intros.
simpl in |- *.
elim (IN_EXType (sup A f) E' H).
intros x e.
cut (EQ (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (IN E'' (pi2 (sup A f) x)).
intros i1.
elim (IN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
apply IN_sound_right with E'; auto with zfc.
Qed.



Theorem IN_INC_Union : forall E E' : Ens, IN E' E -> INC E' (Union E).
unfold INC in |- *; simple induction E; intros A f r; unfold Union in |- *.
intros E' i E'' i'; simpl in |- *; elim (IN_EXType (sup A f) E' i).
intros a e; simpl in a; simpl in e.
elim (IN_EXType E' E'' i').
cut (IN E'' (f a)).
intros i'' a' e''; elim (IN_EXType _ _ i''); simpl in |- *; intros aa ee.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.
apply IN_sound_right with E'; auto with zfc.
Qed.

Theorem Union_IN :
 forall E E' : Ens,
 IN E' (Union E) -> EXType _ (fun E1 : Ens => IN E1 E /\ IN E' E1).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.

apply IN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
Qed.


(* extentionality of union  *)

Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
unfold Union in |- *; simple induction E; intros A f r; simple induction E';
 intros A' f' r'; simpl in |- *; simple induction 1; 
 intros e1 e2; split.
intros x; elim x; intros a aa; elim (e1 a); intros a' ea.
elim (EQ_EXType (f a) (f' a') ea aa); intros aa' eaa.
exists (dep_i A' (fun x : A' => pi1 (f' x)) a' aa'); simpl in |- *;
 auto with zfc.
intros c'; elim c'; intros a' aa'; elim (e2 a'); intros a ea.
cut (EQ (f' a') (f a)).
2: auto with zfc.
intros ea'; elim (EQ_EXType (f' a') (f a) ea' aa'); intros aa eaa.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.

Qed.



(* The union construction is monotone w.r.t. inclusion   *)

Theorem Union_mon : forall E E' : Ens, INC E E' -> INC (Union E) (Union E').
unfold INC in |- *; intros E E' IEE E'' IEE''.
elim (Union_IN E E'').
intros E'''; simple induction 1; intros I1 I2.
apply IN_Union with E'''; auto with zfc.
auto with zfc.

Qed.



(* The  Intersection set   *)

Definition Inter (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun
           c : depprod _
                 (fun a : A =>
                  depprod _
                    (fun b : pi1 (f a) =>
                     forall x : A, IN (pi2 (f a) b) (f x))) =>
         match c with
         | dep_i a (dep_i b p) => pi2 (f a) b
         end)
  end.

(* the axioms *)

Theorem IN_Inter_all :
 forall E E' : Ens,
 IN E' (Inter E) -> forall E'' : Ens, IN E'' E -> IN E' E''.

simple induction E; intros A f r; simpl in |- *; intros E'.
simple induction 1; intros c; elim c; intros a ca; elim ca; intros aa paa;
 simpl in |- *.
intros e E'' e''.
elim e''; intros a1 ea1.
apply IN_sound_right with (f a1); auto with zfc.
apply IN_sound_left with (pi2 (f a) aa); auto with zfc.
Qed.

Theorem all_IN_Inter :
 forall E E' E'' : Ens,
 IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter E).
simple induction E; intros A f r.
intros E' E'' i H.
elim (IN_EXType (sup A f) E'' i).
intros a e; simpl in a.
simpl in e.
cut (IN E' E''); auto with zfc.
intros i'.
cut (IN E' (f a)); auto with zfc.
intros i0.
elim (IN_EXType (f a) E' i0).
intros b e'.
simpl in |- *.
cut (forall x : A, IN (pi2 (f a) b) (f x)).
intros.
exists
 (dep_i A
    (fun a : A =>
     depprod (pi1 (f a))
       (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x))) a
    (dep_i (pi1 (f a))
       (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x)) b H0)).
simpl in |- *.
auto with zfc.
auto with zfc.
intros.
apply IN_sound_left with E'.
auto with zfc.
apply H.
auto with zfc.
simpl in |- *.
exists x; auto with zfc.
apply IN_sound_right with E''; auto with zfc.
Qed.





(*  The powerset and its axioms   *)

Definition Power (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun P : A -> Prop =>
         sup _
           (fun c : depprod A (fun a : A => P a) =>
            match c with
            | dep_i a p => f a
            end))
  end.


Theorem IN_Power_INC : forall E E' : Ens, IN E' (Power E) -> INC E' E.
simple induction E.
intros A f r; unfold INC in |- *; simpl in |- *.
intros E'; simple induction 1; intros P.
elim E'; simpl in |- *.
intros A' f' r'.
simple induction 1; intros HA HB.
intros E''; simple induction 1; intros a' e.
elim (HA a').
simple induction x; intros a p.
intros; exists a.
auto with zfc.
apply EQ_tran with (f' a'); auto with zfc.
Qed.



Theorem INC_IN_Power : forall E E' : Ens, INC E' E -> IN E' (Power E).
simple induction E; intros A f r; unfold INC in |- *; simpl in |- *.
simple induction E'; intros A' f' r' i.
exists (fun a : A => IN (f a) (sup A' f')).
simpl in |- *.
split.
intros.
elim (i (f' x)); auto with zfc.
intros a e.
cut (EQ (f a) (f' x)); auto with zfc.
intros e1.
exists
 (dep_i A (fun a : A => EXType A' (fun y : A' => EQ (f a) (f' y))) a
    (EXTypei A' (fun y : A' => EQ (f a) (f' y)) x e1)).
simpl in |- *.
auto with zfc.

auto with zfc.
simpl in |- *.
exists x; auto with zfc.

simple induction y; simpl in |- *.
simple induction 1; intros.
exists x0; auto with zfc.
Qed.

Theorem Power_mon : forall E E' : Ens, INC E E' -> INC (Power E) (Power E').
intros.
unfold INC in |- *; intros.
apply INC_IN_Power.
cut (INC E0 E).
unfold INC in |- *; unfold INC in H; intros; auto with zfc.
apply IN_Power_INC; auto with zfc.
Qed.

Theorem Power_sound : forall E E' : Ens, EQ E E' -> EQ (Power E) (Power E').
intros E E' e.
apply INC_EQ; unfold INC in |- *.
intros A i.
cut (INC A E').
intros; apply INC_IN_Power; assumption.
cut (INC A E); intros.
apply INC_sound_right with E; auto with zfc.
apply IN_Power_INC; assumption.
intros A i.
cut (INC A E).
intros; apply INC_IN_Power; assumption.
cut (INC A E'); intros.
apply INC_sound_right with E'; auto with zfc.
apply IN_Power_INC; assumption.
Qed.





(* small lemma *)

Theorem not_EQ_Sing_Vide : forall E : Ens, EQ (Sing E) Vide -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
apply IN_sound_right with (Sing E); auto with zfc.
Qed.


Theorem not_EQ_Vide_Sing : forall E : Ens, EQ Vide (Sing E) -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
apply IN_sound_right with (Sing E); auto with zfc.
Qed.



(* The cartesian product and its properties *)


(* This definition of the ordered pair is slightly different from *)
(* the usual one, since we want it to work in an intuisionistic   *)
(* setting. Works the same, neitherless. The soundness proofs are *)
(* unpleasant.                                                    *)


Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).

Theorem Couple_inj_left :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A B.
unfold Couple in |- *; simpl in |- *.
simple induction 1.
intros HA HB; elim (HA true).
intros x; elim x; simpl in |- *; simple induction 1; intros H3 H4;
 elim (H3 true); simpl in |- *; intros xx; elim xx; 
 simpl in |- *; auto with zfc.
elim (H4 false); simpl in |- *.
simple induction x0; simpl in |- *.
intros.
cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.

apply EQ_tran with A; auto with zfc.

intros; cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.

apply EQ_tran with A; auto with zfc.

intros yy.
elim (HB true); simpl in |- *.
simple induction x0.
change (EQ (Sing A) (Sing B) -> EQ A B) in |- *; intros EE.
apply IN_Sing_EQ.
apply IN_sound_right with (Sing A); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Sing B) -> EQ A B) in |- *.
intros zz.
elimtype F.
apply (not_EQ_Sing_Vide A').
apply EQ_tran with B.
apply IN_Sing_EQ.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
apply EQ_sym; apply IN_Sing_EQ;
 apply IN_sound_right with (Paire Vide (Sing A')); 
 auto with zfc.

Qed.



Theorem Couple_inj_right :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A' B'.
unfold Couple in |- *; simpl in |- *.
simple induction 1; intros H1 H2.
elim (H1 false).
intros bb1; elim bb1.
intros HF.
change (EQ (Paire Vide (Sing A')) (Sing B)) in HF.
cut F.
simple induction 1.
apply (not_EQ_Vide_Sing A').
apply EQ_tran with B.
apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A'));
 auto with zfc.
apply EQ_sym; apply IN_Sing_EQ;
 apply IN_sound_right with (Paire Vide (Sing A')); 
 auto with zfc.
change (EQ (Paire Vide (Sing A')) (Paire Vide (Sing B')) -> EQ A' B') in |- *.
intros HP; cut (EQ (Sing A') (Sing B')).
intros; auto with zfc.
cut (IN (Sing A') (Paire Vide (Sing B'))).
intros HI; elim (Paire_IN Vide (Sing B') (Sing A') HI).
intros; cut F.
simple induction 1.
apply not_EQ_Sing_Vide with A'; assumption.
trivial with zfc.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.

Qed.






(* Here we cheat. It is easier to define the cartesian product using    *)
(* the type theoretical product, i.e. we here use non set-theoretical   *)
(* constructions. We could however use the usual definitions.           *)


Definition Prod (E E' : Ens) : Ens :=
  match E, E' with
  | sup A f, sup A' f' =>
      sup _
        (fun c : prod_t A A' =>
         match c with
         | pair_t a a' => Couple (f a) (f' a')
         end)
  end.


Hint Resolve Paire_sound_left Paire_sound_right: zfc.


Theorem Couple_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Couple A B) (Couple A' B).
 unfold Couple in |- *; intros; auto with zfc.
Qed.

Theorem Couple_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Couple A B) (Couple A B').
 unfold Couple in |- *; intros; auto with zfc.
Qed.


Theorem Couple_IN_Prod :
 forall E1 E2 E1' E2' : Ens,
 IN E1' E1 -> IN E2' E2 -> IN (Couple E1' E2') (Prod E1 E2).
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i1 i2.
elim (IN_EXType (sup A1 f1) E1').
intros x e1; simpl in x.
elim (IN_EXType (sup A2 f2) E2').
intros x0 e2; simpl in x.
apply IN_sound_left with (Couple (pi2 (sup A1 f1) x) (pi2 (sup A2 f2) x0));
 auto with zfc.
apply EQ_tran with (Couple (pi2 (sup A1 f1) x) E2'); auto with zfc.
apply Couple_sound_right.
auto with zfc.

apply Couple_sound_left; auto with zfc.

simpl in |- *.
simpl in |- *.
exists (pair_t _ _ x x0).
simpl in |- *.
split.
simple induction x1; simpl in |- *.
exists true; simpl in |- *.
split.
simple induction x2; simpl in |- *.
exists true; auto with zfc.

exists true; auto with zfc.

simple induction y; exists true; auto with zfc.

exists false; simpl in |- *.
split.
simple induction x2.
exists true; simpl in |- *; auto with zfc.
split.
simple induction x3.

simple induction y.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.

auto with zfc.

auto with zfc.
Qed.


Theorem Couple_Prod_IN :
 forall E1 E2 E1' E2' : Ens,
 IN (Couple E1' E2') (Prod E1 E2) -> IN E1' E1 /\ IN E2' E2.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i.
elim (IN_EXType (Prod (sup A1 f1) (sup A2 f2)) (Couple E1' E2') i).
intros xx; elim xx; intros a1 a2 e.
change (EQ (Couple E1' E2') (Couple (f1 a1) (f2 a2))) in e.
cut (EQ E1' (f1 a1)).
cut (EQ E2' (f2 a2)).
intros e1 e2.
split.
apply IN_sound_left with (f1 a1); auto with zfc; simpl in |- *; exists a1;
 auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc; simpl in |- *; exists a2;
 auto with zfc.
apply Couple_inj_right with (A := E1') (B := f1 a1); auto with zfc.
apply Couple_inj_left with E2' (f2 a2); auto with zfc.
Qed.



Theorem IN_Prod_EXType :
 forall E E' E'' : Ens,
 IN E'' (Prod E E') ->
 EXType _ (fun A : Ens => EXType _ (fun B : Ens => EQ (Couple A B) E'')).
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
intros; elim (IN_EXType (Prod (sup A f) (sup A' f')) E'').
simple induction x.
intros; exists (f a); exists (f' b); auto with zfc.
auto with zfc.
Qed.



(* Ordinals *)

Definition Succ (E : Ens) := Union (Paire E (Sing E)).


Inductive Ord : Ens -> Prop :=
  | Oo : Ord Vide
  | So : forall E : Ens, Ord E -> Ord (Succ E)
  | Lo : forall E : Ens, (forall e : Ens, IN e E -> Ord e) -> Ord (Union E)
  | Eo : forall E E' : Ens, Ord E -> EQ E E' -> Ord E'.

Hint Resolve Oo So Lo: zfc.

Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
exact (Succ X).
Defined.

Theorem Nat_Ord : forall n : nat, Ord (Nat n).
simple induction n; simpl in |- *; auto with zfc.
Qed.

Definition Omega : Ens := sup nat Nat.

Theorem IN_Succ : forall E : Ens, IN E (Succ E).
intros E; unfold Succ in |- *; unfold Sing in |- *;
 apply IN_Union with (Paire E E); auto with zfc.
Qed.


Theorem INC_Succ : forall E : Ens, INC E (Succ E).
unfold INC in |- *; unfold Succ in |- *.
intros.
apply IN_Union with E; auto with zfc.
Qed.

Hint Resolve IN_Succ INC_Succ: zfc.


Theorem IN_Succ_or : forall E E' : Ens, IN E' (Succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
apply IN_sound_right with E1; auto with zfc.

Qed.


Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.

simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
exists a; auto with zfc.
Qed.


Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
intros; simpl in |- *; exists n; auto with zfc.
Qed.
Hint Resolve Nat_IN_Omega: zfc.


Theorem IN_Omega_EXType :
 forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
simpl in |- *; simple induction 1.
intros n e.
exists n; auto with zfc.
Qed.

Theorem IN_Nat_EXType :
 forall (n : nat) (E : Ens),
 IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
simple induction n.
simpl in |- *.
simple induction 1.
simple induction x.

intros.
change (IN E (Succ (Nat n0))) in H0.
elim (IN_Succ_or (Nat n0) E H0).
intros; exists n0.
auto with zfc.

intros.
elim (H E); auto with zfc.
Qed.


Theorem Omega_EQ_Union : EQ Omega (Union Omega).
apply INC_EQ; unfold INC in |- *.
intros.
elim (IN_Omega_EXType E H); intros n e.
apply IN_Union with (Nat (S n)).
auto with zfc.

apply IN_sound_left with (Nat n).
auto with zfc.

auto with zfc.
change (IN (Nat n) (Succ (Nat n))) in |- *; auto with zfc.

intros.
elim (Union_IN Omega E H).
intros e h.
elim h.
intros i1 i2.
elim (IN_Omega_EXType e i1).
intros n e1.
cut (IN E (Nat n)).
intros.
elim (IN_Nat_EXType n E H0); intros.
apply IN_sound_left with (Nat x); auto with zfc.

apply IN_sound_right with e; auto with zfc.
Qed.


Theorem Omega_Ord : Ord Omega.

apply Eo with (Union Omega).
apply Lo.
intros.
elim (IN_Omega_EXType e H).
intros n ee.
apply Eo with (Nat n); auto with zfc.
elim n.
auto with zfc.
auto with zfc.
intros.
change (Ord (Succ (Nat n0))) in |- *; auto with zfc.
apply EQ_sym; auto with zfc.
apply Omega_EQ_Union.

Qed.




Definition Alpha : Ens -> Ens.
simple induction 1; intros A f r.
apply Union.
apply (sup A).
intros a.
exact (Power (r a)).

Defined.


(* A Type-theoretical axiom of choice gives us the collection axiom  *)


Definition collection :=
  forall P : Ens -> Ens -> Prop,
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  (forall E : Ens, EXType _ (P E)) ->
  forall E : Ens,
  EXType _
    (fun A : Ens =>
     forall x : Ens, IN x E -> EXType _ (fun y : Ens => IN y A /\ P x y)).


Definition choice :=
  forall (A B : Type) (P : A -> B -> Prop),
  (forall a : A, EXType _ (fun b : B => P a b)) ->
  EXType _ (fun f : A -> B => forall a : A, P a (f a)).


Theorem Choice_Collection : choice -> collection.
unfold collection in |- *; intro; intros P comp G E.
cut (EXType _ (fun f : Ens -> Ens => forall B : Ens, P B (f B))).
simple induction 1; intros f pf.
elim E; intros A g hr; intros.
exists (sup A (fun a : A => f (g a))).
simpl in |- *; intros X i.
elim i; intros a ea.
exists (f (g a)).
split.
exists a; auto with zfc.
apply comp with (g a); auto with zfc.
unfold choice in H.
apply H; intros.
elim (G a); intros b hb; exists b; auto with zfc.
Qed.



(* If we also assume the excluded middle, we can derive         *)
(* the usual replacement schemata.                              *)

Definition functional (P : Ens -> Ens -> Prop) :=
  forall x y y' : Ens, P x y -> P x y' -> EQ y y'.

Definition replacement :=
  forall P : Ens -> Ens -> Prop,
  functional P ->
  (forall x y y' : Ens, EQ y y' -> P x y -> P x y') ->
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  forall X : Ens,
  EXType _
    (fun Y : Ens =>
     forall y : Ens,
     (IN y Y -> EXType _ (fun x : Ens => IN x X /\ P x y)) /\
     (EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).


Theorem classical_Collection_Replacement :
 (forall S : Prop, S \/ (S -> False)) -> collection -> replacement.

unfold replacement in |- *; intros EM Collection P fp comp_r comp_l X.
cut
 (EXType _
    (fun Y : Ens =>
     forall y : Ens, EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).
simple induction 1; intros Y HY.
exists (Comp Y (fun y : Ens => EXType _ (fun x : Ens => IN x X /\ P x y))).
intros y; split.
intros HC.
apply
 (IN_Comp_P Y y
    (fun y0 : Ens => EXType Ens (fun x : Ens => IN x X /\ P x y0)));
 auto with zfc.
intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
intros He.
apply IN_P_Comp.

intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
apply HY; auto with zfc.
auto with zfc.

elim
 (Collection
    (fun x y : Ens =>
     P x y \/ (forall y' : Ens, P x y' -> False) /\ EQ y Vide)) 
  with X.
intros Y HY.
elim (EM (EXType _ (fun x : Ens => IN x X /\ P x Vide))).
intros Hvide; elim Hvide; intros xv Hxv; exists Y.
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
elim (HY x Hx1).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2.
intros Hy'3; apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
simple induction 1; intros Hy'3 Hy'4.
elim (Hy'3 y Hx2).
intros HP; exists (Comp Y (fun y : Ens => EQ y Vide -> False)).
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
apply IN_P_Comp.
intros w1 w2 Hw1 Hw Hw2; apply Hw1; apply EQ_tran with w2; auto with zfc.
elim (HY x).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2; intros Hy'3.
apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
elim Hy'3; intros Hy'4 Hy'5.
elim (Hy'4 y); auto with zfc.
assumption.
intros e; apply HP; exists x; split; auto with zfc; apply comp_r with y;
 auto with zfc; apply fp; auto with zfc.
intros x x' y e Hx; elim Hx; intros Hx1.
left; apply comp_l with x; auto with zfc.
right; elim Hx1; intros Hx2 Hx3; split.
2: assumption.
intros y' Hy'; apply (Hx2 y'); apply comp_l with x'; auto with zfc.
intros x; elim (EM (EXType _ (fun y : Ens => P x y))); intros Hx.
elim Hx; intros x0 Hx0; exists x0; left; assumption.
exists Vide; right; split; auto with zfc.
intros y Hy; elim Hx; exists y; auto with zfc.
Qed.


(* Peter Aczel's Encoding of CZF *)

(* Using the same definition "Ens" of sets, we can developp Peter Aczel's   *)
(* encoding of "Constructive Type Theory" (CZF).                            *)
(* It is basically a simillar developement, but this time, the propositions *)
(* are objects of type "Type", i.e. are on the same level (resp. above) the *)
(* sets. The advantage is that we can extract the constructive witness of an*)
(* existential proof. The drawbacks are:                                    *)
(*  - no definition of the powerset                                         *)
(*  - complicated difference between bounded and unbounded quantification   *)
(*  - excluded middle is now much more "dangerous"                          *)

Definition EQC : Ens -> Ens -> Type.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
refine (prod_t _ _).
exact (forall x : A, depprod _ (fun y : B => eq1 x (g y))).
exact (forall y : B, depprod _ (fun x : A => eq1 x (g y))).
Defined.



(* APPARTENANCE *)

Definition CIN : Ens -> Ens -> Type.
simple induction 2.
intros.
exact (depprod _ (fun y : A => EQC X (e y))).
Defined.



(* INCLUSION *)

Definition CINC : Ens -> Ens -> Type.
intros E1 E2.
exact (forall E : Ens, CIN E E1 -> CIN E E2).
Defined.



(* EQ EST UNE RELATION D'EQUIVALENCE *)

Theorem EQC_refl : forall E : Ens, EQC E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto with zfc.

exists y; auto with zfc.
Qed.

Theorem EQC_tran : forall E1 E2 E3 : Ens, EQC E1 E2 -> EQC E2 E3 -> EQC E1 E3.
simple induction E1; simple induction E2; simple induction E3; simpl in |- *;
 intros.
split; (elim X2; intros; elim X3; intros).
elim (a x); intros.
elim (a0 x0); intros.
exists x1.
apply X with (e0 x0); auto with zfc.
elim (b0 y); intros.
elim (b x); intros.
exists x0.
apply X with (e0 x); auto with zfc.
Qed.

Theorem EQC_sym : forall E1 E2 : Ens, EQC E1 E2 -> EQC E2 E1.
simple induction E1; simple induction E2; simpl in |- *; intros.
elim X1; intros; split; intros.
elim (b x); intros.
exists x0; auto with zfc.
elim (a y); intros; exists x; auto with zfc.
Qed.

Theorem EQC_INC : forall E E' : Ens, EQC E E' -> CINC E E'.
simple induction E; simple induction E'; simpl in |- *; intros;
 unfold CINC in |- *; simpl in |- *.
elim X1; intros.
elim X2; intros.
elim (a x); intros.
exists x0; apply EQC_tran with (e x); auto with zfc.
Qed.

Hint Resolve EQC_sym EQC_refl EQC_INC: zfc.

Theorem CINC_EQC : forall E E' : Ens, CINC E E' -> CINC E' E -> EQC E E'.
simple induction E; simple induction E'; unfold CINC in |- *; simpl in |- *;
 intros; split; intros.
apply X1.
exists x; auto with zfc.
cut (depprod A (fun x : A => EQC (e0 y) (e x)));
 try (simple induction 1; intros x p; exists x; auto with zfc).
apply X2; exists y; auto with zfc.
Qed.

Hint Resolve CINC_EQC: zfc.





Theorem CIN_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CIN E E'' -> CIN E' E''.
simple induction E''; simpl in |- *; intros.
elim X1; intros y p; exists y.
apply EQC_tran with E; auto with zfc.
Qed.

Theorem CIN_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CIN E E' -> CIN E E''.
simple induction E'; simple induction E''; simpl in |- *; intros.
elim X1; intros Xl Xr; elim X2; intros y p; elim (Xl y); intros y0 p0;
 exists y0; apply EQC_tran with (e y); auto with zfc.
Qed.

Theorem CINC_refl : forall E : Ens, CINC E E.
unfold CINC in |- *; auto with zfc.
Qed.

Theorem CINC_tran :
 forall E E' E'' : Ens, CINC E E' -> CINC E' E'' -> CINC E E''.
unfold CINC in |- *; auto with zfc.
Qed.


Theorem CINC_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CINC E E'' -> CINC E' E''.
simple induction E''; unfold CINC in |- *; simpl in |- *;
 intros A f XR e X1 E0 i; apply X1.
apply CIN_sound_right with E'; auto with zfc.
Qed.

Theorem CINC_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CINC E E' -> CINC E E''.
simple induction E'; simple induction E''; unfold CINC in |- *; simpl in |- *;
 intros.
elim (X2 E0); try assumption; intros.
elim X1; intros XA XB; elim (XA x); intros.
exists x0; apply EQC_tran with (e x); auto with zfc.
Qed.





Theorem tout_vide_est_VideC :
 forall E : Ens, (forall E' : Ens, CIN E' E -> F) -> EQC E Vide.
 unfold Vide in |- *; simple induction E; simpl in |- *; intros A e X H;
  split.
intros; elim (H (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.
Qed.


Theorem Paire_sound_leftC :
 forall A A' B : Ens, EQC A A' -> EQC (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.
Qed.

Theorem Paire_sound_rightC :
 forall A B B' : Ens, EQC B B' -> EQC (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
exists false; auto with zfc.
Qed.


Theorem CIN_Paire_left : forall E E' : Ens, CIN E (Paire E E').
unfold Paire in |- *; simpl in |- *; exists true; simpl in |- *;
 auto with zfc.
Qed.

Theorem CIN_Paire_right : forall E E' : Ens, CIN E' (Paire E E').
unfold Paire in |- *; simpl in |- *; exists false; simpl in |- *;
 auto with zfc.
Qed.

Inductive sum_t (A B : Type) : Type :=
  | inl_t : A -> sum_t A B
  | inr_t : B -> sum_t A B.
Hint Resolve inl_t inr_t: zfc.

Theorem Paire_CIN :
 forall E E' A : Ens, CIN A (Paire E E') -> sum_t (EQC A E) (EQC A E').
unfold Paire in |- *; simpl in |- *; simple induction 1; intros b; elim b;
 simpl in |- *; auto with zfc.
Qed.

Hint Resolve CIN_Paire_left CIN_Paire_right: zfc.

(* Singleton *)

Theorem CIN_Sing : forall E : Ens, CIN E (Sing E).
unfold Sing in |- *; auto with zfc.
Qed.

Theorem CIN_Sing_EQ : forall E E' : Ens, CIN E (Sing E') -> EQC E E'.
unfold Sing in |- *; intros E E' H; elim (Paire_CIN E' E' E);
 auto with zfc.
Qed.



Theorem EQC_EQ : forall E E' : Ens, EQC E E' -> EQ E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb;
 simpl in |- *; simple induction 1; intros H1 H2; split.
intros a; elim (H1 a); intros b; intros; exists b; auto with zfc.
intros b; elim (H2 b); intros a; intros; exists a; auto with zfc.
Qed.


Theorem CIN_IN : forall E E' : Ens, CIN E E' -> IN E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb;
 simple induction 1; intros a; unfold IN in |- *; exists a; 
 auto with zfc.
apply EQC_EQ; auto with zfc.
Qed.





Theorem EQC_EXType :
 forall E E' : Ens,
 EQC E E' ->
 forall a : pi1 E,
 depprod (pi1 E') (fun b : pi1 E' => EQC (pi2 E a) (pi2 E' b)).
simple induction E; simple induction E'; simpl in |- *.
intros.
elim X1; intros.
elim (a0 a); intros.
exists x; auto with zfc.

Defined.

Theorem CIN_EXType :
 forall E E' : Ens,
 CIN E' E -> depprod (pi1 E) (fun a : pi1 E => EQC E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
exists x; auto with zfc.
Qed.

Theorem CIN_Union :
 forall E E' E'' : Ens, CIN E' E -> CIN E'' E' -> CIN E'' (Union E).

simple induction E; intros A f r.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intros x e.
cut (EQC (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (CIN E'' (pi2 (sup A f) x)).
intros i1.
elim (CIN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
apply CIN_sound_right with E'; auto with zfc.
Qed.



Theorem CIN_CINC_Union : forall E E' : Ens, CIN E' E -> CINC E' (Union E).
unfold CINC in |- *; simple induction E; intros A f r.
unfold Union in |- *.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intro.
simpl in x.
intros.
simpl in p.
elim (CIN_EXType E' E0 X0).
cut (CIN E0 (f x)).
intros.
elim (CIN_EXType _ _ X1).
simpl in |- *.
intros.
exists (dep_i A (fun x : A => pi1 (f x)) x x1); auto with zfc.

apply CIN_sound_right with E'; auto with zfc.
Qed.

(* idem depprod *)

Inductive depprod' (A : Type) (P : A -> Type) : Type :=
    dep_i' : forall x : A, P x -> depprod' A P.

Theorem Union_CIN :
 forall E E' : Ens,
 CIN E' (Union E) ->
 depprod' _ (fun E1 : Ens => prod_t (CIN E1 E) (CIN E' E1)).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.

apply CIN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
Qed.


Theorem Union_soundC :
 forall E E' : Ens, EQC E E' -> EQC (Union E) (Union E').
unfold Union in |- *.
simpl in |- *.
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
simpl in |- *.
intros.
elim X; intros.
split.
simple induction x.
intros.
elim (a x0).
intros.
elim (EQC_EXType (f x0) (f' x1) p0 p).
intros.
exists (dep_i A' (fun x : A' => pi1 (f' x)) x1 x2).
simpl in |- *.
auto with zfc.

simple induction y; intros.
elim (b x); intros.
cut (EQC (f' x) (f x0)); auto with zfc.
intros e.
elim (EQC_EXType (f' x) (f x0) e p); intros.
exists (dep_i A (fun x0 : A => pi1 (f x0)) x0 x1).
simpl in |- *; auto with zfc.
Qed.

Theorem Union_monC :
 forall E E' : Ens, CINC E E' -> CINC (Union E) (Union E').
unfold CINC in |- *; intros.
elim (Union_CIN E E0 X0); intros.
apply CIN_Union with x; elim p; intros; auto with zfc.
Qed.


(* surprinsingly, the predicative and impredicative definitions of the   *)
(* intersection do not seem equivalent.                                  *)
(* to be checked...                                                      *)



(* This is a step towards inaccessible cardinals                *)
(* We can define "small" sets, using the Type's hierarchy       *)
(* Since Coq does not support universe polymorphism, we need    *)
(* to duplicate some definitions here.                          *)



(* The small sets  *)

Inductive Ens' : Type :=
    sup' : forall A : Type, (A -> Ens') -> Ens'.

(* Existential quantification *)

Inductive EXType' (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei' : forall x : P, Q x -> EXType' P Q.

(* Cartesian product in Type *)

Inductive prod_t' (A B : Type) : Type :=
    pair_t' : A -> B -> prod_t' A B.


(* Existential on the Type level *)

Inductive depprod'' (A : Type) (P : A -> Type) : Type :=
    dep_i'' : forall x : A, P x -> depprod'' A P.


(* Recursive Definition of the extentional equality on sets *)

Definition EQ' : Ens' -> Ens' -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType' _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType' _ (fun x : A => eq1 x (g y))).
Defined.


(* small sets can be injected into big sets             *)

Definition inj : Ens' -> Ens.
simple induction 1; intros A f fr.
exact (sup A fr).
Defined.

Theorem inj_sound : forall E1 E2 : Ens', EQ' E1 E2 -> EQ (inj E1) (inj E2).
simple induction E1; intros A1 f1 fr1; simple induction E2; intros A2 f2 r2;
 simpl in |- *.
simple induction 1; intros HR1 HR2; split.
intros a1; elim (HR1 a1); intros a2 Ha2; exists a2; auto with zfc.
intros a2; elim (HR2 a2); intros a1 Ha1; exists a1; auto with zfc.
Qed.


Definition Power' (E : Ens') : Ens' :=
  match E with
  | sup' A f =>
      sup' _
        (fun P : A -> Prop =>
         sup' _
           (fun c : depprod'' A (fun a : A => P a) =>
            match c with
            | dep_i'' a p => f a
            end))
  end.


Theorem Power_sound_inj :
 forall E : Ens', EQ (inj (Power' E)) (Power (inj E)).
simple induction E; intros A f HR.
simpl in |- *; split.
intros P; exists P; split.
intros c; elim c; intros a p.
exists (dep_i A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros c; elim c; intros a p.
exists (dep_i'' A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros P; exists P; split.
intros c; elim c; intros a p.
exists (dep_i A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros c; elim c; intros a p.
exists (dep_i'' A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
Qed.


(* The set of small sets                        *)

Definition Big := sup Ens' inj.

Theorem Big_is_big : forall E : Ens', IN (inj E) Big.
intros E; unfold Big in |- *; simpl in |- *; exists E; auto with zfc.
Qed.

Theorem IN_Big_small :
 forall E : Ens, IN E Big -> EXType' _ (fun E' : Ens' => EQ E (inj E')).
unfold Big in |- *; simpl in |- *; simple induction 1; intros E' HE';
 exists E'; auto with zfc.
Qed.


Theorem IN_small_small :
 forall (E : Ens) (E' : Ens'),
 IN E (inj E') -> EXType' _ (fun E1 : Ens' => EQ E (inj E1)).
simple induction E'; intros A' f' HR'; simpl in |- *; simple induction 1;
 intros a' e'; exists (f' a'); auto with zfc.
Qed.



Theorem Big_closed_for_power : forall E : Ens, IN E Big -> IN (Power E) Big.
unfold Big in |- *; simpl in |- *; intros E; simple induction 1;
 intros E' HE'; exists (Power' E').
apply EQ_tran with (Power (inj E')).
apply Power_sound; assumption.
apply EQ_sym; apply Power_sound_inj.
Qed.





(* Just for fun : a proof that there is no set of all sets, using       *)
(* Russell's paradox construction                                       *)
(* There, of course, are other proofs (foundation, etc)                 *)

Theorem Russell : forall E : Ens, (forall E' : Ens, IN E' E) -> False.
intros U HU.
cut
 ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False))).
intros HR.
apply HR.
apply IN_P_Comp; auto with zfc.
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc;
 apply IN_sound_right with w2; auto with zfc.
intros H.
cut
 (IN (Comp U (fun x : Ens => IN x x -> False))
    (Comp U (fun x : Ens => IN x x -> False))).
change
  ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False)))
 in |- *.
cut
 (forall w1 w2 : Ens, (IN w1 w1 -> False) -> EQ w1 w2 -> IN w2 w2 -> False).
intros ww.
exact
 (IN_Comp_P U (Comp U (fun x : Ens => IN x x -> False))
    (fun x : Ens => IN x x -> False) ww H).
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc;
 apply IN_sound_right with w2; auto with zfc.
assumption.

Qed.

