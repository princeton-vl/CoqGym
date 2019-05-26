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

(* Definitions of the empty set, pair, union, intersection, comprehension  *)
(*  axiom and powerset, together with their properties                     *)


Require Import Sets.

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


Definition Inter' (E : Ens) : Ens :=
  Comp (Union E) (fun e : Ens => forall a : Ens, IN a E -> IN e a).

Theorem IN_Inter'_all :
 forall E E' : Ens,
 IN E' (Inter' E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
unfold Inter' in |- *.
intros E E' i.
change ((fun e : Ens => forall a : Ens, IN a E -> IN e a) E') in |- *.
apply (IN_Comp_P (Union E) E').
intros.
apply IN_sound_left with w1; auto with zfc.
assumption.
Qed.

Theorem all_IN_Inter' :
 forall E E' E'' : Ens,
 IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter' E).
unfold Inter' in |- *.
intros.
apply IN_P_Comp.
intros; apply IN_sound_left with w1; auto with zfc.
apply IN_Union with (E' := E''); auto with zfc.
auto with zfc.
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
