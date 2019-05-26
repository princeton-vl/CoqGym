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
Require Export Plump.




Lemma Vee_sound : forall E1 E2 : Ens, EQ E1 E2 -> EQ (Vee E1) (Vee E2).
simple induction E1; intros A1 f1 HR1; simple induction E2; intros A2 f2 HR2.
simple induction 1; intros e1 e2.
apply INC_EQ; unfold INC in |- *.
change
  (forall E : Ens,
   IN E (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1))))) ->
   IN E (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2)))))) 
 in |- *.
intros E i.
apply
 IN_sound_right with (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1)))));
 try trivial with zfc.
apply Union_sound.
split.
intros a1; elim (e1 a1).
intros a2 h.
exists a2.
apply Power_sound.
apply HR1.
assumption.

intros a2; elim (e2 a2); intros a1 h; exists a1; apply Power_sound;
 auto with zfc.

change
  (forall E : Ens,
   IN E (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2))))) ->
   IN E (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1)))))) 
 in |- *.


intros E i.
apply
 IN_sound_right with (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2))))).
apply Union_sound.
split.
intros a2; elim (e2 a2); intros a1 h; exists a1.
apply Power_sound; auto with zfc.

intros a1; elim (e1 a1); intros a2 h; exists a2.
apply Power_sound; auto with zfc.

assumption.
Qed.



Lemma IN_Vee :
 forall V W : Ens, IN W V -> forall E : Ens, INC E (Vee W) -> IN E (Vee V).
simple induction V; intros A f HR.
intros W i E inc.
change (IN E (Union (sup A (fun a : A => Power (Vee (f a)))))) in |- *.
apply IN_Union with (Power (Vee W)).
elim i; intros a h.
exists a.
apply Power_sound; apply Vee_sound; auto with zfc.

auto with zfc.
apply INC_IN_Power.
assumption.
Qed.

Lemma INC_IN_Vee_Succ :
 forall E L : Ens, Ord L -> INC E (Vee L) -> IN E (Vee (Succ L)).
simple induction L; intros A f HR.
intros o inc.
unfold Succ in |- *.
apply IN_Vee with (sup A f).
apply IN_P_Comp.
intros; apply Ord_sound with w1; auto with zfc.

auto with zfc.
apply INC_IN_Power; auto with zfc.

assumption.

assumption.
Qed.

Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) :=
  match c with
  | dep_i a p => a
  end.

Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) :=
  match c return (P (PI1 A P c)) with
  | dep_i a p => p
  end.



Lemma IN_Vee_EXType :
 forall E X : Ens,
 IN X (Vee E) -> EXType Ens (fun Y : Ens => IN Y E /\ INC X (Vee Y)).
simple induction E; intros A f HR X.
intros i.
change (IN X (Union (sup A (fun a : A => Power (Vee (f a)))))) in i.
elim (Union_IN _ _ i).
intros T c.
elim c; intros i1 i2.
elim i1; intros a e.
exists (f a); split.
exists a; auto with zfc.

apply IN_Power_INC.
apply IN_sound_right with T; auto with zfc.
Qed.

Lemma mon_Vee : forall E1 E2 : Ens, INC E1 E2 -> INC (Vee E1) (Vee E2).
intros E1 E2 inc; unfold INC in |- *; intros X i.
elim (IN_Vee_EXType _ _ i).
intros Y; simple induction 1; intros i1 inc1.
apply IN_Vee with Y; auto with zfc.

Qed.

 Hint Resolve IN_Power_INC: zfc.
Lemma IN_Succ_INC : forall E X : Ens, IN X (Succ E) -> INC X E.
unfold Succ in |- *.
intros E X i.
cut (IN X (Power E)).
auto with zfc.
auto with zfc.

apply (Comp_INC (Power E) Ord); try trivial with zfc.
Qed.


Hint Resolve Ord_Succ: zfc.

Lemma IN_Vee_Succ_EXType :
 forall E X : Ens,
 Ord E ->
 IN X (Vee (Succ E)) ->
 EXType _ (fun Y : Ens => INC Y E /\ Ord Y /\ INC X (Vee Y)).
intros E X o i.
elim (IN_Vee_EXType _ _ i).
intros Y; simple induction 1; intros i1 inc.
exists Y; split.
apply IN_Succ_INC; auto with zfc.

split.
auto with zfc.
apply IN_Ord_Ord with (Succ E); auto with zfc.

auto with zfc.
Qed.

Lemma IN_Vee_Succ :
 forall E X : Ens,
 Ord E ->
 forall Y : Ens, Ord Y -> INC Y E -> INC X (Vee Y) -> IN X (Vee (Succ E)).
intros E X o Y o1 inc inc1.
apply IN_Vee with Y.
auto with zfc.
unfold Succ in |- *; apply IN_P_Comp; auto with zfc.
intros; apply Ord_sound with w1; auto with zfc.

auto with zfc.
apply INC_IN_Power; auto with zfc.

auto with zfc.
Qed.


Inductive depprod1 (A : Type) (P : A -> Type) : Type :=
    dep_i1 : forall x : A, P x -> depprod1 A P.

Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) :=
  match c with
  | dep_i1 a p => a
  end.

Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) :=
  match c return (P (PI11 A P c)) with
  | dep_i1 a p => p
  end.


Lemma ex_rk :
 forall E : Ens, depprod1 _ (fun L : Ens => Ord L /\ IN E (Vee L)).



simple induction E; intros A f HR.
exists (Succ (Union (sup A (fun a : A => PI11 _ _ (HR a))))).
split.
apply Ord_Succ.
apply Union_Ord.
simple induction 1; intros a h.
apply
 Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
auto with zfc.

elim (PI21 _ _ (HR a)).
auto with zfc.

apply
 IN_Vee_Succ
  with
    (Union
       (sup A
          (fun a : A =>
           PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)))).

apply Union_Ord.
intros E'; simple induction 1; intros a c.
apply
 Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a));
 auto with zfc.

elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a));
 auto with zfc.

apply Union_Ord.
intros E'; simple induction 1; intros a e.
apply
 Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a));
 auto with zfc.
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a));
 auto with zfc.

auto with zfc.

unfold INC in |- *; intros E' i.
elim i; intros a e.
apply IN_sound_left with (f a); auto with zfc.
cut
 (INC (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a))
    (Union
       (sup A
          (fun a0 : A =>
           PI11 Ens (fun L : Ens => Ord L /\ IN (f a0) (Vee L)) (HR a0))))).
intros inc.
apply
 (mon_Vee (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a))
    (Union
       (sup A
          (fun a0 : A =>
           PI11 Ens (fun L : Ens => Ord L /\ IN (f a0) (Vee L)) (HR a0))))
    inc).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
auto with zfc.

apply IN_INC_Union.
exists a; auto with zfc.

Qed.

