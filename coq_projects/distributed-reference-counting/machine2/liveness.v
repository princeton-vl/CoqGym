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


Require Import List.
Require Import DistributedReferenceCounting.machine2.invariant8.

Unset Standard Proposition Elimination Names.

(** 

Here, we study liveness of the algorithm.
We prove 

1. If there is a message in a queue, there always exists a transition
   that can consume that message.

2. We can define notion of measure and prove that every transition
   (except copy) decrease the mesure.
  
3. Then, the idea was to use the notion of well_found relation so
   a to prove that if we prevent copy transitions, we always reach
   a final configuration where no message can be processed.

   There was a bit of 'coding' to use these well-founded relations.
   
   I needed to talk about configuration which were legal.  So
   I defined a inductive type (a strong dependent sum), legal_config,
   which contains a configuration and a proof that it is legal.

   I then reached two problems, one easy to solve (I think), and
   more difficult.

   a.  I need to convert Z numbers into nat, and I don;t know
       how to do it.
      I had to assume the existence of the following axiom:
     Axiom Z_nat_axiom:
    (x,y:Z)  `0<=x` -> `0<=y` -> `y<x` -> (lt (convert_to_nat y) (convert_to_nat x)).

   b.  Well founded relations must be decidable:
      Definition decidable_relation:=
      [E:Set] [R:E->E->Prop] (x:E){y:E | (R y x)}+{((y:E)~(R y x))}.

     In order to prove that, I had to eliminate H in lemma decidable_no_copy_succ.

     H : (EX t:(class_trans c) | ~(copy_p c t)/\(legal (transition c t)))
          \/((t:(class_trans c))(copy_p c t))
 
     Unfortunately, H is a propositition and  and the Well founded
     relation is a set.  Therefore, we cannot perform an elimination.
  
     So I assumed I has axioms ex_rec and or_rec.  
     Why was legal defined as a Config->Prop and not a set?
     Why not do everything with set?


  BUT, HAVE I PROVED that all no_copy sequences terminate?

There are still more things to prove:
- what's happening when we introduce copy, can we say
  anything about infinite transitions?

*)




Lemma always_process_messages :
 forall c : Config,
 legal c ->
 forall (s1 s2 : Site) (m : Message),
 first Message (bm c s1 s2) = value Message m ->
 exists t : class_trans c,
   legal (transition c t) /\
   bm (transition c t) s1 s2 = first_out Message (bm c s1 s2).
Proof.
  intros c H.
  generalize H.
  elim H.
  simpl in |- *.
  intros; discriminate.
  
  intros c0 t H0 H1 H2 s1 s2 m.
  case m.
  
  (* dec *)
  
  intro.
  split with (receive_dec (transition c0 t) s1 s2 H3).
  split.
  apply after.
  auto.
  
  simpl in |- *.
  rewrite collect_here.
  auto.
  
  (* inc_dec *)
  
  intros.
  case (eq_site_dec s2 owner); intro.
  rewrite e in H3.
  split with (receive_inc (transition c0 t) s1 s H3).
  split.
  apply after.
  auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite e.
  rewrite collect_here.
  auto.
  
  left; unfold not in |- *; intro.
  generalize H3; rewrite H4; rewrite empty_q_to_me.
  simpl in |- *.
  intro; discriminate.
  
  auto.
  
  generalize (inc_dec_owner3 (transition c0 t) s1 s2 H2 n); intro.
  elim (H4 s).
  apply first_in.
  auto.

  (* copy *)
  
  elim (decide_rt (transition c0 t) s2); intro.
  case (eq_site_dec s1 owner); intro.
  intro.
  rewrite e in H3.
  split with (receive_copy2 (transition c0 t) s2 a H3).
  split.
  apply after.
  auto.
  
  simpl in |- *.
  rewrite e; rewrite collect_here; auto.
  
  intro.
  cut (s2 <> owner).
  intro.
  split with (receive_copy3 (transition c0 t) s1 s2 a n H4 H3).
  split.
  apply after.
  auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_here; auto.
  left. (* (Left; Auto). *)
  unfold not in |- *; intro; generalize H3.
  rewrite H5; rewrite empty_q_to_me.
  simpl in |- *; intro.
  discriminate.
  
  auto.
  
  unfold not in |- *; intro; generalize a.
  rewrite H4; rewrite owner_rt_true.
  auto with bool.
  
  auto.
  
  intro.
  split with (receive_copy1 (transition c0 t) s1 s2 b H3).
  split.
  apply after; auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_here.
  auto.
  
  case (eq_site_dec s1 s2); intro.
  generalize H3; rewrite e; rewrite empty_q_to_me.
  simpl in |- *; intro; discriminate.
  
  auto.
  
  auto.
Qed.

(* copy predicate *)

Definition copy_p (c : Config) (t : class_trans c) :=
  match t with
  | make_copy s1 s2 h1 h2 => True
  | _ => False
  end.


Section LEGAL_NO_COPY.

(** this inductive definition defines legal_no_copy
   as a predicate over a configuration c, which is accessible
   with legal transitions from a legal config c0,
   without using any copy transition *)

Variable c0 : Config.



Inductive legal_no_copy : Config -> Prop :=
  | no_copy_init : legal c0 -> legal_no_copy c0
  | after_no_copy :
      forall (c : Config) (t : class_trans c),
      ~ copy_p c t -> legal_no_copy c -> legal_no_copy (transition c t).

End LEGAL_NO_COPY.


Lemma legal_no_copy_is_legal :
 forall c c0 : Config, legal_no_copy c0 c -> legal c.
Proof.
  intros.
  elim H.
  auto.
  intros.
  apply after.
  auto.
Qed.


Lemma decide_empty_queue :
 forall (c : Config) (s1 s2 : Site),
 {bm c s1 s2 = empty Message} + {bm c s1 s2 <> empty Message}.
Proof.
  intros.
  elim (bm c s1 s2).
  left; auto.
  
  simpl in |- *; right.
  discriminate.
Qed.


Definition no_message (c : Config) :=
  forall s1 s2 : Site, In s1 LS -> In s2 LS -> bm c s1 s2 = empty Message.

Lemma decide_no_message :
 forall c : Config, {no_message c} + {~ no_message c}.
Proof.
  intros.
  unfold no_message in |- *.
  simpl in |- *.
  pattern LS at 1 3 in |- *.
  elim LS.
  simpl in |- *.
  left; intros; contradiction.
  
  simpl in |- *.
  intros.
  elim H.
  clear H.
  elim LS.
  simpl in |- *.
  intro.
  left.
  intros; contradiction.
  
  intros.
  elim H.
  intros.
  elim (decide_empty_queue c a a0); intro.
  left.
  simpl in |- *.
  intros.
  elim H0; intro.
  elim H1; intro.
  rewrite <- H2; rewrite <- H3; auto.
  
  apply a2.
  auto.
  
  auto.
  
  elim H1; intro.
  apply a1.
  auto.
  
  simpl in |- *.
  auto.
  
  apply a2.
  auto.
  
  auto.
  
  right.
  unfold not in |- *.
  intro.
  generalize (H0 a a0).
  intro.
  elim b.
  apply H1.
  auto.
  
  simpl in |- *; auto.
  
  intro.
  right.
  unfold not in |- *; intro.
  elim b.
  intros.
  apply H0.
  auto.
  
  simpl in |- *; auto.
  
  intros.
  apply a1.
  auto.
  
  simpl in |- *; auto.
  
  intro.
  right.
  unfold not in |- *; intro.
  elim b.
  intros.
  apply H0.
  auto.
  
  auto.
Qed.

Lemma decide_exist_non_empty_queue1 :
 forall (c : Config) (a : Site),
 legal c ->
 {(forall s2 : Site, In s2 LS -> bm c a s2 = empty Message)} +
 {~ (forall s2 : Site, In s2 LS -> s2 <> a -> bm c a s2 = empty Message)}.
Proof.
  intros.
  elim LS.
  simpl in |- *.
  left; intros; contradiction.
  
  simpl in |- *.
  intros.
  elim (decide_empty_queue c a a0); intro.
  case (eq_site_dec a a0); intro.
  elim H0; intro.
  left; intros.
  elim H1; intros.
  rewrite <- H2.
  auto.
  
  apply a2.
  auto.
  
  right.
  unfold not in |- *; intros.
  elim b; intros.
  unfold not in |- *.
  apply H1.
  auto.
  
  intro.
  elim H3; auto.
  
  elim H0; intros.
  left; intros.
  case (eq_site_dec s2 a0); intro.
  rewrite e; auto.
  
  elim H1; intro.
  elim n0; auto.
  
  apply a2; auto.
  
  right.
  unfold not in |- *; intros.
  elim b; intros.
  unfold not in |- *.
  apply H1.
  auto.
  
  intro; elim H3; auto.
  
  elim H0; intros.
  case (eq_site_dec a a0); intro.
  elim b.
  rewrite e.
  rewrite empty_q_to_me.
  auto.
  
  auto.
  
  right.
  unfold not in |- *; intros.
  generalize (H1 a0); intro.
  cut (a0 = a0 \/ In a0 l).
  intro.
  generalize (H2 H3); intro.
  decompose [and] H4.
  elim b; auto.
  
  auto.
  
  right.
  unfold not in |- *; intro.
  elim b0.
  unfold not in |- *; intros.
  apply H1.
  auto.
  
  auto.

Qed.


Lemma exist_non_empty_queue :
 forall c : Config,
 legal c ->
 ~ no_message c ->
 exists s1 : Site,
   (exists s2 : Site, s1 <> s2 /\ bm c s1 s2 <> empty Message).

Proof.
  unfold no_message in |- *.
  intro.
  pattern LS at 1 in |- *.
  elim LS.
  simpl in |- *.
  intros.
  elim H0.
  intros; contradiction.
  
  simpl in |- *.
  intros a l H HLeg.
  elim (decide_exist_non_empty_queue1 c a HLeg); intro.
  intro.
  apply H.
  auto.
  
  unfold not in |- *; intro.
  elim H0; intros.
  elim H2; intro.
  rewrite <- H4.
  apply a0.
  auto.
  
  apply H1.
  auto.
  
  auto.
  
  intros.
  split with a.
  generalize b.
  elim LS.
  simpl in |- *.
  intro.
  elim b0; intros; contradiction.
  
  clear H.
  clear H0.
  clear b.
  simpl in |- *.
  intros.
  elim (decide_empty_queue c a a0); intro.
  apply H.
  unfold not in |- *; intros.
  elim b; intros.
  elim H1; intro.
  rewrite <- H3; auto.
  
  apply H0.
  auto.
  
  auto.
  
  case (eq_site_dec a a0); intro.
  elim b0; rewrite e; rewrite empty_q_to_me; auto.
  
  split with a0.
  split; auto.
Qed.


(**

Define a measure:
  for instance: 2 for inc_dec
                1 for dec.
                2 for rt=true
  Show that any legal_no_copy transition
  decreases the measure.
  By induction, there is a minimum.
*)


Definition termination_count (m : Message) :=
  match m with
  | copy => 5%Z
  | dec => 1%Z
  | inc_dec s3 => 2%Z
  end.

Definition termination_q_count (s1 s2 : Site) (q : queue Message) :=
  reduce Message termination_count q.

Definition termination_q_measure (bm : Bag_of_message) :=
  sigma2_table Site LS LS (queue Message) termination_q_count bm.
Definition termination_rt_count (b : bool) := if b then 2%Z else 0%Z.

Definition termination_rt_measure (t : Site -> bool) :=
  sigma_table Site LS Z (Z_id Site)
    (fun s : Site => termination_rt_count (t s)).

Definition termination_measure (c : Config) :=
  (termination_rt_measure (rt c) + termination_q_measure (bm c))%Z.

Inductive legal_no_copy2 : Config -> Config -> Prop :=
  | no_copy_init2 : forall c : Config, legal c -> legal_no_copy2 c c
  | after_no_copy2 :
      forall (c c0 : Config) (t : class_trans c),
      ~ copy_p c t ->
      legal_no_copy2 c c0 -> legal_no_copy2 (transition c t) c0.


Lemma legal_no_copy_transitive2 :
 forall c0 : Config,
 legal c0 ->
 forall c1 c2 : Config,
 legal_no_copy2 c1 c0 -> legal_no_copy2 c2 c1 -> legal_no_copy2 c2 c0.
Proof.
  intros.
  generalize H0.
  elim H1.
  auto.
  
  intros.
  apply after_no_copy2.
  auto.
  
  apply H4.
  auto.
Qed.

Remark add_reduce2 :
 forall x y z a : Z, x = a -> (x + (y + z))%Z = (a + y + z)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce3 :
 forall x y z a : Z, x = a -> y = z -> (x + y)%Z = (a + z)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce10 :
 forall x y w z a : Z,
 w = y -> (a > 0)%Z -> (x + (y + (z - a)) < x + (w + z))%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce11 :
 forall x1 x2 y w z a b : Z,
 x1 = x2 ->
 w = y -> (b - a < 0)%Z -> (x1 + b + (y + (z - a)) < x2 + (w + z))%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce12 : forall x y : Z, x = y -> x = (y + 0)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce13 :
 forall x1 x2 y w z a b : Z,
 x1 = x2 ->
 w = y -> (b + a < 0)%Z -> (x1 + b + (y + (z + a)) < x2 + (w + z))%Z.
Proof.
intros; omega.
Qed.


Remark add_reduce14 :
 forall x1 x2 x3 y w z a b : Z,
 x1 = x2 ->
 w = y -> (b + a < x3)%Z -> (x1 + b + (y + (z + a)) < x2 + x3 + (w + z))%Z.
Proof.
intros; omega.
Qed.


Remark add_reduce15 : forall x y a : Z, (x < y)%Z -> (a + x < a + y)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce16 :
 forall x1 x2 y b : Z,
 x1 = x2 -> (1 - b < 0)%Z -> (x1 - b + (y + 1) < x2 + y)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce17 : forall x y a : Z, x = y -> (x + a)%Z = (y + a)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce18 : forall x y a : Z, x = y -> a = 0%Z -> x = (y + a)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce19 :
 forall x1 x2 x3 y1 y2 y3 y4 : Z,
 x1 = y1 ->
 (y2 - y4 + (y3 + 1) < x2 + x3)%Z ->
 (y1 + (y2 - y4) + (y3 + 1) < x1 + x2 + x3)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce22 :
 forall a b x0 y0 x1 x2 x3 y1 y2 y3 y4 : Z,
 x1 = y1 ->
 a = b ->
 (x0 + (y2 - y4) + (y3 + 2) < y0 + x2 + x3)%Z ->
 (a + x0 + (y1 + (y2 - y4) + (y3 + 2)) < b + y0 + (x1 + x2 + x3))%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce23 :
 forall x y : Z, (x >= 0)%Z -> (y >= 0)%Z -> (0 <= x + y)%Z.
Proof.
intros; omega.
Qed.

(* 
Section BUT_XY.

Variable Data: Set.
Local Table2:=  Site ->  Site -> Data.
Variable f: Site -> Site -> Data->Z.


Lemma sigma2_sigma2_but_x_y:
 (s0,s1:Site) (t:Table2)
 (sigma2_table Site LS LS Data f t) = `(sigma2_but_table Site eq_site_dec LS LS Data s0 s1 f t) 
                                       + (f s0 s1 (t s0 s1))`.
Proof.
  Intro.
  Intro.
  Intro.
  Generalize (finite_site s1).
  Generalize (finite_site s0).
  (Pattern 1 3 5 LS; Elim LS).
  Simpl.
  (Intros; Contradiction).
  
  Intros.
  Unfold sigma2_table sigma2_but_table.
  Simpl.
  (Case (eq_site_dec a s0); Intro).
  Unfold sigma_table.
  Rewrite (sigma_sigma_but Site a eq_site_dec).
  Rewrite (sigma_sigma_but Site a eq_site_dec) with l:=(cons a l).
  Simpl.
  Case (eq_site_dec a a).
  Intro.
  Case (eq_site_dec a s0).
  Intro.
  Rewrite <- sigma_sigma_but_not_in with x0:=a.
  Rewrite <- sigma_sigma_but_not_in with x0:=a.
  Rewrite (sigma_sigma_but Site s1 eq_site_dec) with l:=LS.
  Unfold sigma_but_table.
  Rewrite e1.
  Unfold Z_id.
  Apply add_reduce2.
  Apply sigma_simpl.
  Intros.
  Case (eq_site_dec x s0).
  Intro.
  (Generalize H0; Rewrite e1).
  Simpl.
  (Case (eq_site_dec s0 s0); Intro).
  Intro.
  (Elim H3; Rewrite <- e2; Auto).
  
  (Elim n; Auto).
  
  Intro.
  Auto.
  
  Auto.
  
  (Generalize H0; Simpl).
  Rewrite e.
  (Case (eq_site_dec s0 s0); Intro).
  Auto.
  
  (Elim n; Auto).
  
  (Generalize H0; Simpl).
  (Case (eq_site_dec s0 a); Intro).
  (Rewrite e; Auto).
  
  (Elim n; Auto).
  
  Intro.
  (Elim n; Auto).
  
  Intro.
  (Elim n; Auto).
  
  (Rewrite e; Auto).
  (Generalize H0; Rewrite e; Auto).
  
  (Generalize H0; Rewrite e).
  Auto.
  
  (Unfold sigma_table; Simpl).
  Generalize H.
  Unfold sigma2_table.
  Unfold sigma_table.
  Intro.
  Rewrite H2.
  (Unfold Z_id; Simpl).
  (Case (eq_site_dec a s0); Intro).
  (Elim n; Auto).
  
  Unfold sigma2_but_table.
  Unfold sigma_table.
  Unfold Z_id.
  Omega.
  
  (Generalize H0; Simpl).
  (Case (eq_site_dec s0 a); Intro).
  (Elim n; Auto).
  
  Auto.
  
  Auto.
    
Save.

Lemma sigma2_but_simpl : (s0,s1:Site) (t:Table2) (f,g:Site->Site->Data->Z)
 ((x,y:Site) ~((x=s0)/\(y=s1))->(f x y (t x y))=(g x y (t x y)))->
  (sigma2_but_table Site eq_site_dec LS LS Data s0 s1 f t)
  =
  (sigma2_but_table Site eq_site_dec LS LS Data s0 s1 g t ).
Proof.
  Intros.
  Generalize (finite_site s1).
  Generalize (finite_site s0).
  (Pattern 1 3 5 LS; Elim LS).
  Simpl.
  (Intros; Contradiction).
  
  Simpl.
  Intros a l.
  (Case (eq_site_dec s0 a); Intro).
  Rewrite e.
  Simpl.
  Intros.
  Unfold sigma2_but_table.
  (Unfold sigma_table; Simpl).
  Unfold Z_id.
  (Case (eq_site_dec a a); Intro).
  Apply add_reduce3.
  Generalize H2.
  (Elim LS; Simpl).
  (Intro; Contradiction).
  
  Intros.
  (Unfold sigma_but_table; Simpl).
  Generalize H4.
  (Case (eq_site_dec a0 s1); Intro).
  Rewrite e1.
  (Case (eq_site_dec s1 s1); Intros).
  Rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  Rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro).
  Decompose [and] H7.
  (Elim H5; Rewrite <- H10; Auto).
  
  Auto.
  
  Exact H5.
  
  (Elim n; Auto).
  
  (Case (eq_site_dec s1 a0); Intro).
  (Elim n; Auto).
  
  Intros.
  Apply add_reduce3.
  Apply H.
  (Unfold not; Intro).
  Decompose [and] H6.
  (Elim n; Auto).
  
  Generalize H3.
  Unfold sigma_but_table.
  Auto.
  
  Apply sigma_simpl.
  Intros.
  (Case (eq_site_dec x a); Intro).
  (Elim H1; Rewrite <- e1; Auto).
  
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro).
  (Decompose [and] H5; Elim n; Rewrite <- e; Auto).
  
  (Elim n; Auto).
  
  Unfold sigma2_but_table.
  (Unfold sigma_table; Simpl).
  Intros.
  (Case (eq_site_dec a s0); Intro).
  (Elim n; Auto).
  
  Rewrite H0.
  Apply add_reduce3.
  Unfold Z_id.
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro; Elim n0).
  (Decompose [and] H4; Auto).
  
  Auto.
  
  Auto.
  
  Auto.

Save.

(* Interestingly, the proof of the following Lemma is exactly the same
as the proof of the previous lemma *)

Lemma sigma2_but_simpl2 : (s0,s1:Site) (t1,t2:Table2) (f:Site->Site->Data->Z)
 ((x,y:Site) ~((x=s0)/\(y=s1))->(f x y (t1 x y))=(f x y (t2 x y)))->
  (sigma2_but_table Site eq_site_dec LS LS Data s0 s1 f t1)
  =
  (sigma2_but_table Site eq_site_dec LS LS Data s0 s1 f t2 ).
Proof.
  Intros.
  Generalize (finite_site s1).
  Generalize (finite_site s0).
  (Pattern 1 3 5 LS; Elim LS).
  Simpl.
  (Intros; Contradiction).
  
  Simpl.
  Intros a l.
  (Case (eq_site_dec s0 a); Intro).
  Rewrite e.
  Simpl.
  Intros.
  Unfold sigma2_but_table.
  (Unfold sigma_table; Simpl).
  Unfold Z_id.
  (Case (eq_site_dec a a); Intro).
  Apply add_reduce3.
  Generalize H2.
  (Elim LS; Simpl).
  (Intro; Contradiction).
  
  Intros.
  (Unfold sigma_but_table; Simpl).
  Generalize H4.
  (Case (eq_site_dec a0 s1); Intro).
  Rewrite e1.
  (Case (eq_site_dec s1 s1); Intros).
  Rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  Rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro).
  Decompose [and] H7.
  (Elim H5; Rewrite <- H10; Auto).
  
  Auto.
  
  Exact H5.
  
  (Elim n; Auto).
  
  (Case (eq_site_dec s1 a0); Intro).
  (Elim n; Auto).
  
  Intros.
  Apply add_reduce3.
  Apply H.
  (Unfold not; Intro).
  Decompose [and] H6.
  (Elim n; Auto).
  
  Generalize H3.
  Unfold sigma_but_table.
  Auto.
  
  Apply sigma_simpl.
  Intros.
  (Case (eq_site_dec x a); Intro).
  (Elim H1; Rewrite <- e1; Auto).
  
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro).
  (Decompose [and] H5; Elim n; Rewrite <- e; Auto).
  
  (Elim n; Auto).
  
  Unfold sigma2_but_table.
  (Unfold sigma_table; Simpl).
  Intros.
  (Case (eq_site_dec a s0); Intro).
  (Elim n; Auto).
  
  Rewrite H0.
  Apply add_reduce3.
  Unfold Z_id.
  Apply sigma_simpl.
  Intros.
  Apply H.
  (Unfold not; Intro; Elim n0).
  (Decompose [and] H4; Auto).
  
  Auto.
  
  Auto.
  
  Auto.
Save.

End BUT_XY.

*)

(* another way of defining sigma_but:

   On the one hand, it is less convenient, because the functional
   argument is changed, which later, if we use sigma2_simpl, will
   imply a tedious case analysis.


   On the other hand, it is more convenient, because I can
   apply sigma2_but several times, there are transformed into
   a sigma2_table.
*)
(*
Lemma new_sigma2_sigma2_but_x_y:
 (s0,s1:Site)(Data:Set) (f:Site->Site->Data->Z)
 (t:Site ->  Site -> Data)
 (sigma2_table Site LS LS Data f t) = `(new_sigma2_but_table Site eq_site_dec LS LS Data s0 s1 f t) 
                                       + (f s0 s1 (t s0 s1))`.
Proof.
  Intros.
  Unfold new_sigma2_but_table.
  Rewrite sigma2_sigma2_but_x_y with s0:=s0 s1:=s1.
  Apply add_reduce17.
  Rewrite sigma2_sigma2_but_x_y with s0:=s0 s1:=s1.
  Apply add_reduce18.
  Apply sigma2_but_simpl.
  Intros.
  (Case (eq_site_dec x s0); Intro).
  (Case (eq_site_dec y s1); Intro).
  (Elim H; Auto).
  Auto.
  Auto.
  Rewrite case_eq.
  Rewrite case_eq.
  Auto.
Save.

*)


Lemma termination_measure_decreases :
 forall (c : Config) (t : class_trans c),
 legal c ->
 ~ copy_p c t ->
 (termination_measure (transition c t) < termination_measure c)%Z.

Proof.
  simple induction t; simpl in |- *;
   unfold termination_measure, termination_rt_measure, termination_q_measure
    in |- *; simpl in |- *; intros.

  (* 1 *)

  elim H0; auto.

  (* 2 *)
  
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s1)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  rewrite collect_here.
  unfold termination_q_count in |- *.
  rewrite reduce_first_out with (m := dec).
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s1)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  apply add_reduce10.
  apply sigma2_but_simpl2.
  intros.
  rewrite collect_elsewhere.
  auto.
  
  case (eq_queue_dec s1 x s2 y); intro.
  elim H1; auto.
  decompose [and] a; split; auto.
  
  auto.
  apply finite_site.
  apply finite_site.

  
  unfold termination_count in |- *; simpl in |- *.
  omega.
  apply finite_site.
  apply finite_site.

  auto.
  apply finite_site.
  apply finite_site.

  (* 3 *)

  apply add_reduce15.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := owner)
                            (s1 := s3)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := owner)
                            (s1 := s3)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  rewrite post_here.
  unfold termination_q_count in |- *; simpl in |- *.
  rewrite collect_elsewhere.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := owner)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := owner)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  case (eq_site_dec s1 owner); intro.
  generalize e; rewrite e0.
  rewrite empty_q_to_me; simpl in |- *.
  intro; discriminate.
  auto.
  rewrite post_elsewhere.
  rewrite collect_here.
  rewrite reduce_first_out with (m := inc_dec s3).
  apply add_reduce19.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intro.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros.
  case (eq_site_dec e0 s1); intro.
  case (eq_site_dec x owner); intro.
  auto.
  case (eq_site_dec e0 owner); intro.
  case (eq_site_dec x s3); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  case (eq_site_dec e0 owner); intro.
  case (eq_site_dec x s3); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  unfold termination_count in |- *; simpl in |- *.
  omega.
  auto.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  left; unfold not in |- *; intro.
  generalize e; rewrite H1; rewrite empty_q_to_me.
  simpl in |- *; intro; discriminate.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.

  (* 4 *)

  apply add_reduce15.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s2)
                            (s1 := s1)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s2)
                            (s1 := s1)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  rewrite post_here.
  unfold termination_q_count in |- *; simpl in |- *.
  rewrite collect_elsewhere.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := s2)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := s2)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  case (eq_site_dec s1 s2); intro.
  generalize e0; rewrite e1; rewrite empty_q_to_me; simpl in |- *.
  intro; discriminate.
  auto.
  rewrite post_elsewhere.
  rewrite collect_here.
  rewrite reduce_first_out with (m := copy).
  apply add_reduce19.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intro.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros.
  case (eq_site_dec e1 s1); intro.
  case (eq_site_dec x s2); intro.
  auto.
  case (eq_site_dec e1 s2); intro.
  case (eq_site_dec x s1); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  case (eq_site_dec e1 s2); intro.
  case (eq_site_dec x s1); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  unfold termination_count in |- *; simpl in |- *.
  omega.
  auto.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  left; unfold not in |- *; intro.
  generalize e0; rewrite H1; rewrite empty_q_to_me; simpl in |- *.
  intro; discriminate.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.

  (* 5 *)
  
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := owner)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  rewrite collect_here.
  unfold termination_q_count in |- *.
  rewrite reduce_first_out with (m := copy).
  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site s2 eq_site_dec).
  unfold Z_id in |- *.
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := owner)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  apply add_reduce11.
  rewrite (sigma_sigma_but Site s2 eq_site_dec).
  rewrite e; unfold termination_rt_count in |- *.
  simpl in |- *.
  apply add_reduce12.
  apply sigma_but_simpl.
  intros.
  unfold Set_rec_table in |- *.
  cut (change_site bool (rt c) s2 true s = rt c s).
  intro.
  rewrite H2.
  auto.
  
  rewrite other_site.
  auto.
  auto.
  apply finite_site.
  apply sigma2_but_simpl2.
  intros.
  case (eq_queue_dec owner x s2 y); intro.
  elim H1; decompose [and] a.
  split; auto.
  rewrite collect_elsewhere.
  auto.
  auto.
 apply finite_site.
 apply finite_site.
  unfold termination_rt_count in |- *; unfold Set_rec_table in |- *.
  unfold termination_count in |- *; simpl in |- *.
  cut (change_site bool (rt c) s2 true s2 = true).
  intro.
  rewrite H1.
  omega.
  rewrite that_site; auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  auto.
  apply finite_site.
  apply finite_site.

  (* 6 *)

  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site s2 eq_site_dec).
  unfold Z_id in |- *.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s2)
                            (s1 := owner)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s2)
                            (s1 := owner)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  rewrite post_here.
  unfold termination_q_count in |- *; simpl in |- *.
  rewrite collect_elsewhere.
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := s2)
                            (eq_site_dec := eq_site_dec).
  rewrite
   new_sigma2_sigma2_but_x_y
                             with
                             (s0 := s1)
                            (s1 := s2)
                            (eq_site_dec := eq_site_dec).
  unfold new_sigma2_but_table in |- *.
  case (eq_site_dec s1 s2); intro.
  generalize e0; rewrite e1; rewrite empty_q_to_me; simpl in |- *.
  intro; discriminate.
  auto.
  rewrite post_elsewhere.
  rewrite collect_here.
  rewrite reduce_first_out with (m := copy).
  rewrite (sigma_sigma_but Site s2 eq_site_dec).
  apply add_reduce22.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intro.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros.
  case (eq_site_dec e1 s1); intro.
  case (eq_site_dec x s2); intro.
  auto.
  case (eq_site_dec e1 s2); intro.
  case (eq_site_dec x owner); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  case (eq_site_dec e1 s2); intro.
  case (eq_site_dec x owner); intro.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  rewrite post_elsewhere.
  rewrite collect_elsewhere; auto.
  auto.
  apply sigma_but_simpl.
  intros.
  unfold Set_rec_table in |- *; rewrite other_site.
  auto.
  auto.
  unfold Set_rec_table in |- *; rewrite that_site.
  rewrite e.
  unfold termination_rt_count in |- *.
  cut (termination_count copy > 4)%Z.
  intro.
  omega.
  simpl in |- *.
  omega.
  apply finite_site.
  auto.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  left; unfold not in |- *; intro; generalize e0.
  rewrite H1; rewrite empty_q_to_me.
  simpl in |- *; intro; discriminate.
  auto.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.


  (* 7 *)
  
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s)
                        (s1 := owner)
                        (eq_site_dec := eq_site_dec).
  rewrite post_here.
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s)
                        (s1 := owner)
                        (eq_site_dec := eq_site_dec).
  unfold termination_q_count in |- *.
  simpl in |- *.
  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site s eq_site_dec).
  unfold Z_id in |- *.
  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site s eq_site_dec).
  apply add_reduce14.
  apply sigma_but_simpl.
  intros.
  unfold Reset_rec_table in |- *.
  rewrite other_site.
  auto.
  auto.
  apply sigma2_but_simpl2.
  intros.
  case (eq_queue_dec s x owner y); intro.
  elim H1; decompose [and] a.
  split; auto.
  rewrite post_elsewhere; auto.
  apply finite_site.
  apply finite_site.
 unfold Reset_rec_table in |- *; rewrite that_site.
  rewrite e0.
  unfold termination_rt_count in |- *; simpl in |- *.
  omega.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
  apply finite_site.
Qed.

Lemma termination_measure_positive :
 forall c : Config, (0 <= termination_measure c)%Z.
Proof.
  unfold termination_measure in |- *.
  unfold termination_rt_measure, termination_q_measure in |- *.
  intros.
  apply add_reduce23.
  unfold sigma_table in |- *.
  apply sigma_pos.
  intros.
  unfold Z_id in |- *.
  unfold termination_rt_count in |- *.
  case (rt c x_).
  omega.
  
  omega.
  
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  apply sigma_pos.
  intros.
  unfold Z_id in |- *.
  apply sigma_pos.
  intros.
  unfold termination_q_count in |- *.
  apply reduce_positive_or_null.
  intros.
  unfold termination_count in |- *.
  case a.
  omega.
  
  intro; omega.
  
  omega.
Qed.

Definition no_rt (c : Config) :=
  forall s1 : Site, In s1 LS -> s1 <> owner -> rt c s1 = false.

Lemma decide_no_rt :
 forall c : Config,
 {no_rt c} + {(exists s1 : Site, s1 <> owner /\ rt c s1 = true)}.
Proof.
  intros.
  unfold no_rt in |- *.
  elim LS.
  simpl in |- *.
  left; contradiction.
  
  intros.
  case (eq_site_dec a owner); intro.
  elim H; intro.
  left.
  intros.
  generalize H0; simpl in |- *.
  case (eq_site_dec s1 a); intro.
  elim H1; rewrite e0; auto.
  
  intro.
  elim H2; auto.
  intro; elim n; auto.
  
  right; auto.
  
  elim (decide_rt c a); intro.
  elim H; intro.
  left; intros.
  case (eq_site_dec s1 a); intro.
  rewrite e; auto.
  
  apply a1.
  generalize H0; simpl in |- *; intro.
  elim H2; intro; auto.
  elim n0; auto.
  
  auto.
  
  right; auto.
  
  right.
  split with a.
  auto.
Qed.


(** to be complete, we might represent explicitly a local gc! 
and we could try to prove something like this.
 If there is a s1, it means that the gc is has kicked in 


Variable local_gc: Config -> Site -> bool.


Lemma decide_no_rt_gc:
  (c:Config) 
   {(s1:Site) (In s1 LS) -> ~(s1=owner) ->  (rt c s1)=true -> (local_gc c s1)=false}
   +
   {(EX s1:Site |  (In s1 LS) -> ~(s1=owner) /\ (rt c s1)=true /\ (local_gc c s1)=true)}.

*)

Lemma blocked_config :
 forall c : Config,
 legal c ->
 no_message c -> no_rt c -> ~ (exists t : class_trans c, ~ copy_p c t).
Proof.
  unfold no_message, no_rt in |- *.
  intros.
  unfold not in |- *; intro.
  elim H2.
  simple induction x; simpl in |- *; intros.
  apply H3; auto.
  generalize e.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0; rewrite H1.
  discriminate.
  apply in_s_LS.
  auto.
Qed.

Lemma blocked_config2 :
 forall c : Config,
 legal c -> no_message c -> no_rt c -> forall t : class_trans c, copy_p c t.
Proof.
  unfold no_message, no_rt in |- *.
  simple induction t; simpl in |- *; intros; auto.
  generalize e.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0.
  rewrite H0.
  simpl in |- *.
  intro; discriminate.
  apply in_s_LS.
  apply in_s_LS.
  generalize e0; rewrite H1.
  discriminate.
  apply in_s_LS.
  auto.
Qed.



Section LOGIC.
Variable U : Set.

Lemma ex_not_not_all :
 forall P : U -> Prop, (exists n : U, ~ P n) -> ~ (forall n : U, P n).
Proof.
unfold not in |- *; intros P exnot allP.
elim exnot; auto.
Qed.


Lemma ex_not_not_all2 :
 forall P : U -> Prop, (exists n : U, P n) -> ~ (forall n : U, ~ P n).
Proof.
  unfold not in |- *; intros P exnot allP.
  elim exnot; auto.
Qed.

Lemma PNNP : forall p : Prop, p -> ~ ~ p.
Proof.
intros.
auto.
Qed.

End LOGIC.


Lemma sigma_f_null :
 forall (E : Set) (f : E -> Z) (l : list E),
 (forall x_ : E, f x_ = 0%Z) -> sigma E l f = 0%Z.
Proof.
 intros; elim l; simpl in |- *.
 omega.

 intros; generalize (H a); omega.
Qed.


Lemma null_st :
 forall (c0 : Config) (s0 : Site),
 legal c0 -> s0 <> owner -> no_message c0 -> st c0 s0 = 0%Z.
Proof.
  intros.
  rewrite invariant2.
  unfold sigma_rooted in |- *.
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  unfold Z_id in |- *.
  apply sigma_f_null.
  intros.
  apply sigma_f_null.
  intros.
  generalize H1; unfold no_message in |- *.
  intro.
  rewrite H2.
  simpl in |- *.
  auto.
  apply in_s_LS.
  apply in_s_LS.
  auto.
  auto.
Qed.

Lemma not_empty_implies_last :
 forall (E : Set) (q : queue E),
 q <> empty E -> exists x : E, first E q = value E x.
Proof.
  intro.
  simple induction q.
  auto.
  intros.
  elim H; auto.
  intros d q0.
  case q0.
  simpl in |- *.
  intros.
  split with d.
  auto.
  simpl in |- *.
  intros.
  apply H.
  discriminate.
Qed.

Lemma different_queue1 :
 forall (E : Set) (q : queue E) (m : E), input E m q <> first_out E q.
Proof.
  intro.
  simple induction q.
  simpl in |- *.
  intros.
  discriminate.
  intros.
  simpl in |- *.
  generalize H.
  case q0.
  simpl in |- *.
  intros.
  discriminate.
  intros.
  cut (input E d (input E e q1) <> first_out E (input E e q1)).
  intro.
  injection.
  intros.
  elim H1; auto.
  auto.
Qed.

Lemma different_queue2 :
 forall (E : Set) (q : queue E) (m : E),
 first E q = value E m -> q <> first_out E q.
Proof.
  intro.
  simple induction q.
  simpl in |- *; intros; discriminate.
  
  intro; intro.
  case q0.
  simpl in |- *.
  intros.
  discriminate.
  
  intros.
  cut
   (first_out E (input E d (input E e q1)) =
    input E d (first_out E (input E e q1))).
  intro.
  rewrite H1.
  injection.
  generalize H; unfold not in |- *; intro.
  intro.
  apply (H3 m).
  auto.
  
  auto.
  
  simpl in |- *; auto.
Qed.

(** decide if there is a legal successor 
   Ideally, I should have introduce a decidable predicate
   to decide if Delete transitions were permitted. *)

Lemma decide_no_copy_successor :
 forall c : Config,
 legal c ->
 (exists t : class_trans c, ~ copy_p c t /\ legal (transition c t)) \/
 (forall t : class_trans c, copy_p c t).

Proof.
  intros.
  elim (decide_no_message c); intro.
  elim (decide_no_rt c); intro.
  right.
  intros.
  apply blocked_config2.
  auto.
  auto.
  auto.
  elim b.
  intros.
  decompose [and] H0.
  generalize (null_st c x H H1 a).
  intro.
  left.
  split with (delete_entry c x H3 H2 H1).
  split.
  unfold copy_p in |- *.
  unfold not in |- *; contradiction.
  
  apply after.
  auto.
  
  elim (exist_non_empty_queue c H b).
  intros.
  elim H0.
  intros.
  decompose [and] H1.
  generalize (not_empty_implies_last Message (bm c x x0) H3).
  intro.
  elim H4.
  intros.
  generalize (always_process_messages c H x x0 x1 H5).
  intro.
  elim H6.
  intros.
  decompose [and] H7.
  left.
  split with x2.
  split.
  unfold copy_p in |- *.
  generalize H9.
  case x2.
  simpl in |- *.
  intros.
  generalize H10.
  case (eq_queue_dec s1 x s2 x0); intro.
  decompose [and] a0.
  rewrite H11; rewrite H12.
  rewrite post_here.
  generalize (different_queue1 Message (bm c x x0) copy).
  intros.
  elim H11; auto.
  
  rewrite post_elsewhere.
  generalize (different_queue2 Message (bm c x x0) x1 H5).
  intros.
  elim H11; auto.
  
  auto.
  
  intros; unfold not in |- *; auto.
  
  intros; unfold not in |- *; auto.
  
  intros; unfold not in |- *; auto.
  
  intros; unfold not in |- *; auto.
  
  intros; unfold not in |- *; auto.
  
  intros; unfold not in |- *; auto.
  
  auto.
Qed.


Section ROOT_SUCC.

Inductive legal_as_set : Config -> Set :=
    intro_leg : forall c : Config, legal c -> legal_as_set c.



Definition legal_config := sigS legal_as_set.

Definition get_c (lc : sigS legal_as_set) :=
  match lc with
  | existS c L => c
  end.

(* WATCH OUT: successor is first argument, predecessor is second *)
Definition no_copy_succ (lc2 lc1 : legal_config) :=
  exists t : class_trans (get_c lc1),
    get_c lc2 = transition (get_c lc1) t /\ ~ copy_p (get_c lc1) t.



Definition convert_to_nat (n : Z) :=
  match n with
  | Zpos x => nat_of_P x
  | _ => 0
  end.


Definition no_copy_measure (lc : legal_config) :=
  match lc with
  | existS c _ => convert_to_nat (termination_measure c)
  end.

Definition decidable_relation (E : Set) (R : E -> E -> Prop) :=
  forall x : E, {y : E | R y x} + {(forall y : E, ~ R y x)}.


Axiom
  or_rec : forall (A B : Prop) (P : Set), (A -> P) -> (B -> P) -> A \/ B -> P.
Axiom
  ex_rec :
    forall (A : Set) (P : A -> Prop) (P0 : Set),
    (forall x : A, P x -> P0) -> ex P -> P0.


Lemma decidable_no_copy_succ : decidable_relation legal_config no_copy_succ.
Proof.
  unfold decidable_relation in |- *.
  intro.
  elim x.
  intros.
  elim p.
  intros.
  generalize (decide_no_copy_successor c l).
  intro.
  elim H.
  intro.
  elim H0.
  intros.
  left.
  decompose [and] H1.
  split
   with
     (existS legal_as_set (transition c x1) (intro_leg (transition c x1) H3)).
  unfold no_copy_succ in |- *.
  unfold get_c in |- *.
  split with x1.
  split; auto.
  intro.
  right.
  intro.
  unfold no_copy_succ in |- *.
  unfold get_c in |- *.
  unfold not in |- *; intro.
  elim H1.
  intros.
  decompose [and] H2.
  apply H4.
  auto.
Qed.

Definition relation_decreases (E : Set) (R : E -> E -> Prop)
  (f : E -> nat) := forall x y : E, R x y -> f x < f y.


Lemma Z_nat_business :
 forall x y : positive, nat_of_P y < nat_of_P x -> (Zpos y < Zpos x)%Z.
Proof.
  intros.
  unfold Zlt in |- *.
  unfold Zcompare in |- *.
  apply nat_of_P_lt_Lt_compare_complement_morphism.
  auto.
Qed.

Lemma Z_nat_business1 :
 forall x y : positive, (Zpos y < Zpos x)%Z -> nat_of_P y < nat_of_P x.
Proof.
  intros.
  apply nat_of_P_lt_Lt_compare_morphism.
  generalize H.
  unfold Zlt in |- *.
  unfold Zcompare in |- *.
  auto.
Qed.

Axiom
  Z_nat_axiom :
    forall x y : Z,
    (0 <= x)%Z ->
    (0 <= y)%Z -> (y < x)%Z -> convert_to_nat y < convert_to_nat x.


(*  What I want to prove.
Lemma Z_nat_business2:
 (x:Z)  `0<=x` -> `0<x` -> (lt (0) (convert_to_nat `x`)).

Lemma Z_nat_business3:
 (x,y:Z)  `0<=x` -> `0<=y` -> `y<x` -> (lt (convert y) (convert x)).

Lemma Z_nat_business4:
 (x,y:positive)  (lt (convert y) (convert x)) -> (lt (convert y) (convert x)).

*)
(* use Theorem bij1 : (m:nat) (convert (anti_convert m)) = (S m). *)


Lemma no_copy_succ_decreases :
 relation_decreases legal_config no_copy_succ no_copy_measure.
Proof.
  unfold relation_decreases in |- *.
  intro.
  elim x.
  intro.
  intro.
  elim p.
  intro; intro; intro.
  elim y.
  intro; intro.
  elim p0.
  intro; intro.
  unfold no_copy_succ in |- *.
  unfold get_c in |- *.
  intro.
  unfold no_copy_measure in |- *.
  elim H.
  intros.
  decompose [and] H0.
  generalize (termination_measure_decreases c0 x2 l0 H2).
  rewrite <- H1.
  intro.
  apply Z_nat_axiom.
  apply termination_measure_positive.
  apply termination_measure_positive.
  auto.
Qed.

Definition last_successor :=
  root legal_config no_copy_measure no_copy_succ decidable_no_copy_succ
    no_copy_succ_decreases.


Lemma last_successor_is_last :
 forall y0 y : legal_config, ~ no_copy_succ y (last_successor y0).
Proof.
  intros.
  unfold last_successor in |- *.
  apply root_no_R.
Qed.


(* QUESTION:  What does the following lemma mean?  
  That there is a given transition sequence that terminates
  or that all of them terminate?
*)

Lemma last_successor_has_no_message :
 forall y0 : legal_config, no_message (get_c (last_successor y0)).
Proof.
  intros.
  generalize (last_successor_is_last y0).
  intro.
  elim (decide_no_message (get_c (last_successor y0))).
  auto.
  
  generalize H.
  elim (last_successor y0).
  simpl in |- *.
  intro; intro.
  elim p.
  intros.
  generalize (exist_non_empty_queue c l b).
  intro.
  elim H1; intro.
  intro.
  elim H2.
  intro.
  intros.
  decompose [and] H3.
  generalize (not_empty_implies_last Message (bm c x0 x1) H5); intro.
  elim H6.
  intros.
  generalize (always_process_messages c l x0 x1 x2 H7); intro.
  elim H8; intro.
  intro.
  decompose [and] H9.
  elim
   (H0
      (existS legal_as_set (transition c x3)
         (intro_leg (transition c x3) H10))).
  unfold no_copy_succ in |- *.
  unfold get_c in |- *.
  split with x3.
  split.
  auto.
  
  unfold copy_p in |- *.
  generalize H11.
  elim x3; simpl in |- *; intros.
  generalize H12.
  case (eq_queue_dec s1 x0 s2 x1); intro.
  decompose [and] a0.
  rewrite H13; rewrite H14.
  rewrite post_here.
  generalize (different_queue1 Message (bm c x0 x1) copy).
  intros.
  elim H13; auto.
  rewrite post_elsewhere.
  generalize (different_queue2 Message (bm c x0 x1) x2 H7).
  intros.
  elim H13; auto.
  auto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
Qed.

End ROOT_SUCC.


