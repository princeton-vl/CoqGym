(** * Coq codes *)
(** ** Dependencies *)

Require Import Recdef.
Require Import Arith.Wf_nat.
Require Import Omega.
Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.
Require Export RegExp.Concat.
Require Export RegExp.Star.

(** ** Define [includes] *)

Definition includes (x y:RegExp) : Prop := (x || y) =R= y. 
Notation "x <= y" := (includes x y) (at level 70).

Definition prop_eq (p q:Prop) : Prop := (p <-> q).
Lemma prop_eq_equiv : equiv Prop prop_eq.
Proof.
  unfold equiv.  split.
    unfold reflexive.  intros.  unfold prop_eq.  tauto.  split.
    unfold transitive.  intros.  unfold prop_eq in *.  tauto.  
    unfold symmetric.  intros.  unfold prop_eq in *.  tauto.  
Qed.

Add Parametric Morphism : includes with
signature re_eq ==> re_eq ==> prop_eq as includes_morphism.
Proof.
  intros x y H x0 y0 H0.  unfold prop_eq.  split.
    unfold includes.  intros H1.  setoid_rewrite <- H.  setoid_rewrite <- H0.  auto.
    unfold includes.  intros H1.  setoid_rewrite H.  setoid_rewrite H0.  auto.
Qed.

Lemma includes_reflexive : reflexive RegExp includes.
Proof.
  unfold reflexive.  intro x.  unfold includes.  eapply Or_idem. 
Qed.

Lemma includes_antisymmetric : forall x y, x <= y -> y <= x -> x =R= y.
Proof.
  intros x y Hxy Hyx.  unfold includes in *.
  setoid_rewrite Or_comm in Hyx.  setoid_symmetry in Hyx.
  setoid_transitivity (x || y); auto.  
Qed.

Lemma includes_transitive : transitive RegExp includes.
Proof.
  unfold transitive.  intros x y z Hxy Hyz.  unfold includes in *.
  setoid_replace (x || z) with (x || (y || z)).
  setoid_rewrite <- Or_assoc.
  setoid_rewrite Hxy.  auto.
  setoid_rewrite Hyz.  setoid_reflexivity.
Qed.

Lemma implies_to_includes : forall x y, (forall s, x ~== s -> y ~== s) -> x <= y.
Proof.
  intros x y Hsxy.
  unfold includes; unfold re_eq.  intros s.
  erewrite matches_Or.  
  case_eq(x ~= s); case_eq(y ~= s); try auto.
    intros Hys Hxs.  rewrite (Hsxy s Hxs) in Hys.  discriminate Hys.
Qed.

Lemma includes_to_implies : forall x y, x <= y -> (forall s, x ~== s -> y ~== s).
Proof.
  intros x y Hxy.  unfold includes in Hxy.  unfold re_eq in Hxy.
  intros s Hx.  specialize(Hxy s).  erewrite matches_Or in Hxy.
  destruct(x ~= s); destruct(y ~= s); try discriminate Hx; try discriminate Hxy; auto.
Qed.

(** [x || y] is the least upper bound of [x] and [y] *) 

Lemma Cat_least_upper_bound : forall x y, x <= (x || y) /\ y <= (x || y) /\
  (forall z, x <= z -> y <= z -> (x || y) <= z).
Proof.
  intros x y.  split.
    (* x <= x || y *)
    unfold includes.  setoid_rewrite <- Or_assoc.  setoid_rewrite Or_idem.
    setoid_reflexivity.
    split.
    (* y <= x || y *)
    unfold includes.  setoid_replace (y || (x || y)) with (y || (y || x)).
    setoid_rewrite <- Or_assoc.  setoid_rewrite Or_idem.
    eapply Or_comm.
    setoid_replace (x || y) with (y || x).  setoid_reflexivity.
    eapply Or_comm.
    (* forall z : RegExp, x <= z -> y <= z -> x || y <= z *)
    intros z Hxz Hyz.  unfold includes in *.
    setoid_rewrite Or_assoc.  setoid_replace (y || z) with z.
    auto.  auto.
Qed.

(** ** Monotonicity of [includes] *)

Lemma includes_right_Or_monotone : forall x y z, x <= y -> (x || z) <= (y || z).
Proof.
  intros x y z Hxy.  unfold includes in *.  
  setoid_rewrite <- Or_assoc.  setoid_replace (y || z) with ((x || y) || z).
  setoid_replace (x || z || y) with (x || y || z).
  setoid_replace (x || y || z || z) with (x || y || (z || z)).
  setoid_rewrite Or_idem.  setoid_reflexivity.
  repeat setoid_rewrite <- Or_assoc.  setoid_reflexivity.
  setoid_rewrite Or_assoc.  setoid_replace (z || y) with (y || z).
  setoid_rewrite Or_comm.  setoid_reflexivity.
  eapply Or_comm.
  setoid_replace (x || y) with y.  setoid_reflexivity.  auto.
Qed.

Lemma includes_left_Or_monotone : forall x y z, x <= y -> (z || x) <= (z || y).
Proof.
  intros x y z Hxy.  unfold includes in *.
  repeat setoid_rewrite <- Or_assoc.
  setoid_replace (z || x || z) with (z || x).
  setoid_rewrite Or_assoc.  setoid_rewrite Hxy.  setoid_reflexivity.
  setoid_rewrite Or_assoc.  setoid_replace (x || z) with (z || x).
  setoid_rewrite <- Or_assoc.  setoid_rewrite Or_idem.  setoid_reflexivity.
  eapply Or_comm.
Qed.

Lemma includes_right_Cat_monotone : forall x y z, x <= y -> (x ++ z) <= (y ++ z).
Proof.
  intros x y z Hxy.  unfold includes in *.
  erewrite <- Cat_right_distr.  setoid_rewrite Hxy.  setoid_reflexivity.
Qed.

Lemma includes_left_Cat_monotone : forall x y z, x <= y -> (z ++ x) <= (z ++ y).
Proof.
  intros x y z Hxy.  unfold includes in *.
  erewrite <- Cat_left_distr.  setoid_rewrite Hxy.  setoid_reflexivity.
Qed.

Lemma includes_Star_monotone : forall x y, x <= y -> (Star x) <= (Star y).
Proof.
  intros x y Hxy.  specialize(includes_to_implies x y Hxy).  intro H01.
  assert(H1: forall s, Star x ~== s -> Star y ~== s).
    intros s HSx.  specialize(Star_to_list s x HSx).  intros H.
    destruct H as [ss [Ha [Hb Hc]]].
    assert(H1': forall zs, forallb (fun s : string => x ~= s) zs = true ->
      forallb (fun s : string => y ~= s) zs = true).
      induction zs.  simpl.  intro H.  auto.        
      simpl.  intro H.
        case_eq(x ~= a); case_eq(forallb (fun s : string => x ~= s) zs); 
        intros H' H''; rewrite H' in H; rewrite H'' in H; simpl in H; 
        try discriminate H.
        replace (y ~= a) with true.  erewrite (IHzs H').  auto.
        symmetry.  eapply H01.  auto.
    specialize(H1' ss Ha).  specialize(list_to_Star ss y H1').  intros H.
    erewrite Hb in H.  auto.  
  assert(H02: forall s, y ~!= s -> x ~!= s).
    intros s Hy.  specialize(Hxy s).  erewrite matches_Or in Hxy.  
    rewrite Hy in Hxy.
    destruct(x ~= s).  
      simpl in Hxy.  discriminate Hxy.  
      auto.
  unfold includes. unfold re_eq. intro s. erewrite matches_Or.
  case_eq (Star x ~= s); case_eq (Star y ~= s); simpl; 
  intros H' H''; try reflexivity.
    specialize(H1 s H'').  rewrite H' in H1.  discriminate H1.
Qed.

(** ** Axioms for [includes] *)
(** See also lemma [matches_Star_right] which is stronger lemma. *)

Theorem Star_right : forall r, (Eps || (r ++ Star r)) <= Star r.
Proof. 
  intros r.
  unfold includes.  setoid_rewrite <- matches_Star_right.
  setoid_rewrite Or_idem.  setoid_reflexivity. 
Qed.

(** See also lemma [matches_Star_left] which is stronger lemma. *)

Theorem Star_left : forall r, (Eps || (Star r ++ r)) <= Star r.
Proof.
  intros r.
  unfold includes.  setoid_rewrite <- matches_Star_left.
  setoid_rewrite Or_idem.  setoid_reflexivity. 
Qed.




Lemma Star_eq_left_s : forall s a b x, (b || (a ++ x)) <= x -> 
  ((Star a) ++ b) ~== s -> x ~== s.
Proof.
  refine (induction_ltof2 string str_length _ _).
  intros s IH a b x Hbax HSab.
  specialize(divide_Cat s (Star a) b HSab).  intro H'.
  destruct H' as [s' [s'' [H01 [H02 H03]]]].
  case_eq (string_dec s' ""%string); intros Hs _.
    (* s = "" *)
    rewrite Hs in *.  simpl in H01.
    unfold includes in Hbax.  cut ((b || (a ++ x) || x) ~== s).  intros H.
    unfold re_eq in Hbax.  specialize(Hbax s).  rewrite <- Hbax.  auto.
    repeat rewrite matches_Or.  rewrite H01.  rewrite H03.  simpl.  auto.
    (* s <> "" *)
    specialize(divide_Star_right s' a H02 Hs).  intro H0.
    destruct H0 as [s'0 [s''0 [H11 [H12 [H13 H14]]]]].
    (* y = s''0 ++ s'' *)
    assert(Hltof: ltof string str_length (s''0 ++ s'')%string s).
     unfold ltof.  rewrite H01.  rewrite H11.
     repeat rewrite str_length_append.
     cut(str_length s'0 > 0).  intro Hs'0.  omega.
     induction s'0.
       elim H12.  auto.  
       simpl.  omega.
    assert(Hy: (Star a ++ b) ~== (s''0 ++ s'')).
      eapply matches_Cat.  auto.  auto.
    assert(Hy': x ~== (s''0 ++ s'')%string).
      apply (IH (s''0 ++ s'')%string Hltof a b x Hbax Hy).
    unfold includes in Hbax.  unfold re_eq in Hbax.
    cut(b || (a ++ x) || x ~== s).  intro H.  rewrite <- (Hbax s).  auto.
    repeat rewrite matches_Or.  cut((a ++ x) ~== s).  intro H.  rewrite H.
    destruct(b ~= s); destruct(x ~= s); reflexivity.
    rewrite H01.  rewrite H11.  rewrite string_assoc.
    eapply matches_Cat.  auto.  auto.
Qed.

Theorem Star_eq_left : forall a b x, (b || (a ++ x)) <= x -> ((Star a) ++ b) <= x.
Proof.
  intros a b x. intro H.  unfold includes.  unfold re_eq.  intro s.
  case_eq((Star a ++ b) ~= s); case_eq(x ~= s); intros H1 H2;  rewrite matches_Or;
  rewrite H1; rewrite H2; try reflexivity.
  specialize(Star_eq_left_s s a b x H H2).  intro H'.  rewrite H' in H1.  
  discriminate H1.
Qed.

Theorem Star_eq_right_s : forall s a b x, (b || (x ++ a)) <= x -> 
  (b ++ (Star a)) ~== s -> x ~== s.
Proof.
  refine (induction_ltof2 string str_length _ _).
  intros s IH a b x Hbxa HbSa.
  specialize(divide_Cat s b (Star a) HbSa).  intro H'.
  destruct H' as [s' [s'' [H01 [H02 H03]]]].
  case_eq (string_dec s'' ""%string); intros Hs _.
    (* s'' = "" *)
    rewrite Hs in *.  rewrite string_right_id in H01.
    unfold includes in Hbxa.  cut ((b || (x ++ a) || x) ~== s).  intros H.
    unfold re_eq in Hbxa.  specialize(Hbxa s).  rewrite <- Hbxa.  auto.
    repeat rewrite matches_Or.  rewrite H01.  rewrite H02.  simpl.  auto.
    (* s'' <> "" *)
    specialize(divide_Star_left s'' a H03 Hs).  intro H0.
    destruct H0 as [s'0 [s''0 [H11 [H12 [H13 H14]]]]].
    (* y = s' ++ s'0 *)
    assert(Hltof: ltof string str_length (s' ++ s'0)%string s).
      unfold ltof.  rewrite H01.  rewrite H11.
      repeat rewrite str_length_append.
      cut(str_length s''0 > 0).  intro Hs''0.  omega.
      induction s''0.  
        elim H12.  auto.  
        simpl.  omega.
    assert(Hy: (b ++ Star a) ~== (s' ++ s'0)).
      eapply matches_Cat.  auto.  auto.
    assert(Hy': x ~== (s' ++ s'0)%string).
      apply (IH (s' ++ s'0)%string Hltof a b x Hbxa Hy).
    unfold includes in Hbxa.  unfold re_eq in Hbxa.
    cut(b || (x ++ a) || x ~== s).  intro H.  rewrite <- (Hbxa s).  auto.
    repeat rewrite matches_Or.  cut((x ++ a) ~== s).  intro H.  rewrite H.
    destruct(b ~= s); destruct(x ~= s); reflexivity.
    rewrite H01.  rewrite H11.  rewrite <- string_assoc.  
    eapply matches_Cat.  auto.  auto.
Qed.

Theorem Star_eq_right : forall a b x, (b || (x ++ a)) <= x -> (b ++ (Star a)) <= x.
Proof.
  intros a b x. intro H.  unfold includes.  unfold re_eq.  intro s.
  case_eq((b ++ Star a) ~= s); case_eq(x ~= s); intros H1 H2;  rewrite matches_Or;
  rewrite H1; rewrite H2; try reflexivity.
  specialize(Star_eq_right_s s a b x H H2).  intro H'.  rewrite H' in H1.  
  discriminate H1.
Qed.













