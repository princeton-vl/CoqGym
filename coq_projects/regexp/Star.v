(** * Coq codes *)
(** ** Dependencies *)

Require Import Recdef.
Require Import Arith.Wf_nat.
Require Import Omega.
Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.
Require Export RegExp.Concat.

Unset Standard Proposition Elimination Names.

(** ** Lemmas for Star *)

Lemma matches_Star_EmptyString : forall r, (Star r) ~== EmptyString.
Proof.
  intros r.  simpl; auto.  
Qed.

Lemma matches_Star_r : forall s r, r ~== s -> (Star r) ~== s.
Proof.
  induction s; simpl.
    intros r nu_r.  auto.
    intros r Hra.  replace s with (s ++ "")%string.
    eapply (matches_Cat s ""%string (r/a) (Star r)); try auto.
      eapply string_right_id.
Qed.

(** ** $ 1 + x x^{\ast} = x $ #1 + x x* = x# *)

Lemma matches_Star_right_s : forall s r, 
  (Star r) ~= s = (Eps || (r ++ Star r)) ~= s.
Proof.
  induction s; simpl; intro r.
    auto.
    repeat erewrite matches_Or.  erewrite Empty_false.  simpl.
    destruct (nu r).
      erewrite Or_idem_s.  auto. 
      auto.
Qed.

Lemma matches_Star_right : forall r, Star r =R= Eps || (r ++ Star r).
Proof.
  unfold re_eq.  intros r s.  eapply matches_Star_right_s.
Qed.

Lemma divide_Star_right : forall s r, (Star r) ~== s -> s <> ""%string -> 
  {s':string & {s'':string | s = (s' ++ s'')%string /\ s' <> ""%string /\ 
   r ~== s' /\ (Star r) ~== s''}}.
Proof.
  induction s; intros r Hstar Hs.
    elim Hs.  auto.
    simpl in Hstar.
    specialize (divide_Cat s (r/a) (Star r) Hstar).  intro H0.
    destruct H0 as [s0' [s0'' [H01 [H02 H03]]]].
    rewrite <- derivation in H02.
    exists (String a s0'). exists s0''.
    split.
      simpl.  rewrite <- H01.  auto.
      split.
        intro H.  discriminate H.
        auto.
Qed.

(** ** Split [Star] to [list string] *)

Lemma Star_to_list : forall s r, (Star r) ~== s -> 
  {ss:list string | forallb (fun s => r ~= s) ss = true /\
   concat_list_string ss = s /\
   forallb (fun s => bneq_empty_string s) ss = true }. 
Proof.
  refine (induction_ltof2 string str_length _ _).
  intros s IHs r Hstar.
  specialize(string_dec s ""%string).  intro Hs_dec.  destruct Hs_dec.
    (* s = "" *)
    exists nil.  auto.
    (* s <> "" *)
    specialize(divide_Star_right s r Hstar n).  intro H1.
    destruct H1 as [s' [s'' [H11 [H12 [H13 H14]]]]].
    assert(Hltof: ltof string str_length s'' s).
      unfold ltof.  rewrite H11.  rewrite str_length_append.
      assert(Hlen_s: forall s, s <> ""%string -> str_length s <> 0).
        induction s0.
          intro H'. elim H'. auto. 
          simpl. intro H'. intro H''. discriminate H''. 
      specialize(Hlen_s s' H12).  omega.
    specialize(IHs s'' Hltof r H14).
    destruct IHs as [ss' [IH1 [IH2 IH3]]].
    exists (s' :: ss').  split.
      simpl. rewrite H13. rewrite IH1. auto.  split.
        simpl. rewrite IH2. rewrite <- H11. auto.
        simpl. rewrite IH3. unfold bneq_empty_string. destruct (string_dec s' ""%string).
          simpl. elim H12. auto.
          auto.
Defined.

Lemma Star_to_list_not_nil : forall s r, (Star r) ~== s -> s <> ""%string ->
  {ss:list string | forallb (fun s => r ~= s) ss = true /\
   concat_list_string ss = s /\ ss <> nil /\
   forallb (fun s => bneq_empty_string s) ss = true }.
Proof.
  intros s r Hstar Hs.
  specialize(Star_to_list s r Hstar). intro H.
  destruct H as [ss' [IH1 [IH2 IH3]]].
  exists ss'.  split; try auto.
    split; try auto.
      split; try auto.
      intro Hss'.  rewrite Hss' in IH2.  simpl in IH2.  elim Hs.  auto.
Defined.

Lemma list_to_Star : forall xs r, 
  forallb (fun s : string => r ~= s) xs = true ->
  Star r ~== concat_list_string xs.
Proof.
  induction xs; intros r0 Hf; simpl.
    auto.
    simpl in Hf.
    case_eq (r0 ~= a); case_eq (forallb (fun s : string => r0 ~= s) xs); intros H1 H2.
      (* true true *)
      cut(Eps || (r0 ++ (Star r0)) ~== (a ++ concat_list_string xs)). intro H3.
      erewrite matches_Star_right.  auto.
        cut((r0 ++ (Star r0)) ~== (a ++ concat_list_string xs)). intro H4.  
        erewrite matches_Or.  rewrite H4.
        destruct (Eps ~= (a ++ concat_list_string xs)); auto.
          erewrite matches_Cat; auto.
       (* false true *)
       rewrite H1 in Hf; rewrite H2 in Hf; simpl in Hf; discriminate Hf.
       (* true false *)
       rewrite H1 in Hf; rewrite H2 in Hf; simpl in Hf; discriminate Hf.
       (* false false *)
       rewrite H1 in Hf; rewrite H2 in Hf; simpl in Hf; discriminate Hf.
Qed.

Lemma divide_Star_left : forall s r, (Star r) ~== s -> s <> ""%string ->
  {s':string & {s'':string | s = (s' ++ s'')%string /\ s'' <> ""%string /\ 
   (Star r) ~== s' /\ r ~== s''}}.
Proof.
  intros s r Hstar Hs.
  specialize(Star_to_list_not_nil s r Hstar Hs). intro H0.
  destruct H0 as [ss' [H01 [H02 [H03 H04]]]].
  specialize (exists_last H03).  intro Hlast.  
  destruct Hlast as [ss0 [s0 Hlast']]. 
  exists (concat_list_string ss0).  exists s0.  split.
    erewrite <- concat_list_string_xs_x.  rewrite <- Hlast'.  auto.  split.
      (* goal: s0 <> ""%string *)
      assert(H': In s0 ss').
        rewrite Hlast'.  eapply In_list_append_right.  eapply in_eq.
      specialize(forallb_forall (fun s => bneq_empty_string s) ss'). intros H''.
      destruct H'' as [H'' _].  specialize(H'' H04).  specialize(H'' s0 H').
      unfold bneq_empty_string in H''.  
      destruct (string_dec s0 ""%string). discriminate H''. auto.
      split.
        (* goal: Star r ~== concat_list_string ss0 *)
        eapply list_to_Star.  rewrite Hlast' in H01.
        apply(forallb_divide_left string (fun s => r ~= s) ss0 (s0::nil) H01).
        (* goal: r ~== s0 *)
        specialize(In_snoc string s0 ss0).  
        intros HIn.  rewrite <- Hlast' in HIn.
        specialize(forallb_forall (fun s => r ~= s) ss'). intro H.
        destruct H as [H _].  eapply H.  auto.
        (* goal: In s0 ss' *)
        auto.
Qed.

(** ** [Star] is morphism *)

Lemma forallb_matches_morphism_s : forall ss r r', r =R= r' ->
  forallb (fun s0 => r ~= s0) ss = forallb (fun s0 => r' ~= s0) ss.
Proof.
  induction ss.
    intros r r' H.  simpl.  auto.
    intros r r' H.  simpl.  rewrite <- (IHss r r' H).  unfold re_eq in H.
    rewrite <- (H a).  auto.
Qed.

Lemma Star_morphism_s : forall s r r', r =R= r' -> (Star r) ~= s = (Star r') ~= s.
Proof.
  induction s.
    intros r r' H.  simpl.  auto.
    intros r r' H.  simpl.
    case_eq ((r / a ++ Star r) ~= s); case_eq ((r' / a ++ Star r') ~= s); 
    intros H0 H1; try auto.
      (* true false *)
      specialize(divide_Cat s (r/a) (Star r) H1).  intros H2.
      destruct H2 as [s' [s'' [H01 [H02 H03]]]].
      erewrite <- derivation in H02.
      unfold re_eq in H.  erewrite H in H02.  erewrite derivation in H02.
      specialize(Star_to_list s'' r H03).  intro H2.
      destruct H2 as [ss [H21 [H22 H23]]].
      rewrite (forallb_matches_morphism_s ss r r') in H21.
      specialize(list_to_Star ss r' H21).  intro H3.  rewrite H22 in H3.
      specialize(matches_Cat s' s'' (r'/a) (Star r') H02 H3).  intro H4.
      rewrite <- H01 in H4.  rewrite H0 in H4.  inversion H4.  auto.
      (* false true *)
      specialize(divide_Cat s (r'/a) (Star r') H0).  intros H2.
      destruct H2 as [s' [s'' [H01 [H02 H03]]]].
      erewrite <- derivation in H02.
      unfold re_eq in H.  erewrite <- H in H02.  erewrite derivation in H02.
      specialize(Star_to_list s'' r' H03).  intro H2.
      destruct H2 as [ss [H21 [H22 H23]]].
      rewrite (forallb_matches_morphism_s ss r' r) in H21.
      specialize(list_to_Star ss r H21).  intro H3.  rewrite H22 in H3.
      specialize(matches_Cat s' s'' (r/a) (Star r) H02 H3).  intro H4.
      rewrite <- H01 in H4.  rewrite H1 in H4.  inversion H4.  
      setoid_symmetry.  auto.
Qed.

Add Parametric Morphism : Star with
signature re_eq ==> re_eq as Star_morphism.
Proof.
  intros x y H.  unfold re_eq.  intros s.  eapply Star_morphism_s.  exact H.
Qed.

(** ** $ 1 + x^{\ast} x = x $ #1 + x* x = x# *)

Lemma matches_Star_left_s : forall s r, (Star r) ~= s = (Eps || (Star r ++ r)) ~= s.
Proof.
  intros s r.
  case_eq (Star r ~= s); intro Hstar;
  case_eq ((Eps || (Star r ++ r)) ~= s); intro H; try auto.
    (* Star r ~== s *)
    destruct (string_dec s ""%string).
      (* s = "" *)
      rewrite e in H.  erewrite matches_Or in H.  simpl in H.  discriminate H.
      (* s <> "" *)
      specialize(divide_Star_left s r Hstar n).  intro H0.
      destruct H0 as [s' [s'' [H01 [H02 [H03 H04]]]]].
      specialize(matches_Cat s' s'' (Star r) r H03 H04).  intro H0.
      rewrite <- H01 in H0.   rewrite matches_Or in H.  rewrite H0 in H.
      destruct (Eps ~= s); simpl in H; discriminate H.
    (* Star r ~!= s *)
    destruct (string_dec s ""%string).
      (* s = "" *)
      rewrite e in Hstar.  simpl in Hstar.  discriminate Hstar.
      (* s <> "".  Prove (H:Eps || (Star r ++ r) ~== s) -> (~Hstar:Star r ~== s) *)
      rewrite matches_Or in H.  replace (Eps ~= s) with false in H.  simpl in H.
      (* H: (Star r ++ r) ~== s. Divide s *)
      specialize(divide_Cat s (Star r) r H).  intro H'.
      destruct H' as [s' [s'' [H01 [H02 H03]]]].
      (* H02 : Star r ~== s'. Parse s' to ss:list string *)
      specialize(Star_to_list s' r H02).  intro H'.
      destruct H' as [ss [H11 [H12 H13]]].
      (* Prove Hf: (Star r) ~== (ss ++ s'::nil) *)
      specialize(forallb_list_xs_x string (fun s => r ~= s) ss s'' H11 H03).
      intros Hf.
      (* Prove Hf': ss ++ s'::nil = s *) 
      specialize(concat_list_string_xs_x ss s'').  intros Hf'.
      rewrite H12 in Hf'.  rewrite <- H01 in Hf'.
      (* Prove (Star r ) ~== s *)
      specialize(list_to_Star (ss ++ s''::nil) r Hf).  intros Hf''.
      rewrite Hf' in Hf''.
      (* Contradiction between Hstar and Hf'' *)
      rewrite Hf'' in Hstar.  discriminate Hstar.
      (* Prove false = Eps ~= s *)
      induction s;  simpl.  
        elim n.  auto.
        symmetry.  eapply Empty_false.
Qed.

Lemma matches_Star_left : forall r, Star r =R= Eps || (Star r ++ r).
Proof.
  unfold re_eq.  intros r s.  eapply matches_Star_left_s.
Qed.









