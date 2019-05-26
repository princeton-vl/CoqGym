(** * Coq codes *)
(** ** Dependencies *)

Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.

(** ** [Cat] is morphism *)

Lemma Cat_morphism_s : forall s r0 r1 r0' r1', 
  r0 =R= r1 -> r0' =R= r1' -> (r0 ++ r0') ~= s = (r1 ++ r1') ~= s. 
Proof.
  induction s.
    (* ""%string *)
    intros r0 r1 r0' r1' H H'.  simpl.  rewrite <- (nu_morphism r0 r1 H).  
    rewrite <- (nu_morphism r0' r1' H').  auto.
    (* String a s *)
    intros r0 r1 r0' r1' H H'.  simpl.  rewrite <- (nu_morphism r0 r1 H).  
    destruct (nu r0).
      (* true *)
      repeat erewrite matches_Or.  
      replace (r1' / a ~= s) with (r0' / a ~= s).
      replace ((r1 / a ++ r1') ~= s) with ((r0 / a ++ r0') ~= s).
      auto.
        (* proof for replace *)
        eapply IHs; try auto.  eapply derive_morphism; try auto.
        unfold ascii_eq; auto.  
        (* proof for replace *)
        eapply derive_morphism; try auto.  unfold ascii_eq; auto.  
      (* false *)
      eapply IHs; try auto.  eapply derive_morphism; try auto.  
      unfold ascii_eq; auto.  
Qed.

Add Parametric Morphism : Cat with
signature re_eq ==> re_eq ==> re_eq as Cat_mor.
Proof.
  intros x y H x0 y0 H0.  unfold re_eq.  intro s.  eapply Cat_morphism_s; auto.
Qed.

(** ** [Empty] *)
(** [Empty] corresponds to 0 in Kleene algebra. *)

Lemma Cat_left_zero_s : forall s r, (Empty ++ r) ~= s = false.
Proof.
  induction s; simpl; auto.
Qed.

Theorem Cat_left_zero : forall r, Empty ++ r =R= Empty.
Proof.
  unfold re_eq.  intros r s.  erewrite Empty_false.  
  eapply Cat_left_zero_s.
Qed.

Lemma Cat_right_zero_s : forall s r, (r ++ Empty) ~= s = false.
Proof.
  induction s; intro r; simpl.
    destruct (nu r); simpl; auto.
    case_eq (nu r); intro nu_r'.
      erewrite matches_Or.  erewrite IHs.  erewrite Empty_false.  simpl; auto.
      erewrite IHs.  auto.
Qed.

Theorem Cat_right_zero : forall r, r ++ Empty =R= Empty.
Proof.
  unfold re_eq.  intros r s.  erewrite Empty_false.  
  eapply Cat_right_zero_s.
Qed.

(** ** [Cat] matches concatination of strings. *) 

Lemma matches_Cat : forall s s' r r', 
  r ~==s -> r' ~== s' -> (r ++ r') ~== (s ++ s')%string.
Proof.
  induction s.
    (* s = ""%string *)
    induction s'.
      (* s' = ""%string *)
      simpl. intros r r' nu_r nu_r'. rewrite nu_r. rewrite nu_r'. simpl; auto.
      (* s' = String a s *)
      simpl. intros r r' nu_r Hra.  rewrite nu_r.  erewrite matches_Or.
      rewrite Hra.  destruct ((r / a ++ r') ~= s'); simpl; auto.
    (* s = String a s *)
    intros s' r r' Hr Hr'.
    replace (String a s ++ s')%string with (String a (s ++ s'))%string.
    rewrite derivation.  simpl.  case_eq (nu r); intro nu_r'.
      (* nu r' = true *)
      rewrite derivation in Hr.  erewrite matches_Or.
      specialize (IHs s' (r/a) r' Hr Hr').  rewrite IHs.  simpl; auto.
      (* nu r' = false *)
      rewrite derivation in Hr.  specialize (IHs s' (r/a) r' Hr Hr').  auto.  
      (* proof for replace *)
      simpl; auto.
Qed.

(** If [Cat] matches a string, the string can be divided into two strings which match the two [RegExp] respectively. *)
 
Lemma divide_Cat : forall s r' r'', (r' ++ r'') ~== s -> 
  {s':string & {s'':string | s = (s' ++ s'')%string /\ r' ~== s' /\ r'' ~== s'' }}.
Proof.
  induction s.
    (* s = ""%string *)
    intros r' r'' H.  exists ""%string.  exists ""%string.  simpl.
    split.  auto.  simpl in H.  
    destruct (nu r'); destruct (nu r''); split; simpl; auto; inversion H.
    (* s = String a s *)
    intros r' r'' H.  simpl in H.  
    case_eq (nu r'); intro nu_r'; rewrite nu_r' in H; simpl in H.
      (* nu r' = true *)
      erewrite matches_Or in H.  
      case_eq ((r' / a ++ r'') ~= s); case_eq (r'' / a ~= s); 
      intros Hr''_a Hr'_r''_a; simpl in H.
        (* true true -> (String a s') ++ s'' *)
        specialize (IHs (r'/a) r'' Hr'_r''_a).
        destruct IHs as [s' [s'' [H1 [H2 H3]]]].
        exists (String a s').  exists s''.
        split.  simpl.  rewrite <- H1.  auto.  split; auto.
        (* (r' / a ++ r'') ~== s *)
        specialize (IHs (r'/a) r'' Hr'_r''_a).
        destruct IHs as [s' [s'' [H1 [H2 H3]]]].
        exists (String a s').  exists s''.
        split.  simpl.  rewrite <- H1.  auto.  split; auto.
        (* r'' / a ~== s *)
        exists ""%string.  exists (String a s).
        split.  simpl.  auto.  split; simpl; auto.  
        (* false false *)
        rewrite Hr''_a in H.  rewrite Hr'_r''_a in H.  simpl in H.  inversion H.
      (* nu r' = false *)
      specialize (IHs (r'/a) r'' H).
      destruct IHs as [s' [s'' [H1 [H2 H3]]]].
      exists (String a s').  exists s''.
      split.  simpl.  rewrite <- H1.  auto.  split; auto.
Defined.

Lemma divide_Cat_false : forall s r' r'', (r' ++ r'') ~!= s -> 
  forall s' s'', ((s = s' ++ s'')%string -> r' ~!= s' \/ r'' ~!= s'').
Proof.
  intros s r' r'' H0.
  intros s' s''.
  case_eq (r' ~= s'); case_eq (r'' ~= s''); intros Hr''s'' Hr's' Hs; try auto.
    (* true true *)
    specialize(matches_Cat s' s'' r' r'' Hr's' Hr''s'').  
    left.  rewrite <- Hs in H.  rewrite H0 in H.  discriminate H.
Qed.

(** ** [Eps] *)
(** [Eps] corresponds to 1 in Kleene algebra. *)

Lemma Cat_left_id_s : forall s r, (Eps ++ r) ~= s = r ~= s.
Proof.
  induction s.
    simpl; auto.  
    simpl. intros r. erewrite matches_Or.  
    erewrite Cat_left_zero_s.  simpl; auto.
Qed.

Theorem Cat_left_id : forall r, Eps ++ r =R= r.
Proof.
  unfold re_eq. intros r s. eapply Cat_left_id_s. 
Qed.

Lemma Cat_right_id_s : forall s r, (r ++ Eps) ~= s = r ~= s.
Proof.
  intros s r.  case_eq (r ~= s); intro Hrs.
    (* r ~== s *)
    replace ((r ++ Eps) ~= s) with ((r ++ Eps) ~= (s ++ EmptyString)).
    eapply matches_Cat; auto.  
    erewrite string_right_id.  auto. 
    (* r ~!= s *)
    generalize dependent r.  
    induction s.      
      intros r H.  simpl in *.  rewrite H.  auto.
      intros r H.  simpl in *.  case_eq (nu r); intro nu_r'.
        (* nu r = true *)
        erewrite matches_Or.  erewrite Empty_false.
        replace (((r / a ++ Eps) ~= s) || false)%bool with ((r / a ++ Eps) ~= s).
        erewrite IHs; auto.  
        destruct ((r / a ++ Eps) ~= s); auto.
        (* nu r = false *)
        erewrite IHs; auto.  
Qed.

Theorem Cat_right_id : forall r, r ++ Eps =R= r.
Proof.
  unfold re_eq.  intros r s.  eapply Cat_right_id_s.
Qed.

(** ** [Cat] is associative. *)

Lemma matches_Cat_Cat_left : forall s s' s'' r r' r'',
  r ~== s -> r' ~== s' -> r'' ~== s'' -> 
  ((r ++ r') ++ r'') ~== ((s ++ s') ++ s'').
Proof.
  intros s s' s'' r r' r'' H H' H''.  
  repeat eapply matches_Cat; auto.  
Qed.

Lemma matches_Cat_Cat_right : forall s s' s'' r r' r'',
  r ~== s -> r' ~== s' -> r'' ~== s'' -> 
  (r ++ (r' ++ r'')) ~== (s ++ (s' ++ s'')).
Proof.
  intros s s' s'' r r' r'' H H' H''.  
  repeat eapply matches_Cat; auto.  
Qed.

Lemma Cat_assoc_s : forall s r r' r'', 
  ((r ++ r') ++ r'') ~= s = (r ++ (r' ++ r'')) ~= s.
Proof.
  intros s r r' r''.  case_eq (((r ++ r') ++ r'') ~= s); intro H; symmetry. 
    (* true *)
    specialize(divide_Cat s (r ++ r') r'' H).  intro H0.
    destruct H0 as [srr' [s_'' [H01 [H02 Hs_''r'']]]].
    specialize(divide_Cat srr' r r' H02).  intro H0.
    destruct H0 as [s_ [s_' [Hs_s_' [Hs_r Hs_'r']]]].
    replace s with (s_ ++ (s_' ++ s_''))%string.
    eapply matches_Cat_Cat_right; auto.  
    rewrite <- string_assoc.  rewrite <- Hs_s_'.  rewrite <- H01.  auto.
    (* false *)
    specialize(divide_Cat_false s (r ++ r') r'' H). intros H0.
    case_eq ((r ++ r' ++ r'') ~= s); intro H1.
      (* true *)
      specialize(divide_Cat s r (r' ++ r'') H1). intros H2.
      destruct H2 as [s0 [s_ [Hs_ [Hrs Hs__]]]].
      specialize (divide_Cat s_ r' r'' Hs__). intros H2.
      destruct H2 as [s0' [s0'' [Hs [Hrs' Hrs'']]]].
      specialize (matches_Cat s0 s0' r r' Hrs Hrs'). intros H2.
      specialize (matches_Cat (s0 ++ s0')%string s0'' (r ++ r') r'' H2 Hrs''). 
      intros H3.
      replace (((s0 ++ s0') ++ s0'')%string) with s in H3.
      rewrite H in H3.  discriminate H3.
        (* proof for replace *)
        erewrite string_assoc.  rewrite <- Hs.  rewrite <- Hs_.  auto.
      (* false *)
      auto.
Qed.

Theorem Cat_assoc : forall r r' r'', (r ++ r') ++ r'' =R= r ++ (r' ++ r'').
Proof.
  intros r r' r''.  unfold re_eq.  intro s.
  eapply Cat_assoc_s.
Qed.

(** ** [Cat] distributes to [Or]. *)

Lemma Cat_left_distr_s : forall s r r' r'', 
  (r ++ (r' || r'')) ~= s = ((r ++ r') || (r ++ r'')) ~= s.
Proof.
  induction s.
    (* s = "" *)
    intros r r' r''.  simpl.  
    destruct(nu r); destruct(nu r'); destruct(nu r''); auto. 
    (* s = String a s *)
    intros r r' r''.  simpl.  case_eq (nu r); intro nu_r.
      (* nu r = true *)
      rewrite (matches_Or s (r / a ++ r' || r'') (r' / a || r'' / a)).
      rewrite (IHs (r / a) r' r'').
      repeat erewrite matches_Or.  
      destruct ((r / a ++ r') ~= s); destruct ((r / a ++ r'') ~= s);
      destruct (r' / a ~= s); destruct (r'' / a ~= s); auto.
      (* nu r = false *)
      eapply IHs.
Qed.

Lemma Cat_left_distr : forall r r' r'', 
  (r ++ (r' || r'')) =R= ((r ++ r') || (r ++ r'')).
Proof.
  unfold re_eq.  intros r r' r'' s.  eapply Cat_left_distr_s.
Qed.

Lemma Cat_right_distr_s : forall s r r' r'', 
  ((r || r') ++ r'') ~= s = ((r ++ r'') || (r' ++ r'')) ~= s.
Proof.
  induction s.
    (* s = "" *)
    intros r r' r''.  simpl.  
    destruct (nu r); destruct (nu r'); destruct (nu r''); auto.
    (* s = String a s *)
    intros r r' r''.  simpl.  
    case_eq (nu r); intro nu_r; case_eq (nu r'); intro nu_r'; simpl.
      (* true true *)
      rewrite (matches_Or s (r / a || r' / a ++ r'') (r'' / a)).
      rewrite (IHs (r / a) (r' / a) r'').
      repeat erewrite matches_Or. 
      destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s); 
      destruct (r'' / a ~= s); auto.
      (* true false *)
      rewrite (matches_Or s (r / a || r' / a ++ r'') (r''/a)).
      rewrite (IHs (r/a) (r'/a) r'').
      repeat erewrite matches_Or. 
      destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s); 
      destruct (r'' / a ~= s); auto.
      (* false true *)
      rewrite (matches_Or s (r / a || r' / a ++ r'') (r''/a)).
      rewrite (IHs (r/a) (r'/a) r'').
      repeat erewrite matches_Or.
      destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s); 
      destruct (r'' / a ~= s); auto.
      (* false false *)
      rewrite (IHs (r/a) (r'/a) r'').
      erewrite matches_Or.  auto.
Qed.

Lemma Cat_right_distr : forall r r' r'', 
  ((r || r') ++ r'') =R= ((r ++ r'') || (r' ++ r'')).
Proof.
  unfold re_eq.  intros r r' r'' s.  eapply Cat_right_distr_s.
Qed.
