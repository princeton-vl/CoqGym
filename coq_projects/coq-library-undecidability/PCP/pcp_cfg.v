Require Import Definitions.

     (* spec    proof comments *)
     (*   24       40      632 pcp_cfg.v *)


(* Lemma list_prefix_double_inv X (x1 x2 : X) A A' B B' : *)
(*   ~ x1 el A -> ~ x1 el A' -> ~ x2 el A -> ~ x2 el A' -> A ++ x1 :: B = A' ++ x2 :: B' -> A = A' /\ B = B'. *)
(* Proof. *)
(*   intro. revert A' B B'. *)
(*   induction A; intros. *)
(*   - destruct A'; inv H3; firstorder. *)
(*   - destruct A';  inv H3. firstorder. *)
(*     eapply IHA in H6; try now firstorder. intuition congruence. *)
(* Qed. *)

(* Lemma list_prefix_inv X (x : X) A A' B B' : *)
(*   ~ x el A -> ~ x el A' -> A ++ x :: B = A' ++ x :: B' -> A = A' /\ B = B'. *)
(* Proof. *)
(*   intros. eapply list_prefix_double_inv; eauto. *)
(* Qed. *)

(* Lemma list_snoc_inv X (A : list X) : *)
(*   A = [] \/ exists x A', A = A' ++ [x]. *)
(* Proof. *)
(*   induction A. *)
(*   - firstorder. *)
(*   - destruct IHA as [-> | (? & ? & ->)]. right. now exists a, []. *)
(*     right. now exists x, (a :: x0). *)
(* Qed. *)

(* Lemma map_injective X Y (f : X -> Y) A B : *)
(*   (forall x y, f x = f y -> x = y) -> map f A = map f B -> A = B. *)
(* Proof. *)
(*   revert B. induction A; intros [] H H0; inv H0; firstorder congruence. *)
(* Qed. *)

Lemma in_concat_iff X (l : list (list X)) x :
  x el concat l <-> exists l', x el l' /\ l' el l.
Admitted.

Lemma concat_rev X (l : list (list X)) :
  concat (rev (map (@rev _) l)) = rev (concat l).
Proof.
  induction l.
  - reflexivity.
  - cbn. rewrite concat_app, IHl, rev_app_distr. cbn. now rewrite <- app_nil_end.
Qed.

Notation "f ∘ g" := (fun x => f (g x)) (at level 100).

Hint Rewrite concat_app map_app map_map : list.
Hint Rewrite <- map_rev  : list.
Hint Rewrite <- concat_rev : list.

Lemma list_split X A B C D E (x : X) :
  A ++ B ++ C = D ++ x :: E -> ~ x el A -> ~ x el C ->
  exists F G,
    D = A ++ F /\
    E = G ++ C /\
    B = F ++ x :: G.
Proof.
  revert B C D E.
  induction A; intros.
  - cbn in *. clear H0. revert B C E H H1. induction D; intros.
    + exists []. cbn in *. revert C E H H1. destruct B; cbn in *; intros; inv H; firstorder. eauto.
    + exists (a :: D). cbn in *. destruct B.
      * cbn in *. subst. destruct H1. right. eapply in_app_iff. firstorder.
      * cbn in *. inv H. eapply IHD in H3 as (? & ? & ? & ? & ?). subst. eauto. eauto.
  -  revert B C E H H1. induction D; intros.
     + cbn in H. inv H. firstorder.
     + cbn in H. inv H. edestruct IHA  as (? & ? & ? & ? & ?); eauto. subst.
       exists x0, x1. eauto.
Qed.

Lemma nil_app_nil X (A : list X) :
  A = [] ++ A ++ [].
Proof.
  now autorewrite with list.
Qed.

     (* spec    proof comments *)
     (*   29       27      638 pcp_cfg.v *)

Section CFGs.

  Notation sig := nat.
  Definition rule : Type := sig * list sig.
  Definition cfg : Type := sig * list rule.

  Definition rules (G : cfg) := snd G.
  Definition startsym (G : cfg) := fst G.

  Inductive rew_cfg : cfg -> list sig -> list sig -> Prop:=
  |rewR R x a y v : (a,v) el rules R -> rew_cfg R (x++[a]++y) (x++v++y).
  Hint Constructors rew_cfg.

  Lemma rewrite_sing R a x :
    (a, x) el rules R -> rew_cfg R [a] x.
  Proof.
    intros. rewrite nil_app_nil, (nil_app_nil [a]). now econstructor.
  Qed.
  
  Inductive rewt (S: cfg) (x: list sig) : list sig -> Prop :=
  |rewtRefl : rewt S x x
  |rewtRule y z : rewt S x y -> rew_cfg S y z -> rewt S x z.
  Hint Constructors rewt.

  Global Instance rewtTrans R :
    PreOrder (rewt R).
  Proof.
    split.
    - hnf. econstructor.
    - induction 2; eauto.
  Qed.

  Global Instance rewrite_proper R :
    Proper (rewt R ==> rewt R ==> rewt R) (@app sig).
  Proof.
    intros x1 y1 H1 x2 y2 H2.
    induction H1.
    - induction H2.
      + reflexivity.
      + rewrite IHrewt. inv H. eapply rewtRule.
        replace (x1 ++ x ++ [a] ++ y0) with ( (x1 ++ x) ++ [a] ++ y0) by now autorewrite with list.
        eauto. replace (x1 ++ x ++ v ++ y0) with ( (x1 ++ x) ++ v ++ y0) by now autorewrite with list. eauto.
    - rewrite IHrewt. inv H. autorewrite with list. eauto.
  Qed.

  Global Instance subrel R :
    subrelation (rew_cfg R) (rewt R).
  Proof.
    intros x y H. econstructor. reflexivity. eassumption.
  Qed.
    
  Definition terminal G x := ~ exists y, rew_cfg G x y.

  Lemma terminal_iff G x :
    terminal G x <-> forall s y, s el x -> ~ (s, y) el rules G.
  Proof.
    split.
    - intros H s y A B. apply H. destruct (@in_split _ _ _ A) as (l1 & l2 & ->).
      exists (l1 ++ y ++ l2). change (s :: l2) with ([s] ++ l2). now econstructor.
    - intros H1 [y H2]. inv H2. eapply (H1 _ v); eauto.
  Qed.

  Definition L (G : cfg) x := rewt G [startsym G] x /\ terminal G x.

  Definition PALIN (G : cfg) := exists x, L G x /\ x = List.rev x.
  
End CFGs.

      (* spec    proof comments *)
      (*  62      154      517 pcp_cfg.v *)

Section Reduction.

  Variable P : SRS.

  Definition Sigma := sym P.
  
  Notation "#" := (fresh Sigma).
  Definition Start := (fresh (# :: Sigma)).
  
  Definition enc x := fst x ++ [#] ++ snd x ++ [#].
  
  Definition G1 : cfg :=
    (Start, (Start, [Start]) ::
        (flat_map
           (fun x => [ (Start, (fst x) ++ [Start] ++ enc x);
                      (Start, (fst x) ++ [#] ++ enc x)]) P)).
  
  Definition G2  : cfg :=
    (Start, (Start, [Start]) ::
        (flat_map
           (fun x => [ (Start, (snd x) ++ [Start] ++ enc x);
                      (Start, (snd x) ++ [#] ++ enc x)]) P)).
  
  Definition inter_nonempty '(G1, G2) :=
    exists x, @L G1 x /\ L G2 x.

  Lemma in_rules1 x A :
    (x, A) el rules G1 -> x = Start /\ (A = [Start] \/ (exists x M, (M = [Start] \/ M = [#]) /\ ({H : x el P | A = (fst x) ++ M ++ enc x}))).
  Proof.
    cbn. intros [ | ].
    - inv H. intuition.
    - eapply in_flat_map in H as (? & ? & [H | [H | []]]); inv H.
      + intuition. right. exists x0, [Start]; firstorder.
      + intuition. right. exists x0, [#]; firstorder.
  Qed.
  
  Lemma terminal_G1 x :
    ~ Start el x <->
    terminal G1 x.
  Proof.
    rewrite terminal_iff. split.
    - now intros ? ? ? ? [-> ?] % in_rules1.
    - intros ? ?. eapply (H _ _ H0). now left.
  Qed.

  
  Lemma in_rules2 x A :
    (x, A) el rules G2 -> x = Start /\ (A = [Start] \/ (exists x M, (M = [Start] \/ M = [#]) /\ ({H : x el P | A = (snd x) ++ M ++ enc x}))).
  Proof.
    cbn. intros [ | ].
    - inv H. intuition.
    - eapply in_flat_map in H as (? & ? & [H | [H | []]]); inv H.
      + intuition. right. exists x0, [Start]; firstorder.
      + intuition. right. exists x0, [#]; firstorder.
  Qed.
  
  Lemma terminal_G2 x :
    ~ Start el x <->
    terminal G2 x.
  Proof.
    rewrite terminal_iff. split.
    - now intros ? ? ? ? [-> ?] % in_rules2.
    - intros ? ?. eapply (H _ _ H0). now left.
  Qed.

  Definition C1 := tau1. 
  Definition C2 := tau2.

  Ltac list_simpl := (repeat (progress (cbn in *; autorewrite with list in *))); cbn in *.
  
  Lemma start_enc x y :
    x <<= Sigma -> y <<= Sigma ->
    ~ Start el enc (x/y).
  Proof.
    unfold enc. intros ? ? [ | [ [ | []] | [ | [ | [] ] ] % in_app_iff ] % in_app_iff ] % in_app_iff; cbn -[fresh] in *.
    - edestruct fresh_spec with (l := # :: Sigma); try reflexivity; eauto.
    - edestruct fresh_spec with (l := # :: Sigma); eauto.
    - edestruct fresh_spec with (l := # :: Sigma); try reflexivity; eauto.
    - edestruct fresh_spec with (l := # :: Sigma); eauto.
  Qed.
  
  Definition encoding A := flat_map enc (rev A).
  
  Lemma start_map_enc A : sym A <<= Sigma ->
    ~ Start el flat_map enc A.
  Proof.
    cbn. intros ? ([x y] & ? & [] % start_enc) % in_flat_map ? ?; eapply H.
    - eapply sym_word_l; eauto.
    - eapply sym_word_R; eauto.
  Qed.

  Hint Rewrite flat_map_concat_map : list.

  Opaque Start.
  
  Lemma G1_inv x :
    rewt G1 [Start] x -> exists A M, A <<= P /\ ((M = [Start] \/ (M = [#] /\ A <> [])) /\ x = (C1 A) ++ M ++ encoding A).
  Proof.
    unfold encoding. induction 1.
    - exists []. exists [Start]. cbn. firstorder.
    - destruct IHrewt as (A & M & Hsub & [-> | [-> ?]] & ->).
      + inv H0. eapply in_rules1 in H3 as (-> & [-> | (? & ? & [-> | ->] & ? & ->)]); try now firstorder.
        * exists A, [Start]. firstorder.
        * exists (A ++ [x0]), [Start]. assert (A ++ [x0] <<= P) by (intros ? [] % in_app_iff; firstorder subst; firstorder).
          firstorder. unfold C1. list_simpl.
          change (Start :: concat (map enc (rev A))) with
              ([Start] ++ concat (map enc (rev A))) in H1. eapply symmetry in H1.
          eapply list_split in H1 as (B1 & B2 & -> & -> & ?); eauto.
          destruct B1, B2; try destruct B1; try inv H1. cbn. destruct x0. now list_simpl.
          -- intros ? % tau1_sym.
          edestruct fresh_spec with (l := # :: Sigma); try reflexivity. right.
          eapply sym_mono. eassumption. rewrite sym_app. eauto.
          -- intros (? & ? & (? & <- & ?) % in_map_iff) % in_concat_iff. destruct x3. eapply start_enc; try eassumption; eapply in_rev in H3.
             ++ eapply sym_word_l in H3. intros ? ?.
                eapply sym_mono with (A := A);  firstorder.
             ++ eapply sym_word_R in H3. intros ? ?.
                eapply sym_mono with (A := A);  firstorder.
        *  exists (A ++ [x0]), [#]. assert (A ++ [x0] <<= P) by (intros ? [] % in_app_iff; firstorder subst; firstorder).
          firstorder. unfold C1. list_simpl.
          change (Start :: concat (map enc (rev A))) with
              ([Start] ++ concat (map enc (rev A))) in H1. eapply symmetry in H1.
          eapply list_split in H1 as (B1 & B2 & -> & -> & ?); eauto.
          destruct B1, B2; try destruct B1; try inv H1. cbn. destruct x0. now list_simpl.
          -- intros ? % tau1_sym.
          edestruct fresh_spec with (l := # :: Sigma); try reflexivity. right.
          eapply sym_mono. eassumption. rewrite sym_app. eauto.
          -- intros (? & ? & (? & <- & ?) % in_map_iff) % in_concat_iff. destruct x3. eapply start_enc; try eassumption; eapply in_rev in H3.
             ++ eapply sym_word_l in H3. intros ? ?.
                eapply sym_mono with (A := A);  firstorder.
             ++ eapply sym_word_R in H3. intros ? ?.
                eapply sym_mono with (A := A);  firstorder.
      + inv H0. assert (a el x ++ a :: y) by firstorder using in_app_iff.
        eapply in_rules1 in H4 as (-> & [-> | (? & ? & [-> | ->] & ? & ->)]).
        * exists A, [#]. firstorder.
        * exfalso. rewrite H2 in H0. eapply in_app_iff in H0 as [ | [ | ] ].
          -- edestruct (fresh_spec) with (l := # :: Sigma).
             right. eapply sym_mono. eauto. eapply tau1_sym. eassumption. reflexivity.
          -- symmetry in H0. edestruct fresh_spec; try exact H0. firstorder.
          -- eapply start_map_enc; eauto. eapply sym_mono. intros ? ? % in_rev; firstorder.
        * exfalso. rewrite H2 in H0. eapply in_app_iff in H0 as [ | [ | ] ].
          -- edestruct (fresh_spec) with (l := # :: Sigma).
             right. eapply sym_mono. eauto. eapply tau1_sym. eassumption. reflexivity.
          -- symmetry in H0. edestruct fresh_spec; try exact H0. firstorder.
          -- eapply start_map_enc; eauto. eapply sym_mono. intros ? ? % in_rev; firstorder.
  Qed.
  
  Lemma L1_inv P x :
    L (f1 P) x -> exists A, A <> nil /\ A <<= P /\ (x = embed_string (C1 A) ++ # :: encoding A).
  Proof.
    unfold encoding.
    intros [H1 H2]. eapply G1_inv in H1 as (A & M & Hsub & [ -> | [-> ? ] ] & ->).
    - eapply terminal_f1 in H2. destruct H2. eapply in_app_iff. firstorder.
    - exists A. cbn. eauto.
  Qed.

  Lemma G1_char P A (H : A <<= P) :
    rewt (f1 P) [Start] (embed_string (C1 A) ++ [Start] ++ encoding A).
  Proof.
    unfold encoding. induction A.
    - cbn. reflexivity.
    - assert (a el P) by firstorder.
      rewrite rewrite_sing at 1. Focus 2.
      right. eapply in_flat_map. eauto. 
      rewrite IHA at 1.
      list_simpl. rewrite map_rev at 2. cbn. list_simpl. reflexivity. firstorder.
  Qed. 

  Lemma L1_char P A (H : A <<= P) : A <> [] ->
    L (f1 P) (embed_string (C1 A) ++ # :: flat_map enc (rev A)).
  Proof.
    intros HA. destruct (list_snoc_inv A) as [-> | (x & A' & ->)]; try congruence. split.
    - cbn. erewrite G1_char with (A := A').
      assert (x el P) by firstorder.
      rewrite rewrite_sing. Focus 2. right. eapply in_flat_map.
      exists x. split. eauto. now right.
      unfold C1, embed_string, encoding. now list_simpl. firstorder.
    - eapply terminal_f1. intros [ [] % start_embed | [ | [] % start_map_enc] ] % in_app_iff. congruence.
  Qed.

  Lemma G2_inv P x :
    rewt (f2 P) [Start] x -> exists A M, A <<= P /\ ((M = [Start] \/ (M = [Hash] /\ A <> [])) /\ x = embed_string (C2 A) ++ M ++ encoding A).
  Proof.
    unfold encoding. induction 1.
    - exists []. exists [Start]. cbn. firstorder.
    - destruct IHrewt as (A & M & Hsub & [-> | [-> ?]] & ->).
      + inv H0. eapply in_rules2 in H3 as (-> & [-> | (? & ? & [-> | ->] & ? & ->)]); try now firstorder.
        * exists A, [Start]. firstorder.
        * exists (A ++ [x0]), [Start]. assert (A ++ [x0] <<= P) by (intros ? [] % in_app_iff; firstorder subst; firstorder).
          firstorder. unfold C2, embed_string. list_simpl.
          change (Start :: concat (map enc (rev A))) with
              ([Start] ++ concat (map enc (rev A))) in H1. eapply symmetry in H1.
          eapply list_split in H1 as (B1 & B2 & -> & -> & ?); eauto.
          destruct B1, B2; try destruct B1; try inv H1. cbn. now list_simpl.
          eapply start_embed. rewrite <- flat_map_concat_map. eapply start_map_enc.
        * exists (A ++ [x0]), [Hash]. assert (A ++ [x0] <<= P) by (intros ? [] % in_app_iff; firstorder subst; firstorder).
          firstorder. unfold C2, embed_string. list_simpl.
          change (Start :: concat (map enc (rev A))) with
              ([Start] ++ concat (map enc (rev A))) in H1. eapply symmetry in H1.
          eapply list_split in H1 as (B1 & B2 & -> & -> & ?); eauto.
          destruct B1, B2; try destruct B1; try inv H1. cbn. now list_simpl.
          eapply start_embed. rewrite <- flat_map_concat_map. eapply start_map_enc.
      + inv H0. assert (a el x ++ a :: y) by firstorder using in_app_iff.
        eapply in_rules2 in H4 as (-> & [-> | (? & ? & [-> | ->] & ? & ->)]); try now firstorder;
          rewrite H2 in H0; eapply in_app_iff in H0 as [ [] % start_embed | [ | [] % start_map_enc]]; congruence.
  Qed.
  
  Lemma L2_inv P x :
    L (f2 P) x -> exists A, A <> nil /\ A <<= P /\ (x = embed_string (C2 A) ++ # :: flat_map enc (rev A)).
  Proof.
    intros [H1 H2]. eapply G2_inv in H1 as (A & M & Hsub & [ -> | [-> ? ] ] & ->).
    - eapply terminal_f2 in H2. destruct H2. eapply in_app_iff. firstorder.
    - exists A. cbn. eauto.
  Qed.

  Lemma G2_char P A (H : A <<= P) :
    rewt (f2 P) [Start] (embed_string (C2 A) ++ [Start] ++ flat_map enc (rev A)).
  Proof.
    induction A.
    - cbn. reflexivity.
    - assert (a el P) by firstorder.
      rewrite rewrite_sing at 1. Focus 2. right. eapply in_flat_map. eauto.
      rewrite IHA at 1. list_simpl. rewrite map_rev at 2. cbn. now list_simpl.
      firstorder.
  Qed.

  Lemma L2_char P A (H : A <<= P) : A <> [] ->
    L (f2 P) (embed_string (C2 A) ++ # :: flat_map enc (rev A)).
  Proof.
    intros HA. destruct (list_snoc_inv A) as [-> | (x & A' & ->)]; try congruence. split.
    - cbn. erewrite G2_char with (A := A').
      assert (x el P) by firstorder.
      rewrite rewrite_sing. Focus 2. right. eapply in_flat_map.
      exists x. split. eauto. now right.
      unfold C2, embed_string, encoding. now list_simpl. firstorder.
    - eapply terminal_f2. intros [ [] % start_embed | [ | [] % start_map_enc] ] % in_app_iff. congruence.
  Qed.

  Lemma enc_inj A1 A2 :
    encoding A1 = encoding A2 -> A1 = A2.
  Proof.
    enough (forall A1 A2, flat_map enc A1 = flat_map enc A2 -> A1 = A2).
    unfold encoding. intros ? % H. now eapply rev_eq. clear.
    intros A1.  induction A1; intros.
    - destruct A2 as [ | [[]]]. reflexivity. inv H. inv H.
    - destruct a as (x, y). destruct A2. cbn in H. destruct x. inv H. inv H.
      cbn in H. destruct p as (x',y'). cbn in H. list_simpl.
      eapply list_prefix_inv in H as [? [] % list_prefix_inv].
      eapply map_injective in H; eapply map_injective in H0; try firstorder congruence. subst.
      f_equal. eapply IHA1. now rewrite H1, flat_map_concat_map.
      all: intros (? & ? & ?) % in_map_iff; congruence.
  Qed.
  
  Lemma reduction P :
    PCP P <-> inter_nonempty (f P).
  Proof.
    split.
    - intros (A & Hm & He & Hs).
      pose proof (L1_char He Hm).
      pose proof (L2_char He Hm).
      rewrite Hs in H. eexists. eauto.
    - intros (x & (A1 & H1 & Hs1 & ?) % L1_inv & (A2 & H2 & Hs2 & ->) % L2_inv).
      eapply list_prefix_inv in H as [].
      unfold embed_string in H. eapply map_injective in H; try firstorder congruence.
      eapply enc_inj in H0. subst.
      exists A1. repeat split. firstorder. firstorder. hnf. unfold C2 in H. now rewrite H.
      all : unfold embed_string; intros (? & ? & ?) % in_map_iff; congruence.
  Qed.

End Reduction.
                     
Definition mapo X Y (f : X -> option Y) (A : list X) : list Y :=
  concat (map (fun x => match f x with None => [] | Some y => [y] end) A).

Lemma mapo_app X Y (f : X -> option Y) A B :
  mapo f (A ++ B) = mapo f A ++ mapo f B.
Proof.
  unfold mapo. now autorewrite with list.
Qed.
Hint Rewrite mapo_app : list.

Section TrivialLift.

  Variable Gamma' : finType.
  Variable Gamma : finType.

  Variable f : Gamma' -> Gamma.
  Variable g : Gamma -> option Gamma'.

  Hypothesis inv : forall x, g (f x) = Some x.
  Hypothesis tight : forall x y, g x = Some y -> f y = x.
  
  Definition up (G : cfg Gamma') : cfg Gamma :=
    (f (startsym G), map (fun '(x,A) => (f x, map f A) ) (rules G)).

  Lemma mapo_map x :
    mapo g  (map f x) = x.
  Proof.
    induction x.
    - reflexivity.
    - cbn. rewrite inv. now rewrite <- IHx at 2.
  Qed.

  Lemma up_rew1 G x y :
    rew_cfg G x y -> rew_cfg (up G) (map f x) (map f y).
  Proof.
    intros H. inv H. autorewrite with list.
    cbn [map]. econstructor.  eapply in_map_iff. exists (a, v). eauto.
  Qed.

  Lemma up_rew2 G x y :
    rew_cfg (up G) x y -> rew_cfg G (mapo g x) (mapo g y).
  Proof.
    intros H. inv H. cbn in H0.
    eapply in_map_iff in H0 as ([] & ? & ?). inv H. autorewrite with list.
    cbn [mapo concat map]. rewrite inv. change ([e] ++ []) with [e].
    econstructor. unfold mapo. autorewrite with list. erewrite map_ext with (g := fun x => [ x ]).
    enough (l = concat (map (fun x => [x]) l)) as <- by trivial.
    clear; induction l; cbn; congruence. intros; now rewrite inv.
  Qed.
 Lemma up_char1 G x y :
    rewt G x y -> rewt (up G) (map f x) (map f y).
  Proof.
    induction 1.
    - reflexivity.
    - rewrite IHrewt. econstructor. reflexivity. eapply up_rew1. eauto.
  Qed.

  Lemma up_char2 G x y :
    rewt (up G) x y -> rewt G (mapo g x) (mapo g y).
  Proof.
    induction 1.
    - reflexivity.
    - rewrite IHrewt. econstructor. reflexivity. eapply up_rew2. eauto.
  Qed.
  
  Lemma up_ter1 G x :
    terminal G x -> terminal (up G) (map f x).
  Proof.
    intros ? [? ?]. eapply H.
    exists (mapo g x0). eapply up_rew2 in H0. now rewrite mapo_map in *.
  Qed.

  Lemma up_ter2 G y :
    terminal (up G) y -> terminal G (mapo g y).
  Proof.
    intros H. rewrite terminal_iff in H.
    eapply terminal_iff. intros. unfold mapo in H0.
    eapply in_concat_iff in H0 as (? & ? & (? & ? & ?) % in_map_iff).
    destruct (g x0) eqn:E; subst; destruct H0. subst. intros ?.
    eapply (H _ (map f y0) H2). cbn. eapply in_map_iff.
    exists (s, y0). eapply tight in E. subst. eauto. destruct H0.
  Qed.

  Lemma up_char G x :
    rewt G [(startsym G)] x <-> rewt (up G) [(startsym (up G))] (map f x).
  Proof.
    split; intros H.
    - eapply up_char1 in H. eassumption.
    - eapply up_char2 in H. cbn in H. now rewrite mapo_map,  inv, app_nil_r in H.
  Qed.
  
End TrivialLift.

Module Hesselink.

Section ReductionHesselink.

  Variable Sigma' : Type.
  
  Variable P : pcp Sigma'.
  
  Inductive Sigma := embed (s : Sigma') | Start | hash.

  Definition embed_string (s : list Sigma') := map embed s.

  Notation "#" := hash.

  Definition f : pcp Sigma' -> cfg Sigma :=
    fun P =>
      (Start, (Start, [Start]) ::
        (flat_map
           (fun x => [ (Start, embed_string (fst x) ++ [Start] ++ embed_string (rev (snd x)));
                          (Start, embed_string (fst x) ++ [#] ++ embed_string (rev (snd x)))])
           P)).

  Lemma in_rules x A :
    (x, A) el rules (f P) -> x = Start /\ (A = [Start] \/ (exists x M, (M = Start \/ M = #) /\ x el P /\ A = embed_string (fst x) ++ [M] ++ embed_string (rev (snd x)))).
  Proof.
    unfold f. cbn. intros [ | (? & ? & [H | [H | []]]) % in_flat_map]; inv H.
    - intuition.
    - intuition. right. exists x0, Start; firstorder.
    - intuition. right. exists x0, #; firstorder.
  Qed.
  
  Lemma terminal_f x :
    ~ Start el x <->
    terminal (f P) x.
  Proof.
    rewrite terminal_iff. split.
    - now intros ? ? ? ? [-> ?] % in_rules.
    - intros ? ?. eapply (H _ _ H0). now left.
  Qed.

  Inductive L_ind (P : pcp Sigma') : list Sigma -> pcp Sigma' -> Prop :=
  | L_ind_stop x y : (x,y) el P -> L_ind P (embed_string x ++ [#] ++ embed_string (rev y)) [(x,y)]
  | L_ind_start : L_ind P [Start] []
  | L_ind_step x y z A : (x, y) el P -> L_ind P z A -> L_ind P (embed_string x ++ z ++ embed_string (rev y)) ((x,y)::A).
  Hint Constructors L_ind.

  Lemma L_ind_to x A :
    L_ind P x A -> rewt (f P) [Start] x.
  Proof.
    intros H.
    induction H.
      + rewrite rewrite_sing. reflexivity. right.
        eapply in_flat_map. exists (x, y). firstorder.
      + reflexivity.
      + rewrite rewrite_sing at 1. Focus 2.
        * right. eapply in_flat_map.
          exists (x, y). firstorder.
          rewrite IHL_ind. reflexivity.
  Qed.
  
  Lemma Start_embed_string x :
    ~ Start el embed_string x.
  Proof.
    unfold embed_string. intros [? ?] % in_map_iff. firstorder congruence.
  Qed.
  Hint Immediate Start_embed_string.
  
  Lemma L_ind_insert M :
    forall (A : list (list Sigma' * list Sigma')) (x0 : list Sigma' * list Sigma'),
      x0 el P -> (M = # \/ M = Start) ->
      forall x y0 : list Sigma,
        L_ind P (x ++ [Start] ++ y0) A ->
        L_ind P (x ++ (embed_string (fst x0) ++ M :: embed_string (rev (snd x0))) ++ y0) (A ++ [(fst x0, snd x0)]).
  Proof.
    intros A x0 H HM.
    induction A; intros x y0 H1; cbn in *; inv H1.
    * destruct x, y0; [ | try destruct x; inv H2..].
      rewrite app_nil_r. destruct x0. destruct HM; subst. now econstructor. cbn.
      change (Start :: map embed (rev l0)) with ([Start] ++ map embed (rev l0)). now econstructor.
    * cbn.
      enough (~ Start el embed_string x1 ++ # :: embed_string (rev y)).
      rewrite H0 in H1. destruct H1.
      eapply in_app_iff. firstorder. unfold embed_string.
      intros [[] % in_map_iff | [? | [] % in_map_iff]] % in_app_iff; firstorder congruence.
    * eapply list_split in H0 as (B1 & B2 & -> & -> & ->); eauto.
      replace (((embed_string x1 ++ B1) ++ (embed_string (fst x0) ++ M :: embed_string (rev (snd x0))) ++ B2 ++ embed_string (rev y))) with
          (embed_string x1 ++ (B1 ++ ((embed_string (fst x0) ++ M :: embed_string (rev (snd x0)))) ++ B2) ++ embed_string (rev y)) by now autorewrite with list. eauto.
  Qed.
    
  Lemma L_ind_char x :
    rewt (f P) [Start] x <-> exists A, L_ind P x A.
  Proof.
    split.
    - induction 1.
      + exists []. econstructor.
      + inv H0. destruct IHrewt as [A IH].
        apply in_rules in H1 as (-> & [-> | (? & ? & [-> | ->] & ? & ->)]); try now firstorder.
        * exists (A ++ [(fst x0, snd x0)]); eapply L_ind_insert; eauto.
        * exists (A ++ [(fst x0, snd x0)]); eapply L_ind_insert; eauto.
    - intros [A H]. eapply L_ind_to. eassumption.
  Qed.

  Lemma L_ind_char2 A :
    A <> nil /\ A <<= P <-> exists x, ~ startsym (f P) el x /\ L_ind P x A.
  Proof.
    split.
    - intros. induction A.
      + tauto.
      + destruct a as (x, y). destruct A.
        * exists (embed_string x ++ [#] ++ embed_string (rev y)). split.
          -- cbn. intros [ | [ | ] ] % in_app_iff; try congruence; eapply Start_embed_string; eauto.
          -- econstructor. firstorder.
        * destruct IHA as [z IH]; try firstorder congruence.
          exists (embed_string x ++ z ++ embed_string (rev y)). split.
          -- cbn in *. intros [ | [ | ] % in_app_iff ] % in_app_iff; try tauto; eapply Start_embed_string; eauto.
          -- econstructor; firstorder.
    - intros [x []]. split.
      + inv H0; firstorder.
      + clear H. induction H0; intuition.
  Qed.

  Ltac list_simpl := (repeat (progress (cbn; autorewrite with list))); cbn.
  
  Definition concat_map A B (f : A -> list B) x := concat (map f x).
  Lemma L_ind_inv x (A : pcp _) :
    L_ind P x A ->
    exists M, (M = Start \/ M = #) /\ x = embed_string (concat_map fst A) ++ [M] ++ embed_string (concat_map (@rev _ ∘ snd) (rev A)).
  Proof.
    induction 1.
    - exists #. list_simpl. firstorder.
    - exists Start. cbn. firstorder.
    - destruct IHL_ind as (M & [-> | ->] & ->).
      + exists Start. firstorder. unfold embed_string, concat_map. now list_simpl.
      + exists #. firstorder. unfold embed_string, concat_map. now list_simpl.
  Qed.

  Lemma L_ind_palindrome x A :
    L_ind P x A ->
    x = rev x <-> solution A.
  Proof.
    intros H. unfold solution.
    enough (exists M, (forall s, ~ M el embed_string s) /\ x = embed_string (concat_map fst A) ++ [M] ++ embed_string (concat_map (@rev _ ∘ snd) (rev A))) as (M & ? & ->).
    unfold embed_string, concat_map. list_simpl. split; intros E.
    - eapply list_prefix_inv in E as [E _]; firstorder.
      eapply map_injective in E; [|  intuition congruence].
      rewrite E. f_equal. eapply map_ext. intros; now list_simpl.
    - rewrite E. f_equal; [|f_equal].
      do 2 f_equal. eapply map_ext; intros; now list_simpl. f_equal.
      rewrite !map_rev. rewrite <- map_map. rewrite !concat_rev. rewrite <- E.
      rewrite <- map_map with (g := @rev _). now rewrite concat_rev.
    - eapply L_ind_inv in H as (? & [-> | ->] & ->); eexists; split; try reflexivity.
      firstorder using Start_embed_string. intros ? ?. unfold embed_string in H.
      eapply in_map_iff in H. firstorder congruence.
  Qed.
  
  Theorem PCP_CFG :
    PCP P <-> PALIN (f P).
  Proof.
    split.
    - intros [A (? & ? & H)].
      edestruct (L_ind_char2) as [ (? & ? & ?) _ ]. eauto.
      unfold PALIN. exists x. split. split.
      + eapply L_ind_char. eauto.
      + eapply terminal_f. exact H2.
      + eapply L_ind_palindrome; eauto.
    - intros (S & [[A H] % L_ind_char H2 % terminal_f] & Hr). unfold PCP.
      exists A. repeat split; [ eapply L_ind_char2; eauto.. | ].
      eapply L_ind_palindrome; eauto.
  Qed.
  
End ReductionHesselink.

Section Palindrome.

  Variable Gamma' : finType.
  Inductive Gamma := emb (x : Gamma') | StartG.

  Global Instance eq_dec_gamma : eq_dec Gamma.
  Proof.
    intros ? ?. hnf. decide equality.
    assert (H : eq_dec Gamma') by exact _. apply H.
  Defined.

  Global Instance fin_gamma : finTypeC (EqType Gamma).
  Proof.
    exists (StartG :: map emb (elem Gamma')).
    intros []; cbn. admit. edestruct notInZero. rewrite H. reflexivity.
    intros (? & ? & ?) % in_map_iff. congruence.
  Admitted.
  
  Definition emb_string := map emb.
  
  Definition palin_G : cfg Gamma :=
    (StartG, (StartG, []) ::
     flat_map (fun g => [ (StartG, [emb g]);  (StartG, [emb g; StartG; emb g]) ]) (elem Gamma')).

  Lemma G_left x :
    rewt palin_G [StartG] x -> rev x = x /\ count x StartG <= 1.
  Proof.
    induction 1.
    - firstorder.
    - destruct IHrewt as [IH Eq]. inv H0. cbn in H1. destruct H1.
      + inv H0. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *. split; try omega.
        assert (count x StartG = 0) as H1 % notInZero by omega.
        assert (count y0 StartG = 0) as H2 % notInZero by omega.
        eapply list_prefix_inv in IH as [<- _]; try rewrite <- in_rev; eauto.
        now rewrite rev_involutive.
      + eapply in_flat_map in H0 as (? & ? & [ | [ | [] ]]).
        * inv H1. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *. split; try omega.
          assert (count x StartG = 0) as H1 % notInZero by omega.
          assert (count y0 StartG = 0) as H2 % notInZero by omega.
          eapply list_prefix_inv in IH as [ <- _]; try rewrite <- in_rev; eauto.
          now rewrite rev_involutive.
        * inv H1. rewrite <- !countSplit in *. autorewrite with list in *. cbn in *. split; try omega.
          assert (count x StartG = 0) as H1 % notInZero by omega.
          assert (count y0 StartG = 0) as H2 % notInZero by omega.
          eapply list_prefix_inv in IH as [<- _]; try rewrite <- in_rev; eauto.
          now rewrite rev_involutive.
  Qed.

  Lemma listI : forall (A : Type) (P : list A -> Prop), P [] -> (forall x, P [x]) -> (forall (x : A) (y : A) (l : list A), P l -> P (x :: l ++ [y])) -> forall l : list A, P l.
  Proof.
    intros. pattern l. revert l. apply size_induction with (f := @length _). intros.
    destruct x.
    - auto.
    - revert H2. pattern x. revert x. apply rev_ind. auto.
      intros. apply H1. apply H3. cbn. rewrite app_length. omega.
  Qed.

  Lemma rev_palin x :
    x = rev x -> count x StartG <= 1 -> rewt palin_G [StartG] x.
  Proof.
    pattern x. revert x. apply listI; intros.
    - rewrite rewrite_sing. reflexivity. now left.
    - destruct x. rewrite rewrite_sing. reflexivity. right. eapply in_flat_map. eauto. reflexivity.
    - cbn in H0. autorewrite with  list in *. inv H0.
      cbn in H1. rewrite <- countSplit in H1.
      destruct y.
      + rewrite rewrite_sing with (x := [emb x] ++ [StartG] ++ [emb x]).
        rewrite H.
        * cbn. reflexivity.
        * now eapply app_inv_tail in H4.
        * cbn in *; omega.
        * right. eapply in_flat_map. cbn. eauto.
      + cbn in *. omega.
  Qed.

  Lemma emb_Start x :
    ~ StartG el emb_string x.
  Proof.
    intros ?. unfold emb_string in *. eapply in_map_iff in H. firstorder congruence.
  Qed.
  
  Lemma G_char (x : list Gamma') :
    x = rev x <-> L palin_G (emb_string x).
  Proof.
    split.
    - intros H. split.
      + assert (emb_string x = rev (emb_string x)). rewrite H. unfold emb_string. autorewrite with list. congruence.
        eapply rev_palin in H0. eassumption.
        enough (count (emb_string x) StartG = 0) by omega.
        eapply notInZero. eapply emb_Start.
      + intros [y Hy].
        inv Hy. destruct H2. inv H1.
        eapply emb_Start. rewrite <- H0. eapply in_app_iff. firstorder.
        eapply in_flat_map in H1 as (? & ? & [ | [ | [] ]]).
        * inv H2. eapply emb_Start. rewrite <- H0. eapply in_app_iff. firstorder.
        * inv H2.  eapply emb_Start. rewrite <- H0. eapply in_app_iff. firstorder.
    - intros [[] % G_left Ht]. unfold emb_string in *.
      autorewrite with list in *. eapply map_injective in H; intuition congruence.
  Qed.
  
  Definition rem_S x := mapo (fun x => match x with StartG => None | emb x => Some x end) x.

  Lemma rem_S_rev x :
    rev (rem_S x) = rem_S (rev x).
  Proof.
    induction x.
    - reflexivity.
    - cbn [rev]. unfold rem_S in *. rewrite mapo_app, <- IHx. unfold  mapo. cbn. destruct a; now autorewrite with list.
  Qed.

  Lemma rem_S_cons x0 x :
    rem_S (emb x0 :: x) = x0 :: rem_S x.
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma rem_S_char x :
    ~ StartG el x -> emb_string (rem_S x) = x.
  Proof.
    induction x.
    - reflexivity.
    - intros. destruct a.
      + rewrite rem_S_cons. cbn. rewrite IHx. reflexivity. firstorder.
      + firstorder.
  Qed.

End Palindrome.

Hint Rewrite mapo_app : list.

Definition inter_nonempty X '(G1, G2) :=
  exists x, @L X G1 x /\ L G2 x.

Theorem intersect (Sigma : finType) (G : cfg Sigma) :
  exists f, PALIN G <-> @inter_nonempty (Gamma Sigma) (f G).
Proof.
  exists (fun G => (palin_G Sigma, up (@emb Sigma) G)). split; intros (? & ? & ?).
  - exists (emb_string x). rewrite <- G_char. intuition. destruct H. split.
    + eapply up_char1 in H. eapply H.
    + eapply up_ter1 with (g :=  fun x => match x with emb x => Some x | _ => None end) in H1.
      eapply H1. reflexivity.
  - destruct H. eapply G_left in H.
    exists (rem_S x). split. destruct H0. split.
    + eapply up_char2 in H0. unfold rem_S. now rewrite <- H0.
      tauto.
    + eapply up_ter2 with (g :=  fun x => match x with emb x => Some x | _ => None end) in H2.
      eapply H2. cbn. intros []; intuition congruence.
    + rewrite rem_S_rev. destruct H. now rewrite H.
Qed.

End Hesselink.
