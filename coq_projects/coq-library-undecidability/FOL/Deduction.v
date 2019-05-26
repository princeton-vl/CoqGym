(** * Natural Deduction *)

Require Export Semantics.

(** ** Definition *)

Inductive nd := intu | class.
Existing Class nd.

Inductive prv : forall {s : nd} {b : logic} (A : list (form b)), form b -> Prop :=
| Ctx {b} {s : nd} (A : list (form b)) phi : In phi A -> prv A phi
| ImpI {b} {s : nd} (A : list (form b)) phi1 phi2 : prv (phi1::A) phi2 -> prv A (phi1 --> phi2)
| ImpE {b} {s : nd} (A : list (form b)) phi1 phi2 : prv A (phi1 --> phi2) -> prv A phi1 -> prv A phi2
| AllI {b} {s : nd} (A : list (form b)) x y phi : fresh y (consts phi ++ consts_l A) -> prv A (subst x (P y) phi) -> prv A (∀ x ; phi)
| AllE {b} {s : nd} (A : list (form b)) x t phi : vars_t t = [] 
                                       -> prv A (All x phi) -> prv A (subst x t phi)

| Exp A phi : @prv intu full A Fal -> @prv intu full A phi
| DN A phi : @prv class full A (¬¬ phi) -> @prv class full A phi.

Notation "A ⊢ phi" := (prv A phi) (at level 30).

Definition prv_min := @prv intu frag.
Definition prv_class := @prv class full.
Definition prv_intu := @prv intu full.

Notation "A ⊢M phi" := (prv_min A phi) (at level 30).
Notation "A ⊢I phi" := (@prv intu _ A phi) (at level 30).
Notation "A ⊢C phi" := (@prv class _ A phi) (at level 30).

Lemma prv_ind_min :
  forall p : list (form frag) -> form frag -> Prop,
       (forall  (A : list (form frag)) (phi : form frag), phi el A -> p A phi) ->
       (forall  (A : list (form frag)) (phi1 phi2 : form frag),
        (phi1 :: A) ⊢I phi2 -> p (phi1 :: A) phi2 -> p A (phi1 --> phi2)) ->
       (forall  (A : list (form frag)) (phi1 phi2 : form frag),
        A ⊢I (phi1 --> phi2) -> p A (phi1 --> phi2) -> A ⊢I phi1 -> p A phi1 -> p A phi2) ->
       (forall  (A : list (form frag)) (x y : nat) (phi : form frag),
        fresh y (consts phi ++ consts_l A) ->
        A ⊢I subst x (P y) phi -> p A (subst x (P y) phi) -> p A (∀ x; phi)) ->
       (forall  (A : list (form frag)) (x : nat) (t : term) (phi : form frag),
           vars_t t = [] ->
        A ⊢I (∀ x; phi) -> p A (∀ x; phi) -> p A (subst x t phi)) ->
       forall (A : list (form frag)) (f9 : form frag), A ⊢I f9 -> p A f9.
Proof.
  remember frag as b. remember intu as s. intros. induction H4; eauto; try congruence.
  - firstorder. 
  - eapply H1. eauto. eapply IHprv1. all:eauto. eapply IHprv2. all:eauto.
  - eapply H2; eauto. eapply IHprv; eauto.
  - eapply H3; eauto. eapply IHprv; eauto.
Qed.



(** ** Soundness *)


Definition cast {domain} (eta eta' : nat -> domain) (I : interp eta) : interp eta'.
  destruct I; econstructor; eauto.
Defined.

Lemma eval_ext_p t dom rho rho' eta eta' (I : interp dom eta) :
  (forall v, v el vars_t t -> rho v = rho' v) ->
  (forall p, p el consts_t t -> eta p = eta' p) ->
  @eval _ _ I rho t = @eval _ _ (cast eta' I) rho' t.
Proof.
  intros. induction t; cbn in *; intros; eauto.
  - rewrite IHt; destruct I; eauto.
  - destruct I; eauto.
Qed.

Lemma eval_ext t dom rho rho' eta (I : interp dom eta) :
  (forall v, v el vars_t t -> rho v = rho' v) -> eval rho t = eval rho' t.
Proof.
  intros H. destruct I. apply eval_ext_p; trivial.
Qed.

Lemma sat_ext_p b (phi : form b) dom rho rho' eta eta' (I : interp dom eta) :
  (forall v, rho v = rho' v) ->
  (forall p, p el consts phi -> eta p = eta' p) ->
  sat I rho phi <-> sat (cast eta' I) rho' phi.
Proof.
  intros. revert rho rho' H; induction phi; cbn in *; intros.
  - destruct I. erewrite eval_ext_p with (eta' := eta').
    erewrite eval_ext_p with (eta := eta).
    cbn. reflexivity. all: cbn in *; firstorder.
  - destruct I; firstorder.
  - firstorder.
  - rewrite IHphi1, IHphi2. reflexivity. all:firstorder.
  - firstorder; eapply IHphi. 6:eapply H1. 3:eapply H1. all:firstorder. all:decs.
Qed.

Lemma sat_ext b (phi : form b) dom rho rho' eta (I : interp dom eta) :
  sat I rho phi -> (forall v, rho v = rho' v) -> sat I rho' phi.
Proof.
  intros H1 H2. rewrite sat_ext_p with (eta' := eta) in H1; trivial. now destruct I.
Qed.

Lemma sat_ext_p_list b (A : list (form b)) dom rho rho' eta eta' (I : interp dom eta) :
  (forall v, rho v = rho' v) ->
  (forall p, p el consts_l A -> eta p = eta' p) ->
  (forall phi, phi el A -> sat I rho phi) <-> (forall phi, phi el A -> sat (cast eta' I) rho' phi).
Proof.
  firstorder.
  - destruct I; cbn. eapply sat_ext_p. 3:eapply H1.
    all:firstorder. symmetry. eapply H0. eapply in_flat_map; eauto.
  - destruct I; cbn.  eapply sat_ext_p. 3:eapply H1.
    all:firstorder. eapply H0. eapply in_flat_map; eauto.
Qed.

Lemma eval_empty t dom eta (I : interp dom eta) rho rho' :
  vars_t t = [] -> eval rho t = eval rho' t.
Proof.
  intros H. apply eval_ext. rewrite H. now intros n [].
Qed.

Lemma subst_eval dom eta (I : interp dom eta) rho x t t' :
  eval rho (subst_t x t' t) = eval (rho [[x:=eval rho t']]) t.
Proof.
  induction t; cbn; try congruence. decs.
Qed.

Lemma subst_sat b (phi : form b) dom eta (I : interp dom eta) rho x t :
  vars_t t = [] -> sat I rho (subst x t phi) <-> sat I (rho [[x:=eval rho t]]) phi.
Proof.
  intros Hy. revert rho.
  induction phi; intros rho; cbn in *; try rewrite fresh_app in *.
  - cbn. now rewrite !subst_eval.
  - reflexivity.
  - reflexivity.
  - cbn. firstorder.
  - cbn. dec.
    + split; intros H d; specialize (H d).
      * eapply (sat_ext H). intros. decs.
      * eapply (sat_ext H). intros. decs.
    + split; intros H d; specialize (H d).
      * rewrite IHphi in H. rewrite eval_empty with (rho':=rho) in H; trivial.
        apply (sat_ext H). intros y. decs.
      * rewrite IHphi. rewrite eval_empty with (rho':=rho); trivial.
        apply (sat_ext H). intros y. decs.
Qed.

Lemma substconst_sat b (phi : form b) dom eta rho x a d (I : interp dom eta) :
  fresh a (consts phi) ->
  sat (eta [[a := d]]) (cast _ I) rho (subst x (P a) phi) <->
  sat eta I (rho [[ x := d ]]) phi.
Proof.
  intros H. rewrite subst_sat; trivial.
  symmetry. apply sat_ext_p; intros n; repeat decs.
Qed.

Lemma soundness' {b} A (phi : form b) :
  A ⊢I phi -> valid (A ==> phi).
Proof.
  remember intu as s. induction 1; intros D eta I rho; eapply impl_sat; intros; subst; try congruence.
  - eauto.
  - intros ?. eapply (impl_sat' (IHprv eq_refl D eta I rho)). now firstorder subst. 
  - now eapply (impl_sat' (IHprv1 eq_refl D eta I rho)), (impl_sat' (IHprv2 eq_refl D eta I rho)).
  - intros d. specialize (IHprv eq_refl D (eta [[y := d]]) (cast _ I) rho ).
    rewrite impl_sat in IHprv. rewrite <- substconst_sat. apply IHprv. 2: firstorder.
    eapply sat_ext_p_list. all:destruct I. 3: eapply H1. all:firstorder.
    cbn. decs. destruct H; firstorder. 
  - eapply subst_sat; trivial.
    now eapply (impl_sat' (IHprv eq_refl D eta I rho)).
  - specialize (IHprv eq_refl D eta I rho) as []  % impl_sat; eauto.
Qed.

Theorem soundness {b} (phi : form b) :
  nil ⊢I phi -> valid phi.
Proof.
  intros H I rho. now eapply (soundness' H).
Qed.

(** ** Generalised Induction *)

Fixpoint size {b} (phi : form b) :=
  match phi with
  | Pr _ _ | Q | Fal => 1
  | Impl phi1 phi2 => 1 + size phi1 + size phi2
  | All n phi => 1 + size phi
  end.

Lemma size_subst {b : logic} x t phi :
  size (subst x t phi) = size phi.
Proof.
  induction phi; cbn; try congruence; decs.
Qed.

Lemma form_ind_subst :
forall P : forall f : logic, form f -> Prop,
(forall (b : logic) (t t0 : term), P b (Pr t t0)) ->
(forall b : logic, P b Q) ->
P full ⊥ ->
(forall (b : logic) (f2 : form b), P b f2 -> forall f3 : form b, P b f3 -> P b (f2 --> f3)) ->
(forall (b : logic) (n : var) (f4 : form b), (forall x, P b (subst n x f4)) -> P b (∀ n; f4)) -> forall (f5 : logic) (f6 : form f5), P f5 f6.
Proof.
  intros. eapply size_induction_dep with (f := @size). intros b x IH. destruct x; eauto.
  - eapply H2; eapply IH; cbn; omega.
  - eapply H3. intros. eapply IH. rewrite size_subst. cbn. omega.
Qed.

Lemma form_logic_ind_subst :
forall P : form frag -> Prop,
(forall t t0 : term, P (Pr t t0)) ->
P Q ->
(forall f3 : form frag, P f3 -> forall f4 : form frag, P f4 -> P (f3 --> f4)) ->
(forall (n : var) (f6 : form frag), (forall x, P (subst n x f6)) -> P (∀ n; f6)) -> forall f8 : form frag, P f8.
Proof.
  intros. remember frag as b.  revert Heqb. pattern f8. eapply size_induction with (f := @size b). intros x IH E. destruct x; eauto.
  - inv E.
  - eapply H1; eapply IH; cbn; eauto; omega.
  - eapply H2. intros. eapply IH. rewrite size_subst. cbn. omega. eauto.
Qed.

(** ** Enumerability *)

Lemma dec_fresh y A : dec (fresh y A).
Proof.
  induction A; try decide (y = a); try destruct IHA; subst; firstorder.
Qed.

Lemma incl_dec X (A B : list X) `{eq_dec X} : dec (A <<= B).
Proof.
  pose proof (forallb_forall (fun a => list_in_dec a B _) A).
  destruct (forallb (fun a : X => list_in_dec a B H) A).
  - left. intros ? ?. eapply H0 in H1. destruct list_in_dec; now inv H1. reflexivity.
  - right. intros ?. enough (false = true) by congruence. eapply H0.
    intros. destruct list_in_dec; cbn. reflexivity. exfalso; eauto.
Qed.

Fixpoint L_ded {b} {s : nd} (A : list (form b)) (n : nat) : list (form b) :=
  match n with
  | 0 => A
  | S n => L_ded A n
                ++ concat [ [ phi1 --> phi2 | phi2 ∈ L_ded (phi1 :: A) n ] | phi1 ∈ L_T (form b) n]
                ++ [ phi2 | (phi1,phi2) ∈ (L_ded A n × L_T (form b) n) , (phi1 --> phi2 el L_ded A n) ]
                ++ [ ∀ x; phi | (phi, x, y) ∈ (L_T (form b) n × L_T var n × L_T var n) ,
                               fresh y (consts phi ++ consts_l A) /\ subst x (P y) phi el L_ded A n ]
                ++ [ subst x t phi | (phi, x, t) ∈ (L_T (form b) n × L_T var n × L_T term n),
                                    vars_t t = [] /\ ∀ x; phi el L_ded A n]
                ++ match b with frag => fun _ => [] | full => fun A =>
                 match s with
                   | intu => [ phi | phi ∈ L_T (form full) n, Fal el L_ded A n ]
                   | class => [ phi | phi ∈ L_T (form full) n, (¬¬ phi) el L_ded A n ]
                   end end A
  end.

Opaque in_dec.
Opaque enumT_nat.

Hint Constructors prv.

Lemma enum_prv b s A : enum (@prv s b A) (L_ded A).
Proof with try (eapply cum_ge'; eauto; omega).
  repeat split.
  - eauto. 
  - rename x into phi. induction 1; try congruence; subst.
    + now exists 0.
    + destruct IHprv as [m1]; eauto. destruct (el_T phi1) as [m2].
      exists (1 + m1 + m2). cbn. in_app 2.
      eapply in_concat_iff. eexists. split.
      2:in_collect phi1...
      in_collect phi2...
    + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi2) as [m3]; eauto.
      exists (1 + m1 + m2 + m3).
      cbn. in_app 3. in_collect (phi1, phi2)...
    + destruct (el_T x) as [m1], (el_T y) as [m2],
               (el_T phi) as [m3], IHprv as [m4]; eauto.
      exists (1 + m1 + m2 + m3 + m4). cbn -[L_T]. in_app 4.
      in_collect (phi, x, y)...
    + destruct (el_T x) as [m1], (el_T t) as [m2],
               (el_T phi) as [m3], IHprv as [m4]; eauto.
      exists (1 + m1 + m2 + m3 + m4). cbn. in_app 5.
      in_collect (phi, x, t)...
    + destruct IHprv as [m1], (el_T phi) as [m2]; eauto.
      exists (1 + m1 + m2). cbn. in_app 9.
      in_collect phi...
    + destruct IHprv as [m1], (el_T phi) as [m2], (el_T true) as [m3]; eauto.
      exists (1 + m1 + m2 + m3). cbn. in_app 9.
      in_collect phi...
  - intros [m]. revert A x H; induction m; intros; cbn in *.
     + eauto.
     + inv_collect; eauto.
       destruct b, s; inv_collect; eauto.
Qed.

Lemma enumerable_min_prv : enumerable (prv_min []).
Proof.
  eapply enum_count, enum_prv.
Qed.
Lemma enumerable_intu_prv : enumerable (prv_intu []).
Proof.
  eapply enum_count, enum_prv.
Qed.
Lemma enumerable_class_prv : enumerable (prv_class []).
Proof.
  eapply enum_count, enum_prv.
Qed.
