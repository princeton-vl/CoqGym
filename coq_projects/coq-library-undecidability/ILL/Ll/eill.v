(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega.

Require Import utils pos vec ill.

Set Implicit Arguments.

(** ** eILL reduces to ILL *)

Local Infix "~p" := (@Permutation _) (at level 70).

Definition ll_vars := nat.

Inductive eill_cmd : Set :=
  | in_ll_cmd_inc  : ll_vars -> ll_vars -> ll_vars -> eill_cmd
  | in_ll_cmd_dec  : ll_vars -> ll_vars -> ll_vars -> eill_cmd
  | in_ll_cmd_fork : ll_vars -> ll_vars -> ll_vars -> eill_cmd.

Notation LL_INC  := in_ll_cmd_inc.
Notation LL_DEC  := in_ll_cmd_dec.
Notation LL_FORK := in_ll_cmd_fork.

Definition eill_cmd_vars c := 
  match c with
    | LL_INC  a p q => a::p::q::nil
    | LL_DEC  a p q => a::p::q::nil
    | LL_FORK p q r => p::q::r::nil
  end.

(* The embedding of eill commands into ill 
   or its (!,&,-o) fragment *) 

Definition eill_cmd_map c :=
  match c with
    | LL_INC  a p q => (£a ⊸ £p) -o £ q
    | LL_DEC  a p q => £a ⊸ £p -o £ q
    | LL_FORK p q r => (£p ﹠ £q) -o £ r
  end. 

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ *)

Notation "'[i' c ']'" := (eill_cmd_map c) (at level 0).

Reserved Notation "Si ; Ga '⊦' x" (at level 70, no associativity).

Inductive G_eill (Σ : list eill_cmd) : list ll_vars -> ll_vars -> Prop :=
  | in_eill_ax  : forall u,                                    Σ; u::∅ ⊦ u
  | in_eill_perm : forall Γ Δ p,    Γ ~p Δ                 ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Δ     ⊦ p
  | in_eill_inc : forall Γ a p q,   In (LL_INC a p q) Σ    ->  Σ; a::Γ  ⊦ p
                                                           ->  Σ; Γ     ⊦ q
  | in_eill_dec : forall Γ Δ p q r, In (LL_DEC p q r) Σ    ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Δ     ⊦ q
                                                           ->  Σ; Γ++Δ  ⊦ r
  | in_eill_fork : forall Γ p q r,  In (LL_FORK p q r) Σ   ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Γ     ⊦ q
                                                           ->  Σ; Γ     ⊦ r
where "Si ; Ga ⊦ u" := (G_eill Si Ga u).

Definition EILL_SEQUENT := (list eill_cmd * list ll_vars * ll_vars)%type.

Definition EILL_PROVABILITY (c : EILL_SEQUENT) := match c with (Σ,Γ,A) => Σ; Γ ⊦ A end. 

Theorem g_eill_mono_Si Σ Σ' Γ u : incl Σ Σ' -> Σ; Γ ⊦ u -> Σ'; Γ ⊦ u.
Proof.
  revert Σ Σ' Γ; intros Si Si' Ga.
  intros H H1; revert H1 Si' H.
  induction 1 as [ u
                 | Ga De p H1 H2 IH2 
                 | Ga a p q H1 H2 IH2
                 | Ga De p q r H1 H2 IH2 H3 IH3
                 | Ga p q r H1 H2 IH2 H3 IH3
                 ]; intros Si' HSi.
  + apply in_eill_ax.
  + apply in_eill_perm with (1 := H1); auto.
  + apply in_eill_inc with (1 := HSi _ H1); auto.
  + apply in_eill_dec with (1 := HSi _ H1); auto.
  + apply in_eill_fork with (1 := HSi _ H1); auto.
Qed.

(* G_eill is sound wrt. the S_ill 

   this proof only uses somes of the rules of
   the cut-free (!,&,-o) fragment
*)

Theorem G_eill_sound Σ Γ p : Σ; Γ ⊦ p -> map (fun c => ![i c]) Σ ++ map £ Γ ⊢ £ p.
Proof.
  revert Σ; intros Si.
  induction 1 as [ u
                 | Ga De p H1 H2 IH2 
                 | Ga a p q H1 H2 IH2
                 | Ga De p q r H1 H2 IH2 H3 IH3
                 | Ga p q r H1 H2 IH2 H3 IH3
                 ].
  + rewrite <- map_map; apply S_ill_weak; apply in_llp_ax.
  + revert IH2; apply in_llp_perm.
    apply Permutation_app; auto.
    apply Permutation_map; auto.
  + rewrite <- map_map; apply S_ill_weak_cntr with (1 := in_map _ _ _ H1); simpl.
    unfold ll_lbang; rewrite map_map.
    apply in_llp_bang_l.
    apply in_llp_perm with (((£ a ⊸ £ p) ⊸ £ q) :: ((map (fun c => ❗ [i c]) Si ++ map £ Ga) ++ nil)).
    * rewrite <- app_nil_end; auto.
    * apply in_llp_limp_l.
      2: apply in_llp_ax.
      apply in_llp_limp_r.
      revert IH2; apply in_llp_perm.
      simpl; apply Permutation_sym, Permutation_cons_app; auto.
  + rewrite <- map_map.
    apply S_ill_cntr.
    unfold ll_lbang; rewrite map_map.
    rewrite <- map_map; apply S_ill_weak_cntr with (1 := in_map _ _ _ H1); simpl; rewrite map_map.
    apply in_llp_bang_l.
    rewrite map_app.
    apply in_llp_perm with (£ p ⊸ £ q ⊸ £ r :: (map (fun c => ❗ [i c]) Si ++ map £ Ga) 
                                            ++ (map (fun c => ❗ [i c]) Si ++ map £ De)).
    * apply Permutation_cons; auto.
      unfold ll_lbang; rewrite map_map.
      rewrite app_ass; apply Permutation_app; auto.
      do 2 rewrite <- app_ass; apply Permutation_app; auto.
      apply Permutation_app_comm.
    * apply in_llp_limp_l; auto.
      apply in_llp_perm with (£ q ⊸ £ r :: ((map (fun c => ❗ [i c]) Si ++ map £ De) ++ nil)).
      - rewrite <- app_nil_end; auto.
      - apply in_llp_limp_l; auto.
        apply in_llp_ax.
  + rewrite <- map_map; apply S_ill_weak_cntr with (1 := in_map _ _ _ H1); simpl.
    unfold ll_lbang; rewrite map_map.
    apply in_llp_bang_l.
    apply in_llp_perm with (£ p & £ q ⊸ £ r :: ((map (fun c => ❗ [i c]) Si ++ map £ Ga) ++ nil)).
    * rewrite <- app_nil_end; auto.
    * apply in_llp_limp_l.
      - apply in_llp_with_r; auto.
      - apply in_llp_ax.
Qed.

Section TPS.

  Variables (n : nat) (s : ll_vars -> vec nat n -> Prop) (rx : pos n -> ll_vars).

  Fact ll_tps_vec_map_list_mono : 
       (forall (p : pos n), s (rx p) (vec_one p)) 
     -> forall v, ll_tps_list s (map £ (vec_map_list v rx)) v.
  Proof.
    intros H v; rewrite map_vec_map_list.
    induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n).
  
    rewrite vec_map_list_zero; simpl; tauto.
  
    rewrite vec_map_list_one; simpl.
    exists (vec_one p), vec_zero; rew vec; repeat split; auto.

    apply ll_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
    apply ll_tps_app.
    exists v, w; repeat split; auto.
  Qed.

  Fact ll_tps_vec_map_list : 
       (forall (p : pos n) (v : vec nat n), s (rx p) v <-> v = vec_one p) 
     -> forall v w, ll_tps_list s (map £ (vec_map_list v rx)) w <-> v = w.
  Proof.
    intros H v; rewrite map_vec_map_list.
    induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n); intros z.
  
    rewrite vec_map_list_zero; simpl; tauto.
  
    rewrite vec_map_list_one; simpl.
    split.
    intros (a & b & H1 & H2 & H3).
    apply H in H2; subst; rew vec.
    intros [].
    exists (vec_one p), vec_zero; rew vec; repeat split; auto.
    apply H; auto.
  
    split.
    intros Hz.
    apply ll_tps_perm with (1 := vec_map_list_plus _ _ _) in Hz.
    apply ll_tps_app in Hz.
    destruct Hz as (a & b & H1 & H2 & H3).
    apply Hv in H2.
    apply Hw in H3.
    subst; auto.
  
    intros [].
    apply ll_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
    apply ll_tps_app.
    exists v, w; repeat split; auto.
    apply Hv; auto.
    apply Hw; auto.
  Qed.

End TPS.

Section g_eill_complete_bound.
 
  Variable (Si : list eill_cmd) (Ga : list ll_vars) (n : nat).

  Notation vars := (flat_map eill_cmd_vars Si ++ Ga).

  (* This is a surjection from [0,n-1] into the vars of Si,Ga *)

  Hypothesis (w : vec ll_vars n)
             (w_surj : forall u, In u vars -> exists p, u = vec_pos w p).

  Let rx p := vec_pos w p.

  Let Hrx l : incl l (flat_map eill_cmd_vars Si ++ Ga) -> exists v, l ~p vec_map_list v rx.
  Proof.
    induction l as [ | x l IHl ]; intros H.
    + exists vec_zero; rewrite vec_map_list_zero; auto.
    + destruct IHl as (v & Hv).
      { intros ? ?; apply H; right; auto. }
      assert (In x vars) as Hx.
      {  apply H; left; auto. }
      destruct w_surj with (u := x)
        as (p & ?); subst; auto. 
      exists (vec_plus (vec_one p) v).
      apply Permutation_sym.
      apply Permutation_trans with (1 := vec_map_list_plus _ _ _).
      rewrite vec_map_list_one.
      apply perm_skip, Permutation_sym; auto.
  Qed.

  Let s x v := Si; vec_map_list v rx ⊦ x.

  Notation "⟦ A ⟧" := (ll_tps s A) (at level 65).
  Notation "'[<' Γ '|-' A '>]'" := (ll_sequent_tps s Γ A) (at level 65).

  Theorem G_eill_complete_bound x : [< map (fun c => ❗[i c]) Si ++ map £ Ga |- £ x >] vec_zero ->
                              Si; Ga ⊦ x.
  Proof.
    intros H.
    do 2 red in H.
    destruct (@Hrx Ga) as (v & Hv).
    { intros ? ?; apply in_or_app; right; auto. }
    apply in_eill_perm with (1 := Permutation_sym Hv).
    fold (s x v).
    rewrite <- (vec_zero_plus v), vec_plus_comm.
    apply H.
    rewrite ll_tps_app.
    exists vec_zero, v.
    repeat split; auto; try (rew vec; fail). 
    all: cycle 1.
    { apply ll_tps_perm with (map £ (vec_map_list v (fun p => rx p))).
      apply Permutation_map, Permutation_sym; auto.
      apply ll_tps_vec_map_list_mono; auto.
      intros p.
      red.
      rewrite vec_map_list_one.
      apply in_eill_ax. }

    rewrite <- map_map.
    apply ll_tps_list_bang_zero.
    intros A HA.
    apply in_map_iff in HA.
    destruct HA as (c & H1 & H2); subst.
    destruct c as [ (* p q | *) a p q | a p q | p q r ]; simpl.

    (* (_ -o _) -o _ *) 

    + intros y Hy; rew vec; unfold s.
      apply in_eill_inc with a p; auto.
      destruct (@Hrx (a::nil)) as (z & Hz).
      intros ? [ [] | [] ]; apply in_or_app; left.
      * apply in_flat_map; exists (LL_INC a p q); simpl; auto.
      * apply in_eill_perm with (vec_map_list (vec_plus z y) rx).
        - apply Permutation_trans with (1 := vec_map_list_plus _ _ _).
          change (a::vec_map_list y rx) with ((a::nil)++vec_map_list y rx).
          apply Permutation_app; auto.
          apply Permutation_sym; auto.
        - apply Hy; red.
          apply in_eill_perm with (1 := Hz), in_eill_ax.

    (* _ -o (_ -o _) *)

    + intros u Hu y Hy.
      rew vec.
      rewrite vec_plus_comm.
      apply in_eill_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
      apply in_eill_dec with a p; auto.

    (* (_ & _) -o _ *)
    
    + intros u (H3 & H4).
      rew vec.
      apply in_eill_fork with p q; auto.
  Qed.

End g_eill_complete_bound.

Section g_eill_complete.
 
  Variable (Si : list eill_cmd) (Ga : list ll_vars).

  Notation vars := (flat_map eill_cmd_vars Si ++ Ga).

  Let vv := nat_sort vars.

  Let Hvv1 : list_injective vv.
  Proof. apply nat_sorted_injective, nat_sort_sorted. Qed.

  Let Hvv2 : incl vv (flat_map eill_cmd_vars Si ++ Ga) 
          /\ incl (flat_map eill_cmd_vars Si ++ Ga) vv.
  Proof. apply nat_sort_eq. Qed.

  Let n := length vv.
  Let w : vec ll_vars n := proj1_sig (list_vec vv).
  Let Hw : vec_list w = vv.
  Proof. apply (proj2_sig (list_vec vv)). Qed.

  Let w_surj : forall u, In u vars -> exists p, u = vec_pos w p.
  Proof.
    intros u Hu.
    apply Hvv2 in Hu; rewrite <- Hw in Hu.
    revert Hu; apply vec_list_inv.
  Qed.

  Variables (x : ll_vars)
            (Hvalid : forall n s, @ll_sequent_tps n s (map (fun c : eill_cmd => ❗ [ic]) Si ++ map £ Ga) (£ x) vec_zero).

  Theorem G_eill_complete : Si; Ga ⊦ x.
  Proof.
    apply G_eill_complete_bound with (1 := w_surj), Hvalid.
  Qed.

End g_eill_complete.

(* eill is a fragment of ILL and G-eill is sound and complete for it *)

Theorem G_eill_correct Si Ga p : 
           Si; Ga ⊦ p <-> map (fun c => ![i c]) Si ++ map £ Ga ⊢ £ p.
Proof.
  split.
  - apply G_eill_sound.
  - intros H. 
    apply G_eill_complete.
    intros n s; revert H; apply ll_tps_sound.
Qed.
