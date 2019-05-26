From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops Functor.Functor_Properties.
From Categories Require Import Cat.Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.Operations.

Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

Local Open Scope nattrans_scope.

Notation "a ≃ b" := (a ≃≃ b ::> Func_Cat _ _)%isomorphism : natiso_scope.

Section NatIso.
  Context {C C' : Category} (F G : (C –≻ C')%functor)
          (n : F –≻ G) (n' : G –≻ F).

  (** Two natural transformation for which individual arrows of arrow
      families form isomorphism form natural isomorphisms. *)
  Program Definition NatIso
          (H : (∀ (c : Obj), (Trans n c) ∘ (Trans n' c)
                             = (id (G _o c)))%morphism)
          (H' : (∀ (c : Obj), (Trans n' c) ∘ (Trans n c)
                              = (id (F _o c)))%morphism)
    : (F ≃ G)%natiso
    := (Build_Isomorphism (Func_Cat _ _) _ _ n n' _ _).

End NatIso.

Section NatTrans_id_Iso.
  Context {C D : Category} (F : (C –≻ D)%functor).

  (** The identity natural transformation is a natural isomorphism. *)
  Definition NatTrans_id_Iso :
    (F ≃ F)%natiso := @Isomorphism_id (Func_Cat _ _) F.

End NatTrans_id_Iso.

(** Horizontal composition of natural isomorphisms is a natural isomorphism. *)
Section NatIso_hor_comp.
  Context {C D E : Category} {F F' : (C –≻ D)%functor}
          {G G' : (D –≻ E)%functor} (N : (F ≃ F')%natiso)
          (N' : (G ≃ G')%natiso).

  Local Obligation Tactic := idtac.

  Program Definition NatIso_hor_comp
    : ((G ∘ F)%functor ≃ (G' ∘ F')%functor)%natiso :=
    {|
      iso_morphism := ((iso_morphism N') ∘_h (iso_morphism N))%nattrans;
      inverse_morphism :=
        ((inverse_morphism N') ∘_h (inverse_morphism N))%nattrans
    |}.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    cbn_rewrite (left_inverse N).
    cbn_rewrite (left_inverse N').
    auto.
  Qed.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    cbn_rewrite (right_inverse N).
    cbn_rewrite (right_inverse N').
    auto.
  Qed.

End NatIso_hor_comp.

Notation "f ∘_h g" := (NatIso_hor_comp g f) : natiso_scope.

(** If two functors are naturally isomorphic then their opposites are too. *)
Section Opposite_NatIso.
  Context {C D : Category} {F G : (C –≻ D)%functor} (N : (F ≃ G)%natiso).

  Program Definition Opposite_NatIso : (F^op%functor ≃ G^op%functor)%natiso :=
    {|
      iso_morphism := (inverse_morphism N)^op%nattrans;
      inverse_morphism := (iso_morphism N)^op%nattrans
    |}.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change ((N⁻¹)%morphism ∘ (iso_morphism N))%nattrans with (N⁻¹ ∘ N)%morphism.
    rewrite left_inverse.
    apply NatTrans_id_Op.
  Qed.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change ((iso_morphism N) ∘ (N⁻¹)%morphism)%nattrans with (N ∘ N⁻¹)%morphism.
    rewrite right_inverse.
    apply NatTrans_id_Op.
  Qed.

End Opposite_NatIso.

Notation "f ^op" := (Opposite_NatIso f) : natiso_scope.

Section Embedding_mono.
  Context {C C' : Category} (F : Embedding C C') {B : Category}.

  Local Obligation Tactic := idtac.

  (** For an embeding F and functors G and G', F ∘ G ≃ F ∘ G' implies
      there is a natural transformation from G to G'. We will use
      this to show that G and G' are naturally isomorphic below. *)
  Section Embedding_mono_NT.
    Context {G G' : (B –≻ C)%functor}
            (H : ((F ∘ G)%functor ≃ (F ∘ G')%functor)%natiso).
    
    Program Definition Embedding_mono_NT :  G –≻ G' :=
      {|
        Trans := fun c => proj1_sig (Emb_Full _ (Trans (iso_morphism H) c))
      |}.

    Next Obligation.
      intros c c' h.
      apply (Emb_Faithful F).
      repeat rewrite F_compose.
      cbn_rewrite (proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))). 
      cbn_rewrite (proj2_sig (Emb_Full _ (Trans (iso_morphism H) c'))).
      apply (@Trans_com _ _ _ _ (iso_morphism H) _ _ h).
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Embedding_mono_NT_obligation_1.
    Qed.

  End Embedding_mono_NT.

  Context {G G' : (B –≻ C)%functor}
          (H : ((F ∘ G)%functor ≃ (F ∘ G')%functor)%natiso).
  
  (** For an embeding F and functors G and G', F ∘ G ≃ F ∘ G' implies G ≃ G'. *)
  Program Definition Embedding_mono : (G ≃ G')%natiso  :=
    {|
      iso_morphism := Embedding_mono_NT H;
      inverse_morphism := Embedding_mono_NT (H⁻¹)
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    apply (Emb_Faithful F).
    repeat rewrite F_compose.
    cbn_rewrite (proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))).
    cbn_rewrite (proj2_sig (Emb_Full _ (Trans (inverse_morphism H) c))).
    rewrite F_id.
    change (Trans (inverse_morphism H) c ∘ Trans (iso_morphism H) c)%morphism
    with (Trans ((inverse_morphism H) ∘ (iso_morphism H))%nattrans c).
    cbn_rewrite (left_inverse H).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    apply (Emb_Faithful F).
    repeat rewrite F_compose.
    cbn_rewrite (proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))).
    cbn_rewrite (proj2_sig (Emb_Full _ (Trans (inverse_morphism H) c))).
    rewrite F_id.
    change (Trans (iso_morphism H) c ∘ Trans (inverse_morphism H) c)%morphism
    with (Trans ((iso_morphism H) ∘ (inverse_morphism H))%nattrans c).
    cbn_rewrite (right_inverse H).
    trivial.
  Qed.    

End Embedding_mono.

Section NatIso_Functor_assoc.
  Context {C1 C2 C3 C4 : Category}
          (F : (C1 –≻ C2)%functor)
          (G : (C2 –≻ C3)%functor)
          (H : (C3 –≻ C4)%functor).
  
  (** Natrual isomorphism form of functor composition associativity. *)
  Program Definition NatIso_Functor_assoc
    : (((H ∘ G) ∘ F)%functor ≃ (H ∘ (G ∘ F))%functor)%natiso :=
    {|
      iso_morphism := NatTrans_Functor_assoc F G H;
      inverse_morphism := NatTrans_Functor_assoc_sym F G H
    |}.

End NatIso_Functor_assoc.

Section NatIso_Image.
  Context {C C' : Category} {F G : (C –≻ C')%functor} (N : (F ≃ G)%natiso).
  
  (** Natrual isomorphism form of functor composition associativity. *)
  Program Definition NatIso_Image (c : C) : ((F _o c) ≃ (G _o c))%isomorphism :=
    {|
      iso_morphism := Trans (iso_morphism N) c;
      inverse_morphism := Trans (inverse_morphism N) c
    |}.

  Next Obligation.
    change (Trans (inverse_morphism N) c ∘ Trans (iso_morphism N) c)%morphism
    with (Trans ((inverse_morphism N) ∘ (iso_morphism N)) c)%morphism.
    cbn_rewrite (left_inverse N).
    trivial.
  Qed.
  
  Next Obligation.
    change (Trans (iso_morphism N) c ∘ Trans (inverse_morphism N) c)%morphism
    with (Trans ((iso_morphism N) ∘ (inverse_morphism N)) c)%morphism.
    cbn_rewrite (right_inverse N).
    trivial.
  Qed.
  
End NatIso_Image.
