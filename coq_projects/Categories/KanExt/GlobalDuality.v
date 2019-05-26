From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func_Prop.
From Categories Require Import Functor.Functor_Extender.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
From Categories Require Import KanExt.Global.

(** In this module we establish the dualit of kan extensions.
That is, the left kan extension along p is just the right kan extension along
pᵒᵖ and vice versa.
 *)
Section GlobalDuality.
  Context {C C' : Category} (p : (C –≻ C')%functor) (D : Category).

  (** We establish this duality though hom functor definition of adjunction. *)

  Local Obligation Tactic := idtac.

  Section Left_to_Right.
    Context (lke : Left_KanExt p D).

    (** The natural Isomorphism underlying the right kan extension which is to
        be shown.
        Hom_{Func_Cat Cᵒᵖ Dᵒᵖ}(– ∘ p, –) ≃ Hom_{Func_Cat C'ᵒᵖ Dᵒᵖ}(–, lkeᵒᵖ)
    *)
    Local Definition KanExt_Left_to_Right_NIso :=
      (
        (
          (
            ((Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D))
               ∘_h (NatTrans_id_Iso
                      (Prod_Functor
                         (Functor_id ((Func_Cat C' D) ^op) ^op) (lke^op)))
            )
              ∘ (Hom_Adjunct_Duality (Adj_to_Hom_Adj (left_kan_ext_adj lke)))
          )
            ∘ (((Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D))⁻¹)
                 ∘_h (NatTrans_id_Iso
                        (Prod_Functor
                           (Left_Functor_Extender p D)
                           (Functor_id (Func_Cat C D) ^op))))
        )
          ∘_h (NatTrans_id_Iso
                 (Prod_Functor
                    ((inverse_morphism (Func_Cat_Op_Iso C' D))^op)
                    (inverse_morphism (Func_Cat_Op_Iso C D))
                 )
              )
      )%natiso
    .

    (** If we give the trans formations (e.g., function given in the first
        obligation) explicitly "Program" generates obligations for
        equalities that are definitional! *)

    Program Definition KanExt_Left_to_Right :
      Right_KanExt  (p^op) (D^op) :=
      {|
        right_kan_ext :=
          ((Op_Func_Cat_to_Func_Cat_Op C' D) ∘
          (lke^op ∘ (Func_Cat_Op_to_Op_Func_Cat C D)))%functor;
        right_kan_ext_adj :=
          Hom_Adj_to_Adj
            {|
              iso_morphism :=
                {|
                  Trans := _
                |};
              inverse_morphism :=
                {|
                  Trans := _
                |}
            |}
      |}.

    Next Obligation.
    Proof.
      exact (fun c => Trans (iso_morphism KanExt_Left_to_Right_NIso) c).
    Defined.

    Next Obligation.
    Proof.
      intros c c' h; simpl.
      set (w := Trans_com (iso_morphism KanExt_Left_to_Right_NIso) h).
      etransitivity; [etransitivity;[| apply w]|];
      clear w; trivial; cbn.
      rewrite NatTrans_hor_comp_Op.
      repeat rewrite <- NatTrans_id_Op.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry; simpl.
      apply KanExt_Left_to_Right_obligation_2.
    Qed.

    Next Obligation.
    Proof.
      exact (fun c => Trans (inverse_morphism KanExt_Left_to_Right_NIso) c).
    Defined.

    Next Obligation.
    Proof.
      intros c c' h; simpl.
      set (w := Trans_com (inverse_morphism KanExt_Left_to_Right_NIso) h).
      etransitivity; [etransitivity;[| apply w]|];
      clear w; trivial; cbn.
      rewrite NatTrans_hor_comp_Op.
      repeat rewrite <- NatTrans_id_Op.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry; simpl.
      apply KanExt_Left_to_Right_obligation_5.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; simpl.
      match goal with
        [|- _ = ?A] =>
        let w := constr:((
                   ((KanExt_Left_to_Right_NIso ⁻¹)
                      ∘ KanExt_Left_to_Right_NIso)%morphism)%nattrans)
        in
        change (
            Trans w = A
          )
      end.
      rewrite (left_inverse KanExt_Left_to_Right_NIso); trivial.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; simpl.
      match goal with
        [|- _ = ?A] =>
        let w := constr:((
                   (KanExt_Left_to_Right_NIso
                      ∘ KanExt_Left_to_Right_NIso⁻¹)%morphism)%nattrans)
        in
        change (
            Trans w = A
          )
      end.
      rewrite (right_inverse KanExt_Left_to_Right_NIso); trivial.
    Qed.

  End Left_to_Right.


  Section Right_to_Left.
    Context (rke : Right_KanExt p D).

    (** The natural Isomorphism underlying the right kan extension which is
        to be shown.

        Hom_{Func_Cat C'ᵒᵖ Dᵒᵖ}(rke, –) ≃ Hom_{Func_Cat Cᵒᵖ Dᵒᵖ}(–, – ∘ p)
     *)
    Local Definition KanExt_Right_to_Left_NIso :=
      (
        (
          (
            (
              (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D))
                ∘_h (
                  NatTrans_id_Iso
                    (Prod_Functor
                       (Functor_id ((Func_Cat C D) ^op) ^op)
                       ((Left_Functor_Extender p D)^op)
                ))
            )
              ∘ (Hom_Adjunct_Duality (Adj_to_Hom_Adj (right_kan_ext_adj rke)))
          )
            ∘ (
              ((Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D))⁻¹)
                ∘_h (NatTrans_id_Iso
                       (Prod_Functor rke (Functor_id (Func_Cat C' D) ^op))))
        )
          ∘_h
          (NatTrans_id_Iso
             (Prod_Functor
                ((inverse_morphism (Func_Cat_Op_Iso C D))^op)
                (inverse_morphism (Func_Cat_Op_Iso C' D))
             )
          )
      )%natiso
    .

    Program Definition KanExt_Right_to_Left :
      Left_KanExt  (p^op) (D^op) :=
      {|
        left_kan_ext :=
          (
            (Op_Func_Cat_to_Func_Cat_Op C' D)
              ∘ (rke^op ∘ (Func_Cat_Op_to_Op_Func_Cat C D))
          )%functor;
        left_kan_ext_adj :=
          Hom_Adj_to_Adj
            {|
              iso_morphism :=
                {|
                  Trans := _
                |};
              inverse_morphism :=
                {|
                  Trans := _
                |}
            |}
      |}.

    Next Obligation.
    Proof.
      exact (fun c => Trans (iso_morphism KanExt_Right_to_Left_NIso) c).
    Defined.

    Next Obligation.
    Proof.
      intros c c' h; simpl.
      set (w := Trans_com (iso_morphism KanExt_Right_to_Left_NIso) h).
      etransitivity; [etransitivity;[| apply w]|];
      clear w; trivial; cbn.
      repeat rewrite NatTrans_hor_comp_Op.
      repeat rewrite NatTrans_id_Op.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry; simpl.
      apply KanExt_Right_to_Left_obligation_2.
    Qed.

    Next Obligation.
    Proof.
      exact (fun c => Trans (inverse_morphism KanExt_Right_to_Left_NIso) c).
    Defined.

    Next Obligation.
    Proof.
      intros c c' h; simpl.
      set (w := Trans_com (inverse_morphism KanExt_Right_to_Left_NIso) h).
      etransitivity; [etransitivity;[| apply w]|];
      clear w; trivial; cbn.
      repeat rewrite NatTrans_hor_comp_Op.
      repeat rewrite NatTrans_id_Op.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry; simpl.
      apply KanExt_Right_to_Left_obligation_5.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; simpl.
      match goal with
        [|- _ = ?A] =>
        let w := constr:((
                   ((KanExt_Right_to_Left_NIso ⁻¹)
                      ∘ KanExt_Right_to_Left_NIso)%morphism)%nattrans)
        in
        change (
            Trans w = A
          )
      end.
      rewrite (left_inverse KanExt_Right_to_Left_NIso); trivial.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; simpl.
      match goal with
        [|- _ = ?A] =>
        let w := constr:((
                   (KanExt_Right_to_Left_NIso
                      ∘ KanExt_Right_to_Left_NIso⁻¹)%morphism)%nattrans)
        in
        change (
            Trans w = A
          )
      end.
      rewrite (right_inverse KanExt_Right_to_Left_NIso); trivial.
    Qed.

  End Right_to_Left.

End GlobalDuality.
