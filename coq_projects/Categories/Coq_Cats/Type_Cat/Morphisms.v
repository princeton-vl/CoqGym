From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.


(** In this section we show that any monic morphism in Type_Cat (
injective function in Coq) can be split in to two morphisms where
one is an iso morphism and the other monic.

The isomorphism is from the domain of the function to its image.
The epic function is from the image of the function to its codomain.
*)
Section Monic_Iso_Monic_Factorization.
  Context
    {A B : Type}
    {f : A → B}
    (fm : @is_Monic Type_Cat _ _ f)
  .

  Definition Monic_Image_of : Type := {x : B & {a : A | f a = x}}.

  Definition Monic_From_Image_forward : Monic_Image_of → B := fun x => projT1 x.

  Program Definition Monic_Iso_Monic_Factor_Monic :
    @Monic Type_Cat Monic_Image_of B :=
    {|
      mono_morphism := Monic_From_Image_forward;
      mono_morphism_monomorphic := fun T g h => _
    |}
  .

  Next Obligation.
  Proof.
    extensionality x.
    assert (H' := equal_f H x); cbn in H'.
    destruct (g x) as [gx Hgx]; destruct (h x) as [hx Hhx].
    cbn in *.
    destruct H'.
    cutrewrite (Hgx = Hhx); trivial.
    apply sig_proof_irrelevance.
    destruct Hgx as [y Hy]; destruct Hhx as [z Hz].
    cbn in *.
    refine (equal_f (fm (unit : Type) (fun _ => y) (fun _ => z) _) tt).
    FunExt; cbn; auto.
  Qed.

  Definition Monic_To_Image : A → Monic_Image_of :=
    fun a => existT _ (f a) (exist _ a eq_refl).

  Definition Monic_From_Image_back : Monic_Image_of → A :=
    fun x => proj1_sig (projT2 x).

  Theorem Monic_From_Image_back_is_Monic :
    @is_Monic Type_Cat _ _ Monic_To_Image.
  Proof.
    intros T g h H.
    extensionality x.
    assert (H' :=
              f_equal
                (fun w : Monic_Image_of => (fun u : unit => projT1 w))
                (equal_f H x)
           ); clear H.
    apply (equal_f (fm (unit : Type) (fun _ => (g x)) (fun _ => (h x)) H') tt).
  Qed.

  Theorem Monic_To_Image_form_split_epic :
    (
      fun (x : Monic_Image_of) =>
        Monic_To_Image (Monic_From_Image_back x)
    ) = (fun x => x).
  Proof.
    extensionality x.
    destruct x as [x [y Hxy]].
    unfold Monic_To_Image.
    cbn in *.
    destruct Hxy; trivial.
  Qed.

  Program Definition Monic_Iso_Monic_Factor_Iso :
    (A ≃≃ Monic_Image_of ::> Type_Cat)%isomorphism
    :=
      Monic_is_split_Epic_Iso
        _
        _
        (is_Monic_Monic Monic_From_Image_back_is_Monic)
        (
          @Build_is_split_Monic
            (Type_Cat ^op)
            _
            _
            Monic_To_Image
            _
            Monic_To_Image_form_split_epic
        )
  .

  Theorem Monic_Iso_Monic_Factorization :
    f = fun x =>  Monic_From_Image_forward (Monic_To_Image x).
  Proof.
    auto.
  Qed.

End Monic_Iso_Monic_Factorization.

(** In the following we show a similar result for any funtion. That is, we show
    that any function can be split into a split epic function followed by a
    monic function. Here the split epic function is not an isomorphism. 

The monic is from the domain of the function to its image.
The epic function is from the image of the function to its codomain.
*)
Require Import Coq.Logic.ChoiceFacts.

Local Axiom ConstructiveIndefiniteDescription_Type :
  forall T : Type, ConstructiveIndefiniteDescription_on T.

(** In this section we show that any morphism in Type_Cat (function
in Coq) can be split in to two morphisms where one is monic and the
other split epic. *)
Section split_Epic_Monic_Factorization.
  Context {A B : Type} (f : A → B).

  Definition Image_of : Type := {x : B | ∃ a, f a = x}.

  Definition From_Image_forward : Image_of → B := fun x => proj1_sig x.

  Program Definition Epic_Monic_Factor_Monic : @Monic Type_Cat Image_of B :=
    {|
      mono_morphism := From_Image_forward;
      mono_morphism_monomorphic := fun T g h => _
    |}
  .

  Next Obligation.
  Proof.
    extensionality x.
    assert (H' := equal_f H x); cbn in H'.
    apply sig_proof_irrelevance.
    destruct (g x); destruct (h x).
    trivial.
  Qed.

  Definition To_Image : A → Image_of :=
    fun a => exist _ (f a) (ex_intro _ a eq_refl).

  Definition From_Image_back : Image_of → A :=
    fun x => proj1_sig (ConstructiveIndefiniteDescription_Type _ _ (proj2_sig x)).

  Theorem From_Image_back_form_split_epic :
    ∀ (x : Image_of), To_Image (From_Image_back x) = x.
  Proof.
    intros x.
    apply sig_proof_irrelevance.
    unfold From_Image_back; cbn.
    destruct
      (ConstructiveIndefiniteDescription_Type
         A
         (fun a : A => f a = proj1_sig x)
         (proj2_sig x)
      ) as [z Hz].
    trivial.
  Qed.

  Program Definition Epic_Monic_Factor_split_Epic :
    @is_split_Epic Type_Cat _ _ To_Image :=
    {|
      is_split_monic_left_inverse := From_Image_back
    |}.

  Next Obligation.
  Proof.
    extensionality x.
    apply From_Image_back_form_split_epic.
  Qed.

  Theorem split_Epic_Monic_Factorization :
    f = fun x =>  From_Image_forward (To_Image x).
  Proof.
    auto.
  Qed.

End split_Epic_Monic_Factorization.
