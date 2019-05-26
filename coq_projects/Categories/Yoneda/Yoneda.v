From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Cat.Facts.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Functor.Representable.Hom_Func.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.

Local Open Scope nattrans_scope.

Section Y_emb.
  Context (C : Category).

  (** The dual of the Yoneda embedding for category C – the curry of hom
      functor of C. *)
  Definition CoYoneda : (C^op –≻ (Func_Cat C Type_Cat))%functor :=
    Exp_Cat_morph_ex (Hom_Func C).

  (** The Yoneda embedding for category C – the curry of hom functor of Cᵒᵖ. *)
  Definition Yoneda : (C –≻ (Func_Cat (C^op) Type_Cat))%functor :=
    Exp_Cat_morph_ex (Hom_Func (C^op)).

End Y_emb.

Section Y_Left_Right.
  Context (C : Category).

  (** The left hand side of the Yoneda lemma's isomorphism *)
  Definition Y_left :
    ((C^op × (Func_Cat (C^op) Type_Cat)) –≻ Type_Cat)%functor
    :=
      ((Hom_Func _)
         ∘ (Prod_Functor
              ((Yoneda C)^op) (Functor_id (Func_Cat (C^op) Type_Cat))))%functor.
  
  (** The right hand side of the Yoneda lemma's isomorphism *)
  Definition Y_right
    : ((C^op × (Func_Cat (C^op) Type_Cat)) –≻ Type_Cat)%functor :=
    ((Exp_Cat_Eval (C^op) Type_Cat) ∘ (Twist_Func _ _))%functor.

End Y_Left_Right.

Local Obligation Tactic := idtac.

(** The left to right natural transformation of Yoneda lemma. *)
Program Definition Y_left_to_right (C : Category) : (Y_left C) –≻ (Y_right C) :=
{|
  Trans := fun c_F => fun N => ((Trans N (fst c_F))) (id (fst c_F))
|}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C [c F] [c' F'] [h1 h2].
  extensionality N; cbn.
  cbn in *.
  match goal with
    [|- _ = ?W] =>
    match W with
      (?F _a ?X (?Y ?Z))%morphism =>
      change W with (((F _a X) ∘ Y) Z)%morphism
    end
  end.
  rewrite <- Trans_com; cbn.
  match goal with
    [|- _ = Trans h2 c' ?W] =>
    match W with
      (?F _a ?X (?Y ?Z))%morphism =>
      change W with (((F _a X) ∘ Y) Z)%morphism
    end
  end.
  rewrite <- Trans_com; cbn.
  auto.
Qed.

Next Obligation.
Proof.
  symmetry; simpl.
  apply Y_left_to_right_obligation_1.
Qed.

(** The natural transformation needed to make the right to left natural
    transformation of Yoneda lemma. *)
Program Definition Y_right_to_left_NT (C : Category) (c : Obj)
        (F : (C^op –≻ Type_Cat)%functor) (h : (F _o c)%object)
  :
    ((Yoneda _) _o c)%object –≻ F :=
{|
  Trans := fun c' => fun g => (F _a g)%morphism h
|}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C c F h c1 c2 h'.
  extensionality g; cbn.
  simpl_ids.
  match goal with
    [|- (?F _a (?X ∘ ?Y) ?Z)%morphism = _] =>
      transitivity (((F _a Y) ∘ (F _a X)) Z)%morphism; trivial
  end.
  auto.
Qed.

Next Obligation.
Proof.
  symmetry; simpl.
  apply Y_right_to_left_NT_obligation_1.
Qed.

(** The right to left natural transformation of Yoneda lemma. *)
Program Definition Y_right_to_left (C : Category) : (Y_right C) –≻ (Y_left C) :=
{|
  Trans := fun c_F => fun h => Y_right_to_left_NT C (fst c_F) (snd c_F) h
|}.

Next Obligation. (* Trans_com *)
Proof.
  intros C [c f] [c' f'] [h N].
  cbn in *.
  extensionality g; cbn.
  apply NatTrans_eq_simplify.
  extensionality d; extensionality g'; cbn.
  simpl_ids.
  match goal with
    [|- ?W = _] =>
    match W with
      (?F _a ?X (?F _a ?Y ?Z))%morphism =>
      change W with (((F _a X) ∘ (F _a Y)) Z)%morphism
    end
  end.
  rewrite <- F_compose; cbn.
  match goal with
    [|- ?W = _] =>
    match W with
      ?X (?Y ?Z) =>
      change W with ((X ∘ Y) Z)%morphism
    end
  end.
  rewrite <- Trans_com; cbn; trivial.
Qed.

Next Obligation.
Proof.
  symmetry; simpl.
  apply Y_right_to_left_obligation_1.
Qed.

(** The Yoneda Lemma*)
Program Definition Yoneda_Lemma (C : Category) :
  ((Y_left C) ≃ (Y_right C))%natiso :=
  NatIso _ _ (Y_left_to_right C) (Y_right_to_left C) _ _.

Next Obligation.
Proof.
  intros C [c F]; FunExt; cbn in *.
  rewrite (F_id F).
  trivial.
Qed.

Next Obligation.
  simpl; intros C [c F]; FunExt.
  apply NatTrans_eq_simplify.
  FunExt.
  cbn in *.
  match goal with
    [|- ?W = _] =>
    match W with
      ?X (?Y ?Z) =>
      change W with ((X ∘ Y) Z)%morphism
    end
  end.
  rewrite <- Trans_com; cbn.
  auto.
Qed.

(** Yoneda embedding is faithful. *)
Lemma Yoneda_Faithful (C : Category) : Faithful_Func (Yoneda C).
Proof.
  intros c c' f f' H.
  cbn in *.
  match type of H with
      ?X = ?Y =>
      assert(H' : Trans X c id= Trans Y c id)
  end.
  + rewrite H; trivial.
  + cbn in H'.
    simpl_ids in H'.
    trivial.
Qed.

(** Yoneda embedding is full. *)
Lemma Yoneda_Full (C : Category) : Full_Func (Yoneda C).
Proof.
  intros c c' N.
  exists (Trans (Y_left_to_right C) (c, (((Yoneda C) _o)%object c')) N).
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h.
  transitivity ((((Yoneda C) _o c')%object _a h ∘ (Trans N c)) id)%morphism.
  + cbn; auto.
  + rewrite <- Trans_com.
    cbn; auto.
Qed.

(** Yoneda embedding is indeed an embedding. *)
Definition Yoneda_Emb (C : Category) : Embedding C (Func_Cat (C^op) Type_Cat) :=
{|
  Emb_Func := Yoneda C;
  Emb_Faithful := Yoneda_Faithful C;
  Emb_Full := Yoneda_Full C
|}.

(** Yoneda is conservative of isomorphisms. *)
Theorem Yoneda_Iso (C : Category) : forall (c c' : Obj),
    ((Yoneda C) _o c ≃ (Yoneda C) _o c')%isomorphism → (c ≃ c')%isomorphism.
Proof.
  intros.
  apply (Emb_Conservative _ _ (Yoneda_Emb C) _); trivial.
Qed.

Ltac Yoneda := apply Yoneda_Iso.

(** The dual of Yoneda is conservative of isomorphisms. *)
Theorem CoYoneda_Iso (C : Category) : forall (c c' : Obj),
    ((CoYoneda C) _o c ≃ (CoYoneda C) _o c')%isomorphism → (c ≃ c')%isomorphism.
Proof.
  intros; Yoneda; trivial.
Qed.

Ltac CoYoneda := apply CoYoneda_Iso.
