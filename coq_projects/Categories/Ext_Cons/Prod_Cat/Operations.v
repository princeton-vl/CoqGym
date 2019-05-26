From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Cat.Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.

Local Obligation Tactic := idtac.

Local Open Scope functor_scope.

Program Definition Prod_Functor
        {C1 C2 C1' C2' : Category} (F : C1 –≻ C2) (F' : C1' –≻ C2')
  : (C1 × C1') –≻ (C2 × C2') :=
{|
  FO := fun a => (F _o (fst a), F' _o (snd a))%object;
  FA := fun _ _ f => (F _a (fst f), F' _a (snd f))%morphism
|}.

Next Obligation.
  intros; cbn; repeat rewrite F_id; trivial.
Qed.

Next Obligation.
  intros; cbn; repeat rewrite F_compose; trivial.
Qed.

Definition Bi_Func_1 {Cx C1 C1' Cy : Category} (F : Cx –≻ C1)
           (F' : (C1 × C1') –≻ Cy)
  : (Cx × C1') –≻ Cy :=
  F' ∘ (Prod_Functor F (@Functor_id C1')).

Definition Bi_Func_2 {Cx C1 C1' Cy : Category} (F : Cx –≻ C1')
           (F' : (C1 × C1') –≻ Cy) : (C1 × Cx) –≻ Cy :=
  Functor_compose (Prod_Functor (@Functor_id C1) F) F'.

Local Hint Extern 2 => cbn.

Local Obligation Tactic := basic_simpl; do 2 auto.

Program Definition Fix_Bi_Func_1 {C1 C1' Cy : Category} (x : C1)
        (F : (C1 × C1') –≻ Cy)
  : C1' –≻ Cy :=
{|
  FO := fun a => (F _o (x, a))%object;
  FA := fun _ _ f => (F @_a (_, _) (_, _) (@id _ x, f))%morphism
|}.

Program Definition Fix_Bi_Func_2 {C1 C1' Cy : Category} (x : C1')
        (F : (C1 × C1') –≻ Cy)
  : C1 –≻ Cy :=
{|
  FO := fun a => (F _o (a, x))%object;
  FA := fun _ _ f => (F @_a (_, _) (_, _) (f, @id _ x))%morphism
|}.

Program Definition Diag_Func (C : Category) : C –≻ (C × C) :=
{|
  FO := fun a => (a, a);
  FA := fun _ _ f => (f, f);
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
|}.

Theorem Prod_Functor_Cat_Proj {C D D' : Category} (F : C –≻ (D × D')) :
  ((Prod_Functor ((Cat_Proj1 _ _) ∘ F) ((Cat_Proj2 _ _) ∘ F))
     ∘ (Diag_Func C))%functor = F.
Proof.
  Func_eq_simpl; trivial.
Qed.  

Program Definition Twist_Func (C C' : Category) : (C × C') –≻ (C' × C) :=
{|
  FO := fun a => (snd a, fst a);
  FA := fun _ _ f => (snd f, fst f);
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
|}.

Section Twist_Prod_Func_Twist.
  Context {C C' : Category} (F : C –≻ C') {D D' : Category} (G : D –≻ D').

  Theorem Twist_Prod_Func_Twist :
    (((Twist_Func _ _) ∘ (Prod_Functor F G)) ∘ (Twist_Func _ _))%functor =
    Prod_Functor G F.
  Proof.  
    Func_eq_simpl; trivial.
  Qed.

End Twist_Prod_Func_Twist.

Section Prod_Functor_compose.
  Context {C D E: Category} (F : C –≻ D) (G : D –≻ E)
          {C' D' E': Category} (F' : C' –≻ D') (G' : D' –≻ E').

  Theorem Prod_Functor_compose :
    ((Prod_Functor G G') ∘ (Prod_Functor F F') =
     Prod_Functor (G ∘ F) (G' ∘ F'))%functor.
  Proof.
    Func_eq_simpl; trivial.
  Qed.    
                                   
End Prod_Functor_compose.
