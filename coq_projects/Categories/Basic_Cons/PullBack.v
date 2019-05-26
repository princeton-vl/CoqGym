From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

Local Open Scope morphism_scope.

Section PullBack.
  Context {C : Category} {a b x : C} (f : a –≻ x) (g : b –≻ x).

  (**
Given two arrows f : a -> x and g : b -> x, their pullback is an object p
together with two arrows π₁ : p -> a and π₂ : p -> b such that the following
diagram commutes:

#
<pre>
        π₂   
   p ————————–> b
   |            |
π₁ |            | g
   |            |
   ↓            ↓
   a —————————> x
        f
</pre>
#

Provided that for any object q and arrows p1 : q -> a and p2 : q -> b that the
following diagram commutes:

#
<pre>
        p2   
   q ————————–> b
   |            |
p1 |            | g
   |            |
   ↓            ↓
   a —————————> x
        f
</pre>
#

there is a unique arrow h : q -> p that makes the following diagram commute:

#
<pre>
                p2
      q ———————————————————–
      |  \                   |
      |    \ ∃!h             |
      |      \               |
      |        ↘     π₂      ↓
  p1  |         p ————————–> b
      |         |            |
      |      π₁ |            | g
      |         |            |
      |         ↓            ↓
       ——————–> a —————————> x
                    f
</pre>
#

We usually use a half square in the corner of p to denote p is the pullback of
f and g. Like so:
#
<pre>
        π₂   
   p ————————–> b
   |__|         |
π₁ |            | g
   |            |
   ↓            ↓
   a —————————> x
        f
</pre>
#
*)
  Record PullBack : Type :=
    {
      pullback : C;

      pullback_morph_1 : pullback –≻ a;

      pullback_morph_2 : pullback –≻ b;

      pullback_morph_com : f ∘ pullback_morph_1 = g ∘ pullback_morph_2;

      pullback_morph_ex (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b) :
        f ∘ pm1 = g ∘ pm2 → p' –≻ pullback;

      pullback_morph_ex_com_1 (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
                              (pmc : f ∘ pm1 = g ∘ pm2)
      :
        pullback_morph_1 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm1;

      pullback_morph_ex_com_2 (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
                              (pmc : f ∘ pm1 = g ∘ pm2)
      :
        pullback_morph_2 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm2;

      pullback_morph_ex_unique
        (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
        (pmc : f ∘ pm1 = g ∘ pm2) (u u' : p' –≻ pullback) :
        pullback_morph_1 ∘ u = pm1 →
        pullback_morph_2 ∘ u = pm2 →
        pullback_morph_1 ∘ u' = pm1 →
        pullback_morph_2 ∘ u' = pm2 → u = u'
    }.

  Coercion pullback : PullBack >-> Obj.

  (** Pullbacks are unique up to isomorphism. *)
  Theorem PullBack_iso (p1 p2 : PullBack) : (p1 ≃ p2)%isomorphism.
  Proof.
    apply
      (
        Build_Isomorphism
          _
          _
          _
          (
            pullback_morph_ex
              p2
              _
              (pullback_morph_1 p1)
              (pullback_morph_2 p1)
              (pullback_morph_com p1)
          )
          (
            pullback_morph_ex
              p1
              _
              (pullback_morph_1 p2)
              (pullback_morph_2 p2)
              (pullback_morph_com p2)
          )
      ); eapply pullback_morph_ex_unique;
    match goal with
      | [|- _ ∘ id = _] => simpl_ids; trivial
      | _ => idtac
    end; try apply pullback_morph_com;
    rewrite <- assoc;
    repeat (rewrite pullback_morph_ex_com_1 || rewrite pullback_morph_ex_com_2);
    trivial.
  Qed.

End PullBack.

(** The predicate form of pullback: *)
Section is_PullBack.
  Context {C : Category} {a b x pb : C} (p1 : pb –≻ a)
          (p2 : pb –≻ b) (f : a –≻ x) (g : b –≻ x).

  Local Open Scope morphism_scope.
  
  Record is_PullBack : Type :=
    {
      is_pullback_morph_com : f ∘ p1 = g ∘ p2;

      is_pullback_morph_ex (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b) :
        f ∘ pm1 = g ∘ pm2 → p' –≻ pb;

      is_pullback_morph_ex_com_1 (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
                                 (pmc : f ∘ pm1 = g ∘ pm2)
      :
        p1 ∘ (is_pullback_morph_ex p' pm1 pm2 pmc) = pm1;

      is_pullback_morph_ex_com_2 (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
                                 (pmc : f ∘ pm1 = g ∘ pm2)
      :
        p2 ∘ (is_pullback_morph_ex p' pm1 pm2 pmc) = pm2;

      is_pullback_morph_ex_unique
        (p' : Obj) (pm1 : p' –≻ a) (pm2 : p' –≻ b)
        (pmc : f ∘ pm1 = g ∘ pm2) (u u' : p' –≻ pb) :
        p1 ∘ u = pm1 →
        p2 ∘ u = pm2 →
        p1 ∘ u' = pm1 →
        p2 ∘ u' = pm2 → u = u'
    }.

End is_PullBack.

Definition Has_PullBacks (C : Category) : Type :=
  ∀ (a b c : C) (f : a –≻ c) (g : b –≻ c), PullBack f g.

Existing Class Has_PullBacks.

Arguments PullBack _ {_ _ _} _ _, {_ _ _ _} _ _.
Arguments pullback {_ _ _ _ _ _} _.
Arguments pullback_morph_1 {_ _ _ _ _ _} _.
Arguments pullback_morph_2 {_ _ _ _ _ _} _.
Arguments pullback_morph_com {_ _ _ _ _ _} _.
Arguments pullback_morph_ex {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_com_1 {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_com_2 {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_unique {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.

Arguments is_PullBack _ { _ _ _ _} _ _ _ _, {_ _ _ _ _ } _ _ _ _.

Arguments is_pullback_morph_com {_ _ _ _ _ _ _ _ _} _.
Arguments is_pullback_morph_ex {_ _ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments is_pullback_morph_ex_com_1 {_ _ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments is_pullback_morph_ex_com_2 {_ _ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments is_pullback_morph_ex_unique {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.

Section is_PullBack_PullBack.
  Context {C : Category} {a b x pb : C} {p1 : pb –≻ a} {p2 : pb –≻ b} {f : a –≻ x}
          {g : b –≻ x} (iPB : is_PullBack p1 p2 f g).

  (** The predicate form of pullbacks implies the compact from of pullbacks.
       See above for details.*)
  Definition is_PullBack_PullBack : PullBack f g :=
    {|
      pullback := pb;
      pullback_morph_1 := p1;
      pullback_morph_2 := p2;
      pullback_morph_com := is_pullback_morph_com iPB;
      pullback_morph_ex := fun p' pm1 pm2 => is_pullback_morph_ex iPB p' pm1 pm2;
      pullback_morph_ex_com_1 :=
        fun p' pm1 pm2 pmc => is_pullback_morph_ex_com_1 iPB p' pm1 pm2 pmc;
      pullback_morph_ex_com_2 :=
        fun p' pm1 pm2 pmc => is_pullback_morph_ex_com_2 iPB p' pm1 pm2 pmc;
      pullback_morph_ex_unique :=
        fun p' pm1 pm2 pmc u u' => is_pullback_morph_ex_unique iPB p' pm1 pm2 pmc u u'
    |}.

End is_PullBack_PullBack.

Section PullBack_is_PullBack.
  Context {C : Category} {a b x : C} {f : a –≻ x}
          {g : b –≻ x} (PB : PullBack f g).

  (** Compact form of pullback implies the predicate form of pullback.
      See above for details. *)
  Definition PullBack_is_PullBack :
    is_PullBack (pullback_morph_1 PB) (pullback_morph_2 PB) f g :=
    {|
      is_pullback_morph_com := pullback_morph_com PB;
      is_pullback_morph_ex := fun p' pm1 pm2 => pullback_morph_ex PB p' pm1 pm2;
      is_pullback_morph_ex_com_1 :=
        fun p' pm1 pm2 pmc => pullback_morph_ex_com_1 PB p' pm1 pm2 pmc;
      is_pullback_morph_ex_com_2 :=
        fun p' pm1 pm2 pmc => pullback_morph_ex_com_2 PB p' pm1 pm2 pmc;
      is_pullback_morph_ex_unique :=
        fun p' pm1 pm2 pmc u u' => pullback_morph_ex_unique PB p' pm1 pm2 pmc u u'
    |}.

End PullBack_is_PullBack.
  
(** PushOut is the dual of PullBack *)
Definition PushOut (C : Category) := @PullBack (C^op).

Arguments PushOut _ {_ _ _} _ _, {_ _ _ _} _ _.

Definition Has_PushOuts (C : Category) : Type :=
  ∀ (a b c : C) (f : c –≻ a) (g : c –≻ b), PushOut f g.

Existing Class Has_PushOuts.
