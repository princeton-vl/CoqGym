From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

Local Open Scope morphism_scope.

Section Equalizer.
  Context {C : Category} {a b : Obj} (f g : a –≻ b).

  (** given two parallel arrows f,g : a -> b, their equalizer is an object e
      together with an arrow eq : e -> a such that f ∘ eq = g ∘ eq such that
      for any other object z and eqz : z -> a that we have f ∘ eqz = g ∘ eqz,
      there is a unique arrow h : z -> e that makes the following diagram
      commute:

#
<pre>

          eqz
/—————————————————\     f
|                 ↓  ———————>
z ———–> e ——————> a          b
   ∃!h      eq       ———–——–>
                        g
</pre>
#
 *)

  Local Open Scope morphism_scope.
  
  Record Equalizer : Type :=
    {
      equalizer : C;

      equalizer_morph : equalizer –≻ a;

      equalizer_morph_com : f ∘ equalizer_morph = g ∘ equalizer_morph;

      equalizer_morph_ex (e' : Obj) (eqm : e' –≻ a) :
        f ∘ eqm = g ∘ eqm → e' –≻ equalizer;

      equalizer_morph_ex_com (e' : Obj) (eqm : e' –≻ a)
                             (eqmc : f ∘ eqm = g ∘ eqm)
      : equalizer_morph ∘ (equalizer_morph_ex e' eqm eqmc) = eqm;

      equalizer_morph_unique (e' : Obj) (eqm : e' –≻ a)
                             (com : f ∘ eqm = g ∘ eqm) (u u' : e' –≻ equalizer)
      : equalizer_morph ∘ u = eqm → equalizer_morph ∘ u' = eqm → u = u'
    }.

  Coercion equalizer : Equalizer >-> Obj.
  
  (** Equalizers are unique up to isomorphism. *)
  Theorem Equalizer_iso (e1 e2 : Equalizer) : (e1 ≃ e2)%isomorphism.
  Proof.
    apply (Build_Isomorphism _ _ _ (equalizer_morph_ex e2 _ (equalizer_morph e1)
                                                       (equalizer_morph_com e1))
                             ((equalizer_morph_ex e1 _ (equalizer_morph e2)
                                                  (equalizer_morph_com e2))));
    eapply equalizer_morph_unique; [| | simpl_ids; trivial| | |simpl_ids;
                                      trivial]; try apply equalizer_morph_com;
    rewrite <- assoc; repeat rewrite equalizer_morph_ex_com; auto.
  Qed.

End Equalizer.

Arguments equalizer_morph {_ _ _ _ _} _.
Arguments equalizer_morph_com {_ _ _ _ _} _.
Arguments equalizer_morph_ex {_ _ _ _ _} _ {_ _} _.
Arguments equalizer_morph_ex_com {_ _ _ _ _} _ {_ _} _.
Arguments equalizer_morph_unique {_ _ _ _ _} _ {_ _ _} _ _ _ _.

Arguments Equalizer _ {_ _} _ _, {_ _ _} _ _.

Definition Has_Equalizers (C : Category) : Type :=
  ∀ (a b : C) (f g : a –≻ b), Equalizer f g.

Existing Class Has_Equalizers.

(** CoEqualizer is the dual of equalzier *)
Definition CoEqualizer {C : Category} := @Equalizer (C^op).

Arguments CoEqualizer _ {_ _} _ _, {_ _ _} _ _.

Definition Has_CoEqualizers (C : Category) : Type := Has_Equalizers (C^op).

Existing Class Has_CoEqualizers.
