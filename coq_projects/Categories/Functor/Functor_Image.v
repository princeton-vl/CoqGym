From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Category.Composable_Chain.
From Categories Require Import Functor.Functor.


(** The image of a functor is not simply the image of its object and arrow maps as
those may not form a category. Consider the following example.

  category C:
#
<pre>
             f
       x1 ——————–> y1

       x2 ——————–> y2
             g
</pre>
#
   category D:
#
<pre>
             h1        h2  
       x ——————–> y ————————> z

       u ——————–> v
            m
</pre>
#
    functor F where:
#
<pre>
       F _o x1 = x
       F _o y1 = y
       F _o x2 = y
       F _o y2 = z

       F _a f = h1
       F _a g = h2
</pre>
#

Here we have not drawn identity arrows and compositions of arrows in categories and
their mappings by the functor as these are trivial details.

In this case, the simple image of arrow map of F has only h1 and h2 but not their
composition and is hence not a category.

We define the image of a functor to be a sum category of the codomain category with
objects the image of object map of the functor and as morphisms image of the arrow
map of the functor closed under composition. That is, each morphism in the image
category is a morphism that corresponds to a composable chain of morohisms in the
image of the arrow map of the functor.

*)
Section Functor_Image.
  Context {C D : Category}
          (F : (C –≻ D)%functor).

  Local Open Scope morphism_scope.

  Program Definition Functor_Image :=
    SubCategory D
                (fun a => ∃ x, (F _o x)%object = a)
                (
                  fun a b f =>
                    ∃ (ch : Composable_Chain D a b),
                      (Compose_of ch) = f
                      ∧
                      Forall_Links ch (
                                     fun x y g =>
                                     ∃ (c d : Obj) (h : c –≻ d)
                                       (Fca : (F _o c)%object = x)
                                       (Fdb : (F _o d)%object = y),
                                       match Fca in (_ = Z) return Z –≻ _ with
                                         eq_refl =>
                                         match Fdb in (_ = Y) return _ –≻ Y with
                                           eq_refl => (F _a h)%morphism
                                         end
                                       end = g)
                )
                _ _.

  Ltac destr_exists :=
    progress
    (repeat
       match goal with
         [H : ∃ x, _ |- _] =>
         let x := fresh "x" in
         let Hx := fresh "H" x in
         destruct H as [x Hx]
       end).
  
  Next Obligation. (* Hom_Cri_id *)
  Proof.
    destr_exists.
    ElimEq.
    exists (Single (F _a id)); simpl; split; auto.
    do 3 eexists; do 2 exists eq_refl; reflexivity.
  Qed.

  Next Obligation. (* Hom_Cri_compose *)
  Proof.
    destr_exists.
    intuition.
    ElimEq.
    match goal with
        [ch1 : Composable_Chain _ ?a ?b, ch2 : Composable_Chain _ ?b ?c|- _] =>
        exists (Chain_Compose ch1 ch2); split
    end.
    rewrite <- Compose_of_Chain_Compose; trivial.
    apply Forall_Links_Chain_Compose; auto.
  Qed.

End Functor_Image.
