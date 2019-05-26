From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.
From Categories Require Import Cat.Cat.

Section NatTrans.
  Context {C C' : Category}.

(**
For categories C and C' and functors F : C -> C' and F' : C -> C', a natural
transformation N : F -> F' is a family of arrows 'Trans N' in the co-domain
category (here C') indexed by objects of the domain category (here C),
Trans N c : F _o c -> F' _o c.

In addition, for all arrows h : c → c' the following diagram must
commute (Trans_com):

#
<pre>
             F _a h
F _o c ————————————————––> F _o c'
 |                          |
 |                          |
 |                          |
 | Trans N c                | Trans N c'
 |                          |
 |                          |
 ∨                          ∨
F' _o c ————————————————–> F' _o c'
            F' _a h
</pre>
#
Trans_com_sym is the symmetric form of Trans_com.
*)
  Record NatTrans (F F' : (C –≻ C')%functor) :=
    {
      Trans (c : C) : ((F _o c) –≻ (F' _o c))%object%morphism;
      Trans_com {c c' : C} (h : (c –≻ c')%morphism) :
        ((Trans c') ∘ F _a h = F' _a h ∘ (Trans c))%morphism;
      Trans_com_sym {c c' : C} (h : (c –≻ c')%morphism) :
        (F' _a h ∘ (Trans c) = (Trans c') ∘ F _a h)%morphism
    }.

  Notation "F –≻ F'" := (NatTrans F F') : nattrans_scope.

  (** Two natural transformations are equal if their arrow families are.
      That is, commutative diagrams are assumed to be equal by
      proof irrelevance. *)
  Lemma NatTrans_eq_simplify {F F' : (C –≻ C')%functor}
        (N N' : (F –≻ F')%nattrans) : (@Trans _ _ N) = (@Trans _ _ N') -> N = N'.
  Proof.
    destruct N; destruct N'.
    basic_simpl.
    ElimEq.
    PIR; trivial.
  Qed.

End NatTrans.

Arguments Trans {_ _ _ _} _ _.
Arguments Trans_com {_ _ _ _} _ {_ _} _.
Arguments Trans_com_sym {_ _ _ _} _ {_ _} _.

Bind Scope nattrans_scope with NatTrans.

Notation "F –≻ F'" := (NatTrans F F') : nattrans_scope.

Local Open Scope nattrans_scope.

Section NatTrans_Compose.
  Context {C C' : Category}.
  
  (** Natural transformations are composable. The arrow family of the result is
      just the composition of corresponding components in each natural
      transformation. Graphically:
#
<pre>
         F                            F
   C ———————————————–> D        C ———————————————–> D 
           ||                           ||
           ||N                          ||
           ||                           ||
           \/                           ||
   C ———————————————–> D                || N' ∘ N
         G                              ||
           ||                           ||
           ||N'                         ||
           ||                           ||
           \/                           \/
   C ———————————————–> D        C ———————————————–> D 
         H                            H
</pre>
#

This kind of composition is sometimes also called vertical composition of
natural transformations.
*)
  Program Definition NatTrans_compose {F F' F'' : (C –≻ C')%functor}
          (tr : F –≻ F') (tr' : F' –≻ F'') : (F –≻ F'')%nattrans :=
    {|
      Trans := fun c : Obj => ((Trans tr' c) ∘ (Trans tr c)) % morphism
    |}.

  Next Obligation. (* Trans_com*)
  Proof.
    rewrite assoc.
    rewrite Trans_com.
    rewrite assoc_sym.
    rewrite Trans_com; auto.
  Qed.

  Next Obligation. (* Trans_com_sym *)
  Proof.
    symmetry.
    apply NatTrans_compose_obligation_1.
  Qed.

End NatTrans_Compose.

Notation "N ∘ N'" := (NatTrans_compose N' N) : nattrans_scope.

Section NatTrans_Props.
  Context {C C' : Category}.
  
  (** The composition of natural transformations is associative. *)
  Theorem NatTrans_compose_assoc {F G H I : (C –≻ C')%functor} (N : F –≻ G)
          (N' : G –≻ H) (N'' : H –≻ I)
    : ((N'' ∘ N') ∘ N = N'' ∘ (N' ∘ N))%nattrans
  .
  Proof.
    apply NatTrans_eq_simplify; cbn; auto.
  Qed.

  (** The identity natural transformation. The arrow family are just
      all identity arrows: *)
  Program Definition NatTrans_id (F : (C –≻ C')%functor) : F –≻ F :=
    {|
      Trans := fun x : Obj => id
    |}.

  Theorem NatTrans_id_unit_left {F G : (C –≻ C')%functor} (N : F –≻ G)
    : (NatTrans_id G) ∘ N = N.
  Proof.
    apply NatTrans_eq_simplify; cbn; auto.
  Qed.

  Theorem NatTrans_id_unit_right {F G : (C –≻ C')%functor} (N : F –≻ G)
    : N ∘ (NatTrans_id F) = N.
  Proof.
    apply NatTrans_eq_simplify; cbn; auto.
  Qed.
  
End NatTrans_Props.

Hint Resolve NatTrans_eq_simplify.
