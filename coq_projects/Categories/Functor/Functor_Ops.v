From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.

(** 
Opposite of a functor F : C -> D is a functor F^op : C^op -> D^op with the same
object and arrow maps.
 *)
Section Opposite_Functor.
  Context {C D : Category} (F : (C –≻ D)%functor).
  
  Local Open Scope morphism_scope.
  Local Open Scope object_scope.
    
  Program Definition Opposite_Functor : (C^op –≻ D^op)%functor :=
    {|
      FO := F _o;
      FA := fun _ _ h => F @_a _ _ h;
      F_id := fun a => F_id F a;
      F_compose := fun _ _ _ f g => F_compose F g f
    |}.

End Opposite_Functor.

Notation "F '^op'" := (Opposite_Functor F) : functor_scope.

(* We can compose functors. The object and arrow maps are simply function
   compositions of object and arrow maps. *)
Section Functor_Compose.
  Context {C C' C'' : Category} (F : (C –≻ C')%functor) (F' : (C' –≻ C'')%functor).

  Local Open Scope morphism_scope.
  Local Open Scope object_scope.
  
  Program Definition Functor_compose : (C –≻ C'')%functor :=
    {|
      FO := fun c => F' _o (F _o c);
      FA := fun c d f => F' _a (F _a f)
    |}.
  
End Functor_Compose.

Notation "F ∘ G" := (Functor_compose G F) : functor_scope. 

(** Associativity of functor composition *)
Section Functor_Assoc.
  Context {C1 C2 C3 C4 : Category}
          (F : (C1 –≻ C2)%functor)
          (G : (C2 –≻ C3)%functor)
          (H : (C3 –≻ C4)%functor).

  Local Open Scope functor_scope.
    
  Theorem Functor_assoc : (H ∘ G) ∘ F = H ∘ (G ∘ F).
  Proof.
    Func_eq_simpl; trivial.
  Qed.

End Functor_Assoc.

(** The identitiy functor *)

Program Definition Functor_id (C : Category) : (C –≻ C)%functor :=
  {|
    FO := fun x => x;
    FA := fun c d f => f
  |}.

Section Functor_Identity_Unit.
  Context  (C C' : Category) (F : (C –≻ C')%functor).

  (** Fucntor_id is the left ididntity of functor composition. *)
  Theorem Functor_id_unit_left : ((Functor_id C') ∘ F)%functor = F.
  Proof.
    Func_eq_simpl; trivial.
  Qed.

  (** Functor_id is the right identity of functor composition. *)
  Theorem Functor_id_unit_right : (Functor_compose (Functor_id _) F) = F.
  Proof.
    Func_eq_simpl; trivial.
  Qed.

End Functor_Identity_Unit.

