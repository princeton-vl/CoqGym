(** Instance for building logics by translating them to
 ** other logics.
 **)
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Tactics.Tactics.

Section from_iso.
  Context {T U : Type} (f : T -> U) (g : U -> T) (ilo : ILogicOps T).

  Instance ILogicOps_iso : ILogicOps U :=
  {| lentails := fun l r => lentails (g l) (g r)
   ; ltrue := f ltrue
   ; lfalse := f lfalse
   ; land := fun l r => f (land (g l) (g r))
   ; lor := fun l r => f (lor (g l) (g r))
   ; limpl := fun l r => f (limpl (g l) (g r))
   ; lforall := fun T P => f (lforall (fun x => g (P x)))
   ; lexists := fun T P => f (lexists (fun x => g (P x)))
   |}.

  Context {il : ILogic T}.
  Hypothesis gf : forall x, g (f x) -|- x.

  Instance ILogic_iso : ILogic U.
  Proof.
    constructor; simpl; intros; repeat rewrite gf in *.
    { constructor.
      { red; simpl; intros; reflexivity. }
      { red; simpl; intros. etransitivity; eassumption. } }
    all: try charge_tauto.
    apply lfalseL.
    eapply lforallL; eauto.
    eapply lforallR; eauto.
    eapply lexistsL; eauto.
    eapply lexistsR; eauto.
    apply lorL; eauto.
  Defined.
End from_iso.
Arguments ILogicOps_iso {_ _} _ _ {_}.
Arguments ILogic_iso {_ _} [_ _ _] {_} _.

Hint Extern 10 (@ILogic _ _) =>
  (eapply ILogic_iso ;
     [ eauto with typeclass_instances
     | intro; eapply RelationClasses.PreOrder_Reflexive ]) : typeclass_instances.
