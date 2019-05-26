Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section ContType.
  Variable Ans : Type.


(*
  Record cont (t : Type) : Type := mkCont
  { runCont : (t -> Ans) -> Ans }.

  Global Instance Monad_cont : Monad cont :=
  { ret  := fun _ v => mkCont (fun k => k v)
  ; bind := fun _ c1 _ c2 =>
    mkCont (fun k =>
      runCont c1 (fun t =>
        runCont (c2 t) k))
  }.

  Global Instance Cont_cont : Cont cont :=
  { callCC := fun _ _ f => mkCont (fun c => runCont (f (fun x => mkCont (fun _ => c x))) c)
  }.

  Definition mapCont (f : Ans -> Ans) {a} (c : cont a) : cont a :=
    mkCont (fun x => f (runCont c x)).

  Definition withCont {a b} (f : (b -> Ans) -> (a -> Ans)) (c : cont a) : cont b :=
    mkCont (fun x => runCont c (f x)).
*)

  Variable m : Type -> Type.

  Record contT (t : Type) : Type := mkContT
  { runContT : (t -> m Ans) -> m Ans }.

  Global Instance Monad_contT : Monad contT :=
  { ret := fun _ x => mkContT (fun k => k x)
  ; bind := fun _ c1 _ c2 =>
    mkContT (fun c =>
      runContT c1 (fun a => runContT (c2 a) c))
  }.

  Global Instance Cont_contT : Cont contT :=
  { callCC := fun _ _ f => mkContT (fun c => runContT (f (fun x => mkContT (fun _ => c x))) c)
  }.

  Global Instance MonadT_contT (M : Monad m) : MonadT contT m :=
  { lift := fun _ c => mkContT (bind c)
  }.

(*
  Definition mapContT (f : m Ans -> m Ans) {a} (c : contT a) : contT a :=
    mkContT (fun x => f (runContT c x)).

  Definition withContT {a b} (f : (b -> m Ans) -> (a -> m Ans)) (c : contT a) : contT b :=
    mkContT (fun x => runContT c (f x)).
*)

End ContType.
*)