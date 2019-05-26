Class monad (mon : Type -> Type) :=
  {
    ret : forall {A : Type},  A -> mon A;
    bind : forall {A B : Type}, mon A -> (A -> mon B) -> mon B
  }.


Delimit Scope monad_scope with monad.

Notation "x >>= f" := (bind x f) (at level 50, left associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                                  (at level 100, c1 at next level, right associativity) : monad_scope.

Open Scope monad.

Definition liftM {M : Type -> Type} `{monad M} {A B : Type} (f : A -> B)
           (m1: M A) : M B :=
  n1 <- m1 ;;
  ret (f n1).

Definition liftM2 {M : Type -> Type} `{monad M} {A1 A2 B : Type} (f : A1 -> A2 -> B)
           (m1: M A1) (m2 : M A2)  : M B :=
  n1 <- m1 ;;
  n2 <- m2 ;;
  ret (f n1 n2).

Instance optionMonad : monad option :=
  {
    ret A x := Some x;
    bind A B x f :=
      match x with
        | Some y => f y
        | None => None
      end
  }.


Definition State (St : Type) (A: Type) := St -> (A * St)%type.

Instance stateMonad {St : Type} : monad (State St) :=
  {
    ret A x := fun s => (x, s);
    bind A B x f := 
      fun s => 
        let (y, s') := x s in 
        f y s'
  }.

Definition get {St} : State St St := fun st => (st, st).

Definition set {St} (ns : St) : State St unit := fun _ => (tt, ns).
