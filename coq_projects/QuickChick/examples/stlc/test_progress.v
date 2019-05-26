From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrbool.
Require Import String. (* ?? *)
From QuickChick.stlc Require Import monad lambda.


(* Note : In general we would need a type checking/inferring function for this.
          Since our generator only generates well-typed terms this is not needed
          for this example. However, it would be nice to have one for other examples.*) 

Definition is_some {A} (o : option A) : bool :=
  match o with 
    | Some _ => true
    | None => false
  end.

Definition has_progress (t : term) := is_value t || (is_some (step t)).

Fixpoint term_size (t : term) : nat :=
  match t with
    | Const _ | Id _ => 1
    | Abs t => 1 + (term_size t)
    | App t1 t2 => 1 + (term_size t1 + term_size t2)
  end.

(* Extract Constant Test.defNumTests => "1000000". *)
QuickCheck (forAll gen_type (fun tau => forAll (gen_term tau) (fun t
  => (collect (append "size " (show (term_size t))) (has_progress t))))).

Fixpoint step_bug (t : term) : option term :=
  match t with
    | Const _ | Id _ => None | Abs x => None
    | App t1 t2 =>
      if is_value t1 then 
        match t1 with 
          | Abs t => 
            if is_value t2 then ret (subst 0 t1 t)
            else None
          | _ => None
        end
      else
        t1' <- step t1;;
        ret (App t1' t2)
  end.

Definition has_progress_bug (t : term) := is_value t || (is_some (step_bug t)).

QuickCheck (forAll gen_type (fun tau => 
                               forAll (gen_term tau) has_progress_bug)).

QuickCheck (forAll arbitrary (fun tau : type =>
                                forAll (genST (fun t => typing' nil t tau))
                                       (fun mt =>
                                          match mt with
                                          | Some t => has_progress_bug t
                                          | None => false
                                          end))).
