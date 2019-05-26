Require Import String List.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Inductive data T : (T -> Type) -> Type :=
| Inj   : forall X, Type -> data X
| Get   : forall X, T -> data X
| Prod  : forall X, data X -> data X -> data X
| Sigma : forall X (S : Type), (S -> data X) -> data X
| Pi    : forall X (S : Type), (S -> data X) -> data X.

Fixpoint dataD (T : Type) (X : T -> Type) (d : data X) : Type :=
  match d with
    | Inj _X x => x
    | Get X i => X i
    | Prod l r => prod (dataD l) (dataD r)
    | @Sigma _ _ i s => @sigT i (fun v => dataD (s v))
    | @Pi _ _ i s => forall v : i, dataD (s v)
  end.

(** Example of lists as data **)
Definition dataList (a : Type) : @data unit (fun _ => list a) :=
  @Sigma _ _ bool (fun x => match x with 
                              | true => @Inj _ _ unit
                              | false => @Prod _ _ (Inj _ a) (Get _ tt)
                            end).

Theorem dataList_to_list : forall T (x : dataD (dataList T)), list T.
  simpl. intros.
  destruct x. destruct x.
  apply nil.
  simpl in *.
  apply (fst d :: snd d).
Defined.

Theorem list_to_dataList : forall T (ls : list T), dataD (dataList T).
  simpl. destruct 1.
  exists true. apply tt.
  exists false. apply (t, ls).
Defined.


Fixpoint dataP (T : Type) (X : T -> Type) (d : data X) (R : Type) : Type :=
  match d with
    | Inj _X x => x -> R
    | Get X x => X x -> R
    | @Prod _ _ l r => dataP l (dataP r R)
    | @Sigma _ _ i s => forall i, dataP (s i) R
    | @Pi _ _ i s => (forall i, dataD (s i)) -> R
  end.

Fixpoint dataMatch (T : Type) (X : T -> Type) (d : data X) {struct d} 
  : forall (R : Type), dataP d R -> dataD d -> R :=
    match d as d return forall (R : Type), dataP d R -> dataD d -> R with
      | Inj _ _ => fun _ p => p
      | Get X x => fun _ p => p
      | @Prod _ _ l r => fun _ p v => 
        dataMatch r _ (dataMatch l _ p (fst v)) (snd v)
      | @Sigma _ _ i d => fun _ p v => 
        match v with
        | existT _ x y => dataMatch (d x) _ (p _) y
        end
      | @Pi _ _ i d => fun _ p v => p v
    end.

(* This used to work
(** You really need a fold! **)
Fixpoint dataLength {x} (l : list x) Z {struct l} : nat :=
  dataMatch (dataList x) _ (fun tag => match tag with
                                       | true => fun _ => 0
                                       | false => fun h t => S (Z t) (* (dataLength t) *)
                                       end) (list_to_dataList l).
*)