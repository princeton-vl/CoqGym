Require Import List.
Import ListNotations.
Require Import Arith.EqNat.

Section Sort.

Variable Element : Type.
Variable beqElement : Element -> Element -> bool.
Variable beqEqElement : forall x y : Element, {x = y} + {x <> y}.
Definition GraphEntry := (Element * list Element)%type.
Definition Graph := list GraphEntry.
Definition Order := list (list Element).

Definition graphLookup (elem: Element) (graph: Graph) : list Element :=
  match find (fun entry => beqElement elem (fst entry)) graph with
    | Some (_, es) => es
    | None => []
  end.

Definition bElemIn (elem: Element) (es: list Element) : bool :=
  if find (beqElement elem) es then true else false.
Definition bElemNotIn (elem: Element) (es: list Element) : bool :=
  if find (beqElement elem) es then false else true.

Fixpoint cycleEntryAux (graph: Graph) (seens: list Element) (elem: Element) (counter: nat) : Element :=
  if bElemIn elem seens
  then elem
  else match counter with
         | S c => match graphLookup elem graph with
                   | e' :: _ =>
                     (* cas où elem est bien dans le graphe et a au moins un successeur *)
                     (* on devrait toujours être dans ce cas quand on utilise la fonction *)
                     cycleEntryAux graph (elem :: seens) e' c
                   | _ => elem
                 end
         | _ => elem
       end.

Definition cycleEntry (graph : Graph) : option Element :=
  match graph with
    | (e, _) :: _ => Some (cycleEntryAux graph [] e (length graph))
    | _ => None
  end.

Fixpoint cycleExtractAux (graph: Graph) (counter: nat) (elem: Element) (cycl: list Element) : list Element :=
  match counter with
    | S c => if bElemIn elem cycl
            then cycl (* déjà présent dans le cycle, on arrête le parcours sur cette branche *)
            else
              let es := graphLookup elem graph in
                fold_right (cycleExtractAux graph c) (elem :: cycl) es
    | _ => cycl (* peut arriver si tous les nœuds sont dans le cycle *)
  end.

Definition cycleExtract (graph: Graph): list Element :=
  match cycleEntry graph with
    | None => []
    | Some elem => cycleExtractAux graph (length graph) elem []
  end.

(* Définition utile ? *)
Definition comp {A B C: Type} (f: B -> C) (g: A -> B) (x: A) := f (g x).
Definition null {A: Type} (xs: list A) : bool :=
  if xs then true else false.

Fixpoint topologicalSortAux (graph: Graph) (counter: nat) : Order :=
  match counter with
    | S c =>
      if null graph
      then []
      else
        let mins := map (@fst _ _) (filter (comp null (@snd _ _)) graph) in
        let mins' := if null mins then cycleExtract graph else mins in
        let rest := filter (fun entry => bElemNotIn (fst entry) mins') graph in
        let rest' := map (fun entry => (fst entry, filter (fun e => bElemNotIn e mins') (snd entry))) rest in
        mins' :: topologicalSortAux rest' c
    | _ => []
  end.

Definition topologicalSort (graph: Graph) : Order :=
  topologicalSortAux graph (length graph).

Definition topologicalRankList (graph : Graph) : list (Element * nat) :=
  let lorder := topologicalSort graph in
  concat (map (fun (x: list Element * nat) => let (fs, rk) := x in map (fun f => (f, rk)) fs)
              (combine lorder (seq 0 (length lorder)))).

End Sort.

Ltac autorank elem_beq ranklist :=
  intros f;
  pose (f' := f);
  destruct f;
  match eval compute in (find (fun fr => elem_beq f' (fst fr)) ranklist) with
    | Some (_, ?r) => exact r
      (* cas des fonctions n’apparaissant pas dans le programme *)
    | None         => exact 0
  end.

(*
Eval compute in (topologicalSort nat beq_nat [ (1, [2]); (2, []) ]).
Eval compute in (topologicalSort nat beq_nat [ (1, [2]); (2, [1]) ]).

Eval compute in (topologicalSort nat beq_nat [ (1, [2; 3]);
                                   (2, [1]);
                                   (3, []) ]).

Eval compute in (topologicalSort nat beq_nat [ (1, [2; 3]);
                                   (2, [1]);
                                   (3, []);
                                   (4, [2; 3])]).
*)
