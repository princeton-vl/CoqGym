Require Import Cheerios.Combinators.
Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Tactics.
Require Import Cheerios.Types.

Require Import List.
Require Import FMapPositive.

Import ListNotations.
Import DeserializerNotations.

Set Implicit Arguments.


(*
   Most user-defined datatypes are tree-like, which are typically nontrivial to
   deserialize by structural recursion on the bitstream. This file provides a
   generic multi-arity tree type and its serializer/deserializer. Other tree-like
   types can be serialized by first converting to a tree and then serializing.
*)

Section tree.
  (* The tree is parametrized on the type of data stored at the leaves. *)
  Variable A : Type.

  (* Each node of the tree contains a list of subtrees.
     Coq does not generate a useful induction scheme for such types,
     so we just tell it not to generate anything, and we'll write our own. *)
  Local Unset Elimination Schemes.

  Inductive tree : Type :=
  | atom : A -> tree
  | node : list tree -> tree
  .

  (* Here is an actually useful recursion principle for tree,
     which requires an additional motive P_list. *)
  Section tree_rect.
    Variable P : tree -> Type.
    Variable P_list : list tree -> Type.
    Hypothesis P_nil : P_list [].
    Hypothesis P_cons : forall t l, P t -> P_list l -> P_list (t :: l).
    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, P_list l -> P (node l).

    Fixpoint tree_rect (t : tree) : P t :=
      let fix go_list (l : list tree) : P_list l :=
          match l with
          | [] => P_nil
          | t :: l => P_cons (tree_rect t) (go_list l)
          end
      in
      match t with
      | atom a => P_atom a
      | node l => P_node (go_list l)
      end.
  End tree_rect.

  (* Setting P_list := List.Forall P is a reasonable default. *)
  Section tree_ind.
    Variable P : tree -> Prop.

    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, List.Forall P l -> P (node l).

    Definition tree_ind (t : tree) : P t :=
      tree_rect P (List.Forall P)
                (List.Forall_nil _)
                (fun t l Pt Pl => List.Forall_cons _ Pt Pl) P_atom P_node t.
  End tree_ind.
End tree.


Fixpoint rev_rec {A} (l : list A) (acc : list A) :=
  match l with
  | [] => acc
  | a :: l => rev_rec l (a :: acc)
  end.

Lemma rev_rec_spec : forall {A : Type} (l : list A) acc,
    rev_rec l acc = rev l ++ acc.
Proof.
  intros A l.
  induction l.
  - reflexivity.
  - intros.
    simpl.
    rewrite <- app_assoc.
    now rewrite IHl.
Qed.

Definition rev' {A} (l : list A) :=
  rev_rec l [].

Theorem rev'_spec : forall {A : Type} (l : list A),
    rev' l = rev l.
Proof.
  intros. unfold rev'.
  now rewrite rev_rec_spec, app_nil_r.
Qed.


Fixpoint map_rec {A B} (f : A -> B) (l : list A) (acc : list B) :=
  match l with
  | [] => rev' acc
  | a :: l => map_rec f l (f a :: acc)
  end.

Lemma map_rec_spec : forall {A B} (f : A -> B) (l : list A) (acc : list B),
    map_rec f l acc = rev acc ++ List.map f l.
Proof.
  intros A B f l.
  induction l.
  - intros.
    simpl.
    unfold rev'.
    now rewrite rev_rec_spec.
  - intros.
    simpl.
    rewrite IHl.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Definition list_map' {A B} (f : A -> B) (l : list A) :=
  map_rec f l [].

Theorem map'_spec : forall {A B} (f : A -> B) (l : list A),
    List.map f l = list_map' f l.
  intros.
  unfold list_map'.
  now rewrite map_rec_spec.
Qed.

(* The shape of a tree can be expressed by mapping (fun _ => tt) over it. *)
Fixpoint map {A B} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | atom a => atom (f a)
  | node l => node (List.map (map f) l)
  end.

Definition shape {A} (t : tree A) : tree unit :=
  map (fun _ => tt) t.

Fixpoint tree_map' {A B} (f : A -> B) (t : tree A) : tree B :=
  let fix tree_map_loop {A B} (f : A -> B) (l : list (tree A)) acc :=
      match l with
      | [] => rev_rec acc []
      | a :: l => tree_map_loop f l (map f a :: acc)
      end in
  match t with
  | atom a => atom (f a)
  | node l => node (tree_map_loop f l [])
  end.

Definition tree_map_loop :=
  fix tree_map_loop {A B} (f : A -> B) (l : list (tree A)) acc :=
    match l with
    | [] => rev_rec acc []
    | a :: l => tree_map_loop f l (map f a :: acc)
    end.

Lemma tree_map_loop_spec :
  forall {A B} (f : A -> B) l acc,
    tree_map_loop f l acc = rev acc ++ List.map (map f) l.
Proof.
  intros A B f l.
  induction l; intros.
  - simpl.
    now rewrite rev_rec_spec.
  - simpl.
    rewrite IHl.
    simpl.
    now rewrite <- app_assoc.
Qed.

Theorem tree_map'_spec : forall {A B} (f : A -> B) (t : tree A),
    tree_map' f t = map f t.
Proof.
  intros.
  destruct t.
  - reflexivity.
  - simpl.
    now rewrite tree_map_loop_spec.
Qed.

(* Fill out a tree using a list of elements given in preorder traversal order. *)
Fixpoint fill' {A B} (x : tree A) (bs : list B) : option (tree B * list B) :=
  let fix fill'_list (l : list (tree A)) (bs : list B) : option (list (tree B) * list B) :=
      match l with
      | [] => Some ([], bs)
      | x :: l => match fill' x bs with None => None
                                   | Some (x, bs) =>
                                     match fill'_list l bs with None => None
                                                           | Some (l, bs) =>
                                                             Some (x :: l, bs)
                                     end
                  end
      end in
  match x with
  | atom _ => match bs with
              | [] => None
              | b :: bs => Some (atom b, bs)
              end
  | node l => match fill'_list l bs with None => None
                                    | Some (l, bs) => Some (node l, bs)
              end

  end.

(* Copy paste of local definition above. *)
Definition fill'_list {A B} :=
  fix fill'_list (l : list (tree A)) (bs : list B) : option (list (tree B) * list B) :=
    match l with
    | [] => Some ([], bs)
    | x :: l => match fill' x bs with None => None
                                 | Some (x, bs) =>
                                   match fill'_list l bs with None => None
                                                         | Some (l, bs) =>
                                                           Some (x :: l, bs)
                                   end
                end
    end.

Definition fill {A B} (x : tree A) (bs : list B) : option (tree B) :=
  match fill' x bs with None => None
                   | Some (t, _) => Some t
  end.

(* Produce a preorder traversal list of elements *)
Fixpoint preorder {A} (x : tree A) : list A :=
  let fix preorder_list (l : list (tree A)) : list A :=
      match l with
      | [] => []
      | x :: l => preorder x ++ preorder_list l
      end
  in
  match x with
  | atom a => [a]
  | node l => preorder_list l
  end.

Definition preorder_list {A} :=
  fix preorder_list (l : list (tree A)) : list A :=
    match l with
    | [] => []
    | x :: l => preorder x ++ preorder_list l
    end.

Fixpoint preorder' {A} (x : tree A) : list A :=
  let fix preorder_list (l : list (tree A)) acc : list A :=
      match l with
      | [] => acc
      | x :: l => preorder_list l (acc ++ preorder x)
      end
  in
  match x with
  | atom a => [a]
  | node l => preorder_list l []
  end.

(* Since the shape is expressed as mapping, we will need the fact that filling
   out the a mapped tree with the elements of the original tree gives the
   original.
 *)
Lemma fill'_preorder :
  forall A B (f : B -> A) t (bs : list B),
    fill' (map f t) (preorder t ++ bs) = Some (t, bs).
Proof.
  intros A B f.
  induction t using tree_rect
    with (P_list := fun l =>
                      forall bs,
                        fill'_list (List.map (map f) l) (preorder_list l ++ bs) = Some (l, bs)); intros.
  - auto.
  - simpl.
    rewrite app_ass. rewrite  IHt. rewrite IHt0. auto.
  - auto.
  - simpl.
    fold (@preorder_list B).
    fold (@fill'_list A B).
    now rewrite IHt.
Qed.

Lemma fill_preorder :
  forall A B (f : A -> B) t,
    fill (map f t) (preorder t) = Some t.
Proof.
  unfold fill.
  intros.
  rewrite <- app_nil_r with (l := preorder t).
  now rewrite fill'_preorder.
Qed.

Section serializer.
  Variables A : Type.
  Variable sA :Serializer A.

  (* Now we're ready to serialize trees. First, we serialize their shape. *)

  Fixpoint serialize_tree_shape (t : tree A) : IOStreamWriter.t :=
    let fix serialize_list_tree_shape (l : list (tree A)) : IOStreamWriter.t :=
        match l with
        | [] => IOStreamWriter.empty
        | x :: xs => IOStreamWriter.append (fun _ => serialize_tree_shape x)
                                   (fun _ => serialize_list_tree_shape xs)
        end in
    match t with
    | atom _ => serialize x00 (* ignore the data, since we're just focused on the shape *)
    | node l => IOStreamWriter.append (fun _ => serialize x01)
                              (fun _ => (IOStreamWriter.append
                                           (fun _ => serialize_list_tree_shape l)
                                           (fun _ => serialize x02)))
    end.

  Definition serialize_list_tree_shape :=
    fix serialize_list_tree_shape (l : list (tree A)) : IOStreamWriter.t :=
      match l with
      | [] => IOStreamWriter.empty
      | x :: xs => IOStreamWriter.append (fun _ => serialize_tree_shape x)
                                 (fun _ => serialize_list_tree_shape xs)
      end.

  Definition deserialize_tree_shape_step (b : byte) (s : list (list (tree unit))) :
    fold_state (list (list (tree unit))) (tree unit) :=
    match b with
    | x00 => match s with
             | [] => Done (atom tt)
             | ts :: s => More ((atom tt :: ts) :: s)
             end
    | x01 => More ([] :: s)
    | x02 => match s with
             | [] => Error
             | ts :: s => let t := node (rev' ts) in
                          match s with
                          | [] => Done t
                          | ts :: acc => More ((t :: ts) :: acc)
                          end
             end

    | _ => Error
    end.

  Lemma shape_aux :
    forall t acc bytes,
      ByteListReader.unwrap (ByteListReader.fold deserialize_tree_shape_step acc)
                    (IOStreamWriter.unwrap (serialize_tree_shape t) ++ bytes) =
      match acc with
      | [] => Some (shape t, bytes)
      | j :: js => ByteListReader.unwrap
                     (ByteListReader.fold deserialize_tree_shape_step
                                  ((shape t :: j) :: js)) bytes
      end.
  Proof using.
    induction t using tree_rect with
        (P_list := fun l =>
                     (* We need to extend the statement to a list of subtrees for the mutual induction
          hypothesis.
          It says that serializing and then deserializing a list of trees `l` is the same
          as `List.map (map (fun _ => tt) l)`.
          `deserialize_list_tree_shape'` is always called with at least one element on the
          accumulator, so there's no need for a match like there was above.
                      *)
                     forall ts acc bytes,
                       ByteListReader.unwrap
                         (ByteListReader.fold deserialize_tree_shape_step (ts :: acc))
                         (IOStreamWriter.unwrap (serialize_list_tree_shape l) ++ bytes) =
                       ByteListReader.unwrap
                         (ByteListReader.fold
                            deserialize_tree_shape_step
                            ((rev (List.map shape l) ++ ts) :: acc)) bytes);
      intros;
      try (unfold serialize_list_tree_shape;
           rewrite IOStreamWriter.append_unwrap, app_ass, IHt, IHt0;
           simpl;
           now rewrite app_ass).
    (cheerios_crush; simpl; cheerios_crush; simpl).
    -  destruct acc;
         repeat (cheerios_crush;
                 simpl).
    - destruct acc;
        simpl;
        rewrite IOStreamWriter.append_unwrap,
        ByteListReader.fold_unwrap,
        IOStreamWriter.append_unwrap,
        IOStreamWriter.putByte_unwrap;
        simpl;
        fold serialize_list_tree_shape;
        rewrite app_ass, IHt, ByteListReader.fold_unwrap,
        IOStreamWriter.putByte_unwrap;
        simpl;
        rewrite app_nil_r, rev'_spec, rev_involutive;
        reflexivity.
  Qed.

  Definition deserialize_tree_shape : ByteListReader.t (tree unit) :=
    ByteListReader.fold deserialize_tree_shape_step [].

  (* This is the top level statement about serializing and deserializing tree shapes:
     it results in `shape` of the original tree. *)
  Lemma serialize_deserialize_shape_id :
    forall t bytes,
      ByteListReader.unwrap deserialize_tree_shape
                    (IOStreamWriter.unwrap (serialize_tree_shape t) ++ bytes)
      = Some (shape t, bytes).
  Proof using.
    intros.
    unfold deserialize_tree_shape.
    now rewrite shape_aux.
  Qed.

  Fixpoint serialize_tree_elements (t : tree A) : IOStreamWriter.t :=
    let fix serialize_tree_elements_list (l : list (tree A)) : IOStreamWriter.t :=
        match l with
        | [] => IOStreamWriter.empty
        | t :: l' => IOStreamWriter.append (fun _ => serialize_tree_elements t)
                                   (fun _ => serialize_tree_elements_list l')
        end
    in match t with
       | atom a => serialize a
       | node l => serialize_tree_elements_list l
       end.

  Definition serialize_tree_elements_list :=
    fix serialize_tree_elements_list (l : list (tree A)) : IOStreamWriter.t :=
      match l with
      | [] => IOStreamWriter.empty
      | t :: l' => IOStreamWriter.append (fun _ => serialize_tree_elements t)
                                 (fun _ => serialize_tree_elements_list l')
      end.

  Fixpoint deserialize_tree_elements (t : tree unit) : ByteListReader.t (tree A) :=
    let fix deserialize_tree_elements_list (l : list (tree unit)) :=
        match l with
        | [] => ByteListReader.ret []
        | t :: l' => cons <$> deserialize_tree_elements t
                          <*> deserialize_tree_elements_list l'
        end
    in match t with
       | atom tt => @atom _ <$> deserialize
       | node l => @node _ <$> deserialize_tree_elements_list l
       end.

  Definition deserialize_tree_elements_list :=
    fix deserialize_tree_elements_list (l : list (tree unit)) :=
      match l with
      | [] => ByteListReader.ret []
      | t :: l' => cons <$> deserialize_tree_elements t
                        <*> deserialize_tree_elements_list l'
      end.

  Lemma serialize_deserialize_tree_elements_id :
    forall t bytes,
      ByteListReader.unwrap (deserialize_tree_elements (shape t))
                    (IOStreamWriter.unwrap (serialize_tree_elements t) ++ bytes) =
      Some (t, bytes).
  Proof using.
    induction t using tree_rect with
        (P_list := fun l => forall bytes,
                       ByteListReader.unwrap (deserialize_tree_elements_list (List.map shape l))
                                     (IOStreamWriter.unwrap (serialize_tree_elements_list l) ++ bytes) =
                       Some (l, bytes));
      intros;
      cbn [shape map List.map
                 serialize_tree_shape deserialize_tree_shape
                 serialize_tree_elements deserialize_tree_elements
                 serialize_tree_elements_list deserialize_tree_elements_list].
    - now cheerios_crush.
    - cheerios_crush.
      rewrite IHt.
      cheerios_crush.
      rewrite IHt0.
      cheerios_crush.
    - now cheerios_crush.
    - fold deserialize_tree_elements_list.
      fold serialize_tree_elements_list.
      cheerios_crush.
      now rewrite IHt.
  Qed.

  (* Now we serialize the tree itself by first serializing the shape, and then a
     preorder traversal of the elements. *)
  Definition tree_serialize (t : tree A) : IOStreamWriter.t :=
    IOStreamWriter.append (fun _ => serialize_tree_shape t)
                  (fun _ => serialize_tree_elements t).

  (* To deserialize, we deserialize the shape and the elements, and then fill out
     the shape with the elements. *)
  Definition tree_deserialize : ByteListReader.t (tree A) :=
    shape <- deserialize_tree_shape ;;
          deserialize_tree_elements shape.

  (* To prove this correct, we need to know that serializ-/deserializing the shape of `t`
     results in `shape t` (`serialize_deserialize_shape_id`), and that
     filling out a `map f t` with the elements of `preorder t` results in `t`
     (`fill_preorder`).
   *)
  Lemma tree_serialize_deserialize_id :
    serialize_deserialize_id_spec tree_serialize tree_deserialize.
  Proof using.
    unfold tree_serialize, tree_deserialize. cheerios_crush.
    rewrite serialize_deserialize_shape_id.
    now rewrite serialize_deserialize_tree_elements_id.
  Qed.

  Global Instance tree_Serializer : Serializer (tree A) :=
    {| serialize := tree_serialize;
       deserialize := tree_deserialize;
       serialize_deserialize_id := tree_serialize_deserialize_id
    |}.
End serializer.

Module sexp.
  Import String.

  Definition sexp := tree string.

  Module examples.
    (*
       (define (id x) x)
     *)
    Definition id : sexp :=
      node [atom "define"; node [atom "id"; atom "x"]; atom "x"]%string.

    Lemma foo:
      ByteListReader.unwrap deserialize
                    (IOStreamWriter.unwrap (serialize id)) = Some (id, []).
    Proof using.
      now rewrite serialize_deserialize_id_nil.
    Qed.
    (*
       (define (Y f) ((lambda (x) (f (x x)))
                      (lambda (x) (f (x x)))))
     *)
    Definition Y : sexp :=
      node [atom "define"; node [atom "Y"; atom "f"];
              node [node [atom "lambda"; node [atom "x"]; node [atom "f"; node [atom "x"; atom "x"]]];
                      node [atom "lambda"; node [atom "x"]; node [atom "f"; node [atom "x"; atom "x"]]]]]
           %string.

    Lemma foo' : ByteListReader.unwrap deserialize (IOStreamWriter.unwrap (serialize Y)) = Some (Y, []).
    Proof using.
      now rewrite serialize_deserialize_id_nil.
    Qed.
  End examples.
End sexp.

Module JSON.
  Module json.
    Inductive t :=
    | Null : t
    | Bool : bool -> t
    | Num : nat -> t
    | String : String.string -> t
    | Arr : list t -> t
    | Obj : list (String.string * t) -> t.

    Section json_rect.
      Variable P : t -> Type.

      Variable P_list : list t -> Type.
      Variable P_list' : list (String.string * t) -> Type.

      Hypothesis P_nil : P_list [].
      Hypothesis P_cons : forall j l, P j -> P_list l -> P_list (j :: l).

      Hypothesis P_nil' : P_list' [].
      Hypothesis P_cons' : forall s j l, P j -> P_list' l -> P_list' ((s, j) :: l).

      Hypothesis P_null : P Null.
      Hypothesis P_bool : forall b, P (Bool b).
      Hypothesis P_num : forall n, P (Num n).
      Hypothesis P_string : forall s, P (String s).

      Hypothesis P_arr : forall l, P_list l -> P (Arr l).
      Hypothesis P_obj : forall l, P_list' l -> P (Obj l).

      Fixpoint json_rect (j : t) : P j :=
        let fix go_list (l : list t) : P_list l :=
            match l with
            | [] => P_nil
            | j :: l => P_cons (json_rect j) (go_list l)
            end in
        let fix go_list' (l : list (String.string * t)) : P_list' l :=
            match l with
            | [] => P_nil'
            | (s, j) :: l => P_cons' s (json_rect j) (go_list' l)
            end in
        match j with
        | Null => P_null
        | Bool b => P_bool b
        | Num n => P_num n
        | String s => P_string s
        | Arr l => P_arr (go_list l)
        | Obj l => P_obj (go_list' l)
        end.
    End json_rect.

    (* Setting P_list := List.Forall P is a reasonable default. *)
    Section json_ind.
      Variable P : t -> Prop.

      Hypothesis P_null : P Null.
      Hypothesis P_bool : forall b, P (Bool b).
      Hypothesis P_num : forall n, P (Num n).
      Hypothesis P_string : forall s, P (String s).
      Hypothesis P_arr : forall l, List.Forall P l -> P (Arr l).
      Hypothesis P_obj : forall l, List.Forall (fun s => P (snd s)) l -> P (Obj l).

      Definition json_ind (j : t) : P j :=
        json_rect P (List.Forall P)
                  (List.Forall (fun s => P (snd s)))
                  (List.Forall_nil _) (fun j l Pt Pl => List.Forall_cons j Pt Pl)
                  (List.Forall_nil _)
                  (fun s j l Pj Pt => List.Forall_cons (s, j) Pj Pt)
                  P_null
                  P_bool
                  P_num
                  P_string
                  P_arr
                  P_obj
                  j.
    End json_ind.
  End json.

  Module tag.
    Inductive t :=
    | Null : t
    | Bool : bool -> t
    | Num : nat -> t
    | Str : String.string -> t
    | Arr : t
    | Obj : t.

    (* tag serializer *)
    Definition tag_serialize (t : t) : IOStreamWriter.t :=
      match t with
      | Null => serialize x00
      | Bool b => IOStreamWriter.append (fun _ => serialize x01)
                                        (fun _ => serialize b)
      | Num n => IOStreamWriter.append (fun _ => serialize x02)
                               (fun _ => serialize n)
      | Str s => IOStreamWriter.append (fun _ => serialize x03)
                               (fun _ => serialize s)
      | Arr => serialize x04
      | Obj => serialize x05
      end.

    Definition tag_deserialize : ByteListReader.t t :=
      tag <- deserialize ;;
          match tag with
          | x00 => ByteListReader.ret Null
          | x01 => Bool <$> deserialize
          | x02 => Num <$> deserialize
          | x03 => Str <$> deserialize
          | x04 => ByteListReader.ret Arr
          | x05 => ByteListReader.ret Obj
          | _ => ByteListReader.error
          end.

    Lemma tag_serialize_deserialize_id :
      serialize_deserialize_id_spec tag_serialize tag_deserialize.
    Proof using.
      intros.
      destruct a;
        unfold tag_serialize, tag_deserialize;
        cheerios_crush;
        unfold app;
        cheerios_crush.
    Qed.

    Instance tag_Serializer : Serializer t.
    Proof.
      exact {| serialize := tag_serialize;
               deserialize := tag_deserialize;
               serialize_deserialize_id := tag_serialize_deserialize_id |}.
    Qed.
    (* json <-> tree tag conversion *)

    Fixpoint json_treeify (j : json.t) : tree tag.t :=
      let fix obj_list_to_tree_list (l : list (String.string * json.t)) :=
          match l with
          | [] => []
          | (s, j) :: l => atom (tag.Str s)
                                :: json_treeify j
                                :: obj_list_to_tree_list l
          end
      in
      match j with
      | json.Null => atom tag.Null
      | json.Bool b => atom (tag.Bool b)
      | json.Num n => atom (tag.Num n)
      | json.String s => atom (tag.Str s)
      | json.Arr l => node (atom tag.Arr :: List.map json_treeify l)
      | json.Obj l => node (atom tag.Obj :: obj_list_to_tree_list l)
      end.

    Definition obj_list_to_tree_list :=
      fix obj_list_to_tree_list (l : list (String.string * json.t)) :
        list (tree tag.t) :=
        match l with
        | [] => []
        | (s, j) :: l => atom (tag.Str s) :: json_treeify j :: obj_list_to_tree_list l
        end.

    Fixpoint json_untreeify (t : tree tag.t) : option json.t :=
      let fix untreeify_list (l : list (tree tag.t)) : option (list json.t) :=
          match l with
          | [] => Some []
          | x :: l => match json_untreeify x with
                      | None => None
                      | Some y => match untreeify_list l with
                                  | None => None
                                  | Some l => Some (y :: l)
                                  end
                      end
          end in
      let fix untreeify_obj_list (l : list (tree tag.t)) :
            option (list (String.string * json.t)) :=
          match l with
          | [] => Some []
          | atom (tag.Str s) :: t :: l =>
            match json_untreeify t with
            | None => None
            | Some j => match untreeify_obj_list l with
                        | None => None
                        | Some l => Some ((s, j) :: l)
                        end
            end
          | _ => None
          end in
      match t with
      | atom (tag.Num n) => Some (json.Num n)
      | atom (tag.Bool b) => Some (json.Bool b)
      | atom (tag.Str s) => Some (json.String s)
      | node (atom tag.Arr :: l) => match untreeify_list l with
                                    | None => None
                                    | Some l => Some (json.Arr l)
                                    end
      | atom (tag.Null) => Some (json.Null)
      | node (atom tag.Obj :: l) => match untreeify_obj_list l with
                                    | None => None
                                    | Some l => Some (json.Obj l)
                                    end
      | _ => None
      end.

    Definition untreeify_obj_list :=
      fix untreeify_obj_list (l : list (tree tag.t)) :
        option (list (String.string * json.t)) :=
        match l with
        | [] => Some []
        | atom (tag.Str s) :: t :: l =>
          match json_untreeify t with
          | None => None
          | Some j => match untreeify_obj_list l with
                      | None => None
                      | Some l => Some ((s, j) :: l)
                      end
          end
        | _ => None
        end.

    Definition untreeify_list :=
      fix untreeify_list l : option (list json.t) :=
        match l with
        | [] => Some []
        | x :: l => match json_untreeify x with
                    | None => None
                    | Some y => match untreeify_list l with
                                | None => None
                                | Some l => Some (y :: l)
                                end
                    end
        end.

    Definition treeify_untreeify_aux (j : json.t) :=
      json_untreeify (json_treeify j) = Some j.

    Lemma treeify_untreeify_id : forall j : json.t,
        treeify_untreeify_aux j.
    Proof using.
      induction j using json.json_rect with
          (P_list := fun l => untreeify_list (List.map json_treeify l) = Some l)
          (P_list' := fun l => untreeify_obj_list (obj_list_to_tree_list l) = Some l);
        unfold treeify_untreeify_aux;
        auto;
        simpl;
        try (fold untreeify_list);
        try (fold untreeify_obj_list);
        try (fold obj_list_to_tree_list);
        try (rewrite IHj);
        try (rewrite IHj0);
        auto.
    Qed.

    Definition json_serialize (j : json.t) : IOStreamWriter.t :=
      serialize (json_treeify j).

    Definition json_deserialize : ByteListReader.t json.t :=
      j <- deserialize;;
        match json_untreeify j with
        | Some j => ByteListReader.ret j
        | None => ByteListReader.error
        end.

    Lemma json_serialize_deserialize_id :
      serialize_deserialize_id_spec json_serialize json_deserialize.
    Proof using.
      intros.
      unfold json_serialize, json_deserialize.
      cheerios_crush.
      rewrite treeify_untreeify_id.
      cheerios_crush.
    Qed.

    Instance json_Serializer : Serializer json.t.
    Proof.
      exact {| serialize := json_serialize;
               deserialize := json_deserialize;
               serialize_deserialize_id := json_serialize_deserialize_id |}.
    Qed.
  End tag.

  Definition string_eqb s s' :=
    if (String.string_dec s s') then true else false.

  Lemma string_eqb_true : forall s s', string_eqb s s' = true -> s = s'.
  Proof using.
    intros.
    unfold string_eqb in H.
    destruct (String.string_dec s s').
    + assumption.
    + congruence.
  Qed.

  Lemma string_eqb_refl : forall s, string_eqb s s = true.
  Proof using.
    intros.
    unfold string_eqb.
    destruct (String.string_dec s s); congruence.
  Qed.

  Fixpoint json_eqb (j j' : json.t) : bool :=
    let fix loop_arr (l l': list json.t) : bool :=
        match (l, l') with
        | ([], []) => true
        | (j :: l, j' :: l') => andb (json_eqb j j') (loop_arr l l')
        | (_, _) => false
        end in
    let fix loop_obj (l l' : list (String.string * json.t)) : bool :=
        match (l, l') with
        | ([], []) => true
        | ((s, j) :: l, (s', j') :: l') => andb (string_eqb s s')
                                                (andb (json_eqb j j')
                                                      (loop_obj l l'))
        | (_, _) => false
        end in
    match (j, j') with
    | (json.Null, json.Null) => true
    | (json.Bool b, json.Bool b') => Bool.eqb b b'
    | (json.Num n, json.Num n') => Nat.eqb n n'
    | (json.String s, json.String s') => string_eqb s s'
    | (json.Arr l, json.Arr l') => loop_arr l l'
    | (json.Obj l, json.Obj l') => loop_obj l l'
    | _ => false
    end.
  Definition loop_arr :=
    fix loop_arr (l l': list json.t) : bool :=
      match (l, l') with
      | ([], []) => true
      | (j :: l, j' :: l') => andb (json_eqb j j') (loop_arr l l')
      | (_, _) => false
      end.
  Definition loop_obj :=
    fix loop_obj (l l' : list (String.string * json.t)) : bool :=
      match (l, l') with
      | ([], []) => true
      | ((s, j) :: l, (s', j') :: l') => andb (string_eqb s s')
                                              (andb (json_eqb j j') (loop_obj l l'))
      | (_, _) => false
      end.

  Lemma json_eqb_eq : forall j j', json_eqb j j' = true -> j = j'.
  Proof using.
    induction j using json.json_rect with (P_list := fun l =>
                                                       forall l', loop_arr l l' = true -> l = l')
                                          (P_list' := fun l =>
                                                        forall l', loop_obj l l' = true -> l = l');
      unfold json_eqb.
    - intros.
      destruct l'.
      + reflexivity.
      + simpl in H. congruence.
    - intros.
      destruct l'.
      + simpl in H. congruence.
      + simpl in H.
        apply Bool.andb_true_iff in H.
        assert (j = t).
        * apply IHj. apply H.
        * assert (l = l').
          -- apply IHj0. apply H.
          -- now rewrite H0, H1.
    - intros.
      destruct l'.
      * reflexivity.
      * simpl in H. congruence.
    - intros.
      destruct l'; simpl in H.
      + congruence.
      + destruct p.
        apply Bool.andb_true_iff in H. destruct H.
        apply Bool.andb_true_iff in H0. destruct H0.
        assert (s = s0). now apply string_eqb_true in H.
        assert (j = t). apply (IHj t H0).
        assert (l = l'). apply (IHj0 _ H1).
        now rewrite H2, H3, H4.
    - destruct j'; try congruence.
    - destruct j'; try congruence.
      intros.
      apply Bool.eqb_prop in H.
      now rewrite H.
    - destruct j'; try congruence.
      intros.
      apply EqNat.beq_nat_true in H.
      now rewrite H.
    - destruct j'; try congruence.
      intros.
      apply string_eqb_true in H.
      now rewrite H.
    - fold json_eqb.
      fold loop_arr.
      destruct j'; try congruence.
      intros.
      apply IHj in H.
      now rewrite H.
    - fold json_eqb.
      fold loop_obj.
      destruct j'; try congruence.
      intros.
      apply IHj in H.
      now rewrite H.
  Qed.

  Lemma json_eq_eqb : forall j j', j = j' -> json_eqb j j' = true.
  Proof using.
    induction j using json.json_rect with (P_list := fun l => loop_arr l l = true)
                                          (P_list' := fun l => loop_obj l l = true).
    - reflexivity.
    - simpl.
      specialize IHj with j.
      rewrite IHj0.
      rewrite IHj; reflexivity.
    - reflexivity.
    - simpl.
      rewrite string_eqb_refl, IHj0.
      rewrite IHj; auto.
    - intros. now rewrite <- H.
    - intros. rewrite <- H. simpl.
      apply Bool.eqb_reflx.
    - intros. rewrite <- H. simpl.
      symmetry.
      apply EqNat.beq_nat_refl.
    - intros.
      rewrite <- H.
      simpl.
      apply string_eqb_refl.
    - intros.
      rewrite <- H.
      simpl.
      assumption.
    - intros.
      rewrite <- H.
      simpl.
      assumption.
  Qed.

  Lemma json_eq_dec : forall j j' : json.t, {j = j'} + {j <> j'}.
  Proof using.
    intros.
    destruct (json_eqb j j') eqn:H.
    + left. now apply json_eqb_eq.
    + right. intuition.
      rewrite json_eq_eqb in H;
        congruence.
  Qed.
End JSON.

Section Ptree.
  Context {A : Type} {sA : Serializer A}.

  Fixpoint tree_of_ptree (t : PositiveMap.t A) : tree (option A) :=
    match t with
    | PositiveMap.Leaf _ => atom None
    | PositiveMap.Node t1 v t2 =>
      node [tree_of_ptree t1; atom v; tree_of_ptree t2]
    end.

  Fixpoint ptree_of_tree (t : tree (option A)) : option (PositiveMap.t A) :=
    match t with
    | atom None => Some (PositiveMap.Leaf A)
    | node [t1; atom v; t2] =>
      match ptree_of_tree t1, ptree_of_tree t2 with
      | Some pt1, Some pt2 =>
        Some (PositiveMap.Node pt1 v pt2)
      | _, _ => None
      end
    | _ => None
    end.

  Lemma tree_of_ptree_ptree_of_tree :
    forall t, ptree_of_tree (tree_of_ptree t) = Some t.
  Proof using.
    induction t using PositiveMap.tree_ind; auto.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  Qed.

  Definition ptree_serialize (t : PositiveMap.t A) : IOStreamWriter.t :=
    serialize (tree_of_ptree t).

  Definition ptree_deserialize : ByteListReader.t (PositiveMap.t A) :=
    t <- deserialize;;
    match ptree_of_tree t with
    | Some pt => ByteListReader.ret pt
    | None => ByteListReader.error
    end.

  Lemma ptree_serialize_deserialize_id :
    serialize_deserialize_id_spec ptree_serialize ptree_deserialize.
  Proof using.
    unfold ptree_serialize, ptree_deserialize. cheerios_crush.
    rewrite tree_of_ptree_ptree_of_tree.
    cheerios_crush.
  Qed.

  Global Instance ptree_Serializer : Serializer (PositiveMap.t A) :=
    {| serialize := ptree_serialize;
       deserialize := ptree_deserialize;
       serialize_deserialize_id := ptree_serialize_deserialize_id
    |}.
End Ptree.
