Require Import List.
Import ListNotations.
Require Vector String.

Require Import Cheerios.BasicSerializers.
Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Tactics.
Require Import Cheerios.Types.

Require Import StructTact.StructTactics.
Import DeserializerNotations.

(* These functions are either missing obvious implicits, or have
   implicit arguments that are not marked "maximally inserted", which
   means they cannot easily be used with map or fmap. *)
Arguments Some {_} _.
Arguments cons {_} _ _.
Arguments option_map {_ _} _ _.
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.

(* This section gives instances for various type constructors, including pairs
    and lists. *)

Section BasicCombinators.
  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.

  Definition option_serialize (x : option A) : IOStreamWriter.t :=
    match x with
    | Some a => IOStreamWriter.append (fun _ => serialize true)
                              (fun _ => serialize a)
    | None => serialize false
    end.

  Definition option_deserialize : ByteListReader.t (option A) :=
    b <- deserialize ;;
      match b with
      | true => Some <$> deserialize
      | false => ByteListReader.ret None
      end.

  Lemma option_serialize_deserialize_id :
    serialize_deserialize_id_spec option_serialize option_deserialize.
  Proof using.
    intros.
    unfold option_serialize, option_deserialize.
    destruct a;
      repeat (cheerios_crush; simpl).
  Qed.

  Global Instance option_Serializer : Serializer (option A).
  Proof.
    exact {| serialize := option_serialize;
             deserialize := option_deserialize;
             serialize_deserialize_id := option_serialize_deserialize_id |}.
  Qed.


  Definition pair_serialize (x : A * B) : IOStreamWriter.t :=
    let (a, b) := x in IOStreamWriter.append (fun _ => serialize a)
                                     (fun _ => serialize b).

  Definition pair_deserialize : ByteListReader.t (A * B) :=
    a <- deserialize ;;
      b <- deserialize ;;
      ByteListReader.ret (a, b).

  Lemma pair_serialize_deserialize_id :
    serialize_deserialize_id_spec pair_serialize pair_deserialize.
  Proof using.
    intros.
    unfold pair_serialize, pair_deserialize.
    destruct a.
    cheerios_crush.
  Qed.

  Global Instance pair_Serializer : Serializer (A * B).
  Proof.
    exact {| serialize := pair_serialize;
             deserialize := pair_deserialize;
             serialize_deserialize_id := pair_serialize_deserialize_id |}.
  Qed.

  Definition sum_serialize (x : A + B) : IOStreamWriter.t :=
    match x with
    | inl a => IOStreamWriter.append (fun _ => serialize true)
                             (fun _ => serialize a)
    | inr b => IOStreamWriter.append (fun _ => serialize false)
                             (fun _ => serialize b)
    end.

  Definition sum_deserialize : ByteListReader.t (A + B) :=
    b <- deserialize ;;
      match b with
      | true => inl <$> deserialize
      | false => inr <$> deserialize
      end.

  Lemma sum_serialize_deserialize_id :
    serialize_deserialize_id_spec sum_serialize sum_deserialize.
  Proof using.
    unfold sum_serialize, sum_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance sum_Serializer : Serializer (A + B).
  Proof.
    exact {| serialize := sum_serialize;
             deserialize := sum_deserialize;
             serialize_deserialize_id := sum_serialize_deserialize_id
          |}.
  Qed.

  Fixpoint list_serialize_rec (l : list A) : IOStreamWriter.t :=
    match l with
    | [] => IOStreamWriter.empty
    | a :: l' => IOStreamWriter.append (fun _ => serialize a)
                               (fun _ => list_serialize_rec l')
    end.

  Definition list_serialize (l : list A) : IOStreamWriter.t :=
    IOStreamWriter.append (fun _ => serialize (length l))
                  (fun _ => list_serialize_rec l).

  Fixpoint list_deserialize_rec (n : nat) : ByteListReader.t (list A) :=
    match n with
    | 0 => ByteListReader.ret []
    | S n' => cons <$> deserialize <*> list_deserialize_rec n'
    end.

  Definition list_deserialize : ByteListReader.t (list A) :=
    deserialize >>= list_deserialize_rec.

  Lemma list_serialize_deserialize_id_rec :
    forall l bin, ByteListReader.unwrap (list_deserialize_rec (length l))
                                (IOStreamWriter.unwrap (list_serialize_rec l) ++ bin)
                  = Some(l, bin).
  Proof using.
    intros.
    unfold list_serialize_rec.
    cheerios_crush. simpl.
    induction l.
    - simpl. cheerios_crush.
    - simpl.
      rewrite sequence_rewrite.
      rewrite ByteListReader.bind_unwrap.
      rewrite ByteListReader.map_unwrap.
      rewrite IOStreamWriter.append_unwrap.
      rewrite app_ass.
      rewrite serialize_deserialize_id.
      rewrite ByteListReader.bind_unwrap.
      rewrite IHl.
      cheerios_crush.
  Qed.

  Lemma serialize_snoc : forall (a : A) l,
      (IOStreamWriter.unwrap
         (list_serialize_rec (l ++ [a]))) =
      (IOStreamWriter.unwrap (list_serialize_rec l) ++ IOStreamWriter.unwrap (serialize a)).
  Proof using.
    intros.
    induction l.
    - simpl. cheerios_crush.
      rewrite app_nil_r.
      reflexivity.
    - simpl.
      cheerios_crush.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma list_serialize_deserialize_id :
    serialize_deserialize_id_spec list_serialize list_deserialize.
  Proof using.
    unfold list_serialize, list_deserialize.
    cheerios_crush.
    now rewrite list_serialize_deserialize_id_rec.
  Qed.

  Global Instance list_Serializer : Serializer (list A).
  Proof.
    exact {| serialize := list_serialize;
             deserialize := list_deserialize;
             serialize_deserialize_id := list_serialize_deserialize_id
          |}.
  Qed.

  Fixpoint vector_serialize {n} (v : Vector.t A n) : IOStreamWriter.t :=
    match v with
    | Vector.nil => IOStreamWriter.empty
    | Vector.cons a v' => IOStreamWriter.append (fun _ => serialize a)
                                        (fun _ => vector_serialize v')
    end.

  Fixpoint vector_deserialize {n} : ByteListReader.t (Vector.t A n) :=
    match n as n0 return ByteListReader.t (Vector.t A n0) with
    | 0 => ByteListReader.ret Vector.nil
    | S n' => a <- deserialize ;;
                v <- vector_deserialize ;;
                ByteListReader.ret (Vector.cons a v)
    end.

  Lemma vector_serialize_deserialize_id :
    forall n, serialize_deserialize_id_spec vector_serialize (@vector_deserialize n).
  Proof using.
    induction n; intros.
    - destruct a using Vector.case0. auto. unfold vector_serialize,  vector_deserialize.
      cheerios_crush.
    - destruct a using Vector.caseS'.
      simpl.
      cheerios_crush.
      rewrite IHn.
      cheerios_crush.
  Qed.

  Global Instance vector_Serializer n : Serializer (Vector.t A n).
  Proof.
    exact {| serialize := vector_serialize;
             deserialize := vector_deserialize;
             serialize_deserialize_id := vector_serialize_deserialize_id n
          |}.
  Qed.
End BasicCombinators.


(* This has to go here because it depends on having a serializer for
   lists available. *)

Fixpoint string_to_list s :=
  match s with
  | String.EmptyString => nil
  | String.String c s' => c :: (string_to_list s')
  end.

Fixpoint list_to_string l :=
  match l with
  | nil => String.EmptyString
  | h::l' => String.String h (list_to_string l')
  end.

Lemma string_to_list_to_string :
  forall s, list_to_string (string_to_list s) = s.
Proof.
  induction s; auto; simpl.
  now rewrite IHs.
Qed.

Definition string_serialize (s : String.string) :=
  serialize (string_to_list s).

Definition string_deserialize : ByteListReader.t String.string :=
  list_to_string <$> deserialize.

Lemma string_serialize_deserialize_id :
  serialize_deserialize_id_spec string_serialize string_deserialize.
Proof.
  unfold string_deserialize, string_serialize.
  cheerios_crush.
  now rewrite string_to_list_to_string.
Qed.

Instance string_Serializer : Serializer String.string.
Proof.
  exact {| serialize := string_serialize;
           deserialize := string_deserialize;
           serialize_deserialize_id := string_serialize_deserialize_id
        |}.
Qed.
