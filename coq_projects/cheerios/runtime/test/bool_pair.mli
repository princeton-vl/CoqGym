type __ = Obj.t

module type SERIALIZER =
 sig
  type t

  val empty : t

  val append : t -> t -> t

  val putBit : bool -> t

  val unwrap : t -> bool list
 end

module Serializer :
 SERIALIZER

module type DESERIALIZER =
 sig
  type 'x t

  val getBit : bool t

  val unwrap : 'a1 t -> bool list -> ('a1 * bool list) option

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val ret : 'a1 -> 'a1 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val fold : (bool -> 'a1 -> ('a1, 'a2) Serializer_primitives.fold_state) -> 'a1 -> 'a2 t
 end

module Deserializer :
 DESERIALIZER

type 'a serializer = { serialize : ('a -> Serializer.t); deserialize : 'a Deserializer.t }

val serialize : 'a1 serializer -> 'a1 -> Serializer.t

val deserialize : 'a1 serializer -> 'a1 Deserializer.t

val bool_Serializer : bool serializer

val pair_serialize : 'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) -> Serializer.t

val pair_deserialize : 'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) Deserializer.t

val pair_Serializer : 'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) serializer

val serialize_bool_pair : (bool * bool) -> Serializer.t

val deserialize_bool_pair : (bool * bool) Deserializer.t
