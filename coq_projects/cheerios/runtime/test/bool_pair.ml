type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type SERIALIZER =
 sig
  type t

  val empty : t

  val append : t -> t -> t

  val putBit : bool -> t

  val unwrap : t -> bool list
 end

module Serializer =
 struct
  type t = Serializer_primitives.serializer

  (** val empty : t **)

  let empty = Serializer_primitives.empty

  (** val putBit : bool -> t **)

  let putBit = Serializer_primitives.putBit

  (** val append : t -> t -> t **)

  let append = Serializer_primitives.append

  (** val unwrap : t -> bool list **)

  let unwrap = Obj.magic

  (** val empty_unwrap : __ **)

  let empty_unwrap =
    __

  (** val putBit_unwrap : __ **)

  let putBit_unwrap =
    __

  (** val append_unwrap : __ **)

  let append_unwrap =
    __
 end

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

module Deserializer =
 struct
  type 'a t = 'a Serializer_primitives.deserializer

  (** val unwrap : 'a1 t -> 'a1 t **)

  let unwrap = Obj.magic

  (** val getBit : bool list -> (bool * bool list) option **)

  let getBit = Serializer_primitives.getBit

  (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

  let bind = Serializer_primitives.bind

  (** val ret : 'a1 -> 'a1 t **)

  let ret = Serializer_primitives.ret

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f d =
    bind d (fun a -> ret (f a))

  (** val getBit_unwrap : __ **)

  let getBit_unwrap =
    __

  (** val bind_unwrap : __ **)

  let bind_unwrap =
    __

  (** val fold :
      (bool -> 'a1 -> ('a1, 'a2) Serializer_primitives.fold_state) -> 'a1 -> bool list ->
      ('a2 * bool list) option **)

  let rec fold = Serializer_primitives.fold

  (** val ret_unwrap : __ **)

  let ret_unwrap =
    __

  (** val map_unwrap : __ **)

  let map_unwrap =
    __

  (** val fold_unwrap : __ **)

  let fold_unwrap =
    __
 end

type 'a serializer = { serialize : ('a -> Serializer.t); deserialize : 'a Deserializer.t }

(** val serialize : 'a1 serializer -> 'a1 -> Serializer.t **)

let serialize x = x.serialize

(** val deserialize : 'a1 serializer -> 'a1 Deserializer.t **)

let deserialize x = x.deserialize

(** val bool_Serializer : bool serializer **)

let bool_Serializer =
  { serialize = Serializer.putBit; deserialize = Deserializer.getBit }

(** val pair_serialize :
    'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) -> Serializer.t **)

let pair_serialize sA sB = function
| (a, b) -> Serializer.append (sA.serialize a) (sB.serialize b)

(** val pair_deserialize :
    'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) Deserializer.t **)

let pair_deserialize sA sB =
  Deserializer.bind sA.deserialize (fun a ->
    Deserializer.bind sB.deserialize (fun b -> Deserializer.ret (a, b)))

(** val pair_Serializer : 'a1 serializer -> 'a2 serializer -> ('a1 * 'a2) serializer **)

let pair_Serializer sA sB =
  { serialize = (pair_serialize sA sB); deserialize = (pair_deserialize sA sB) }

(** val serialize_bool_pair : (bool * bool) -> Serializer.t **)

let serialize_bool_pair =
  (pair_Serializer bool_Serializer bool_Serializer).serialize

(** val deserialize_bool_pair : (bool * bool) Deserializer.t **)

let deserialize_bool_pair =
  (pair_Serializer bool_Serializer bool_Serializer).deserialize
