type serializer
type 'a deserializer
type wire = bytes

type ('s, 'a) fold_state =
  | Done of 'a
  | More of 's
  | Error

(* serializer *)
val empty : serializer
val putByte : char -> serializer
val append : (unit -> serializer) -> (unit -> serializer) -> serializer
val putInt : int32 -> serializer
val putChars : char list -> serializer
val putBytes : bytes -> serializer
  
(* deserializer *)
val getByte : char deserializer
val getInt : int32 deserializer
val bind : 'a deserializer -> ('a -> 'b deserializer) -> 'b deserializer
val ret : 'a -> 'a deserializer
val fail : 'a deserializer
val map : ('a -> 'b) -> 'a deserializer -> 'b deserializer
val fold : (char -> 's -> ('s, 'a) fold_state) -> 's -> 'a deserializer
val getChars : int -> (char list) deserializer
val getBytes : bytes deserializer
  
(* wire *)
val wire_wrap : serializer -> wire
val size : wire -> int
val dump : wire -> unit
val deserialize_top : 'a deserializer -> wire -> 'a option

(* channel *)
val to_channel : serializer -> out_channel -> unit
val from_channel : 'a deserializer -> in_channel -> 'a option
