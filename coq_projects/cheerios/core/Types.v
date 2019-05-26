Require Import List.
Import ListNotations.

Inductive fold_state S A :=
| Done (a : A)
| More (s : S)
| Error.
Arguments Done {_} {_} _.
Arguments More {_} {_} _.
Arguments Error {_} {_}.

Inductive byte :=
| x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c
| x0d | x0e | x0f | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19
| x1a | x1b | x1c | x1d | x1e | x1f | x20 | x21 | x22 | x23 | x24 | x25 | x26
| x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f | x30 | x31 | x32 | x33
| x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f | x40
| x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d
| x4e | x4f | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a
| x5b | x5c | x5d | x5e | x5f | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67
| x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f | x70 | x71 | x72 | x73 | x74
| x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f | x80 | x81
| x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e
| x8f | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b
| x9c | x9d | x9e | x9f | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8
| xa9 | xaa | xab | xac | xad | xae | xaf | xb0 | xb1 | xb2 | xb3 | xb4 | xb5
| xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf | xc0 | xc1 | xc2
| xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf
| xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc
| xdd | xde | xdf | xe0 | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9
| xea | xeb | xec | xed | xee | xef | xf0 | xf1 | xf2 | xf3 | xf4 | xf5 | xf6
| xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff.

Module Type WRITER.
  Parameter t : Type.
  Parameter wire : Type.
  Parameter wire_eq_dec : forall w w' : wire, {w = w'}+{w <> w'}.
  Parameter out_channel : Type.
  Parameter in_channel : Type.

  Parameter empty : t.
  Parameter append : (unit -> t) -> (unit -> t) -> t.
  Parameter putByte : byte -> t.

  (* For proof only! Do not call from serializers. *)
  Parameter unwrap : t -> list byte.
  Parameter wire_wrap : t -> wire.
  Parameter wire_unwrap : wire -> list byte.

  Parameter out_channel_wrap : t -> out_channel.
  Parameter channel_send : out_channel -> in_channel.
  Parameter in_channel_unwrap : in_channel -> list byte.
  Parameter channel_wrap_unwrap : forall x,
      in_channel_unwrap (channel_send (out_channel_wrap x)) = unwrap x.

  Parameter empty_unwrap : unwrap empty = [].
  Parameter append_unwrap :
    forall x y : unit -> t,
      unwrap (append x y) = unwrap (x tt) ++ unwrap (y tt).
  Parameter putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
  Parameter wire_wrap_unwrap : forall x, wire_unwrap (wire_wrap x) = unwrap x.
End WRITER.

Module Type READER.
  Parameter t : Type -> Type.

  Parameter getByte : t byte.
  Parameter unwrap : forall {A}, t A -> list byte -> option (A * list byte).

  Parameter getByte_unwrap : forall l,
      unwrap getByte l = match l with
                         | [] => None
                         | a :: l => Some (a, l)
                         end.

  Parameter bind : forall {A B}, t A -> (A -> t B) -> t B.
  Parameter ret : forall {A}, A -> t A.
  Parameter map : forall {A B}, (A -> B) -> t A -> t B.
  Parameter error : forall {A}, t A.

  Parameter fold : forall {S A},
      (byte -> S -> fold_state S A) -> S -> t A.

  Parameter bind_unwrap : forall A B (m : t A)
                             (f : A -> t B) bytes,
      unwrap (bind m f) bytes = match unwrap m bytes with
                                | None => None
                                | Some (v, bytes) => unwrap (f v) bytes
                              end.
  Parameter ret_unwrap : forall A (x: A) bytes, unwrap (ret x) bytes = Some (x, bytes).

  Parameter map_unwrap: forall A B (f: A -> B) (d: t A) bin,
      unwrap (map f d) bin =
      match (unwrap d bin) with
      | None => None
      | Some (v, bin) => Some (f v, bin)
      end.

  Parameter fold_unwrap : forall {S A : Type}
                             (f : byte -> S -> fold_state S A) (s : S) l,
      unwrap (fold f s) l =
      match l with
      | [] => None
      | b :: l => match f b s with
                  | Done a => Some (a, l)
                  | More s => unwrap (fold f s) l
                  | Error => None
                  end
      end.
End READER.
