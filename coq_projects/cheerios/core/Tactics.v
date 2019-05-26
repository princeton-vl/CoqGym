Require Import List.

Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Types.

Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

Hint Rewrite app_ass
     IOStreamWriter.empty_unwrap IOStreamWriter.putByte_unwrap
     IOStreamWriter.append_unwrap
     ByteListReader.getByte_unwrap ByteListReader.bind_unwrap ByteListReader.ret_unwrap
     ByteListReader.map_unwrap @ByteListReader.fold_unwrap : cheerios.
