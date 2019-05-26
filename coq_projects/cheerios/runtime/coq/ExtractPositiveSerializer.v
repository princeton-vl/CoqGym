Require Import Cheerios.ExtractPositiveSerializerDeps.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Definition positive_serialize : positive -> IOStreamWriter.t := serialize.

Definition positive_deserialize : ByteListReader.t positive := deserialize.

Definition positive_serialize_top : positive -> IOStreamWriter.wire :=
  fun p => serialize_top (serialize p).

Definition positive_deserialize_top : IOStreamWriter.wire -> option positive :=
  deserialize_top deserialize.

Extraction "runtime/test/positive_serializer.ml" positive_serialize positive_deserialize positive_serialize_top positive_deserialize_top.


