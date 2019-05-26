Require Import Cheerios.Cheerios.
Require Extraction.

Extract Inlined Constant fin_serialize => "(fun _ i -> Serializer_primitives.putInt (Int32.of_int i))".
Extract Inlined Constant fin_deserialize => "(fun _ -> Serializer_primitives.map Int32.to_int Serializer_primitives.getInt)".
