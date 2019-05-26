open OUnit2
open ListLabels
open Util

let tear_down () text_ctxt = ()


let test_serialize_output_not_leader text_ctxt =
  assert_equal ("0aac4d743ccc4473a2e04f4072734722", Bytes.of_string "NotLeader 15")
    (VarDSerializedSerialization.serializeOutput (VarDRaftSerialized.NotLeader (Obj.magic (char_list_of_string "0aac4d743ccc4473a2e04f4072734722"), 15)))

let test_serialize_output_client_response test_ctxt =
  let o = VarDRaftSerialized.Response (char_list_of_string "awesome", None, None) in
  assert_equal ("0f5f33f091094d5db68a72e9f4cf9b14", Bytes.of_string "Response 34 awesome - -")
    (VarDSerializedSerialization.serializeOutput (VarDRaftSerialized.ClientResponse (Obj.magic (char_list_of_string "0f5f33f091094d5db68a72e9f4cf9b14"), 34, (Obj.magic o))))
  
let test_list =
  [
    "serialize NotLeader", test_serialize_output_not_leader;
    "serialize ClientResponse", test_serialize_output_client_response
  ]

let tests =
  "VarDSerializedSerialization" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
