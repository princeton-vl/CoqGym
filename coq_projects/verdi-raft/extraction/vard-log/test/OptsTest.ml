open OUnit2
open ListLabels
open Util

let tear_down () text_ctxt =
  Opts.cluster := Opts.cluster_default;
  Opts.me := Opts.me_default;
  Opts.port := Opts.port_default;
  Opts.dbpath := Opts.dbpath_default;
  Opts.debug := Opts.debug_default

let test_parse_correct_line test_ctxt =
  Opts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal 0 !Opts.me;
  assert_equal 8000 !Opts.port;
  assert_equal [(0, ("localhost", 9000)); (1, ("localhost", 9001)); (2, ("localhost", 9002))] !Opts.cluster;
  assert_equal "/tmp/vard-8000" !Opts.dbpath;
  assert_equal false !Opts.debug

let test_validate_correct_line test_ctxt =
  Opts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal () (Opts.validate ())

let test_validate_missing_me text_ctxt =
  Opts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_raises (Arg.Bad "Please specify the node name -me") Opts.validate

let test_validate_empty_cluster text_ctxt =
  Opts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000");
  assert_raises (Arg.Bad "Please specify at least one -node") Opts.validate

let test_validate_me_not_cluster_member text_ctxt =
  Opts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_raises (Arg.Bad "0 is not a member of this cluster") Opts.validate

let test_list =
  ["parse correct line", test_parse_correct_line;
   "validate correct line", test_validate_correct_line;
   "validate missing me", test_validate_missing_me;
   "validate empty cluster", test_validate_empty_cluster;
   "validate me not member of cluster", test_validate_me_not_cluster_member;
  ]
  
let tests =
  "Opts" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
