(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

open Ltac_plugin

(* XXX: Move to ser_cmap *)
type 'a cstring_map = 'a CString.Map.t

let from_bindings bl =
  let open CString.Map in
  List.fold_left (fun m (k,v) -> add k v m) empty bl

let cstring_map_of_sexp f s =
  let s_f = Sexplib.Conv.pair_of_sexp string_of_sexp f in
  let bl  = list_of_sexp s_f s                         in
  from_bindings bl

let sexp_of_cstring_map f m =
  let s_f = Sexplib.Conv.sexp_of_pair sexp_of_string f in
  let l   = CString.Map.bindings m                     in
  sexp_of_list s_f l

type treenode =
  [%import: Profile_ltac.treenode
  [@with CString.Map.t   := cstring_map;
         CString.Map.key := string
  ]]
  [@@deriving sexp]
