(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let debug = false
let ml_path = ref []

let add_ml_path path =
  ml_path := path :: !ml_path

(* Should improve *)
let map_serlib ml_mod =
  let plugin_name = Filename.(remove_extension (basename ml_mod)) in
  let supported = match plugin_name with
    (* Linked-in statically *)
    | "ltac_plugin"
    | "tauto_plugin" -> false
    (* Supported *)
    | "ground_plugin"
    | "recdef_plugin"
    | "newring_plugin" -> true
    | _ ->
      if debug then Format.eprintf "missing serlib: %s@\n%!" ml_mod;
      false
  in
  if supported
  then Some ("coq-serapi.serlib." ^ plugin_name)
  else None

let plugin_handler user_handler =
  let loader = Option.default Dynlink.loadfile user_handler in
  fun ml_mod ->
    try
      let _, ml_file = System.find_file_in_path ~warn:true !ml_path ml_mod in
      let () = loader ml_file in
      Option.iter (fun pkg -> Fl_dynload.load_packages [pkg]) (map_serlib ml_mod)
    with
      Dynlink.Error err ->
      let msg = Dynlink.error_message err in
      Format.eprintf "[sertop] Critical Dynlink error %s@\n%!" msg
