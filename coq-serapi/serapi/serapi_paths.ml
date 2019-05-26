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
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(******************************************************************************)
(* Coq Prelude Loading Defaults (to be improved)                              *)
(******************************************************************************)

let coq_loadpath_default ~implicit ~coq_path =
  let open Mltop in
  let mk_path prefix = coq_path ^ "/" ^ prefix in
  let mk_lp ~ml ~root ~dir ~implicit =
    { recursive = true;
      path_spec = VoPath {
          unix_path = mk_path dir;
          coq_path  = root;
          has_ml    = ml;
          implicit;
        };
    } in
  (* in 8.8 we can use Libnames.default_* *)
  let coq_root     = Names.DirPath.make [Libnames.coq_root] in
  let default_root = Libnames.default_root_prefix in
  [mk_lp ~ml:AddRecML ~root:coq_root     ~implicit       ~dir:"plugins";
   mk_lp ~ml:AddNoML  ~root:coq_root     ~implicit       ~dir:"theories";
   mk_lp ~ml:AddRecML ~root:default_root ~implicit:false ~dir:"user-contrib";
  ]

(******************************************************************************)
(* Generate a module name given a file                                        *)
(******************************************************************************)
let dirpath_of_file f =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let file = Filename.chop_extension (Filename.basename f) in
  let id = Names.Id.of_string file in
  Libnames.add_dirpath_suffix ldir0 id
