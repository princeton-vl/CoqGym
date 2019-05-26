(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Names   = Ser_names

module Rel = struct

  module Declaration = struct

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Rel.Declaration.pt]
    [@@deriving sexp]

  end

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Rel.pt]
    [@@deriving sexp]

end

module Named = struct

  module Declaration = struct

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Named.Declaration.pt]
    [@@deriving sexp]

  end

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Named.pt]
    [@@deriving sexp]

end

module Compacted = struct

  module Declaration = struct

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Compacted.Declaration.pt]
    [@@deriving sexp]

  end

  type ('constr, 'types) pt =
    [%import: ('constr, 'types) Context.Compacted.pt]
    [@@deriving sexp]

end

