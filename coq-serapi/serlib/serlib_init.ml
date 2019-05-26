let init ~omit_loc ~omit_att ~exn_on_opaque =
  Ser_loc.omit_loc  := omit_loc;
  Ser_cAst.omit_att := omit_att;
  Serlib_base.exn_on_opaque := exn_on_opaque;
  ()
