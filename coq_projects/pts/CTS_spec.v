
  Record CTS_spec : Type := 
    {cts_axiom : relation sort;
     cts_rules : sort -> sort -> sort -> Prop;
     universes : relation sort;
     head_reduct : Basic_rule}.


  Variable the_CTS : CTS_spec.


  (* open the_CTS *)
  Let axiom := cts_axiom the_CTS.
  Let rule := cts_rules the_CTS.
  Let univ := universes the_CTS.
  Let hd_rule := head_reduct the_CTS.

  Let hdr := Rule hd_rule.
  Let lifts : R_lift hdr := R_lifts hd_rule.
  Let substs : R_subst hdr := R_substs hd_rule.
  Let stable : R_stable_env hdr := R_stable hd_rule.

  Let red_step := ctxt hdr.


  (* short-cuts *)
  Let stable_conv : R_stable_env (conv hdr).
Proof R_rst_stable red_step (ctxt_stable hdr stable).

  Hint Resolve stable: pts.