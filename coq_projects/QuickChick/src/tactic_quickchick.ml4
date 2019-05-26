open Ltac_plugin

DECLARE PLUGIN "quickchick_plugin"

open Pp
open Constrexpr

let quickchick_goal =
  Proofview.Goal.enter begin fun gl ->

    (* Convert goal to a constr_expr *)
    let c = Proofview.Goal.concl gl in
    let e = Proofview.Goal.env gl in
    let evd = Evd.from_env e in

    (* Make an evar with the goal as the type *)
    let evar_info = Evd.make_evar (Environ.named_context_val e) c in
    let evd, evar = Evd.new_evar evd evar_info in

    Printf.printf "So far so good\n"; flush stdout;
    
    (* Externalize it *)
    let ct = Constrextern.extern_constr false e evd (EConstr.mkEvar (evar , [||])) in

    (* Construct : show (quickCheck (_ : ct)) *)
    let qct =
      (CAst.make @@ CApp((None,QuickChick.quickCheck), [ct, None])) in    
    let sqct = CAst.make @@ CApp((None,QuickChick.show), [(qct,None)]) in

    Printf.printf "So far so good2\n"; flush stdout;

    (* From here on I've tried a couple of things. 
       Calling run_test directly with qct. Fails.
       Internalize here before calling define and run, fails.

       It always seems to fail in the 'interp' phase, with an 
       unknown existential variable error. So I'm probably doing something
       stupid with the evar maps *)
    let evd, to_run = Constrintern.interp_open_constr e evd sqct in

    Printf.printf "So far so good 2.5\n"; flush stdout;
    
    let s = QuickChick.define_and_run to_run e evd in

    Printf.printf "So far so good3\n"; flush stdout;
    
    match s with
    | Some bytes ->
       Tacticals.New.tclZEROMSG (str ("\n" ^ bytes) ++ fnl ())
    | None -> Tacticals.New.tclZEROMSG (str "Something went wrong. Report." ++ fnl ())

    end

    
    (*
    (* Admit a constant with that type *)
    let tmpid = QuickChick.fresh_name "temporary_constant" in
    let _interp_st = Vernacentries.interp (CAst.make @@ Vernacexpr.VernacExpr ([],
      (* TODO: NoDischarge or DoDischarge? *)
      Vernacexpr.VernacAssumption ((NoDischarge, Decl_kinds.Conjectural),
                        NoInline,
                        [
                          (false,
                           (
                             [CAst.make tmpid, None]
                           ,
                             ct
                           )
                          )
                        ]
                       ))) in

    (* I need to create an existential of type Checkable ct, and then
       call QuickChick.quickChick on that in the ast, before running
       QuickChick.runTest on the constr_expr. *)

    
    (*

       HACK (there *has* to be a better way): 
         (\x : Checkable ct -> x) _ *)

    let base = Names.Id.of_string "x" in
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    let xid = Namegen.next_ident_away_from base is_visible_name in

    let binder_list = [CLocalAssum ([CAst.make @@ Names.Name xid], Default Explicit, ct)]  in
    let f_body = CAst.make @@ CRef (CAst.make @@ Libnames.Ident xid,None) in
    let f = mkCLambdaN binder_list f_body in
    let hack_value = mkAppC (f , [ CAst.make @@ CEVarHole (None, Misctypes.IntroAnonymous, None) ] ) in
     *)
(*

    (* Refactor - needs to see internals... *)
    let base = Names.id_of_string "x" in
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    let xid = Namegen.next_ident_away_from base is_visible_name in


    let f_body = mkAppC (QuickChick.show, [mkAppC (QuickChick.quickCheck, [mkAppC (QuickChick.mk_ref "checker", [ CRef (Ident ((Loc.dummy_loc, xid)),None) ])])]) in
    let f = mkCLambdaN Loc.dummy_loc bind_list f_body in

    let env = Global.env () in
    let evd = Evd.from_env env in
    let (cf,evd) = Constrintern.interp_constr env evd f in

    let actual_term = Constr.mkApp (cf, Array.of_list [c]) in
 *)



(*
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let hyps = named_context_val (Proofview.Goal.env gl) in
    let store = Proofview.Goal.extra gl in
    let env = Proofview.Goal.env gl in
    let () = if check && mem_named_context_val id hyps then
      errorlabstrm "Tactics.introduction"
        (str "Variable " ++ pr_id id ++ str " is already declared.")
    in
    match kind_of_term (whd_evar sigma concl) with
    | Prod (_, t, b) -> unsafe_intro env store (LocalAssum (id, t)) b
    | LetIn (_, c, t, b) -> unsafe_intro env store (LocalDef (id, c, t)) b
    | _ -> raise (RefinerError IntroNeedsProduct)
  end }
 *)

TACTIC EXTEND quickchick
  | ["quickchick"] -> [ quickchick_goal ]
END;;
