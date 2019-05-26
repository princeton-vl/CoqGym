(* Writing already translated problems to FOF TPTP format *)

open Coqterms
open Coq_transl_opts
open Hhlib

let const_hash = Hashtbl.create 100
let pred_hash = Hashtbl.create 100
let mconst_hash = Hashtbl.create 100
let tconst_hash = Hashtbl.create 100

(******************************************************************************)
(* Constant hashes *)

let rec add_consts_to_hash tm =
  match tm with
  | Var(_) ->
      ()
  | Const(c) ->
      Hashtbl.replace const_hash c 0
  | App(_) ->
      begin
        let (x, args) = flatten_app tm
        in
        begin
          match x with
          | Const(c) ->
            let n = List.length args
            and m = try Hashtbl.find const_hash c with Not_found -> Pervasives.max_int
            in
            if n < m then
              Hashtbl.replace const_hash c n
          | _ ->
            ()
        end;
        List.iter add_consts_to_hash args
      end
  | Quant(_, (_, _, body)) ->
      add_consts_to_hash body
  | Equal(x, y) ->
      add_consts_to_hash x;
      add_consts_to_hash y
  | _ -> failwith "not FOL"

let rec prune_pred_hash tm =
  assert (is_fol tm);
  match tm with
  | Const(c) ->
    Hashtbl.replace pred_hash c (-1)
  | Equal(x, y) ->
    prune_pred_hash x;
    prune_pred_hash y
  | App(_) when opt_multiple_arity_optimization ->
    let (x, args) = flatten_app tm
    in
    begin
      match x with
      | Const(c) ->
        let n = List.length args
        in
        assert (n > 0);
        Hashtbl.replace pred_hash (c ^ "_$a" ^ string_of_int n) (-1)
      | _ ->
        ()
    end;
    List.iter prune_pred_hash args
  | App(x, y) ->
    prune_pred_hash x;
    prune_pred_hash y
  | Var(_) ->
    ()
  | _ ->
    print_coqterm tm;
    failwith "prune_pred_hash"

let rec build_pred_hash tm =
  assert (is_fol tm);
  match tm with
  | Quant(_, (_, ty, body)) ->
    assert (ty = type_any);
    build_pred_hash body
  | App(App(Const(c), x), y) when is_bin_logop c ->
    build_pred_hash x;
    build_pred_hash y
  | App(Const("~"), x) ->
    build_pred_hash x
  | App(_) ->
    let (x, args) = flatten_app tm
    in
    begin
      match x with
      | Const(c) when c <> "$HasType" ->
        let n = List.length args
        in
        assert (n > 0);
        if opt_multiple_arity_optimization then
          begin
            let c2 = c ^ "_$a" ^ string_of_int n
            in
            if not (Hashtbl.mem pred_hash c2) then
              Hashtbl.replace pred_hash c2 n
          end
        else
          let m = try Hashtbl.find pred_hash c with Not_found -> Hashtbl.add pred_hash c n; n
          in
          if n <> m then
            Hashtbl.replace pred_hash c (-1)
      | _ ->
        ()
    end;
    List.iter prune_pred_hash args
  | Const(c) ->
    begin
      try
        let n = Hashtbl.find pred_hash c
        in
        if n <> 0 && not opt_multiple_arity_optimization then
          Hashtbl.replace pred_hash c (-1)
      with Not_found ->
        Hashtbl.add pred_hash c 0
    end
  | _ ->
    prune_pred_hash tm

let rec build_mconst_hash tm =
  match tm with
  | Var(_) | Const(_) ->
      ()
  | App(_) ->
      begin
        let (x, args) = flatten_app tm
        in
        begin
          match x with
          | Const(c) when not (is_logop c) && c <> "$HasType" ->
            let n = List.length args
            in
            Hashtbl.replace mconst_hash (c ^ "_$a" ^ string_of_int n) (n, c)
          | _ ->
            ()
        end;
        List.iter build_mconst_hash args
      end
  | Quant(_, (_, _, body)) ->
      build_mconst_hash body
  | Equal(x, y) ->
      build_mconst_hash x;
      build_mconst_hash y
  | _ -> failwith "not FOL"

let rec build_tconst_hash tm =
  match tm with
  | Var(_) | Const(_) ->
      ()
  | App(App(Const("$HasType"), _), ty) ->
      begin
        let (x, args) = flatten_app ty
        in
        begin
          match x with
          | Const(c) ->
            Hashtbl.replace tconst_hash c (List.length args)
          | _ ->
            ()
        end
      end
  | App(App(Const(c), x), y) when is_bin_logop c ->
    build_tconst_hash x;
    build_tconst_hash y
  | App(Const("~"), x) ->
    build_tconst_hash x
  | Quant(_, (_, _, body)) ->
    build_tconst_hash body
  | App(_, _) | Equal(_, _) ->
    ()
  | _ -> failwith "not FOL"

(******************************************************************************)
(* Escaping *)

(* Escape characters not accepted by the TPTP format. *)
let escape_to_hex s =
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n + (match String.unsafe_get s i with
     'a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
    |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
    |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' -> 1
    |'_' -> 2 | _ -> 3)
  done;
  if !n = String.length s then s else begin
    let s' = Bytes.create !n in
    n := 0;
    for i = 0 to String.length s - 1 do begin
      match String.unsafe_get s i with
      ('a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
      |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
      |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' as c) -> Bytes.unsafe_set s' !n c
      | '_' -> Bytes.unsafe_set s' !n '_'; incr n; Bytes.unsafe_set s' !n '_'
      | c -> let c = Char.code c in
             Bytes.unsafe_set s' !n '_'; incr n;
             Bytes.unsafe_set s' !n (Printf.sprintf "%x" (c / 16)).[0]; incr n;
             Bytes.unsafe_set s' !n (Printf.sprintf "%x" (c mod 16)).[0]
    end; incr n; done;
    Bytes.to_string s'
  end

let is_primed name =
  name.[0] = '\'' && name.[String.length name - 1] = '\''
let add_prime s =
  if is_primed s then s else "\'" ^ s ^ "\'"

let escape_special_thm s =
  Str.global_replace (Str.regexp_string "'") "\\'"
    (Str.global_replace (Str.regexp_string "\\") "\\\\" s)

let escape_var s = "V" ^ escape_to_hex s
let escape_const s = "c" ^ escape_to_hex s
let escape_thm s =
  if (s.[0] = '\'') then s
  else
    add_prime (escape_special_thm s)

(******************************************************************************)
(* Writing *)

let rec write_fol_rapp out write f args =
  match args with
  | [] ->
      f ()
  | h :: t ->
      out "happ(";
      write_fol_rapp out write f t;
      out ",";
      write h;
      out ")"

let write_fol_app out write f args = write_fol_rapp out write f (List.rev args)

let rec write_fol_term out tm =
  match tm with
  | Const(c) ->
      out (escape_const c)
  | Var(v) ->
      out (escape_var v)
  | Equal(x, y) ->
      out (escape_const "=");
      out "(";
      write_fol_term out x;
      out ", ";
      write_fol_term out y;
      out ")"
  | App(_) ->
      let (x, args) = flatten_app tm
      in
      begin
        match x with
        | Const(c) ->
          if opt_multiple_arity_optimization ||
            (opt_hastype && Hashtbl.mem tconst_hash c &&
               Hashtbl.find tconst_hash c = List.length args)
          then
            write_fol_appterm out (c ^ "_$a" ^ string_of_int (List.length args)) args
          else
            let n =
              if opt_arity_optimization then
                Hashtbl.find const_hash c
              else
                0
            in
            assert (n <= List.length args);
            write_fol_papp out c n args
        | Var(_) ->
            write_fol_app out (write_fol_term out) (fun () -> write_fol_term out x) args
        | _ ->
            print_newline ();
            print_coqterm x;
            print_coqterm tm;
            failwith "write_fol_term (2)"
      end
  | _ ->
      print_newline ();
      print_coqterm tm;
      failwith "write_fol_term"

and write_fol_appterm out c args =
  out (escape_const c);
  match args with
  | [] -> ()
  | _ ->
    out "(";
    oiter out (write_fol_term out) "," args;
    out ")"

and write_fol_papp out c n args =
  write_fol_app out (write_fol_term out)
    begin fun () ->
      write_fol_appterm out c (Hhlib.take n args)
    end
    (Hhlib.drop n args)

let rec write_fol_formula out tm =
  assert (is_fol tm);
  match tm with
  | Quant(op, (vname, ty, body)) ->
      assert (ty = type_any);
      let (body2, vars) = flatten_fol_quant op tm
      in
      out op;
      out "[";
      oiter out out "," (List.map escape_var vars);
      out "]:";
      write_fol_formula out body2
  | Equal(x, y) ->
      out "(";
      write_fol_term out x;
      out " = ";
      write_fol_term out y;
      out ")"
  | App(App(Const(c), x), y) when is_bin_logop c ->
      out "(";
      write_fol_formula out x;
      out " ";
      out c;
      out " ";
      write_fol_formula out y;
      out ")"
  | App(Const("~"), x) ->
      out "~ (";
      write_fol_formula out x;
      out ")"
  | App(App(Const("$HasType"), y), ty) ->
    let (x, args) = flatten_app ty
    in
    begin
      match x with
      | Const(c) when Hashtbl.find tconst_hash c = List.length args ->
        write_fol_appterm out (c ^ "_$t") (args @ [y])
      | _ ->
        out "t(";
        write_fol_term out y;
        out ", ";
        write_fol_term out ty;
        out ")"
    end
  | App(_) when opt_predicate_optimization ->
      let (x, args) = flatten_app tm
      in
      begin
        match x with
        | Const(c) ->
          if opt_multiple_arity_optimization then
            begin
              let n = List.length args
              in
              let c2 = (c ^ "_$a" ^ string_of_int n)
              in
              if Hashtbl.find pred_hash c2 <> (-1) then
                write_fol_appterm out c2 args
              else
                begin
                  out "p(";
                  write_fol_term out tm;
                  out ")"
                end
            end
          else
            begin
              let n = Hashtbl.find pred_hash c
              in
              if n >= 0 then
                begin
                  assert (n = List.length args);
                  write_fol_appterm out c args
                end
              else
                begin
                  out "p(";
                  write_fol_term out tm;
                  out ")"
                end
            end
        | _ ->
          out "p(";
          write_fol_term out tm;
          out ")"
      end
  | _ ->
      out "p(";
      write_fol_term out tm;
      out ")"

let write_fol what out (name, formula) =
  out "fof(";
  out (escape_thm name);
  out ", ";
  out what;
  out ", ";
  write_fol_formula out formula;
  out ").\n"

let write_mult_arity_axioms out =
  let do_write k v n m =
    let rec hlp lst n =
      if n = 0 then
        begin
          let lst2 = List.map escape_var lst
          and args = List.map (fun name -> Var(name)) lst
          in
          out "![";
          oiter out out "," lst2;
          out "]:(";
          if opt_predicate_optimization && Hashtbl.find pred_hash k <> (-1) then
            begin
              out "p(";
              write_fol_papp out v m args;
              out ") <=> ";
              write_fol_appterm out k args
            end
          else
            begin
              write_fol_papp out v m args;
              out " = ";
              write_fol_appterm out k args
            end;
          out ")"
        end
      else
        let vname = "$X" ^ string_of_int n
        in
        hlp (vname :: lst) (n - 1)
    in
    out "fof(";
    out (escape_thm ("$adef_" ^ k));
    out ", axiom, ";
    hlp [] n;
    out ").\n"
  in
  Hashtbl.iter
    begin fun k (n, v) ->
      if opt_always_zero_arity && not (Hashtbl.mem tconst_hash v) then
        do_write k v n 0
      else
        let m = Hashtbl.find const_hash v
        in
        if n <> m then
          do_write k v n m
    end
    mconst_hash

let write_type_axioms out =
  let rec hlp c lst n =
    if n = 0 then
      begin
        let lst2 = List.map escape_var lst
        and args = List.map (fun name -> Var(name)) lst
        and v = escape_var "$Y"
        in
        let k = List.length args
        in
        let c2 =
          if k = 0 then c
          else if opt_multiple_arity_optimization then c ^ "_$a" ^ string_of_int k
          else c
        in
        out "![";
        oiter out out "," (lst2 @ [v]);
        out "]:(";
        write_fol_appterm out (c ^ "_$t") (args @ [Var("$Y")]);
        out " <=> ";
        out "t(";
        out v;
        out ", ";
        write_fol_appterm out c2 args;
        out "))"
      end
    else
      let vname = "$X" ^ string_of_int n
      in
      hlp c (vname :: lst) (n - 1)
  in
  Hashtbl.iter
    begin fun c n ->
      out "fof(";
      out (escape_thm ("$tdef_" ^ c));
      out ", axiom, ";
      hlp c [] n;
      out ").\n"
    end
    tconst_hash

let write_fol_problem out axioms thm =
  log 1 ("write_fol_problem: " ^ fst thm);
  Hashtbl.clear tconst_hash;
  Hashtbl.clear mconst_hash;
  Hashtbl.clear const_hash;
  Hashtbl.clear pred_hash;
  if opt_hastype then
    begin
      List.iter build_tconst_hash (List.map snd axioms);
      build_tconst_hash (snd thm)
    end;
  if opt_multiple_arity_optimization then
    begin
      List.iter build_mconst_hash (List.map snd axioms);
      build_mconst_hash (snd thm)
    end;
  if opt_arity_optimization || opt_multiple_arity_optimization then
    begin
      List.iter add_consts_to_hash (List.map snd axioms);
      add_consts_to_hash (snd thm)
    end;
  if opt_predicate_optimization then
    begin
      List.iter build_pred_hash (List.map snd axioms);
      build_pred_hash (snd thm)
    end;
  List.iter (write_fol "axiom" out) axioms;
  if opt_multiple_arity_optimization then
    begin
      write_mult_arity_axioms out
    end;
  if opt_hastype then
    begin
      write_type_axioms out
    end;
  write_fol "conjecture" out thm;
  Hashtbl.clear tconst_hash;
  Hashtbl.clear mconst_hash;
  Hashtbl.clear const_hash;
  Hashtbl.clear pred_hash
