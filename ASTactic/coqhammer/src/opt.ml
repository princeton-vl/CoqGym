open Goptions

let predictions_num = ref 1024

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Predictions";
      optkey=["Hammer";"Predictions"];
      optread=(fun ()->Some !predictions_num);
      optwrite=
   (function
        None -> predictions_num := 128
      |	Some i -> predictions_num := (max i 16))}
  in
  declare_int_option gdopt

let scrush_timelimit = ref 1

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer CrushLimit";
      optkey=["Hammer";"CrushLimit"];
      optread=(fun ()->Some !scrush_timelimit);
      optwrite=
   (function
        None -> scrush_timelimit := 1
      |	Some i -> scrush_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let atp_timelimit = ref 10

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer ATPLimit";
      optkey=["Hammer";"ATPLimit"];
      optread=(fun ()->Some !atp_timelimit);
      optwrite=
   (function
        None -> atp_timelimit := 10
      |	Some i -> atp_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let reconstr_timelimit = ref 10

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer ReconstrLimit";
      optkey=["Hammer";"ReconstrLimit"];
      optread=(fun ()->Some !reconstr_timelimit);
      optwrite=
   (function
        None -> reconstr_timelimit := 10
      |	Some i -> reconstr_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let minimize_threshold = ref 6

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer MinimizationThreshold";
      optkey=["Hammer";"MinimizationThreshold"];
      optread=(fun ()->Some !minimize_threshold);
      optwrite=
   (function
        None -> minimize_threshold := 0
      |	Some i -> minimize_threshold := (max i 0))}
  in
  declare_int_option gdopt

let gs_mode = ref 8

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer GSMode";
      optkey=["Hammer";"GSMode"];
      optread=(fun ()->Some !gs_mode);
      optwrite=
   (function
        None -> gs_mode := 16
      |	Some i -> gs_mode := i)}
  in
  declare_int_option gdopt

let eprover_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Eprover";
      optkey=["Hammer";"Eprover"];
      optread=(fun () -> !eprover_enabled);
      optwrite=(fun b -> eprover_enabled := b)}
  in
  declare_bool_option gdopt

let vampire_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Vampire";
      optkey=["Hammer";"Vampire"];
      optread=(fun () -> !vampire_enabled);
      optwrite=(fun b -> vampire_enabled := b)}
  in
  declare_bool_option gdopt

let z3_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Z3";
      optkey=["Hammer";"Z3"];
      optread=(fun () -> !z3_enabled);
      optwrite=(fun b -> z3_enabled := b)}
  in
  declare_bool_option gdopt

let cvc4_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer CVC4";
      optkey=["Hammer";"CVC4"];
      optread=(fun () -> !cvc4_enabled);
      optwrite=(fun b -> cvc4_enabled := b)}
  in
  declare_bool_option gdopt

let predict_path = ref "predict"

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer PredictPath";
      optkey=["Hammer";"PredictPath"];
      optread=(fun () -> !predict_path);
      optwrite=(fun s -> predict_path := s)}
  in
  declare_string_option gdopt

let predict_method = ref "knn"

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer PredictMethod";
      optkey=["Hammer";"PredictMethod"];
      optread=(fun () -> !predict_method);
      optwrite=
        begin fun s ->
          if s = "knn" || s = "nbayes" || s = "rforest" then
            predict_method := s
          else
            Msg.error "Invalid method. Available predict methods: knn, nbayes."
        end}
  in
  declare_string_option gdopt

let parallel_mode = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Parallel";
      optkey=["Hammer";"Parallel"];
      optread=(fun () -> !parallel_mode);
      optwrite=(fun b -> parallel_mode := b)}
  in
  declare_bool_option gdopt

let debug_mode = ref false

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Debug";
      optkey=["Hammer";"Debug"];
      optread=(fun () -> !debug_mode);
      optwrite=(fun b -> debug_mode := b)}
  in
  declare_bool_option gdopt

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer ClosureGuards";
      optkey=["Hammer";"ClosureGuards"];
      optread=(fun () -> !Coq_transl_opts.opt_closure_guards);
      optwrite=(fun b -> Coq_transl_opts.opt_closure_guards := b)}
  in
  declare_bool_option gdopt

let filter_program = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer FilterProgram";
      optkey=["Hammer";"FilterProgram"];
      optread=(fun () -> !filter_program);
      optwrite=(fun b -> filter_program := b)}
  in
  declare_bool_option gdopt

let filter_classes = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer FilterClasses";
      optkey=["Hammer";"FilterClasses"];
      optread=(fun () -> !filter_classes);
      optwrite=(fun b -> filter_classes := b)}
  in
  declare_bool_option gdopt

let filter_hurkens = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer FilterHurkens";
      optkey=["Hammer";"FilterHurkens"];
      optread=(fun () -> !filter_hurkens);
      optwrite=(fun b -> filter_hurkens := b)}
  in
  declare_bool_option gdopt

let search_blacklist = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optname="Hammer Blacklist";
      optkey=["Hammer";"Blacklist"];
      optread=(fun () -> !search_blacklist);
      optwrite=(fun b -> search_blacklist := b)}
  in
  declare_bool_option gdopt
