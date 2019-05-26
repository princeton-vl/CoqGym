(* Parallel function invocation (for Unix) *)

type ('a, 'b) sum = Inl of 'a | Inr of 'b | Err of int

let run_parallel (progress_fn : 'a -> unit) (sec_fn : unit -> unit)
    time (lst : (('a -> unit) -> 'b) list) =
  let piper, pipew = Unix.pipe () in
  let start f =
    let pid = Unix.fork () in
    let oc = Unix.out_channel_of_descr pipew in
    if pid = 0 then
      begin
        try
          Unix.close piper;
          let progress_sub_fn a =
            output_value oc (Inl a); flush oc
          in
          let ret = f progress_sub_fn in
          output_value oc (Inr ret);
          flush oc;
          exit 0
        with _ ->
          try output_value oc (Err (Unix.getpid ())); flush oc; exit 0
          with _ -> exit 0
      end;
    pid
  in
  let subprocesses = ref (List.map start lst) in
  let clean () =
    List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) !subprocesses;
    Unix.close piper;
    List.iter (fun i -> try ignore (Unix.waitpid [] i) with _ -> ()) !subprocesses;
    List.iter (fun i -> try Unix.kill i Sys.sigkill with _ -> ()) !subprocesses;
  in
  try
    Unix.close pipew;
    let rec select desc time =
      if time <= 0. then 0. else
        let (r, _, _) = Unix.select [desc] [] [] 1. in
        if r <> [] then time else (sec_fn (); select desc (time -. 1.))
    in
    Unix.set_nonblock piper;
    let inc = Unix.in_channel_of_descr piper in
    let rec ret time =
      if !subprocesses = [] then None else
        let interp time = function
          | Inl pr -> progress_fn pr; ret time
          | Inr ret -> Some (ret)
          | Err pid ->
             subprocesses := List.filter (fun i -> i <> pid) !subprocesses;
            ignore (Unix.waitpid [] pid);
            ret time
        in
        try interp time (input_value inc) with Sys_blocked_io | Unix.Unix_error _ ->
          let ntime = select piper time in
          if ntime > 0. then interp ntime (input_value inc) else None
    in
    let ret = ret time in
    clean ();
    (ret : 'b option)
  with
  | End_of_file ->
     clean (); None
  | e ->
     clean (); raise e
