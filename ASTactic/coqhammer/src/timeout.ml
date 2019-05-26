(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml
   runtime. This file contains a timeout implementation based on
   Unix.fork and Unix.sleep. See:

   https://caml.inria.fr/mantis/view.php?id=7709
   https://caml.inria.fr/mantis/view.php?id=4127
   https://github.com/coq/coq/issues/7430
   https://github.com/coq/coq/issues/7408

*)

(* ptimeout implements timeout using fork and sleep *)
let ptimeout n tac =
  let pid = Unix.fork () in
  if pid = 0 then
    begin (* the worker *)
      Proofview.tclOR
        (Proofview.tclBIND tac (fun _ -> exit 0))
        (fun _ -> exit 1)
    end
  else
    begin
      let pid2 = Unix.fork () in
      if pid2 = 0 then
        begin (* the watchdog *)
          Unix.sleep n;
          Unix.kill pid Sys.sigterm;
          exit 0
        end;
      let clean () =
        ignore (try Unix.kill pid2 Sys.sigterm with _ -> ())
      in
      try
        let (_, status) = Unix.waitpid [] pid
        in
        match status with
        | Unix.WEXITED 0 -> clean (); tac
        | _ -> clean(); Proofview.tclZERO Proofview.Timeout
      with
      | _ -> clean (); Proofview.tclZERO Proofview.Timeout
    end
