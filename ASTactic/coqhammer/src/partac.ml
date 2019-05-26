(* Parallel invocation of tactics *)

let partac time lst0 cont =
  let rec pom lst pids =
    match lst with
    | [] ->
       let pid2 = Unix.fork () in
       if pid2 = 0 then
         begin (* the watchdog *)
           if time > 0 then
             begin
               Unix.sleep time;
               List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids
             end;
           exit 0
         end
       else
         let clean () =
           List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids;
           ignore (try Unix.kill pid2 Sys.sigterm with _ -> ());
           List.iter (fun i -> try ignore (Unix.waitpid [] i) with _ -> ()) pids
         in
         let n = List.length lst0 in
         let rec wait k =
           if k = 0 then
               begin
                 clean ();
                 cont (-1) (Proofview.tclZERO Proofview.Timeout)
               end
           else
             let (pid, status) = Unix.wait () in
             if pid = pid2 && time > 0 then
               begin
                 clean ();
                 cont (-1) (Proofview.tclZERO Proofview.Timeout)
               end
             else if List.mem pid pids then
               match status with
               | Unix.WEXITED 0 ->
                  begin
                    clean ();
                    let i = n - Hhlib.index pid pids - 1 in
                    cont i (List.nth lst0 i)
                  end
               | _ -> wait (k - 1)
             else
               wait k
         in
         wait n
    | tac :: t ->
       let pid = Unix.fork () in
       if pid = 0 then
         begin (* a worker *)
           Proofview.tclOR
             (Proofview.tclBIND tac (fun _ -> exit 0))
             (fun _ -> exit 1)
         end
       else
         pom t (pid :: pids)
  in
  pom lst0 []
