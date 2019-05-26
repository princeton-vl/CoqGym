open Util

let print_list (a_printer : out_channel -> 'a -> unit) (f : out_channel) (l : 'a list) =
  let rec go f = function
    | [] ->  ()
    | [a] ->  a_printer f a
    | a :: l -> Printf.fprintf f "%a; " a_printer a; go f l
  in Printf.fprintf f "[%a]" go l

let print_pair (a_printer : out_channel -> 'a -> unit) (b_printer : out_channel -> 'b -> unit)
               (f : out_channel) (x : 'a * 'b) =
  let (a, b) = x in
  Printf.fprintf f "(%a, %a)" a_printer a b_printer b

let print_nat f n = Printf.fprintf f "%d" (int_of_nat n)

let sprint_nat () n = Printf.sprintf "%d" (int_of_nat n)

let print_finmap print_key print_value f fm =
  let rec go f = function
    | [] -> ()
    | [(k, v)] -> Printf.fprintf f "%a |-> %a" print_key k (print_value k) v
    | (k, v) :: l -> Printf.fprintf f "%a |-> %a, " print_key k (print_value k) v; go f l
  in Printf.fprintf f "[%a]" go fm

let print_um print_key print_value f = function
  | Unionmap.UM.Undef -> Printf.fprintf f "Undef"
  | Unionmap.UM.Def fm -> print_finmap print_key print_value f fm

let print_heap print_key print_value f = function
  | Heap.Heap.Undef -> Printf.fprintf f "Undef"
  | Heap.Heap.Def fm -> print_finmap print_key print_value f fm

let print_ordered_sort_which_is_nat f o =
  print_nat f (Obj.magic o)

(*
let print_cstate f = function
  | TwoPhaseProtocol.TPCProtocol.States.CInit -> Printf.fprintf f "CInit"
  | TwoPhaseProtocol.TPCProtocol.States.CSentPrep _ -> Printf.fprintf f "CSentPrep"
  | TwoPhaseProtocol.TPCProtocol.States.CWaitPrepResponse _ -> Printf.fprintf f "CWaitPrepResponse"
  | TwoPhaseProtocol.TPCProtocol.States.CSentCommit _ -> Printf.fprintf f "CSentCommit"
  | TwoPhaseProtocol.TPCProtocol.States.CSentAbort _ -> Printf.fprintf f "CSentAbort"
  | TwoPhaseProtocol.TPCProtocol.States.CWaitAckCommit _ -> Printf.fprintf f "CWaitAckCommit"
  | TwoPhaseProtocol.TPCProtocol.States.CWaitAckAbort _ -> Printf.fprintf f "CWaitAckAbort"

let print_pstate f = function
  | TwoPhaseProtocol.TPCProtocol.States.PInit -> Printf.fprintf f "PInit"
  | TwoPhaseProtocol.TPCProtocol.States.PGotRequest _ -> Printf.fprintf f "PGotRequest"
  | TwoPhaseProtocol.TPCProtocol.States.PRespondedYes _ -> Printf.fprintf f "PRespondedYes"
  | TwoPhaseProtocol.TPCProtocol.States.PRespondedNo _ -> Printf.fprintf f "PRespondedNo"
  | TwoPhaseProtocol.TPCProtocol.States.PCommitted _ -> Printf.fprintf f "PCommitted"
  | TwoPhaseProtocol.TPCProtocol.States.PAborted _ -> Printf.fprintf f "PAborted"

let super_hacky_print_TPC_heap this k f (v : (Heap.__, Heap.__) Idynamic.idynamic) =
  let v = Idynamic.idyn_val v in
  match int_of_nat (Obj.magic k) with
  | 1 -> let (round, st) = Obj.magic v in
         let print_state = match int_of_nat this with
           | 0 -> (fun f x -> print_cstate f (Obj.magic x))
           | _ -> (fun f x -> print_pstate f (Obj.magic x))
         in
         Printf.fprintf f "{round = %a, state = %a}" print_nat round print_state st
  | 2 -> print_list (fun f (b, data) ->
             Printf.fprintf f "(%s, %a)" (if b then "true" else "false")
                            (print_list print_nat) data)
                    f (Obj.magic v)
  | n -> Printf.fprintf f "<value for %d>" n
 *)

let super_hacky_print_calc_heap this k f v =
  Printf.fprintf f "%s" "<heap>"

let super_hacky_print_system_heap = super_hacky_print_calc_heap

let print_dstatelet l f x =
  Printf.fprintf f "{dstate = %a; dsoup = <>}"
     (print_um print_ordered_sort_which_is_nat
         (fun node -> print_heap print_ordered_sort_which_is_nat
                                 (super_hacky_print_system_heap (Obj.magic node))))
     (Obj.magic x.State.dstate)

let print_state f x =
  Printf.fprintf f "%a" (print_um print_ordered_sort_which_is_nat print_dstatelet) x

let print_protocol f (x : Protocols.Protocols.protocol) =
  let l : Ordtype.Ordered.sort = x.Protocols.Protocols.plab in
  Printf.fprintf f "<protocol with label %a>" print_ordered_sort_which_is_nat l

let print_world f x =
  Printf.fprintf f "%a" (print_um print_ordered_sort_which_is_nat (fun _ -> print_protocol)) x
