open GenericLib
open Stdarg
open Error
open Pp
open Constrexpr
open Libnames

module CtrMap = Map.Make(Ord_ctr)

type weight_ast = 
  | WNum of int
  | WSize 

let weight_ast_to_string = function
  | WNum n -> string_of_int n
  | WSize  -> "size"
  
let weight_env : weight_ast CtrMap.t ref =
  Summary.ref ~name:"QC_weight_environ" CtrMap.empty

let weight_env_to_string () =
  let all = CtrMap.fold (fun ctr w acc -> (Printf.sprintf "%s : %s\n" 
                                                          (constructor_to_string ctr) 
                                                          (weight_ast_to_string w))::acc) 
                        !weight_env [] in
  String.concat "" all

let register_weights (l : (constructor * weight_ast) list) =
  List.iter (fun (c,w) -> weight_env := CtrMap.add c w !weight_env) l

let convert_constr_to_weight c = 
  match c with 
  | { CAst.v = CPrim (Numeral (i,s)) } -> 
     if s then WNum (int_of_string i)
     else failwith "QC: Numeric weights should be greater than 0."
  | { CAst.v = CRef (r, _) } -> 
     if string_of_qualid r = "size" then WSize
     else failwith "QC: Expected number or 'size'."

let convert_constr_to_cw_pair c : (constructor * weight_ast) = 
  match c with 
  | {CAst.v = CNotation (_,([a],[[b]],_,_)) } -> begin
      let ctr = 
        match a with 
        | { CAst.v = CRef (r, _) } -> injectCtr (string_of_qualid r)
        | _ -> failwith "First argument should be a constructor name"
      in 
      let w = convert_constr_to_weight b in
      (ctr,w)
    end
  | _ -> failwith "Not a pair?"

let register_weights_object = 
  Libobject.declare_object
    {(Libobject.default_object ("QC_register_weights")) with
       cache_function = (fun (_,ws) -> register_weights ws);
       load_function = (fun _ (_,ws) -> register_weights ws)}

let lookup_weight ctr size_var = 
  try match CtrMap.find ctr !weight_env with
      | WNum n -> gInt n
      | WSize  -> gSucc (gVar (size_var))
  with Not_found -> gInt 1

VERNAC COMMAND EXTEND QuickChickWeights CLASSIFIED AS SIDEFF
  | ["QuickChickWeights" constr(c)] -> 
     [
       let weight_assocs = 
         match c with 
         | { CAst.v = CNotation (_,([a],[b],_,_)) } -> begin
             let c = convert_constr_to_cw_pair a in
             let cs = List.map convert_constr_to_cw_pair b in
             c :: cs
           end
         | _ -> failwith "QC: Expected list of constructor -> weights"
       in 
       msg_debug (str "Current weights: " ++ fnl ());
       msg_debug (str (weight_env_to_string ()) ++ fnl ());
       Lib.add_anonymous_leaf (register_weights_object weight_assocs)
     ]
END;;

(*
let s1' = Names.string_of_id s1 in
       let s2' = Names.string_of_id s2 in 
       Lib.add_anonymous_leaf (set_debug_flag s1' (s1',s2')) ]
 *)
