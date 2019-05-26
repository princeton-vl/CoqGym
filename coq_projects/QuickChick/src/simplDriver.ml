open Libnames
open Util
open Constrexpr
open GenericLib
open SizeUtils
open Sized
open SizeMon
open SizeSMon
open SizeCorr

open ArbitrarySized

type derivable =
    Shrink
  | Show
  | GenSized
  | Sized
  | CanonicalSized
  | SizeMonotonic
  | SizedMonotonic
  | SizedCorrect

let derivable_to_string = function
  | Shrink -> "Shrink"
  | Show   -> "Show"
  | GenSized -> "GenSized"
  | Sized -> "Sized"
  | CanonicalSized -> "CanonicalSized"
  | SizeMonotonic -> "SizeMonotonic"
  | SizedMonotonic -> "SizedMonotonic"
  | SizedCorrect ->  "SizedCorrect"
  
let mk_instance_name der tn = 
  let prefix = derivable_to_string der in
  let strip_last s = List.hd (List.rev (Str.split (Str.regexp "[.]") s)) in
  var_to_string (fresh_name (prefix ^ strip_last tn))

let repeat_instance_name der tn = 
  let prefix = derivable_to_string der in
  let strip_last s = List.hd (List.rev (Str.split (Str.regexp "[.]") s)) in
  (prefix ^ strip_last tn)

(* Generic derivation function *)
let derive (cn : derivable) (c : constr_expr) (instance_name : string) (name1 : string) (name2 : string) =

  let (ty_ctr, ty_params, ctrs) =
    match coerce_reference_to_dt_rep c with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in

  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gTyParam ty_params in

  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  let ind_name = match c with
    | { CAst.v = CRef (r, _) } ->
         string_of_qualid r
    | _ -> failwith "Implement me for functions" 
  in

  let class_name = derivable_to_string cn in

  let size_config =
    { _ty_ctr  = ty_ctr
    ; _ctrs    = ctrs
    ; _coqTyCtr = coqTyCtr
    ; _coqTyParams = coqTyParams
    ; _full_dt  = full_dt
    ; _isCurrentTyCtr = sameTypeCtr ty_ctr
    } in

  let param_class_names = match cn with
    | Sized -> ["Sized"]
    | Shrink -> ["Shrink"]
    | Show -> ["Show"]
    | GenSized -> ["Gen"]
    | CanonicalSized -> ["CanonicalSized"]
    | SizeMonotonic -> ["GenMonotonic"]
    | SizedMonotonic -> ["Gen"]
    | SizedCorrect ->  ["GenMonotonicCorrect"; "CanonicalSized"]
  in

  let extra_arguments = match cn with
    | Show -> []
    | Shrink -> []
    | Sized -> []
    | GenSized -> []
    | CanonicalSized -> []
    | SizeMonotonic -> [(gInject "s", gInject "nat")]
    | SizedMonotonic -> []
    | SizedCorrect -> []
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments =
    let params =
      (List.concat (List.map (fun tp ->
                                ((gArg ~assumName:tp ~assumImplicit:true ()) ::
                                (List.map (fun name -> gArg ~assumType:(gApp (gInject name) [tp]) ~assumGeneralized:true ()) param_class_names))
                             ) coqTyParams))
    in
    let args = (List.map (fun (name, typ) -> gArg ~assumName:name ~assumType:typ ()) extra_arguments) in
    (* Add extra instance arguments *)
    params @ args
  in

  (* The instance type *)
  let instance_type iargs =
    match cn with
    | SizeMonotonic ->
      let (_, size) = take_last iargs [] in
      gApp ~explicit:true (gInject class_name) [full_dt; gApp (gInject ("arbitrarySized")) [gVar size]]
    | SizedMonotonic ->
      gApp ~explicit:true (gInject class_name) [full_dt; gInject ("arbitrarySized")]
    | SizedCorrect ->
      gApp ~explicit:true (gInject class_name)
        [full_dt; hole; gInject ("arbitrarySized")]
    | _ -> gApp (gInject class_name) [full_dt]
  in
  (* Create the instance record. Only need to extend this for extra instances *)
  let instance_record iargs =
    (* Copying code for Arbitrary, Sized from derive.ml *)
    match cn with
    | Show -> show_decl ty_ctr ctrs iargs 
    | Shrink -> shrink_decl ty_ctr ctrs iargs
    | GenSized -> arbitrarySized_decl ty_ctr ctrs iargs
    | Sized -> sized_decl ty_ctr ctrs
    | CanonicalSized ->
      let ind_scheme =  gInject ((ty_ctr_to_string ty_ctr) ^ "_ind") in
      sizeEqType ty_ctr ctrs ind_scheme iargs
    | SizeMonotonic ->
      let (iargs', size) = take_last iargs [] in
      sizeMon size_config (gVar size) iargs' (gInject name1)
    | SizedMonotonic ->
      sizeSMon size_config iargs
    | SizedCorrect ->
      let s_inst = gInject (repeat_instance_name Sized ind_name) in
      let c_inst = gInject (repeat_instance_name CanonicalSized ind_name) in
      (* TODO : use default names for gen and mon as well (?) *)
      genCorr size_config iargs (gInject name1) s_inst c_inst (gInject name2)
  in

  (* msg_debug (str "Defined record" ++ fnl ()); *)
  (* debug_coq_expr (instance_record []); *)

  declare_class_instance instance_arguments instance_name instance_type instance_record

