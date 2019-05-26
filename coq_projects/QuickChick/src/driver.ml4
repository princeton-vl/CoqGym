open Libnames
open Util
open Constrexpr
open Names
open Stdarg
open Error

type derivation = SimpleDer of SimplDriver.derivable list
                | DepDer of DepDriver.derivable

let simpl_dispatch ind classes name1 name2 =
  let ind_name = match ind with
    | { CAst.v = CRef (r, _) } -> string_of_qualid r
    | _ -> failwith "Implement me for functions"
  in
  List.iter (fun cn -> SimplDriver.derive cn ind (SimplDriver.mk_instance_name cn ind_name) name1 name2) classes


let class_assoc_opts = [ ("GenSized"                 , SimpleDer [SimplDriver.GenSized])
                       ; ("Shrink"                   , SimpleDer [SimplDriver.Shrink])
                       ; ("Arbitrary"                , SimpleDer [SimplDriver.GenSized; SimplDriver.Shrink])
                       ; ("Show"                     , SimpleDer [SimplDriver.Show])
                       ; ("Sized"                    , SimpleDer [SimplDriver.Sized])
                       ; ("CanonicalSized"           , SimpleDer [SimplDriver.CanonicalSized])
                       ; ("SizeMonotonic"            , SimpleDer [SimplDriver.SizeMonotonic])
                       ; ("SizedMonotonic"           , SimpleDer [SimplDriver.SizedMonotonic])
                       ; ("SizedCorrect"             , SimpleDer [SimplDriver.SizedCorrect])
                       ; ("DecOpt"                   , DepDer DepDriver.DecOpt)
                       ; ("ArbitrarySizedSuchThat"   , DepDer DepDriver.ArbitrarySizedSuchThat)
                       ; ("SizeMonotonicSuchThatOpt" , DepDer DepDriver.GenSizedSuchThatMonotonicOpt)
                       ; ("SizedProofEqs"            , DepDer DepDriver.SizedProofEqs)
                       ; ("GenSizedSuchThatCorrect"  , DepDer DepDriver.GenSizedSuchThatCorrect)
                       ; ("GenSizedSuchThatSizeMonotonicOpt", DepDer DepDriver.GenSizedSuchThatSizeMonotonicOpt)
                       ]

let class_assoc_table =
  let h = Hashtbl.create (List.length class_assoc_opts) in
  List.iter (fun (kwd, tok) -> Hashtbl.add h kwd tok) class_assoc_opts;
  h

let dispatch cn ind name1 name2 =
  let convert_reference_to_string c =
    match c with
    | {CAst.v = CRef (r, _)} -> string_of_qualid r
    | _ -> failwith "Usage: Derive <class_name> for <inductive_name> OR  Derive (<class_name>, ... , <class_name>) for <inductive_name>" in
  let ss = match cn with
     | { CAst.v = CNotation (_,([a],[b],_,_)) } -> begin
         let c = convert_reference_to_string a in
         let cs = List.map convert_reference_to_string b in
         c :: cs
       end
     | _ -> [convert_reference_to_string cn]
  in

  let get_class_names s =
    try Hashtbl.find class_assoc_table s
    with Not_found -> begin
        (* TODO: Figure out how to pretty print in a failwith... *)
        failwith ( "Not a valid class name. Expected one of : " ^ (String.concat " , " (List.map fst class_assoc_opts)))
      end
  in

  let class_names =
    match ss with
    | s::ss -> List.fold_left (fun der s ->
                               match der, get_class_names s with
                               | SimpleDer ds1, SimpleDer ds2 -> SimpleDer (ds1 @ ds2)
                               | DepDer ds1, DepDer ds2 ->
                                  qcfail "Implement dependent derive for multiple classes"
                              ) (get_class_names s) ss
    | _ -> qcfail "At least one class name expected" in

  match class_names with
  | SimpleDer classes -> simpl_dispatch ind classes name1 name2
  | DepDer class_name -> DepDriver.dep_dispatch ind class_name

VERNAC COMMAND EXTEND Derive CLASSIFIED AS SIDEFF
   | ["Derive" constr(class_name) "for" constr(inductive)] ->
     [dispatch class_name inductive "" ""]
   | ["Derive" constr(class_name) "for" constr(inductive) "using" ident(genInst)] ->
     [dispatch class_name inductive (Id.to_string genInst) ""]
   | ["Derive" constr(class_name) "for" constr(inductive) "using" ident(genInst) "and" ident(monInst) ] ->
     [dispatch class_name inductive (Id.to_string genInst) (Id.to_string monInst)]
END;;

(*

VERNAC COMMAND EXTEND DeriveArbitrarySized
  | ["DeriveArbitrarySized" constr(c) "as" string(s1)] -> [derive ArbitrarySized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveSized
  | ["DeriveSized" constr(c) "as" string(s1)] -> [derive Sized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveCanonicalSized
  | ["DeriveCanonicalSized" constr(c) "as" string(s1)] -> [derive CanonicalSized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveArbitrarySizedMonotonic
  | ["DeriveArbitrarySizedMonotonic" constr(c) "as" string(s1) "using" string(s2)] ->
  (* s2 is the instance name for ArbitrarySized *)
    [derive SizeMonotonic c s1 s2 ""]
END;;

VERNAC COMMAND EXTEND DeriveArbitrarySizedSizeMonotonic
  | ["DeriveArbitrarySizedSizeMonotonic" constr(c) "as" string(s1)] ->
    [derive SizeSMonotonic c s1 "" ""]
END;;


VERNAC COMMAND EXTEND DeriveArbitrarySizedCorrect
  | ["DeriveArbitrarySizedCorrect" constr(c) "as" string(s1) "using" string(s2) "and" string(s3)] ->
    [derive GenSizeCorrect c s1 s2 s3]
END;;
 *)
