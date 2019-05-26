type mutant_info =
  { file_name   : string
  ; line_number : int
  ; tag         : string option } 

let default_info =
  { file_name = "" ; line_number = -1 ; tag = None }
  
type mutant =
  { mut_info  : mutant_info
  ; mut_begin : string
  ; mut_body  : string
  ; mut_end   : string }

type node =
  (* Base chunk of text *)
  | Text of string 
  (* Commented out QuickChick call *)
  | QuickChick of
      { qc_begin : string
      ; qc_body  : string
      ; qc_end   : string }
  (* Mutant: start of mutant, base, list of mutants *)
  | Mutants of
      { ms_begin   : string
      ; ms_base    : string
      ; ms_mutants : mutant list }

type extend =
  { ext_begin   : string
  ; ext_extends : string list
  ; ext_end     : string }

type section = 
  (* Sections: Start comment, section name, end comment, extends, contents *)
  { sec_begin   : string
  ; sec_name    : string
  ; sec_end     : string
  ; sec_extends : extend option
  ; sec_nodes   : node list }
  
let rec output_mutant (m : mutant) : string =
  m.mut_begin ^ m.mut_body ^ m.mut_end

let rec output_node (n : node) : string =
  match n with
  | Text s -> s 
  | QuickChick qc ->
     (qc.qc_begin ^ qc.qc_body ^ qc.qc_end)
  | Mutants ms ->
     Printf.sprintf "%s%s%s" ms.ms_begin ms.ms_base (String.concat "" (List.map output_mutant ms.ms_mutants))

let output_extends (me : extend option) : string =
  match me with 
  | Some ext -> ext.ext_begin ^ String.concat "" ext.ext_extends ^ ext.ext_end
  | None -> ""

let output_section (sec : section) : string =
     let qual s = if sec.sec_name = "" || sec.sec_name.[0] = '_' then "" else s in
     Printf.sprintf "%s%s%s%s%s" (qual sec.sec_begin) (qual sec.sec_name) (qual sec.sec_end) (output_extends sec.sec_extends) (String.concat "" (List.map output_node sec.sec_nodes))


