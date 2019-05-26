(* The program to extract "theorems" from Coq source code *)

module Lib = Utils

let is_idchar = function 'A'..'Z'|'a'..'z'|'0'..'9'|'_'|'\'' -> true | _ -> false

let get_name s n =
  let len = String.length s in
  let rec pom s n =
    if n >= len then
      n
    else if is_idchar (String.get s n) then
      pom s (n + 1)
    else
      n
  in
  if n >= len then
    ""
  else
    let k = pom s n in
    String.sub s n (k - n)

let find_dot s i =
  let len = String.length s
  in
  let rec pom j in_quote =
    if j >= len then
      j
    else if (not in_quote) && String.get s j = '.' then
      j + 1
    else
      pom (j + 1) (if String.get s j = '\"' then not in_quote else in_quote)
  in
  pom i false

let remove_hammer_hook s =
  try
    let i =  Str.search_forward (Str.regexp "hammer_hook ") s 0 in
    let len = String.length s in
    let k = find_dot s i in
    String.sub s 0 i ^ String.sub s k (len - k)
  with Not_found ->
    s

let process_file fname =
  let nametab = Hashtbl.create 64
  in
  let create_nametab tfname =
    let rec pom prefix ic =
      begin
        try
          let s = input_line ic in
          let i = String.index s ' ' in
          let p = String.sub s 0 i in
          let x = String.sub s (i + 1) (String.length s - i - 1) in
          let v =
            if p <> "<>" then
              prefix ^ "." ^ p
            else
              prefix
          in
          if Hashtbl.mem nametab x then
            Queue.push v (Hashtbl.find nametab x)
          else
            begin
              let stack = Queue.create () in
              Queue.push v stack;
              Hashtbl.add nametab x stack
            end
        with Not_found -> ()
      end;
      pom prefix ic
    in
    let ic = open_in tfname
    in
    let s = input_line ic in
    let prefix = String.sub s 1 (String.length s - 1) in
    try
      pom prefix ic
    with End_of_file ->
      close_in ic; prefix
  in
  let rec pom prefix ic oc last =
    let s = String.trim (input_line ic) in
    let last2 =
      if Lib.string_begins_with s "Instance " then
        get_name s (String.length "Instance ")
      else if Lib.string_begins_with s "Theorem " then
        get_name s (String.length "Theorem ")
      else if Lib.string_begins_with s "Lemma " then
        get_name s (String.length "Lemma ")
      else if Lib.string_begins_with s "Definition " then
        get_name s (String.length "Definition ")
      else if Lib.string_begins_with s "Fact " then
        get_name s (String.length "Fact ")
      else if Lib.string_begins_with s "Corollary " then
        get_name s (String.length "Corollary ")
      else if Lib.string_begins_with s "Example " then
        get_name s (String.length "Example ")
      else if Lib.string_begins_with s "Remark " then
        get_name s (String.length "Remark ")
      else if Lib.string_begins_with s "Global Instance " then
        get_name s (String.length "Global Instance ")
      else if Lib.string_begins_with s "Program Instance " then
        get_name s (String.length "Program Instance ")
      else if Lib.string_begins_with s "Program Definition " then
        get_name s (String.length "Program Definition ")
      else if Lib.string_begins_with s "Program Lemma " then
        get_name s (String.length "Program Lemma ")
      else if Lib.string_begins_with s "Program Theorem " then
        get_name s (String.length "Program Theorem ")
      else if Lib.string_begins_with s "Program Fact " then
        get_name s (String.length "Program Fact ")
      else if Lib.string_begins_with s "Program Corollary " then
        get_name s (String.length "Program Corollary ")
      else if Lib.string_begins_with s "Global Program Instance " then
        get_name s (String.length "Global Program Instance ")
      else if Lib.string_begins_with s "Local Instance " then
        get_name s (String.length "Local Instance ")
      else if Lib.string_begins_with s "Local Program Instance " then
        get_name s (String.length "Local Program Instance ")
      else if Lib.string_begins_with s "Let " then
        get_name s (String.length "Let ")
      else
        last
    in
    begin
      let s = remove_hammer_hook s in
      try
        if Lib.string_begins_with s "Proof." ||
          Lib.string_begins_with s "Proof with " ||
          Lib.string_begins_with s "Proof using " ||
          Lib.string_begins_with s "Proof using."
        then
          begin
            let pref = Queue.pop (Hashtbl.find nametab last2) in
            let path = pref ^ "." ^ last2 in
            let i = String.index s '.' in
            let p = String.sub s 0 (i + 1) in
            let r =
              if i + 1 = String.length s then "" else
                (String.sub s (i + 1) (String.length s - i - 1))
            in
            output_string oc (p ^ " hammer_hook \"" ^ prefix ^ "\" \"" ^ path ^ "\"." ^
                                r ^ "\n");
            print_endline path
          end
        else if Lib.string_begins_with s "Proof " then
          begin
            let pref = Queue.pop (Hashtbl.find nametab last2) in
            let path = pref ^ "." ^ last2 in
            let p = String.sub s 6 (String.length s - 7) in
            output_string oc ("Proof. hammer_hook \"" ^ prefix ^ "\" \"" ^ path ^ "\"." ^
                                 "exact (" ^ p ^ "). Qed.\n");
            print_endline path
          end
        else
          output_string oc (s ^ "\n")
      with Not_found | Queue.Empty ->
        output_string oc (s ^ "\n")
    end;
    pom prefix ic oc last2
  in
  let gname = (Filename.chop_suffix fname ".v") ^ ".glob"
  in
  let cmd1 = "grep \"^F\" " ^ gname
  and cmd2 = "grep -v \"^R\" " ^ gname ^ " | tail -n+2 | cut -d ' ' -f 3,4"
  in
  let tfname = Filename.temp_file "coqnames" ".glob"
  and ofname = Filename.temp_file "coqnames" ".v"
  in
  ignore (Sys.command (cmd1 ^ " > " ^ tfname));
  ignore (Sys.command (cmd2 ^ " >> " ^ tfname));
  let prefix = create_nametab tfname in
  Sys.remove tfname;
  let ic = open_in fname
  and oc = open_out ofname
  in
  output_string oc "From Hammer Require Import Hammer.\n\n";
  try
    pom prefix ic oc ""
  with End_of_file ->
    close_in ic;
    close_out oc;
    ignore (Sys.command ("mv " ^ ofname ^ " " ^ fname))

let rec process_dir dir =
  let entries = Sys.readdir dir in
  Sys.chdir dir;
  Array.iter
    begin fun fname ->
      if Sys.is_directory fname then
        process_dir fname
      else if Filename.check_suffix fname ".v" then
        process_file fname
      else
        ()
    end
    entries;
  Sys.chdir ".."

;;

process_dir "."
