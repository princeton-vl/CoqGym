open Utils;;
let reconstr_mode = ref false
let comma_rxp = Str.regexp ",";;
let pom l s nos fg g2 = (Str.split comma_rxp l, Str.split comma_rxp s, List.sort compare (List.map int_of_string (Str.split comma_rxp nos)), Str.split comma_rxp fg,  bool_of_string g2);;
let (collabels, sortmode, merge_nos, fixgreed, greed2) = match Array.to_list Sys.argv with
  |  [_; "-r"; l; s; nos; fg; g2] -> reconstr_mode := true; pom l s nos fg g2
  |  [_; l; s; nos; fg; g2] -> pom l s nos fg g2
  | _ -> failwith "Usage: stath (labels) (sorting) (merging) (fixgreed) greed2\nwhere [sorting] can be none, sort, greed and [megring] are nos to merge from back";;

let proto_rxp = Str.regexp "protokoll";;
let dirents d =
  let dirh = Unix.opendir d in
  let goodname s = s <> "." && s <> ".." &&
    (try ignore (Str.search_forward proto_rxp s 0); false with Not_found -> true) in
  let rec fs acc = try fs (let l = Unix.readdir dirh in if goodname l then l :: acc else acc)
    with End_of_file -> acc in
  let ret = fs [] in
  Unix.closedir dirh; ret
;;

let rec rdirents prefix acc d =
  try
    let dirh = Unix.opendir (prefix ^ d) in
    let goodname s = s <> "." && s <> ".." &&
      (try ignore (Str.search_forward proto_rxp s 0); false with Not_found -> true) in
    let rec fs acc = try fs (let l = Unix.readdir dirh in if goodname l then rdirents (prefix ^ d ^ "/") acc l else acc)
      with End_of_file -> acc in
    let ret = fs acc in
    Unix.closedir dirh; ret
  with Unix.Unix_error (Unix.ENOTDIR, _, _) -> (prefix ^ d) :: acc
;;

let rdirents () =
  if !reconstr_mode then
    let l = rdirents "" [] "atp/i/f" in
    List.map (fun s -> String.sub s 8 (String.length s - 8)) l
  else
    let l = rdirents "" [] "i/f" in
    List.map (fun s -> String.sub s 4 (String.length s - 4)) l
;;


let dash_rxp = Str.regexp "-";;
let unmerged_atps = Array.of_list (dirents (if !reconstr_mode then "out" else "o"));;
let rec replace_nos str_lst = function
    [] -> str_lst
  | no :: nos ->
      match str_lst with
        [] -> failwith "Merge non-existing fields"
      | sh :: st ->
        let pnos = List.map pred nos in
        if no = 0 then "*" :: replace_nos st pnos else sh :: replace_nos st (pred no :: pnos);;
let replace_nos s = String.concat "-" (List.rev (replace_nos (List.rev (Str.split dash_rxp s)) merge_nos));;

let merged_atps = Hashtbl.create 100;;
let merged_atp_no = ref 0;;
let replh = Hashtbl.create 100;;
let replnoh = Hashtbl.create 100;;

Array.iteri (fun un ua -> let ma = replace_nos ua in Hashtbl.replace replh ua ma;
  try let mn = Hashtbl.find merged_atps ma in Hashtbl.replace replnoh un mn
  with Not_found -> Hashtbl.add merged_atps ma !merged_atp_no; Hashtbl.replace replnoh un !merged_atp_no;
    incr merged_atp_no) unmerged_atps;;

let reverse_hash h =
  let nh = Hashtbl.create (Hashtbl.length h) in
  Hashtbl.iter (fun a b -> Hashtbl.add nh b a) h;
  nh;;

let atpno = !merged_atp_no;;
let no_atp = reverse_hash merged_atps;;
let atps = Array.init atpno (Hashtbl.find no_atp);;

let fixgreed = List.map (fun i -> try Hashtbl.find merged_atps i with _ -> -1) fixgreed;;

let fs = Array.of_list (rdirents ());;
let fsno = Array.length fs;;

Printf.eprintf "e%!";;

let reg1 = Str.regexp ".*\\(SZS status Theorem\\|SZS status Unsatisfiable\\| : Valid (\\|SPASS beiseite: Proof found.\\|^Success \\|^THEOREM PROVED$\\)";;
let reg2 = Str.regexp ".*\\(SZS status CounterSatisfiable\\|Non-Theorem\\)";;
let reg3 = Str.regexp ".*\\(SZS status Timeout\\|SZS status Unknown\\| : Unknown (\\|SZS status ResourceOut\\|^Failure \\|^SPASS beiseite: Ran out of time. SPASS was killed.$\\)";;
let reg4 = Str.regexp ".*\\( [eE]rror\\| HighFailure\\|ExitFailure\\|PARSE ERROR\\)";;
let evalf fname =
  try let inc = open_in fname in
  let rec ans () = try
    let l = input_line inc in
    if Str.string_match reg1 l 0 then 5 else
    if Str.string_match reg2 l 0 then 4 else
    if Str.string_match reg3 l 0 then 3 else
    if Str.string_match reg4 l 0 then 2 else
    ans ()
    with End_of_file -> close_in inc; 1 in
  let ret = ans () in
  close_in inc; ret
  with _ -> 0
;;

let ans = Array.init atpno (fun atp -> Array.create fsno 0);;
for uatpno = 0 to Array.length unmerged_atps - 1 do
  let uatpn = unmerged_atps.(uatpno) in
  let matpno = Hashtbl.find replnoh uatpno in
  let fv = ans.(matpno) in
  for f = 0 to fsno - 1 do
    let oret = fv.(f) in
    if oret = 5 then () else
      begin
        let name = (if !reconstr_mode then "out/" else "o/") ^ uatpn ^ "/" ^ fs.(f) in
        let name =
          if !reconstr_mode then
            Filename.chop_extension name ^ ".out"
          else name
        in
        let nret = evalf name in
        if nret > oret then fv.(f) <- nret
      end
  done
done;;

Printf.eprintf "a%!";;

(* Problems per atp *)
let pps = Array.init atpno (fun matpno ->
  Array.fold_left (fun s x -> if x > 0 then s + 1 else s) 0 ans.(matpno));;


let yes = Array.init atpno (fun atp ->
  Array.fold_left (fun o i -> o + (if i = 5 then 1 else 0)) 0 ans.(atp));;
let no = Array.init atpno (fun atp ->
  Array.fold_left (fun o i -> o + (if i = 4 then 1 else 0)) 0 ans.(atp));;
let maybe = Array.init atpno (fun atp ->
  Array.fold_left (fun o i -> o + (if i = 3 then 1 else 0)) 0 ans.(atp));;
let error = Array.init atpno (fun atp ->
  Array.fold_left (fun o i -> o + (if i = 2 then 1 else 0)) 0 ans.(atp));;

let anyyes, anyno = ref 0, ref 0;;
for f = 0 to fsno - 1 do
  let canayes, canano = ref false, ref false in
  for a = 0 to atpno - 1 do
    if ans.(a).(f) = 5 then canayes := true
    else if ans.(a).(f) = 4 then canano := true
  done;
  (if !canayes then incr anyyes);
  (if !canano then incr anyno);
done;;

let addl e l = if List.mem e l then l else e :: l;;

let uniq = Array.create atpno 0;;
for f = 0 to fsno - 1 do
  let conf1, conf2 = ref [], ref [] in
  for atp = 0 to atpno - 1 do
    if ans.(atp).(f) = 5 then begin
      let canayes = ref true in
      for a = 0 to atpno - 1 do
        if ans.(a).(f) = 4 then (conf1 := addl atp !conf1; conf2 := addl a !conf2) else
        if a <> atp && ans.(a).(f) = 5 then canayes := false else ()
      done;
      if !canayes then (uniq.(atp) <- uniq.(atp) + 1; print_endline ("Uniq: " ^ atps.(atp) ^ " : " ^ fs.(f)))
    end
  done;
  if !conf1 <> [] then Printf.printf "Conflict: %i Yes: %s No: %s\n" f
    (String.concat "," (List.map (fun a -> atps.(a)) !conf1))
    (String.concat "," (List.map (fun a -> atps.(a)) !conf2))
done;;

let sotac = Array.create atpno 0.;;
let counter_sotac = false;;
for f = 0 to fsno - 1 do
  let sum = ref 0 in
  for atp = 0 to atpno - 1 do
    if ans.(atp).(f) = 5 || (counter_sotac && ans.(atp).(f) = 4) then incr sum;
  done;
  let factor = if !sum = 0 then 0. else 1. /. (float_of_int !sum) in
  for atp = 0 to atpno - 1 do
    if ans.(atp).(f) = 5 || (counter_sotac && ans.(atp).(f) = 4) then sotac.(atp) <- sotac.(atp) +. factor
  done
done;;

let sotacavg = Array.init atpno (fun i -> if yes.(i) = 0 then 0. else sotac.(i) /. (float_of_int (yes.(i) + no.(i))));;

let sum2 a1 a2 =
  let rec sumi acc n =
    if n = fsno then acc else
    sumi (if a1.(n) > 4 || a2.(n) > 4 then 1 + acc else acc) (n + 1)
  in sumi 0 0;;

let sum3 a1 a2 a3 =
  let rec sumi acc n =
    if n = fsno then acc else
    sumi (if a1.(n) > 4 || a2.(n) > 4 || a3.(n) > 4 then 1 + acc else acc) (n + 1)
  in sumi 0 0;;

let suml l =
  let rec sumi acc n =
    if n = fsno then acc else
    sumi (if List.fold_left (fun sofar a -> sofar || a.(n) > 4) false l then 1+acc else acc) (n + 1)
  in sumi 0 0;;

let update1 a a1 =
  let rec ui n =
    if n = fsno then () else (
    (if a1.(n) > 4 then a.(n) <- 5);
    ui (n + 1))
  in ui 0;;

let update2 a a1 a2 =
  let rec ui n =
    if n = fsno then () else (
    (if a1.(n) > 4 || a2.(n) > 4 then a.(n) <- 5);
    ui (n + 1))
  in ui 0;;

let arraymaxes f a =
  let cm = ref 0 and ci = ref [] in
  for i = 0 to Array.length a - 1 do
    let fa = f a.(i) in
    if fa > !cm then (ci := [i]; cm := fa) else
    if fa = !cm then ci := i :: !ci
  done; (!ci, !cm);;

let current = Array.create fsno 0;;
let sofar = ref 0;;

let greed_reset () = Array.fill current 0 (Array.length current) 0; sofar := 0;;

let id x = x;;

let greed_add1 () =
  let sums = Array.init atpno (fun i -> sum2 current ans.(i)) in
  let (is, s) = arraymaxes id sums in
  if s <= !sofar then raise Exit;
  let a = try List.hd is with Failure _ -> failwith "empty!!!" in
  let alts = List.tl is in
  sofar := s;
  update1 current ans.(a);
  ((a, alts), s);;

let greed_add2 () =
  let sums = Array.init (atpno * atpno)
    (fun i -> let a1 = i / atpno and a2 = i mod atpno in sum3 current ans.(a1) ans.(a2)) in
  let (is, s) = arraymaxes id sums in
  if s <= !sofar then raise Exit;
  let is = List.map (fun i -> (i / atpno, i mod atpno)) is in
  let ((a1, a2) as a) = try List.hd is with Failure _ -> failwith "empty!!!" in
  let alts = List.tl is in
  sofar := s;
  update2 current ans.(a1) ans.(a2);
  ((a, alts), s);;

let greed_add2m () =
  let sums = Array.init (atpno * atpno)
    (fun i -> let a1 = i / atpno and a2 = i mod atpno in sum3 current ans.(a1) ans.(a2)) in
  let (is, s) = arraymaxes id sums in
  if s <= !sofar then raise Exit;
  let is = setify (List.concat (List.map (fun i -> [i / atpno; i mod atpno]) is)) in
  let sums = Array.of_list (List.map (fun i -> (i, sum2 current ans.(i))) is) in
  let (is, s) = arraymaxes snd sums in
  let a = fst (sums.(try List.hd is with Failure _ -> failwith "empty!!!")) in
  sofar := s;
  update1 current ans.(a);
  (a, s);;

let greed_del1 curlst =
  let sums = Array.of_list (List.map (fun i -> (i, suml (List.map (Array.get ans) (List.filter (fun j -> j <> i) curlst)))) curlst) in
  let (is, s) = arraymaxes snd sums in
  let a = fst (sums.(try List.hd is with Failure _ -> failwith "empty!!!")) in
  let nlst = (List.filter (fun j -> j <> a) curlst) in
  sofar := suml (List.map (Array.get ans) nlst);
  Array.fill current 0 (Array.length current) 0;
  List.iter (update1 current) (List.map (Array.get ans) nlst);
  ((a, nlst), !sofar);;

Printf.eprintf "s%!";;

let greed = ref [];;
greed_reset ();;
List.iter (fun i -> if i >= 0 then
  update1 current ans.(i);
  sofar := suml (List.map (Array.get ans) (i :: (List.map (fun i -> fst (fst i)) !greed)));
  greed := ((i, []), !sofar) :: !greed;
) fixgreed;;
try while true do
  greed := (greed_add1 ()) :: !greed
done with Exit -> ();;
let greedy = Array.of_list (List.rev !greed);;

Printf.eprintf "g%!";;

let name_comp n i = try List.nth (List.rev (Str.split dash_rxp atps.(i))) n with _ -> "";;

let rec interp_sort i = function
    [] | "-" :: _ -> [Printf.sprintf "%010i" i]
  | "p" :: t -> atps.(i) :: interp_sort i t
(*  | "g" :: t -> Printf.sprintf "%010i" (1000000000 - (snd (fst greedy.(i)))) :: interp_sort i t*)
  | "y" :: t -> Printf.sprintf "%010i" (1000000000 - yes.(i)) :: interp_sort i t
  | "n" :: t -> Printf.sprintf "%010i" (1000000000 - no.(i)) :: interp_sort i t
  | "s" :: t -> Printf.sprintf "%09.5f" (1000000.0 -. sotac.(i)) :: interp_sort i t
  | n :: t -> let n = int_of_string n in name_comp n i :: (interp_sort i t)
let sort_atp = Array.init atpno (fun i -> (i, interp_sort i sortmode));;
Array.sort (fun a b -> compare (snd a) (snd b)) sort_atp;;

let proc a b =
  if b = 0 then "?" else try
  Printf.sprintf "%.3f" ((100. *. float_of_int a) /. (float_of_int b))
  with _ -> "....";;

let oc = open_out "statistics.html";;
Printf.fprintf oc "<html><head>\n<link rel=\"stylesheet\" type=\"text/css\" href=\"style_experiments.css\">\n</head></body>";;

let print_table oc l =
  os oc "<table><tr>";
  List.iter (fun (h, _, _) -> os oc "<th>"; os oc h; os oc "</th>") l;
  os oc "</tr>\n";
  for i = 0 to atpno - 1 do
    os oc "<tr>";
    let a = fst (sort_atp.(i)) in
    List.iter (fun (_, (c, v), _) -> os oc "<td class='"; os oc c; os oc"'>"; os oc (v a); os oc "</td>") l;
    os oc "</tr>\n"
  done;
  os oc "<tr>";
  List.iter (fun (_, _, t) -> os oc "<td>"; os oc t; os oc "</td>") l;
  os oc "</tr>\n</table>\n"
;;

print_table oc [
  ("Str", ("", name_comp 2), "any");
  ("Predict", ("", name_comp 1), "any");
  ("PrArg", ("", name_comp 0), "");
  ("Thm%", ("yes", fun a -> proc yes.(a) pps.(a)), proc !anyyes fsno);
  ("CoS%", ("no", fun a -> proc no.(a) pps.(a)), proc !anyno fsno);
  ("Uniq", ("time", fun a -> string_of_int uniq.(a)), "");
  ("ST&#x2300;", ("time", fun a -> Printf.sprintf "%.3f" sotacavg.(a)), "");
  ("ST&#x3a3;", ("time", fun a -> Printf.sprintf "%.2f" sotac.(a)), "");
  ("Thm", ("yes", fun a -> string_of_int yes.(a)), string_of_int !anyyes);
  ("CoS", ("no", fun a -> string_of_int no.(a)), string_of_int !anyno);
  ("Maybe", ("maybe", fun a -> string_of_int maybe.(a)), "");
  ("Empty", ("timeout", fun a -> string_of_int (pps.(a) - yes.(a) - no.(a) - maybe.(a) - error.(a))),"");
  ("Err", ("error", fun a -> if error.(a) = 0 then "" else string_of_int error.(a)), "");
  ("Found", ("time", fun a -> string_of_int pps.(a)), string_of_int fsno)
];;
os oc "</table>\n";;

let greed = ref [];;
if greed2 then begin
  greed_reset ();
  try while true do
      let (((a1,a2), _), s) = greed_add2 () in greed := s :: (-1) :: !greed;
      Printf.printf "Greed2: %s, %s\n" (Array.get atps a1) (Array.get atps a2)
  done with Exit -> ()
end
let greedy2 = Array.of_list (List.rev !greed);;

if greed2 then begin
  greed := [];
  greed_reset ();
  greed := snd (greed_add1 ()) :: !greed;
  try while true do
    let (_, s) = greed_add2 () in greed := s :: (-1) :: !greed
  done with Exit -> ()
end
let greedy2a = Array.of_list (List.rev !greed);;

if greed2 then begin
  let nos = ref [] in
  greed := [];
  greed_reset ();
  let (((a1, a2), _), s) = greed_add2 () in
  greed := s :: (-1) :: !greed;
  nos := a1 :: a2 :: !nos;
  try while true do
    let sum = !sofar in
    let ((_, nnos), _) = greed_del1 !nos in
    nos := nnos;
    let (((a1, a2), _), s) = greed_add2 () in
    nos := a1 :: a2 :: !nos;
    if s = sum then raise Exit;
    greed := s :: !greed
  done with Exit -> ()
end
let greedym1p2 = Array.of_list (List.rev !greed);;

if greed2 then begin
  greed := [];
  greed_reset ();
  try while true do
    let (a, s) = greed_add2m () in greed := s :: !greed
  done with Exit -> ()
end
let greedy2m = Array.of_list (List.rev !greed);;

Printf.fprintf oc "<h3>Greedy sequence</h3><table><tr><td>Prover</td><td>Sum%%</td><td>Sum</td><td>G+2</td><td>G1+2</td><td>G-1+2</td><td>G+2M</td><td>Alt</td></tr>\n";;
try for i = 0 to Array.length greedy - 1 do
  let ((a, alt), m) = greedy.(i) in
  let alt5s = String.concat " = " (List.map (Array.get atps) (cut_list [] 3 alt)) in
  let alts =
    if alt = [] then "" else if List.length alt > 3 then "= " ^ alt5s ^ " = ... (" ^ (string_of_int (List.length alt)) ^ ")" else "= " ^ alt5s
  in
  let g2 = if i < Array.length greedy2 && greedy2.(i) >= 0 then string_of_int greedy2.(i) else "" in
  let g2a = if i < Array.length greedy2a && greedy2a.(i) >= 0 then string_of_int greedy2a.(i) else "" in
  let g3 = if i < Array.length greedym1p2 && greedym1p2.(i) >= 0 then string_of_int greedym1p2.(i) else "" in
  let gm = if i < Array.length greedy2m && greedy2m.(i) >= 0 then string_of_int greedy2m.(i) else "" in
  Printf.fprintf oc "<tr><td>%s</td><td class='yes'>%s</td><td>%i</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td style='font-size: 50%%'>%s</td></tr>\n" atps.(a) (proc m fsno) m g2 g2a g3 gm alts;
  if m = !anyyes then raise Exit else ()
done with Exit -> ();;
os oc "</table>\n";;

close_out oc;;
