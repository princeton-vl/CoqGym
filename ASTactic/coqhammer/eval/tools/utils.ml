let runline s =
  let ic = Unix.open_process_in s in
  let ret = input_line ic in
  close_in ic;
  ret;;

let uniq l =
  let rec uniq2 acc = function
      x::(y::_ as t) -> uniq2 (if Pervasives.compare x y = 0 then acc else x :: acc) t
    | [x] -> List.rev (x :: acc)
    | [] -> List.rev acc
  in uniq2 [] l;;

(*let rec uniq = function (x::(y::_ as t) as l) ->
  let t' = uniq t in if compare x y = 0 then t'
  else if t'==t then l else x::t'
  | l -> l;;*)

let setify l = uniq (List.sort compare l);;

let file_iter fname fn =
  let ic = try open_in fname with Sys_error _ -> failwith ("file_iter: "^fname) in
  let next = ref 0 in
  let rec suck_lines () = fn !next (input_line ic); incr next; suck_lines () in
  try suck_lines () with End_of_file -> close_in ic;;

let os = output_string;;
let rec oiter oc fn sep = function
    [] -> ()
  | [e] -> fn e
  | h :: t -> fn h; os oc sep; oiter oc fn sep t;;

let cutoff = 5;;
let stable_sort cmp a lb rb =
  let merge src1ofs src1len src2 src2ofs src2len dst dstofs =
    let src1r = src1ofs + src1len and src2r = src2ofs + src2len in
    let rec loop i1 s1 i2 s2 d =
      if cmp s1 s2 <= 0 then begin
        Array.set dst d s1;
        let i1 = i1 + 1 in
        if i1 < src1r then
          loop i1 (Array.get a i1) i2 s2 (d + 1)
        else
          Array.blit src2 i2 dst (d + 1) (src2r - i2)
      end else begin
        Array.set dst d s2;
        let i2 = i2 + 1 in
        if i2 < src2r then
          loop i1 s1 i2 (Array.get src2 i2) (d + 1)
        else
          Array.blit a i1 dst (d + 1) (src1r - i1)
      end
    in loop src1ofs (Array.get a src1ofs) src2ofs (Array.get src2 src2ofs) dstofs;
  in
  let isortto srcofs dst dstofs len =
    for i = 0 to len - 1 do
      let e = (Array.get a (srcofs + i)) in
      let j = ref (dstofs + i - 1) in
      while (!j >= dstofs && cmp (Array.get dst !j) e > 0) do
        Array.set dst (!j + 1) (Array.get dst !j);
        decr j;
      done;
      Array.set dst (!j + 1) e;
    done;
  in
  let rec sortto srcofs dst dstofs len =
    if len <= cutoff then isortto srcofs dst dstofs len else begin
      let l1 = len / 2 in
      let l2 = len - l1 in
      sortto (srcofs + l1) dst (dstofs + l1) l2;
      sortto srcofs a (srcofs + l2) l1;
      merge (srcofs + l2) l1 dst (dstofs + l1) l2 dst dstofs;
    end;
  in
  let l = rb - lb + 1 in
  if l <= cutoff then isortto lb a lb l else begin
    let l1 = l / 2 in
    let l2 = l - l1 in
    let t = Array.make l2 (Array.get a lb) in
    sortto (lb + l1) t 0 l2;
    sortto lb a (lb + l2) l1;
    merge (lb + l2) l1 t 0 l2 a lb;
  end;
;;


let pivot a l r =
  let i = ref l and j = ref (r - 1) and p = snd a.(r) in
  while !i < !j do
    while snd a.(!i) >= p && !i < r do incr i done;
    while snd a.(!j) <= p && !j > l do decr j done;
    if !i < !j then (let t = a.(!i) in a.(!i) <- a.(!j); a.(!j) <- t)
  done;
  if snd a.(!i) < p then (let t = a.(!i) in a.(!i) <- a.(r); a.(r) <- t);
  !i;;

let rec qsort a l r upto =
  if upto > r - l then stable_sort (fun a b -> compare (snd b) (snd a)) a l r  else
  if upto > 0 && l < r then
    let p = pivot a l r in
    qsort a l (p - 1) upto;
    qsort a (p + 1) r (upto + l - p - 1);
  else ();;

let qsort a upto = qsort a 0 (Array.length a - 1) upto;;

exception Bottom of int;;
let heapsort compare bound a =
  let maxson l i =
    let i31 = i+i+i+1 in
    let x = ref i31 in
    if i31+2 < l then begin
      if compare (Array.get a i31) (Array.get a (i31+1)) < 0 then x := i31+1;
      if compare (Array.get a !x) (Array.get a (i31+2)) < 0 then x := i31+2;
      !x
    end else
      if i31+1 < l && compare (Array.get a i31) (Array.get a (i31+1)) < 0
      then i31+1
      else if i31 < l then i31 else raise (Bottom i)
  in
  let rec trickledown l i e =
    let j = maxson l i in
    if compare (Array.get a j) e > 0 then begin
      Array.set a i (Array.get a j);
      trickledown l j e;
    end else begin
      Array.set a i e;
    end;
  in
  let rec trickle l i e = try trickledown l i e with Bottom i -> Array.set a i e in
  let rec bubbledown l i =
    let j = maxson l i in
    Array.set a i (Array.get a j);
    bubbledown l j
  in
  let bubble l i = try bubbledown l i with Bottom i -> i in
  let rec trickleup i e =
    let father = (i - 1) / 3 in
    assert (i <> father);
    if compare (Array.get a father) e < 0 then begin
      Array.set a i (Array.get a father);
      if father > 0 then trickleup father e else Array.set a 0 e;
    end else begin
      Array.set a i e;
    end;
  in
  let l = Array.length a in
  for i = (l + 1) / 3 - 1 downto 0 do trickle l i (Array.get a i); done;
  for i = l - 1 downto max 2 (l - bound) do
    let e = (Array.get a i) in
    Array.set a i (Array.get a 0);
    trickleup (bubble i 0) e;
  done;
  if l > 1 then (let e = (Array.get a 1) in Array.set a 1 (Array.get a 0); Array.set a 0 e);
;;

let rec cut_list acc n = function
    [] -> List.rev acc | h :: t -> if n = 0 then List.rev acc else cut_list (h :: acc) (n - 1) t;;

let list_to_hash exp l =
  let h = Hashtbl.create exp in
  List.iter (fun e -> Hashtbl.add h e ()) l; h
;;

(* Generate the (inclusive) sequence [l, .., u]. *)
let rec fromto l u = if l > u then [] else l :: fromto (l+1) u

let string_begins_with s1 s2 =
  try
    String.sub s1 0 (String.length s2) = s2
  with _ ->
    false
