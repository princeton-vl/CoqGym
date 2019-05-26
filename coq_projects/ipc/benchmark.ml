open Search
open Test_formulae


let test_prover a =
  let t0 = Sys.time() in
  let res = search a Nil in
  let t1 = Sys.time() in

  (match res with
  | (Refutable0 _) -> print_string "no; "
  | _              -> print_string "yes; "); (* Derivable0 *)

  print_string "time taken: ";
  print_float (t1 -. t0);
  print_newline();;


let prov_loop f step max_time =
  let rec loop n =
    print_int n;
    let a = (f n) in
    let t0 = Sys.time() in
    let res = search a Nil in
    let t1 = Sys.time() in
    let t = (t1 -. t0) in
    
    (match res with
    | (Refutable0 _) -> print_string "  no; "
    | _              -> print_string "  yes; "); (* Derivable0 *)
    
    print_string "time taken: ";
    print_float t;
    print_newline();

    if t < max_time then
      loop  (step n)
  in
  loop 1;
  print_newline ();
  print_newline ();;   


let rec pow2 n =
  if n=0 then
    1
  else
    2 * (pow2 (n-1));;


    
let prov_1sec f = prov_loop f succ 1.0;;
let prov_1sec_pow f = prov_loop f pow2 1.0;;


print_endline "testing formulae: f1";
prov_1sec f1;

print_endline "testing formulae: de_bruijn_p";
prov_1sec de_bruijn_p;

print_endline "testing formulae: de_bruijn_n'";
prov_1sec de_bruijn_n';

print_endline "testing formulae: pigeonhole_p";
prov_1sec pigeonhole_p;

print_endline "testing formulae: pigeonhole_n";
prov_1sec pigeonhole_n;

print_endline "testing formulae: franzen_p'";
prov_1sec franzen_p';

print_endline "testing formulae: franzen_n";
prov_1sec franzen_n;

print_endline "testing formulae: schwicht_p";
prov_1sec schwicht_p;

print_endline "testing formulae: schwicht_n";
prov_1sec schwicht_n;

print_endline "testing formulae: korn_kreitz_p'";
prov_1sec korn_kreitz_p';

print_endline "testing formulae: korn_kreitz_n'";
prov_1sec korn_kreitz_n';

print_endline "testing formulae: equiv_p";
prov_1sec equiv_p;

print_endline "testing formulae: equiv_n";
prov_1sec equiv_n;
