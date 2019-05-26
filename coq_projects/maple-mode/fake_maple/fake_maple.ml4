let answers =
 [ "p := simplify((x0*(1/x0))):", "1";
   "p := simplify(((1+x0)*(1/(1+x0)))):", "1";
   "p := simplify(((((((x0*(1/x1))+(x1*(1/x0)))*x0)*x1)+(-((x0^2)+(x1^2))))+1)):", "1";
   "p := simplify(((x0*(1/(x0+x1)))+(x1*(1/(x0+x1))))):", "1";
   "p := factor((((x0^2)+((2*x0)*x1))+(x1^2))):", "(x0 + x1)^2";
   "p := factor((((x0^2)+(-((2*x0)*x1)))+(x1^2))):", "(x0-x1)^2";
   "p := factor(((x0^2)+(-(x1^2)))):", "(x0-x1)*(x0+x1)";
   "p := factor(((((x0^3)+((3*(x0^2))*x1))+((3*x0)*(x1^2)))+(x1^3))):", "(x0+x1)^3";
   "p := expand(((x0+x1)^2)):", "x0^2+(1+1)*x0*x1+x1^2";
   "p := expand(((x0+(-x1))^2)):", "x0^2-2*x0*x1+x1^2";
   "p := expand(((x0+(-x1))*(x0+x1))):", "x0^2-x1^2";
   "p := expand(((x0+x1)^3)):", "x0^3+3*x0^2*x1+3*x0*x1^2+x1^3";
   "p := normal(((x0*(1/x1))+(x1*(1/x0)))):", "(x0^2+x1^2)/x1/x0";
   "p := normal(((1/x0)+(x0*(1/(x0+1))))):", "(x0+1+x0^2)/x0/(x0+1)";
   "p := normal(((x0*(x0*(1/((x0+(-x1))^2))))+(-(x1*(x1*(1/((x0+(-x1))^2))))))):", "(x0+x1)/(x0-x1)";
   "p := normal((((x0*(1/(x0+(-x1))))+(x1*(1/(x0+x1))))+((2*x1)*(x1*(1/((x0^2)+(-(x1^2)))))))):", "(x0+x1)/(x0-x1)";
   "p := simplify(((x0*(1/x0))+(x1*(1/x1)))):", "2";
   "p := factor(((x0*(1/x0))+(x0*(1/x1)))):", "(x1+x0)/x1";
   "p := expand((((3*x0)+3)*(x1+(-(5*(1/3)))))):", "3*x0*x1-5*x0+3*x1-5";
   "p := normal(((x0*(1/(x1*x0)))+(x0*(1/x1)))):", "(1+x0)/x1";
   "p := simplify((1*(1/1))):", "1";
   "p := simplify((((x0*(1/x1))+x1)*x1)):", "x0+x1^2";
   "p := factor(((x0*x1)+x0)):", "x0*(x1+1)";
   "p := factor(((((x0*x1)+(-(3*x0)))+(7*x1))+(-21))):", "(x0+7)*(x1-3)";
   "p := expand(((x0+x1)*x0)):", "x0^2+x0*x1";
   "p := expand(((x0+(-7))*(x1+4))):", "x0*x1-7*x1+4*x0-28";
   "p := normal(((1/x0)+(1/x1))):", "(x1+x0)/x0/x1";
   "p := normal(((((x0^2)*x1)*(1/(x0+x1)))+(((x1*x0)*x1)*(1/(x0+x1))))):", "x1^2";
 ]
;;

let main () =
 (* A query has the following form:                          *)
 (* p := simplify((x0*(1/x0))):save p,"/tmp/coqc5a0d6maple": *)
 let compute = read_line () in
 if compute = "quit" then exit 0 ;
 let save = read_line () in
 assert(try ignore (read_line ()) ; false with End_of_file -> true);
 let filename =
  match Str.split (Str.regexp "\"") save with
     [ "save p," ; filename; ":" ] -> filename
   | _ -> assert false
 in
  let ans =
   try let result = List.assoc compute answers in ("p := " ^ result ^ ";")
    (* for debugging only: the query is returned as the answer *)
   with Not_found ->
     Printf.eprintf "fake_maple: cannot answer %s\n" compute;
     compute in
  let fo = open_out filename in
   output_string fo ans;
   close_out fo
;;

main ()
