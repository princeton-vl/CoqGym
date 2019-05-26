open Search;;

(*  let f1 = Imp(Atom 0, Atom 1) *)


let neg a = Imp(a, Falsum);;
let eqv a b = AndF( Imp(a,b), Imp(b,a));;


(********************************************************)
(* general tools                                        *)
(********************************************************)


(* map_conj n f= (AndF (f 0) (f 1) ... (f n)) *)

let rec map_conj n f =
  if n=0 then
    (f 0)
  else
    AndF( (map_conj (n-1) f), (f n));;

let rec conj_n n = (map_conj n (fun n -> (Atom n)));;


let rec map_conj_rev n f =
  if n=0 then
    (f 0)
  else
    AndF( (f n), (map_conj_rev (n-1) f) );;



(* map_disj n f= (OrF (f 0) (f 1) ... (f n)) *)

let rec map_disj n f =
  if n=0 then
    (f 0)
  else
    OrF( (map_disj (n-1) f), (f n));;

let rec disj_n n = (map_disj n (fun n -> (Atom n)));;

let map_disj2 n m f = (map_disj (n*m) (fun i -> (f (i / m) (i mod n))));;


(********************************************************)
(* de Bruijn's formulae                                 *)
(********************************************************)


let rec de_bruijn_lhs m n c=
  (map_conj m (fun m -> Imp( (eqv (Atom m) (Atom ((m + 1) mod n))), c)));;


let de_bruijn_p n =
  let n0 = 2 * n  in
  let n1 = n0+1 in
  let c = (conj_n n0) in
  Imp( (de_bruijn_lhs n0 n1 c), c);;

let de_bruijn_n n =
  let n0 = 2 * n - 1 in
  let n1 = n0+1 in
  let c = (conj_n n0) in
  Imp( (de_bruijn_lhs n0 n1 c), c);;


(* last formula modified to make it classically provable  *)
let de_bruijn_n' n =
  let n0 = 2 * n - 1 in
  let n1 = n0+1 in
  let c = (conj_n n0) in
  let d = Atom( n1 ) in
  Imp( (de_bruijn_lhs n0 n1 c), OrF( OrF(d,c), (neg d)));;


    
(********************************************************)
(* Pigeonhole formulae                                  *)
(********************************************************)

let pigeon_atom k l n = Atom( k*n + l);;


let pigeon_right n =
  (map_disj (n-1)
     (fun h ->
       (map_disj n
	  (fun p1 ->
	    (map_disj (n-p1) 
	       (fun p2' ->
		 let p2=p2'+p1 in
		 AndF( (pigeon_atom p1 h n), (pigeon_atom p2 h n))))))))

let pigeon_left_p n =
  (map_conj n (fun i -> (map_disj n (fun j -> (pigeon_atom i j n)))));;
let pigeon_left_n n =
  (map_conj n 
     (fun i -> 
       (map_disj n 
	  (fun j -> 
	    if i=j then
	      (neg (neg (pigeon_atom i j n)))
	    else
	      (pigeon_atom i j n)))));;

let pigeonhole_p n = Imp( (pigeon_left_p n), (pigeon_right n));;
let pigeonhole_n n = Imp( (pigeon_left_n n), (pigeon_right n));;

(********************************************************)
(* Franzen's formulae                                   *)
(********************************************************)


let franzen_p n =
  (neg (neg (OrF( (map_disj (n-1) (fun i -> (neg (Atom i)))), 
		 (conj_n (n-1))))));;

let franzen_p' n =
  let nneg a = Imp( a, (Atom n)) in
  (nneg (nneg  (OrF( (conj_n (n-1)), 
		    (map_disj (n-1) (fun i -> (nneg (Atom i))))))));;


let franzen_n n =
  let nneg a = Imp( a, (Atom n)) in
  (nneg (nneg  (OrF( (conj_n (n-1)), 
		    (map_disj (n-1) 
		       (fun i -> (nneg (neg (neg (Atom i))))))))));;


(********************************************************)
(* Schwichtenberg's formulae                            *)
(********************************************************)

let schwicht_p n =
  let n1=(n-1) in
  Imp( AndF( Atom(n1), 
	    (map_conj n1 
	       (fun i -> 
		 let i1 = if i=0 then n else (i-1) in
		 Imp( Atom(i), Imp( Atom(i), Atom(i1)))))),
       Atom(n) );;


let schwicht_n n =
  let n1=(n-1) in
  Imp( AndF( (neg (neg (Atom n1))),
	    (map_conj n1 
	       (fun i -> 
		 let i1 = if i=0 then n else (i-1) in
		 Imp( Atom(i), Imp( Atom(i), Atom(i1)))))),
       Atom(n) );;

let schwicht100_p n = schwicht_p (100*n);;
let schwicht100_n n = schwicht_n (100*n);;

(********************************************************)
(* Korn & Kreitz's formulae                             *)
(********************************************************)

let korn_kreitz_p n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  (neg (AndF( AndF( (neg (a 0)), Imp( Imp( (b n), (b 0)), (a n))),
             (map_conj (n-1) 
		(fun i -> Imp( Imp( (b i), (a (i+1))), (a i)))))));;

let korn_kreitz_p' n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  let nneg a = Imp( a, Atom(n+n) ) in
  (nneg (AndF( AndF( (nneg (a 0)), Imp( Imp( (b n), (b 0)), (a n))),
             (map_conj (n-1) 
		(fun i -> Imp( Imp( (b i), (a (i+1))), (a i)))))));;


let korn_kreitz_n n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  (neg (AndF( AndF( (neg (a 0)), Imp( Imp( (neg (neg (b n))), (b 0)), (a n))),
             (map_conj (n-1) 
		(fun i -> 
		  Imp( Imp( (neg (neg (b i))), (a (i+1))), (a i)))))));;

let korn_kreitz_n' n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  let nneg a = Imp( a, Atom(n+n) ) in
  (nneg (AndF( AndF( (nneg (a 0)), Imp( Imp( (neg (neg (b n))), (b 0)), (a n))),
             (map_conj (n-1) 
		(fun i ->
		  Imp( Imp( (neg (neg (b i))), (a (i+1))), (a i)))))));;

let korn_kreitz_n'' n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  let nneg a = Imp( a, Atom(n+n) ) in
  (nneg (AndF( AndF( (nneg (a 0)), 
		   (map_conj (n-1) 
		      (fun i ->
			Imp( Imp( (neg (neg (b i))), (a (i+1))), (a i))))),
	      Imp( Imp( (neg (neg (b n))), (b 0)), (a n)))));;

(********************************************************)
(* Equivalences                                         *)
(********************************************************)


let rec equiv_left n =
  if n=0 then
    Atom(0)
  else
    (eqv (equiv_left (n-1)) (Atom n));;

let rec equiv_right n =
  if n=0 then
    Atom(0)
  else
    (eqv (Atom n) (equiv_right (n-1)));;


let equiv_p n = (eqv (equiv_left (n)) (equiv_right (n)));;
let equiv_n n = (eqv 
		   (eqv (equiv_left (n-1)) (neg (neg (Atom n))))
		   (equiv_right n));;

let equiv_n' n = (eqv 
		   (equiv_left n)
		   (eqv (neg (neg (Atom n))) (equiv_right (n-1))));;



(********************************************************)
(* other formulae                                       *)
(********************************************************)

let f1 n =
  let a m = Atom(m) in
  let b m = Atom(n+m) in
  let c m = Atom(n+n+m) in
  Imp( (map_conj (n-1) (fun i -> Imp( Imp( (a i), (b i)), (c i)))),
       Atom(n+n+n) );;



let korn_kreitz_x n =
  let a m = Atom(m + m) in
  let b m = Atom(m + m + 1) in
  Imp( AndF( Imp( Imp( (b n), (b (n-1))), (a n)),
	    (map_conj (n-1) 
	       (fun i -> Imp( Imp( (b i), (a (i+1))), (a i))))),
	    
       (a 0));;


