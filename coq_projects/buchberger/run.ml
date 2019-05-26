type prop = unit
let prop = ()

type arity = unit
let arity = ()

type 'A list =
    Nil
  | Cons of 'A * 'A list

let letP h h' =
  h' h prop

let acc_rec f =
  let rec acc_rec0 x _ =
    f x prop (fun y _ -> acc_rec0 y prop)
  in acc_rec0

let well_founded_induction _ h a =
  acc_rec (fun x _ h1 -> h x h1) a prop

type 'A sumor =
    Inleft of 'A
  | Inright

type sumbool =
    Left
  | Right

type ('A, 'B) prod =
    Pair of 'A * 'B

type nat =
    O
  | S of nat

type mon =
    N_0
  | C_n of nat * nat * mon

type bool =
    True
  | False

let le_lt_dec n =
  let rec f = function
    O -> (fun m -> Left)
  | S n1 -> (fun m ->
      let rec f0 = function
        O -> Right
      | S n3 -> (match f n1 n3 with
                   Left -> Left
                 | Right -> Right)
      in f0 m)
  in f n

let pmon1 d = function
  N_0 -> O
| C_n (d', n, p) -> n

let pmon2 d = function
  N_0 -> N_0
| C_n (d', n, p) -> p

let minus x =
  let rec minus0 n m =
    match n with
      O -> O
    | S k -> (match m with
                O -> S k
              | S l -> minus0 k l)
  in minus0 x

let div_mon_clean d =
  let rec f = function
    O -> (fun h' h'0 -> Pair (N_0, True))
  | S n0 -> (fun s1 s2 ->
      match le_lt_dec (pmon1 (S n0) s2) (pmon1 (S n0) s1) with
        Left ->
          (match f n0 (pmon2 (S n0) s1) (pmon2 (S n0) s2) with
             Pair (res, b) -> Pair ((C_n (n0,
               (minus (pmon1 (S n0) s1) (pmon1 (S n0) s2)), res)), b))
      | Right -> Pair (s1, False))
  in f d

let mk_clean n a b =
  div_mon_clean n a b

let divTerm_dec a0 a1 plusA invA minusA multA divA _ n a b =
  match a with
    Pair (a2, m) ->
      (match b with
         Pair (b2, c2) -> (fun _ _ ->
           match mk_clean n m c2 with
             Pair (c, b4) ->
               (match b4 with
                  True -> Left
                | False -> Right)))

let divP_dec a0 a1 plusA invA minusA multA divA _ n a b _ _ =
  match divTerm_dec a0 a1 plusA invA minusA multA divA prop n a b prop
          prop with
    Left -> Left
  | Right -> Right

let selectdivf a0 a1 plusA invA minusA multA divA _ n a _ q =
  let rec f = function
    Nil -> Inright
  | Cons (a2, l0) ->
      (match a2 with
         Nil ->
           (match f l0 with
              Inleft h'1 -> Inleft h'1
            | Inright -> Inright)
       | Cons (a3, l1) ->
           (match divP_dec a0 a1 plusA invA minusA multA divA prop n a
                    a3 prop prop with
              Left -> Inleft (Cons (a3, l1))
            | Right ->
                (match f l0 with
                   Inleft hyp1 -> Inleft hyp1
                 | Inright -> Inright)))
  in f q

let false_rec _ =
  failwith "False_rec"

let projsig1 h =
  h

let plus x =
  let rec plus0 n m =
    match n with
      O -> m
    | S p -> S (plus0 p m)
  in plus0 x

let mult_mon d =
  let rec f = function
    O -> (fun h' h'0 -> N_0)
  | S n0 -> (fun s1 s2 -> C_n (n0,
      (plus (pmon1 (S n0) s1) (pmon1 (S n0) s2)),
      (f n0 (pmon2 (S n0) s1) (pmon2 (S n0) s2))))
  in f d

let multTerm multA n = function
  Pair (b2, c2) -> (fun h1' ->
    match h1' with
      Pair (b3, c3) -> Pair ((multA b2 b3), (mult_mon n c2 c3)))

let mults multA n a p =
  let rec f = function
    Nil -> Nil
  | Cons (a0, l0) -> Cons ((multTerm multA n a a0), (f l0))
  in f p

let zero_mon d =
  let rec f = function
    O -> N_0
  | S n0 -> C_n (n0, O, (f n0))
  in f d

let m1 n =
  zero_mon n

let t2M n = function
  Pair (a, m) -> m

let ltT_dec n ltM_dec x y =
  ltM_dec (t2M n x) (t2M n y)

let minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec l =
  well_founded_induction prop (fun x ->
    match x with
      Pair (l1, l2) ->
        (match l1 with
           Nil -> (fun h' ->
             mults multA n (Pair ((invA a1), (m1 n))) l2)
         | Cons (a2, m2) ->
             (match l2 with
                Nil -> (fun h' -> Cons (a2, m2))
              | Cons (a3, m3) -> (fun h' ->
                  match ltT_dec n ltM_dec a2 a3 with
                    Inleft p ->
                      (match p with
                         Left -> Cons
                           ((match a3 with
                               Pair (b2, c2) -> Pair ((invA b2), c2)),
                           (h' (Pair ((Cons (a2, m2)), m3)) prop))
                       | Right -> Cons (a2,
                           (h' (Pair (m2, (Cons (a3, m3)))) prop)))
                  | Inright ->
                      let orec = h' (Pair (m2, m3)) prop in
                      letP
                        (match a2 with
                           Pair (b2, c2) ->
                             (match a3 with
                                Pair (b3, c3) -> Pair ((minusA b2 b3),
                                  c2))) (fun u _ ->
                        match match u with
                                Pair (b, h'0) -> eqA_dec b a0 with
                          Left -> orec
                        | Right -> Cons (u, orec)))))) l

let minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec l1 l2 =
  projsig1
    (minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec (Pair (l1, l2)))

let div_mon d =
  let rec f = function
    O -> (fun h' h'0 -> N_0)
  | S n0 -> (fun s1 s2 -> C_n (n0,
      (minus (pmon1 (S n0) s1) (pmon1 (S n0) s2)),
      (f n0 (pmon2 (S n0) s1) (pmon2 (S n0) s2))))
  in f d

let divTerm a0 divA n = function
  Pair (b2, c2) -> (fun h' ->
    match h' with
      Pair (b3, c3) -> (fun _ -> Pair ((divA b2 b3 prop),
        (div_mon n c2 c3))))

let spminusf a0 a1 invA minusA multA divA eqA_dec n ltM_dec a b _ p q =
  minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec p
    (mults multA n (divTerm a0 divA n a b prop) q)

let reducef a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ q p =
  well_founded_induction prop (fun x ->
    match x with
      Nil -> (fun h' -> Nil)
    | Cons (a, l) -> (fun h' ->
        match selectdivf a0 a1 plusA invA minusA multA divA prop n a
                prop q with
          Inleft div1 ->
            (match div1 with
               Nil -> false_rec prop
             | Cons (a2, l0) ->
                 h'
                   (spminusf a0 a1 invA minusA multA divA eqA_dec n
                     ltM_dec a a2 prop l l0) prop)
        | Inright -> Cons (a, (h' l prop)))) p

let unit a0 a1 divA n = function
  Nil -> Pair (a1, (m1 n))
| Cons (a, l) ->
    (match a with
       Pair (co, m) -> Pair ((divA a1 co prop), (m1 n)))

let nf a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ p l =
  letP
    (reducef a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
      prop l p) (fun u _ -> mults multA n (unit a0 a1 divA n u) u)

let app x =
  let rec app0 l m =
    match l with
      Nil -> m
    | Cons (a, l1) -> Cons (a, (app0 l1 m))
  in app0 x

let redacc a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ h' =
  let rec f = function
    Nil -> (fun l0 -> Nil)
  | Cons (a, l0) ->
      let rec0 = f l0 in (fun acc ->
      letP
        (nf a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
          prop a (app l0 acc)) (fun u _ ->
        match match u with
                Nil -> Left
              | Cons (a2, l1) -> Right with
          Left -> rec0 acc
        | Right -> Cons (u, (rec0 (Cons (u, acc))))))
  in f h'

let red a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ l =
  redacc a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec prop
    l Nil

let prod_rec f = function
  Pair (a, b) -> f a b

let eq_nat_dec n =
  let rec f = function
    O -> (fun m ->
      let rec f0 = function
        O -> Left
      | S n2 -> Right
      in f0 m)
  | S n1 -> (fun m ->
      let rec f0 = function
        O -> Right
      | S n3 -> (match f n1 n3 with
                   Left -> Left
                 | Right -> Right)
      in f0 m)
  in f n

let eqmon_dec d =
  let rec f = function
    O -> (fun x y -> Left)
  | S n0 -> (fun x y ->
      match eq_nat_dec (pmon1 (S n0) x) (pmon1 (S n0) y) with
        Left ->
          (match f n0 (pmon2 (S n0) x) (pmon2 (S n0) y) with
             Left -> Left
           | Right -> Right)
      | Right -> Right)
  in f d

let eqT_dec n x y =
  eqmon_dec n (t2M n x) (t2M n y)

let max h' =
  let rec f = function
    O -> (fun n1 -> n1)
  | S n0 -> (fun h0 -> match h0 with
                         O -> S n0
                       | S n2 -> S (f n0 n2))
  in f h'

let ppcm_mon d =
  let rec f = function
    O -> (fun m3 m2 -> N_0)
  | S n0 -> (fun s1 s2 -> C_n (n0,
      (max (pmon1 (S n0) s1) (pmon1 (S n0) s2)),
      (f n0 (pmon2 (S n0) s1) (pmon2 (S n0) s2))))
  in f d

let ppc a1 n = function
  Pair (b2, c2) -> (fun h' ->
    match h' with
      Pair (b3, c3) -> Pair (a1, (ppcm_mon n c2 c3)))

let foreigner_dec a0 a1 multA n a = function
  Nil -> Left
| Cons (a2, l) ->
    (match a with
       Nil -> Left
     | Cons (a3, l0) ->
         eqT_dec n (ppc a1 n a2 a3) (multTerm multA n a2 a3))

type 'A sig0 = 'A

type 'A term = ('A, mon) prod

type 'A poly = 'A term list sig0

type 'A cpRes =
    Keep of 'A poly list
  | DontKeep of 'A poly list

let divp_dec a0 a1 plusA invA minusA multA divA _ n a = function
  Nil -> (match a with
            Nil -> Right
          | Cons (a2, l) -> Right)
| Cons (t, l) ->
    (match a with
       Nil -> Right
     | Cons (a2, l0) ->
         divP_dec a0 a1 plusA invA minusA multA divA prop n a2 t prop
           prop)

let ppcp a0 a1 plusA invA minusA multA divA _ n = function
  Nil -> (fun h'1 -> Nil)
| Cons (a, l) -> (fun h'1 ->
    match h'1 with
      Nil -> Nil
    | Cons (a2, l0) -> Cons ((ppc a1 n a a2), Nil))

let slice a0 a1 plusA invA minusA multA divA _ n i a q =
  let rec f = function
    Nil ->
      (match foreigner_dec a0 a1 multA n i a with
         Left -> DontKeep Nil
       | Right -> Keep Nil)
  | Cons (a2, l0) ->
      let rec0 = f l0 in
      (match divp_dec a0 a1 plusA invA minusA multA divA prop n
               (ppcp a0 a1 plusA invA minusA multA divA prop n i a) a2 with
         Left -> DontKeep (Cons (a2, l0))
       | Right ->
           (match divp_dec a0 a1 plusA invA minusA multA divA prop n
                    (ppcp a0 a1 plusA invA minusA multA divA prop n i
                      a2) a with
              Left -> rec0
            | Right ->
                (match rec0 with
                   Keep h'0 -> Keep (Cons (a2, h'0))
                 | DontKeep h'0 -> DontKeep (Cons (a2, h'0)))))
  in f q

let spolyf a0 a1 invA minusA multA divA eqA_dec n ltM_dec = function
  Nil -> (fun p2 _ _ -> Nil)
| Cons (a, p11) -> (fun p2 ->
    match p2 with
      Nil -> (fun _ _ -> Nil)
    | Cons (b, p22) -> (fun _ _ ->
        letP (ppc a1 n a b) (fun u _ ->
          minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec
            (mults multA n (divTerm a0 divA n u a prop) p11)
            (mults multA n (divTerm a0 divA n u b prop) p22))))

let spolyp a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ p q =
  spolyf a0 a1 invA minusA multA divA eqA_dec n ltM_dec q p prop prop

let genPcPf0 a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ i aP =
  well_founded_induction prop (fun aP0 ->
    match aP0 with
      Nil -> (fun h' r -> r)
    | Cons (a, l1) -> (fun rec0 l ->
        match slice a0 a1 plusA invA minusA multA divA prop n i a l1 with
          Keep l2 ->
            let rec f = function
              Nil -> Cons
                ((spolyp a0 a1 plusA invA minusA multA divA prop
                   eqA_dec n ltM_dec prop i a), Nil)
            | Cons (a2, l3) -> Cons (a2, (f l3))
            in f (rec0 l2 prop l)
        | DontKeep l2 -> rec0 l2 prop l)) aP

let genPcPf a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ i aP q =
  genPcPf0 a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
    prop i aP q

let pbuchf a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ pq =
  well_founded_induction prop (fun x ->
    prod_rec (fun p q ->
      match q with
        Nil -> (fun h' -> p)
      | Cons (a, q2) -> (fun rec0 ->
          letP
            (nf a0 a1 plusA invA minusA multA divA prop eqA_dec n
              ltM_dec prop a p) (fun a2 _ ->
            match match a2 with
                    Nil -> Left
                  | Cons (a3, l) -> Right with
              Left -> rec0 (Pair (p, q2)) prop
            | Right ->
                rec0 (Pair
                  ((let rec f = function
                      Nil -> Cons (a2, Nil)
                    | Cons (a3, l0) -> Cons (a3, (f l0))
                    in f p),
                  (genPcPf a0 a1 plusA invA minusA multA divA prop
                    eqA_dec n ltM_dec prop a2 p q2))) prop))) x) pq

let genOCPf a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ h' =
  let rec f = function
    Nil -> Nil
  | Cons (a, l0) ->
      genPcPf a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
        prop a l0 (f l0)
  in f h'

let buch a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ p =
  pbuchf a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec prop
    (Pair (p,
    (genOCPf a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
      prop p)))

let redbuch a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ l =
  red a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec prop
    (buch a0 a1 plusA invA minusA multA divA prop eqA_dec n ltM_dec
      prop l)

let plusp a0 plusA eqA_dec n ltM_dec l =
  well_founded_induction prop (fun x ->
    match x with
      Pair (p, q) ->
        (match p with
           Nil -> (fun h' -> q)
         | Cons (a1, m2) ->
             (match q with
                Nil -> (fun h' -> Cons (a1, m2))
              | Cons (a2, m3) -> (fun h' ->
                  match ltT_dec n ltM_dec a1 a2 with
                    Inleft p0 ->
                      (match p0 with
                         Left -> Cons (a2,
                           (h' (Pair ((Cons (a1, m2)), m3)) prop))
                       | Right -> Cons (a1,
                           (h' (Pair (m2, (Cons (a2, m3)))) prop)))
                  | Inright ->
                      letP
                        (match a1 with
                           Pair (b2, c2) ->
                             (match a2 with
                                Pair (b3, c3) -> Pair ((plusA b2 b3),
                                  c2))) (fun letA _ ->
                        match match letA with
                                Pair (b, h'0) -> eqA_dec b a0 with
                          Left -> h' (Pair (m2, m3)) prop
                        | Right -> Cons (letA,
                            (h' (Pair (m2, m3)) prop))))))) l

let pluspf a0 plusA eqA_dec n ltM_dec l1 l2 =
  projsig1 (plusp a0 plusA eqA_dec n ltM_dec (Pair (l1, l2)))

let splus a0 plusA eqA_dec n ltM_dec _ sp1 sp2 =
  pluspf a0 plusA eqA_dec n ltM_dec sp2 sp1

let multpf a0 plusA multA eqA_dec n ltM_dec =
  let rec multpf0 p q =
    match p with
      Nil -> Nil
    | Cons (a, p') ->
        pluspf a0 plusA eqA_dec n ltM_dec (mults multA n a q)
          (multpf0 p' q)
  in multpf0

let smult a0 a1 plusA invA minusA multA divA _ eqA_dec n ltM_dec _ sp1 sp2 =
  multpf a0 plusA multA eqA_dec n ltM_dec sp2 sp1

let tmults a0 multA eqA_dec n a =
  match match a with
          Pair (b, h') -> eqA_dec b a0 with
    Left -> (fun h' -> Nil)
  | Right -> (fun p -> mults multA n a p)

let sscal a0 a1 plusA invA minusA multA divA _ eqA_dec n _ a p =
  tmults a0 multA eqA_dec n (Pair (a, (m1 n))) p

let spO a0 n =
  Nil

let sp1 a0 a1 plusA invA minusA multA divA _ n =
  Cons ((Pair (a1, (m1 n))), Nil)

let gen_mon d =
  let rec f = function
    O -> (fun n0 -> N_0)
  | S n0 ->
      let h' = f n0 in (fun n' ->
      match n' with
        O -> C_n (n0, (S O), (h' n0))
      | S n'' -> C_n (n0, O, (h' n'')))
  in f d

let sgen a0 a1 plusA invA minusA multA divA _ n m =
  Cons ((Pair (a1, (gen_mon n m))), Nil)

let mon_rec f0 f =
  let rec f1 n = function
    N_0 -> f0
  | C_n (d, n0, m0) -> f d n0 m0 (f1 d m0)
  in f1

let lt_eq_lt_dec n =
  let rec f = function
    O -> (fun m ->
      let rec f0 = function
        O -> Inleft Right
      | S n2 -> Inleft Left
      in f0 m)
  | S n1 -> (fun m ->
      let rec f0 = function
        O -> Inright
      | S n3 ->
          (match f n1 n3 with
             Inleft a ->
               (match a with
                  Left -> Inleft Left
                | Right -> Inleft Right)
           | Inright -> Inright)
      in f0 m)
  in f n

let orderc_dec n a =
  mon_rec (fun b -> Inright) (fun d n0 m h' b ->
    match h' (pmon2 (S d) b) with
      Inleft h'0 ->
        (match h'0 with
           Left -> Inleft Left
         | Right -> Inleft Right)
    | Inright ->
        (match lt_eq_lt_dec n0 (pmon1 (S d) b) with
           Inleft a0 ->
             (match a0 with
                Left -> Inleft Right
              | Right -> Inright)
         | Inright -> Inleft Left)) n a

let degc n h' =
  mon_rec O (fun d n1 m n2 -> plus n1 n2) n h'

let total_orderc_dec n a b =
  letP (degc n a) (fun u _ ->
    letP (degc n b) (fun u0 _ ->
      match le_lt_dec u u0 with
        Left ->
          (match match lt_eq_lt_dec u u0 with
                   Inleft a0 -> a0
                 | Inright -> false_rec prop with
             Left -> Inleft Left
           | Right ->
               (match orderc_dec n a b with
                  Inleft h'3 ->
                    (match h'3 with
                       Left -> Inleft Left
                     | Right -> Inleft Right)
                | Inright -> Inright))
      | Right -> Inleft Right))


(***********************************************************************)
(* To run the code on examples you first need a top level that includes
   the bignum. To create that under unix do 
     ocamlmktop -custom -o ocaml_num nums.cma -cclib -lnums
   then start ocaml_num and enter the following ML code 
 *)

open Ratio;;
open Big_int;;


type r6 =  (ratio, mon) prod list;;

let rec n_to_p n  =  if n = 0 then O else (S (n_to_p (n-1)));;

let eqd n m = if (eq_ratio n m) then  Left else Right;;

let ri = ratio_of_int;;

let plusP: int -> r6 -> r6 -> r6 =  
  fun n -> 
   let n = n_to_p n in 
   (splus (ri 0) (add_ratio) eqd n (total_orderc_dec n) n);;



let multP: int -> r6 -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
  (smult (ri 0)(ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n eqd n (total_orderc_dec n) n);;


let scalP: int -> int -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
      fun m -> 
      (sscal (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n eqd n n (ri m));;

let spO a0 n =
  Nil


let p0 : int -> r6 = fun n -> (spO  (ri 0) (n_to_p n));;

let p1 : int -> r6 = (fun n -> (sp1 (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n (n_to_p n) )) ;;


let mon : int -> int -> r6 = fun n -> fun m -> sgen (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div_ratio) n (n_to_p n)  (n_to_p m);;

let div1_ratio a b c = div_ratio a b;;


let tbuch : int -> r6 list -> r6 list =
    (fun n ->
      let n = n_to_p n in 
      redbuch (ri 0) (ri 1) (add_ratio) (minus_ratio) (sub_ratio) (mult_ratio)
         (div1_ratio) n eqd  n  (total_orderc_dec n) n);;

let rec l2l l = match l with [] -> Nil | (a::tl) -> Cons (a, l2l tl);;
let rec l5l l = match l with Nil -> [] | Cons (a,tl) -> a :: (l5l tl);;

let tbuchl = fun n -> fun l -> (l5l (tbuch n (l2l l)));;

let dim = 6;;
let plus = plusP dim;;
let mult = multP dim;;
let scal = scalP dim;;
let p1 = p1 dim;;
let gen = mon dim;;
let tbuch = tbuchl dim;;

let a = gen 0;;
let b = gen 1;;
let c = gen 2;;
let p1 =  gen 6;;

let r0 = (plus a (plus b c));;
let r1 = (plus (mult a b) (plus (mult b c) (mult c a)));;
let r2 = (plus (mult a (mult b c)) (scal (-1) p1));;


tbuch [r2;r1;r0];;

print_string "3"; print_newline();;


let d = gen 3;;

let r0 = (plus a (plus b (plus c d)));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (mult d a))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d a)) 
             (mult d (mult a b)))));;
let r3 = (plus (mult a (mult b (mult c d))) (scal (-1) p1));;




tbuch [r3;r2;r1;r0];;

print_string "4"; print_newline();;

let e = gen 4;;

let r0 = (plus a (plus b (plus c (plus d e))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (mult e a)))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e a))
             (mult e(mult a b))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e a)))
(plus (mult d (mult e (mult a b)))
             (mult e(mult a (mult b c)))))));;
let r4 = (plus (mult a (mult b (mult c (mult d e)))) (scal (-1) p1));;



tbuch [r4;r3;r2;r1;r0];;

print_string "5"; print_newline();;

let f = gen 5;;

let r0 = (plus a (plus b (plus c (plus d (plus e f)))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (plus (mult e f) (mult f a))))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e f))
(plus (mult e (mult f a))
             (mult f (mult a b)))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e f)))
(plus (mult d (mult e (mult f a)))
(plus (mult e (mult f (mult a b)))
             (mult f(mult a (mult b c))))))));;
let r4= (plus (mult a (mult b (mult c (mult d e)))) (plus (mult b (mult c (mult d (mult e f)))) 
(plus (mult c (mult d (mult e (mult f a))))
(plus (mult d (mult e (mult f (mult a b))))
(plus (mult e (mult f (mult a (mult b c))))
             (mult f(mult a (mult b (mult c d)))))))));;
let r5 = (plus (mult a (mult b (mult c (mult d (mult e f))))) (scal (-1) p1));;

tbuch [r5;r4;r3;r2;r1;r0];;


print_string "6"; print_newline();;
