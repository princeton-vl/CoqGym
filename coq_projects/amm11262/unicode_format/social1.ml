type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type 'a option =
  | Some of 'a
  | None

type ('a, 'b) prod =
  | Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
  | Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
  | Pair (x, y) -> y

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
  | Left
  | Right

type 'a sumor =
  | Inleft of 'a
  | Inright

(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u

(** val lt_eq_lt_dec : nat -> nat -> sumbool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
    | O -> (match m with
              | O -> Inleft Right
              | S n0 -> Inleft Left)
    | S n0 -> (match m with
                 | O -> Inright
                 | S m0 -> lt_eq_lt_dec n0 m0)

(** val le_lt_eq_dec : nat -> nat -> sumbool **)

let le_lt_eq_dec n m =
  match lt_eq_lt_dec n m with
    | Inleft x -> x
    | Inright -> assert false (* absurd case *)

type 'x x_Relation_Class =
  | SymmetricReflexive
  | AsymmetricReflexive of 'x
  | SymmetricAreflexive
  | AsymmetricAreflexive of 'x
  | Leibniz

type variance =
  | Covariant
  | Contravariant

type reflexive_Relation_Class =
  | RSymmetric
  | RAsymmetric
  | RLeibniz

type function_type_of_morphism_signature = __

type morphism_Theory =
  function_type_of_morphism_signature
  (* singleton inductive, whose constructor was Build_Morphism_Theory *)

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
  | Nil -> O
  | Cons (a, m) -> S (length m)

type 'x compare =
  | LT
  | EQ
  | GT

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
 end

module OrderedTypeFacts = 
 functor (O:OrderedType) ->
 struct 
  (** val eq_dec : O.t -> O.t -> sumbool **)
  
  let eq_dec x y =
    match O.compare x y with
      | EQ -> Left
      | _ -> Right
  
  (** val lt_dec : O.t -> O.t -> sumbool **)
  
  let lt_dec x y =
    match O.compare x y with
      | LT -> Left
      | _ -> Right
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    match eq_dec x y with
      | Left -> True
      | Right -> False
 end

module Nat_as_OT = 
 struct 
  type t = nat
  
  (** val compare : t -> t -> nat compare **)
  
  let compare x y =
    match lt_eq_lt_dec x y with
      | Inleft s -> (match s with
                       | Left -> LT
                       | Right -> EQ)
      | Inright -> GT
 end

module type S = 
 sig 
  module E : 
   sig 
    type t 
    
    val compare : t -> t -> t compare
   end
  
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val compare : t -> t -> t compare
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
 end

module Raw = 
 functor (X:OrderedType) ->
 struct 
  module E = X
  
  module MX = OrderedTypeFacts(X)
  
  type elt = X.t
  
  type t = elt list
  
  (** val empty : t **)
  
  let empty =
    Nil
  
  (** val is_empty : t -> bool **)
  
  let is_empty = function
    | Nil -> True
    | Cons (x, x0) -> False
  
  (** val mem : elt -> t -> bool **)
  
  let rec mem x = function
    | Nil -> False
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> False
           | EQ -> True
           | GT -> mem x l)
  
  (** val add : elt -> t -> t **)
  
  let rec add x s = match s with
    | Nil -> Cons (x, Nil)
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> Cons (x, s)
           | EQ -> s
           | GT -> Cons (y, (add x l)))
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Cons (x, Nil)
  
  (** val remove : elt -> t -> t **)
  
  let rec remove x s = match s with
    | Nil -> Nil
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> s
           | EQ -> l
           | GT -> Cons (y, (remove x l)))
  
  (** val union : t -> t -> t **)
  
  let rec union s x =
    match s with
      | Nil -> x
      | Cons (x0, l) ->
          let rec union_aux s' = match s' with
            | Nil -> s
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> Cons (x0, (union l s'))
                   | EQ -> Cons (x0, (union l l'))
                   | GT -> Cons (x', (union_aux l')))
          in union_aux x
  
  (** val inter : t -> t -> t **)
  
  let rec inter s x =
    match s with
      | Nil -> Nil
      | Cons (x0, l) ->
          let rec inter_aux s' = match s' with
            | Nil -> Nil
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> inter l s'
                   | EQ -> Cons (x0, (inter l l'))
                   | GT -> inter_aux l')
          in inter_aux x
  
  (** val diff : t -> t -> t **)
  
  let rec diff s x =
    match s with
      | Nil -> Nil
      | Cons (x0, l) ->
          let rec diff_aux s' = match s' with
            | Nil -> s
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> Cons (x0, (diff l s'))
                   | EQ -> diff l l'
                   | GT -> diff_aux l')
          in diff_aux x
  
  (** val equal : t -> t -> bool **)
  
  let rec equal s s' =
    match s with
      | Nil -> (match s' with
                  | Nil -> True
                  | Cons (e, l) -> False)
      | Cons (x, l) ->
          (match s' with
             | Nil -> False
             | Cons (x', l') ->
                 (match X.compare x x' with
                    | EQ -> equal l l'
                    | _ -> False))
  
  (** val subset : t -> t -> bool **)
  
  let rec subset s s' =
    match s with
      | Nil -> True
      | Cons (x, l) ->
          (match s' with
             | Nil -> False
             | Cons (x', l') ->
                 (match X.compare x x' with
                    | LT -> False
                    | EQ -> subset l l'
                    | GT -> subset s l'))
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let rec fold f s i =
    match s with
      | Nil -> i
      | Cons (x, l) -> fold f l (f x i)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let rec filter f = function
    | Nil -> Nil
    | Cons (x, l) ->
        (match f x with
           | True -> Cons (x, (filter f l))
           | False -> filter f l)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let rec for_all f = function
    | Nil -> True
    | Cons (x, l) ->
        (match f x with
           | True -> for_all f l
           | False -> False)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let rec exists_ f = function
    | Nil -> False
    | Cons (x, l) -> (match f x with
                        | True -> True
                        | False -> exists_ f l)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let rec partition f = function
    | Nil -> Pair (Nil, Nil)
    | Cons (x, l) ->
        let Pair (s1, s2) = partition f l in
        (match f x with
           | True -> Pair ((Cons (x, s1)), s2)
           | False -> Pair (s1, (Cons (x, s2))))
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    length s
  
  (** val elements : t -> elt list **)
  
  let elements x =
    x
  
  (** val min_elt : t -> elt option **)
  
  let min_elt = function
    | Nil -> None
    | Cons (x, l) -> Some x
  
  (** val max_elt : t -> elt option **)
  
  let rec max_elt = function
    | Nil -> None
    | Cons (x, l) ->
        (match l with
           | Nil -> Some x
           | Cons (e, l0) -> max_elt l)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    min_elt s
  
  (** val compare : t -> t -> t compare **)
  
  let rec compare l s' =
    match l with
      | Nil -> (match s' with
                  | Nil -> EQ
                  | Cons (e, l0) -> LT)
      | Cons (a, l0) ->
          (match s' with
             | Nil -> GT
             | Cons (a', l') ->
                 (match X.compare a a' with
                    | LT -> LT
                    | EQ ->
                        (match compare l0 l' with
                           | LT -> LT
                           | EQ -> EQ
                           | GT -> GT)
                    | GT -> GT))
 end

module Make = 
 functor (X:OrderedType) ->
 struct 
  module Raw = Raw(X)
  
  module E = X
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  (** val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rect f s =
    f s __
  
  (** val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rec f s =
    f s __
  
  (** val this : slist -> Raw.t **)
  
  let this s =
    s
  
  type t = slist
  
  type elt = X.t
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    Raw.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    Raw.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Raw.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    Raw.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    Raw.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    Raw.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    Raw.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    Raw.max_elt (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s x =
    Raw.fold f (this s) x
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    Raw.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    Raw.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    Raw.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f s =
    let p = Raw.partition f (this s) in Pair ((fst p), (snd p))
  
  (** val compare : t -> t -> t compare **)
  
  let compare s s' =
    match Raw.compare (this s) (this s') with
      | LT -> LT
      | EQ -> EQ
      | GT -> GT
 end

module type DecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
 end

module OT_as_DT = 
 functor (O:OrderedType) ->
 struct 
  module OF = OrderedTypeFacts(O)
  
  type t = O.t
  
  (** val eq_dec : O.t -> O.t -> sumbool **)
  
  let eq_dec x y =
    OF.eq_dec x y
 end

module type Coq_S = 
 sig 
  module E : 
   sig 
    type t 
   end
  
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end

module Facts = 
 functor (M:Coq_S) ->
 functor (D:DecidableType with type t= M.E.t with type eq=
 __) ->
 struct 
  (** val eqb : D.t -> D.t -> bool **)
  
  let eqb x y =
    match D.eq_dec x y with
      | Left -> True
      | Right -> False
  
  (** val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class **)
  
  let coq_EltSetoid v =
    SymmetricReflexive
  
  (** val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class **)
  
  let coq_EltSetoid_precise_relation_class =
    RSymmetric
  
  (** val coq_EltSetoid_morphism : morphism_Theory **)
  
  let coq_EltSetoid_morphism =
    Obj.magic __
  
  (** val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class **)
  
  let coq_EqualSetoid v =
    SymmetricReflexive
  
  (** val coq_EqualSetoid_precise_relation_class :
      reflexive_Relation_Class **)
  
  let coq_EqualSetoid_precise_relation_class =
    RSymmetric
  
  (** val coq_EqualSetoid_morphism : morphism_Theory **)
  
  let coq_EqualSetoid_morphism =
    Obj.magic __
  
  (** val coq_In_m_morphism_theory : morphism_Theory **)
  
  let coq_In_m_morphism_theory =
    Obj.magic __
  
  (** val is_empty_m_morphism_theory : morphism_Theory **)
  
  let is_empty_m_morphism_theory =
    Obj.magic M.is_empty
  
  (** val coq_Empty_m_morphism_theory : morphism_Theory **)
  
  let coq_Empty_m_morphism_theory =
    Obj.magic __
  
  (** val mem_m_morphism_theory : morphism_Theory **)
  
  let mem_m_morphism_theory =
    Obj.magic M.mem
  
  (** val singleton_m_morphism_theory : morphism_Theory **)
  
  let singleton_m_morphism_theory =
    Obj.magic M.singleton
  
  (** val add_m_morphism_theory : morphism_Theory **)
  
  let add_m_morphism_theory =
    Obj.magic M.add
  
  (** val remove_m_morphism_theory : morphism_Theory **)
  
  let remove_m_morphism_theory =
    Obj.magic M.remove
  
  (** val union_m_morphism_theory : morphism_Theory **)
  
  let union_m_morphism_theory =
    Obj.magic M.union
  
  (** val inter_m_morphism_theory : morphism_Theory **)
  
  let inter_m_morphism_theory =
    Obj.magic M.inter
  
  (** val diff_m_morphism_theory : morphism_Theory **)
  
  let diff_m_morphism_theory =
    Obj.magic M.diff
  
  (** val coq_Subset_m_morphism_theory : morphism_Theory **)
  
  let coq_Subset_m_morphism_theory =
    Obj.magic __
  
  (** val subset_m_morphism_theory : morphism_Theory **)
  
  let subset_m_morphism_theory =
    Obj.magic M.subset
  
  (** val equal_m_morphism_theory : morphism_Theory **)
  
  let equal_m_morphism_theory =
    Obj.magic M.equal
  
  (** val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class **)
  
  let coq_SubsetSetoid v =
    AsymmetricReflexive v
  
  (** val coq_SubsetSetoid_precise_relation_class :
      reflexive_Relation_Class **)
  
  let coq_SubsetSetoid_precise_relation_class =
    RAsymmetric
  
  (** val coq_SubsetSetoid_morphism : morphism_Theory **)
  
  let coq_SubsetSetoid_morphism =
    Obj.magic __
  
  (** val coq_In_s_m_morphism_theory : morphism_Theory **)
  
  let coq_In_s_m_morphism_theory =
    Obj.magic __
  
  (** val coq_Empty_s_m_morphism_theory : morphism_Theory **)
  
  let coq_Empty_s_m_morphism_theory =
    Obj.magic __
  
  (** val add_s_m_morphism_theory : morphism_Theory **)
  
  let add_s_m_morphism_theory =
    Obj.magic M.add
  
  (** val remove_s_m_morphism_theory : morphism_Theory **)
  
  let remove_s_m_morphism_theory =
    Obj.magic M.remove
  
  (** val union_s_m_morphism_theory : morphism_Theory **)
  
  let union_s_m_morphism_theory =
    Obj.magic M.union
  
  (** val inter_s_m_morphism_theory : morphism_Theory **)
  
  let inter_s_m_morphism_theory =
    Obj.magic M.inter
  
  (** val diff_s_m_morphism_theory : morphism_Theory **)
  
  let diff_s_m_morphism_theory =
    Obj.magic M.diff
 end

module WeakDecide = 
 functor (M:Coq_S) ->
 functor (D:DecidableType with type t= M.E.t with type eq=
 __) ->
 struct 
  module FSetLogicalFacts = 
   struct 
    
   end
  
  module FSetDecideAuxiliary = 
   struct 
    module F = Facts(M)(D)
   end
  
  module FSetDecideTestCases = 
   struct 
    
   end
 end

module Properties = 
 functor (M:S) ->
 struct 
  module D = OT_as_DT(M.E)
  
  module FM = Facts(M)(D)
  
  module Dec = WeakDecide(M)(D)
  
  (** val coq_In_dec : M.elt -> M.t -> sumbool **)
  
  let coq_In_dec x s =
    match M.mem x s with
      | True -> Left
      | False -> Right
  
  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)
  
  let cardinal_inv_2 s n =
    match M.elements s with
      | Nil -> assert false (* absurd case *)
      | Cons (e, l) -> e
  
  (** val cardinal_inv_2b : M.t -> M.elt **)
  
  let cardinal_inv_2b s =
    match M.cardinal s with
      | O -> assert false (* absurd case *)
      | S n ->
          (match M.elements s with
             | Nil -> assert false (* absurd case *)
             | Cons (e, l) -> e)
  
  (** val cardinal_m_morphism_theory : morphism_Theory **)
  
  let cardinal_m_morphism_theory =
    Obj.magic M.cardinal
  
  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1 **)
  
  let set_induction x x0 s =
    let rec f n s0 =
      match n with
        | O -> x s0 __
        | S n0 ->
            let s1 =
              match M.elements s0 with
                | Nil -> assert false (* absurd case *)
                | Cons (e, l) -> e
            in
            x0 (M.remove s1 s0) s0 (f n0 (M.remove s1 s0)) s1 __ __
    in f (M.cardinal s) s
 end

module NatSet = Make(Nat_as_OT)

module GeneralProperties = Properties(NatSet)

(** val extendible_to_n : NatSet.t -> nat -> NatSet.t -> NatSet.t **)

let rec extendible_to_n town n b' =
  match n with
    | O -> NatSet.empty
    | S n0 ->
        (match le_lt_eq_dec (NatSet.cardinal b') (S n0) with
           | Left ->
               let s = extendible_to_n town n0 b' in
               NatSet.add
                 (GeneralProperties.cardinal_inv_2 
                   (NatSet.diff town s)
                   (pred (NatSet.cardinal (NatSet.diff town s)))) s
           | Right -> b')

(** val inductive_invariant :
    NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> nat ->
    NatSet.t **)

let rec inductive_invariant town n property = function
  | O -> NatSet.empty
  | S n0 ->
      let s = inductive_invariant town n property n0 in
      NatSet.add (property (extendible_to_n town n s) __ __) s

(** val aMM11262 :
    NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> NatSet.elt **)

let aMM11262 town n property =
  let s = inductive_invariant town n property n in
  property (NatSet.diff town (NatSet.add (property s __ __) s)) __ __

(** val town_1 : NatSet.t **)

let town_1 =
  NatSet.add (S O)
    (NatSet.add (S (S O)) (NatSet.add (S (S (S O))) NatSet.empty))

(** val subsets_1 : NatSet.t -> sumbool sumor **)

let subsets_1 b =
  match GeneralProperties.coq_In_dec (S O) b with
    | Left -> Inleft Left
    | Right ->
        (match GeneralProperties.coq_In_dec (S (S O)) b with
           | Left -> Inleft Right
           | Right ->
               (match GeneralProperties.coq_In_dec (S (S (S O))) b with
                  | Left -> Inright
                  | Right -> assert false (* absurd case *)))

(** val acquintance_1 : NatSet.t -> NatSet.elt **)

let acquintance_1 b =
  match subsets_1 b with
    | Inleft s -> (match s with
                     | Left -> S (S O)
                     | Right -> S O)
    | Inright -> S (S O)

(** val social_citizen_1 : NatSet.elt **)

let social_citizen_1 =
  aMM11262 town_1 (S O) (fun x _ _ -> acquintance_1 x)

