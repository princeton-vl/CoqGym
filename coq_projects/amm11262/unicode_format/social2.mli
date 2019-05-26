type __ = Obj.t

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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
  | Left
  | Right

type 'a sumor =
  | Inleft of 'a
  | Inright

val pred : nat -> nat

val lt_eq_lt_dec : nat -> nat -> sumbool sumor

val le_lt_eq_dec : nat -> nat -> sumbool

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

val length : 'a1 list -> nat

type 'x compare =
  | LT
  | EQ
  | GT

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
 end

module OrderedTypeFacts : 
 functor (O:OrderedType) ->
 sig 
  val eq_dec : O.t -> O.t -> sumbool
  
  val lt_dec : O.t -> O.t -> sumbool
  
  val eqb : O.t -> O.t -> bool
 end

module Nat_as_OT : 
 sig 
  type t = nat
  
  val compare : t -> t -> nat compare
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

module Raw : 
 functor (X:OrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare
   end
  
  module MX : 
   sig 
    val eq_dec : X.t -> X.t -> sumbool
    
    val lt_dec : X.t -> X.t -> sumbool
    
    val eqb : X.t -> X.t -> bool
   end
  
  type elt = X.t
  
  type t = elt list
  
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
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
  
  val compare : t -> t -> t compare
 end

module Make : 
 functor (X:OrderedType) ->
 sig 
  module Raw : 
   sig 
    module E : 
     sig 
      type t = X.t
      
      val compare : t -> t -> t compare
     end
    
    module MX : 
     sig 
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t = elt list
    
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
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val cardinal : t -> nat
    
    val elements : t -> elt list
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
    
    val choose : t -> elt option
    
    val compare : t -> t -> t compare
   end
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare
   end
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val this : slist -> Raw.t
  
  type t = slist
  
  type elt = X.t
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> nat
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val compare : t -> t -> t compare
 end

module type DecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
 end

module OT_as_DT : 
 functor (O:OrderedType) ->
 sig 
  module OF : 
   sig 
    val eq_dec : O.t -> O.t -> sumbool
    
    val lt_dec : O.t -> O.t -> sumbool
    
    val eqb : O.t -> O.t -> bool
   end
  
  type t = O.t
  
  val eq_dec : O.t -> O.t -> sumbool
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

module Facts : 
 functor (M:Coq_S) ->
 functor (D:DecidableType with type t= M.E.t with type eq=
 __) ->
 sig 
  val eqb : D.t -> D.t -> bool
  
  val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
  
  val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
  
  val coq_EltSetoid_morphism : morphism_Theory
  
  val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
  
  val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
  
  val coq_EqualSetoid_morphism : morphism_Theory
  
  val coq_In_m_morphism_theory : morphism_Theory
  
  val is_empty_m_morphism_theory : morphism_Theory
  
  val coq_Empty_m_morphism_theory : morphism_Theory
  
  val mem_m_morphism_theory : morphism_Theory
  
  val singleton_m_morphism_theory : morphism_Theory
  
  val add_m_morphism_theory : morphism_Theory
  
  val remove_m_morphism_theory : morphism_Theory
  
  val union_m_morphism_theory : morphism_Theory
  
  val inter_m_morphism_theory : morphism_Theory
  
  val diff_m_morphism_theory : morphism_Theory
  
  val coq_Subset_m_morphism_theory : morphism_Theory
  
  val subset_m_morphism_theory : morphism_Theory
  
  val equal_m_morphism_theory : morphism_Theory
  
  val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
  
  val coq_SubsetSetoid_precise_relation_class : reflexive_Relation_Class
  
  val coq_SubsetSetoid_morphism : morphism_Theory
  
  val coq_In_s_m_morphism_theory : morphism_Theory
  
  val coq_Empty_s_m_morphism_theory : morphism_Theory
  
  val add_s_m_morphism_theory : morphism_Theory
  
  val remove_s_m_morphism_theory : morphism_Theory
  
  val union_s_m_morphism_theory : morphism_Theory
  
  val inter_s_m_morphism_theory : morphism_Theory
  
  val diff_s_m_morphism_theory : morphism_Theory
 end

module WeakDecide : 
 functor (M:Coq_S) ->
 functor (D:DecidableType with type t= M.E.t with type eq=
 __) ->
 sig 
  module FSetLogicalFacts : 
   sig 
    
   end
  
  module FSetDecideAuxiliary : 
   sig 
    module F : 
     sig 
      val eqb : M.E.t -> M.E.t -> bool
      
      val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
      
      val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
      
      val coq_EltSetoid_morphism : morphism_Theory
      
      val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
      
      val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
      
      val coq_EqualSetoid_morphism : morphism_Theory
      
      val coq_In_m_morphism_theory : morphism_Theory
      
      val is_empty_m_morphism_theory : morphism_Theory
      
      val coq_Empty_m_morphism_theory : morphism_Theory
      
      val mem_m_morphism_theory : morphism_Theory
      
      val singleton_m_morphism_theory : morphism_Theory
      
      val add_m_morphism_theory : morphism_Theory
      
      val remove_m_morphism_theory : morphism_Theory
      
      val union_m_morphism_theory : morphism_Theory
      
      val inter_m_morphism_theory : morphism_Theory
      
      val diff_m_morphism_theory : morphism_Theory
      
      val coq_Subset_m_morphism_theory : morphism_Theory
      
      val subset_m_morphism_theory : morphism_Theory
      
      val equal_m_morphism_theory : morphism_Theory
      
      val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
      
      val coq_SubsetSetoid_precise_relation_class : reflexive_Relation_Class
      
      val coq_SubsetSetoid_morphism : morphism_Theory
      
      val coq_In_s_m_morphism_theory : morphism_Theory
      
      val coq_Empty_s_m_morphism_theory : morphism_Theory
      
      val add_s_m_morphism_theory : morphism_Theory
      
      val remove_s_m_morphism_theory : morphism_Theory
      
      val union_s_m_morphism_theory : morphism_Theory
      
      val inter_s_m_morphism_theory : morphism_Theory
      
      val diff_s_m_morphism_theory : morphism_Theory
     end
   end
  
  module FSetDecideTestCases : 
   sig 
    
   end
 end

module Properties : 
 functor (M:S) ->
 sig 
  module D : 
   sig 
    module OF : 
     sig 
      val eq_dec : M.E.t -> M.E.t -> sumbool
      
      val lt_dec : M.E.t -> M.E.t -> sumbool
      
      val eqb : M.E.t -> M.E.t -> bool
     end
    
    type t = M.E.t
    
    val eq_dec : M.E.t -> M.E.t -> sumbool
   end
  
  module FM : 
   sig 
    val eqb : M.E.t -> M.E.t -> bool
    
    val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_EltSetoid_morphism : morphism_Theory
    
    val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_EqualSetoid_morphism : morphism_Theory
    
    val coq_In_m_morphism_theory : morphism_Theory
    
    val is_empty_m_morphism_theory : morphism_Theory
    
    val coq_Empty_m_morphism_theory : morphism_Theory
    
    val mem_m_morphism_theory : morphism_Theory
    
    val singleton_m_morphism_theory : morphism_Theory
    
    val add_m_morphism_theory : morphism_Theory
    
    val remove_m_morphism_theory : morphism_Theory
    
    val union_m_morphism_theory : morphism_Theory
    
    val inter_m_morphism_theory : morphism_Theory
    
    val diff_m_morphism_theory : morphism_Theory
    
    val coq_Subset_m_morphism_theory : morphism_Theory
    
    val subset_m_morphism_theory : morphism_Theory
    
    val equal_m_morphism_theory : morphism_Theory
    
    val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_SubsetSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_SubsetSetoid_morphism : morphism_Theory
    
    val coq_In_s_m_morphism_theory : morphism_Theory
    
    val coq_Empty_s_m_morphism_theory : morphism_Theory
    
    val add_s_m_morphism_theory : morphism_Theory
    
    val remove_s_m_morphism_theory : morphism_Theory
    
    val union_s_m_morphism_theory : morphism_Theory
    
    val inter_s_m_morphism_theory : morphism_Theory
    
    val diff_s_m_morphism_theory : morphism_Theory
   end
  
  module Dec : 
   sig 
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      module F : 
       sig 
        val eqb : M.E.t -> M.E.t -> bool
        
        val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
        
        val coq_EltSetoid_morphism : morphism_Theory
        
        val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
        
        val coq_EqualSetoid_morphism : morphism_Theory
        
        val coq_In_m_morphism_theory : morphism_Theory
        
        val is_empty_m_morphism_theory : morphism_Theory
        
        val coq_Empty_m_morphism_theory : morphism_Theory
        
        val mem_m_morphism_theory : morphism_Theory
        
        val singleton_m_morphism_theory : morphism_Theory
        
        val add_m_morphism_theory : morphism_Theory
        
        val remove_m_morphism_theory : morphism_Theory
        
        val union_m_morphism_theory : morphism_Theory
        
        val inter_m_morphism_theory : morphism_Theory
        
        val diff_m_morphism_theory : morphism_Theory
        
        val coq_Subset_m_morphism_theory : morphism_Theory
        
        val subset_m_morphism_theory : morphism_Theory
        
        val equal_m_morphism_theory : morphism_Theory
        
        val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_SubsetSetoid_precise_relation_class :
          reflexive_Relation_Class
        
        val coq_SubsetSetoid_morphism : morphism_Theory
        
        val coq_In_s_m_morphism_theory : morphism_Theory
        
        val coq_Empty_s_m_morphism_theory : morphism_Theory
        
        val add_s_m_morphism_theory : morphism_Theory
        
        val remove_s_m_morphism_theory : morphism_Theory
        
        val union_s_m_morphism_theory : morphism_Theory
        
        val inter_s_m_morphism_theory : morphism_Theory
        
        val diff_s_m_morphism_theory : morphism_Theory
       end
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  val coq_In_dec : M.elt -> M.t -> sumbool
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
  
  val cardinal_m_morphism_theory : morphism_Theory
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
 end

module NatSet : 
 sig 
  module Raw : 
   sig 
    module E : 
     sig 
      type t = nat
      
      val compare : t -> t -> nat compare
     end
    
    module MX : 
     sig 
      val eq_dec : nat -> nat -> sumbool
      
      val lt_dec : nat -> nat -> sumbool
      
      val eqb : nat -> nat -> bool
     end
    
    type elt = nat
    
    type t = elt list
    
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
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val cardinal : t -> nat
    
    val elements : t -> elt list
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
    
    val choose : t -> elt option
    
    val compare : t -> t -> t compare
   end
  
  module E : 
   sig 
    type t = nat
    
    val compare : t -> t -> nat compare
   end
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val this : slist -> Raw.t
  
  type t = slist
  
  type elt = nat
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> nat
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val compare : t -> t -> t compare
 end

module GeneralProperties : 
 sig 
  module D : 
   sig 
    module OF : 
     sig 
      val eq_dec : nat -> nat -> sumbool
      
      val lt_dec : nat -> nat -> sumbool
      
      val eqb : nat -> nat -> bool
     end
    
    type t = nat
    
    val eq_dec : nat -> nat -> sumbool
   end
  
  module FM : 
   sig 
    val eqb : nat -> nat -> bool
    
    val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_EltSetoid_morphism : morphism_Theory
    
    val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_EqualSetoid_morphism : morphism_Theory
    
    val coq_In_m_morphism_theory : morphism_Theory
    
    val is_empty_m_morphism_theory : morphism_Theory
    
    val coq_Empty_m_morphism_theory : morphism_Theory
    
    val mem_m_morphism_theory : morphism_Theory
    
    val singleton_m_morphism_theory : morphism_Theory
    
    val add_m_morphism_theory : morphism_Theory
    
    val remove_m_morphism_theory : morphism_Theory
    
    val union_m_morphism_theory : morphism_Theory
    
    val inter_m_morphism_theory : morphism_Theory
    
    val diff_m_morphism_theory : morphism_Theory
    
    val coq_Subset_m_morphism_theory : morphism_Theory
    
    val subset_m_morphism_theory : morphism_Theory
    
    val equal_m_morphism_theory : morphism_Theory
    
    val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
    
    val coq_SubsetSetoid_precise_relation_class : reflexive_Relation_Class
    
    val coq_SubsetSetoid_morphism : morphism_Theory
    
    val coq_In_s_m_morphism_theory : morphism_Theory
    
    val coq_Empty_s_m_morphism_theory : morphism_Theory
    
    val add_s_m_morphism_theory : morphism_Theory
    
    val remove_s_m_morphism_theory : morphism_Theory
    
    val union_s_m_morphism_theory : morphism_Theory
    
    val inter_s_m_morphism_theory : morphism_Theory
    
    val diff_s_m_morphism_theory : morphism_Theory
   end
  
  module Dec : 
   sig 
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      module F : 
       sig 
        val eqb : nat -> nat -> bool
        
        val coq_EltSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_EltSetoid_precise_relation_class : reflexive_Relation_Class
        
        val coq_EltSetoid_morphism : morphism_Theory
        
        val coq_EqualSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_EqualSetoid_precise_relation_class : reflexive_Relation_Class
        
        val coq_EqualSetoid_morphism : morphism_Theory
        
        val coq_In_m_morphism_theory : morphism_Theory
        
        val is_empty_m_morphism_theory : morphism_Theory
        
        val coq_Empty_m_morphism_theory : morphism_Theory
        
        val mem_m_morphism_theory : morphism_Theory
        
        val singleton_m_morphism_theory : morphism_Theory
        
        val add_m_morphism_theory : morphism_Theory
        
        val remove_m_morphism_theory : morphism_Theory
        
        val union_m_morphism_theory : morphism_Theory
        
        val inter_m_morphism_theory : morphism_Theory
        
        val diff_m_morphism_theory : morphism_Theory
        
        val coq_Subset_m_morphism_theory : morphism_Theory
        
        val subset_m_morphism_theory : morphism_Theory
        
        val equal_m_morphism_theory : morphism_Theory
        
        val coq_SubsetSetoid : 'a1 -> 'a1 x_Relation_Class
        
        val coq_SubsetSetoid_precise_relation_class :
          reflexive_Relation_Class
        
        val coq_SubsetSetoid_morphism : morphism_Theory
        
        val coq_In_s_m_morphism_theory : morphism_Theory
        
        val coq_Empty_s_m_morphism_theory : morphism_Theory
        
        val add_s_m_morphism_theory : morphism_Theory
        
        val remove_s_m_morphism_theory : morphism_Theory
        
        val union_s_m_morphism_theory : morphism_Theory
        
        val inter_s_m_morphism_theory : morphism_Theory
        
        val diff_s_m_morphism_theory : morphism_Theory
       end
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  val coq_In_dec : NatSet.elt -> NatSet.t -> sumbool
  
  val cardinal_inv_2 : NatSet.t -> nat -> NatSet.elt
  
  val cardinal_inv_2b : NatSet.t -> NatSet.elt
  
  val cardinal_m_morphism_theory : morphism_Theory
  
  val set_induction :
    (NatSet.t -> __ -> 'a1) -> (NatSet.t -> NatSet.t -> 'a1 -> NatSet.elt ->
    __ -> __ -> 'a1) -> NatSet.t -> 'a1
 end

val extendible_to_n : NatSet.t -> nat -> NatSet.t -> NatSet.t

val inductive_invariant :
  NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> nat -> NatSet.t

val aMM11262 :
  NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> NatSet.elt

val town_2 : NatSet.t

val subsets_2 :
  NatSet.t -> sumbool sumor sumor sumor sumor sumor sumor sumor sumor

val acquintance_2 : NatSet.t -> NatSet.elt

val social_citizen_2 : NatSet.elt

