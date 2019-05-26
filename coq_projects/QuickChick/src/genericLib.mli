open Names
open Declarations
open Constrexpr

type coq_expr

val hole : coq_expr

val debug_coq_expr : coq_expr -> unit

type var
val var_of_id : Id.t -> var   
val var_to_string : var -> string
val gVar : var -> coq_expr

val gInject : string -> coq_expr 

type ty_param 
val ty_param_to_string : ty_param -> string
val gTyParam : ty_param -> coq_expr

type ty_ctr
val ty_ctr_to_string : ty_ctr -> string
val gInjectTyCtr : string -> ty_ctr
val gTyCtr : ty_ctr -> coq_expr

type arg
val gArg : ?assumName:coq_expr ->
           ?assumType:coq_expr ->
           ?assumImplicit:bool ->
           ?assumGeneralized:bool ->
           unit -> arg

val arg_to_var : arg -> var
  
val str_lst_to_string : string -> string list -> string

type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

val coq_type_to_string : coq_type -> string

type constructor 
val constructor_to_string : constructor -> string
val gCtr : constructor -> coq_expr
val injectCtr : string -> constructor
val ty_ctr_to_ctr : ty_ctr -> constructor
val ctr_to_ty_ctr : constructor -> ty_ctr 

module type Ord_ty_ctr_type = sig
  type t = ty_ctr 
  val compare : t -> t -> int
  end
module Ord_ty_ctr : Ord_ty_ctr_type

module type Ord_ctr_type = sig
  type t = constructor
  val compare : t -> t -> int
  end
module Ord_ctr : Ord_ctr_type

val num_of_ctrs : constructor -> int

type ctr_rep = constructor * coq_type 
val ctr_rep_to_string : ctr_rep -> string

type dt_rep = ty_ctr * ty_param list * ctr_rep list
val dt_rep_to_string : dt_rep -> string

(* Supertype of coq_type handling potentially dependent stuff - TODO : merge *)
type dep_type = 
  | DArrow of dep_type * dep_type (* Unnamed arrows *)
  | DProd  of (var * dep_type) * dep_type (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * dep_type list (* Type Constructor *)
  | DCtr of constructor * dep_type list (* Type Constructor *)
  | DTyVar of var (* Use of a previously captured type variable *)
  | DApp of dep_type * dep_type list (* Type-level function applications *)
  | DNot of dep_type (* Negation as a toplevel *)

module OrdDepType : sig
    type t = dep_type
    val compare : t -> t -> int
end

val dep_type_to_string : dep_type -> string

type dep_ctr = constructor * dep_type
val dep_ctr_to_string : dep_ctr -> string

type dep_dt = ty_ctr * ty_param list * dep_ctr list * dep_type
val dep_dt_to_string : dep_dt -> string

val gType : ty_param list -> dep_type -> coq_expr
val get_type : Id.t -> unit
val is_inductive : constructor -> bool
val is_inductive_dt : dep_type -> bool

val nthType : int -> dep_type -> dep_type

val dep_type_len : dep_type -> int

val dep_result_type : dep_type -> dep_type

(* option type helpers *)
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val cat_maybes : 'a option list -> 'a list
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option

val qualid_to_mib : Libnames.qualid -> mutual_inductive_body
val dt_rep_from_mib : mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option

val dep_dt_from_mib : mutual_inductive_body -> dep_dt option
val coerce_reference_to_dep_dt : constr_expr -> dep_dt option

val fresh_name : string -> var 
val make_up_name : unit -> var

(* Generic Combinators *)
val gApp : ?explicit:bool -> coq_expr -> coq_expr list -> coq_expr 
val gFun : string list -> (var list -> coq_expr) -> coq_expr
val gRecFunIn : ?assumType:coq_expr -> string -> string list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gLetIn : string -> coq_expr -> (var -> coq_expr) -> coq_expr
(* TODO: HOAS-ify *)
val gLetTupleIn : var -> var list -> coq_expr -> coq_expr
  
val gMatch : coq_expr -> ?catchAll:(coq_expr option) -> ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr
val gMatchReturn : coq_expr -> ?catchAll:(coq_expr option) -> string -> (var -> coq_expr) ->
  ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr

val gRecord : (string * coq_expr) list -> coq_expr 

val gAnnot : coq_expr -> coq_expr -> coq_expr
val gFunTyped : (string * coq_expr) list -> (var list -> coq_expr) -> coq_expr
val gFunWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr
val gRecFunInWithArgs : ?assumType:coq_expr -> string -> arg list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gProdWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr

(* Specialized Pattern Matching *)

type matcher_pat = 
  | MatchCtr of constructor * matcher_pat list
  | MatchU of var

val matcher_pat_to_string : matcher_pat -> string 

val construct_match : coq_expr -> ?catch_all:(coq_expr option) -> (matcher_pat * coq_expr) list -> coq_expr 
val construct_match_with_return : coq_expr -> ?catch_all:(coq_expr option) ->
  string -> (var -> coq_expr) -> (matcher_pat * coq_expr) list -> coq_expr

(* Generic List Manipulations *)
val list_nil : coq_expr
val lst_append : coq_expr -> coq_expr -> coq_expr
val lst_appends : coq_expr list -> coq_expr
val gCons : coq_expr -> coq_expr -> coq_expr 
val gList : coq_expr list -> coq_expr

(* Generic String Manipulations *)
val gStr : string -> coq_expr
val emptyString : coq_expr 
val str_append  : coq_expr -> coq_expr -> coq_expr 
val str_appends : coq_expr list -> coq_expr
val smart_paren : coq_expr -> coq_expr

(* Pair *)
val gPair : coq_expr * coq_expr -> coq_expr
val gProd : coq_expr * coq_expr -> coq_expr
val listToPairAux : (('a *'a) -> 'a) -> ('a list) -> 'a
val gTuple      : coq_expr list -> coq_expr
val gTupleType  : coq_expr list -> coq_expr
val dtTupleType : dep_type list -> dep_type

(* Int *)
val gInt : int -> coq_expr
val gSucc : coq_expr -> coq_expr
val maximum : coq_expr list -> coq_expr
val glt : coq_expr -> coq_expr -> coq_expr
val gle : coq_expr -> coq_expr -> coq_expr

(* Eq *)
val gEq : coq_expr -> coq_expr -> coq_expr

(* Maybe *)
val gOption : coq_expr -> coq_expr
val gNone : coq_expr -> coq_expr
val gSome : coq_expr -> coq_expr -> coq_expr

(* boolean *)
val gNot   : coq_expr -> coq_expr
val g_true  : coq_expr
val g_false : coq_expr               
val decToBool : coq_expr -> coq_expr
val gBool  : coq_expr

(* unit *)
val gUnit : coq_expr
val gTT   : coq_expr
  
(* (\* Gen combinators *\) *)
(* val gGen : coq_expr -> coq_expr *)
(* val returnGen  : coq_expr -> coq_expr  *)
(* val bindGen    : coq_expr -> string -> (var -> coq_expr) -> coq_expr  *)
(* val bindGenOpt : coq_expr -> string -> (var -> coq_expr) -> coq_expr  *)

(* val oneof : coq_expr list -> coq_expr *)
(* val frequency : (coq_expr * coq_expr) list -> coq_expr *)
(* val backtracking : (coq_expr * coq_expr) list -> coq_expr *)
(* val uniform_backtracking : coq_expr list -> coq_expr *)

(* Recursion combinators / fold *)
val fold_ty  : ('a -> coq_type -> 'a) -> (ty_ctr * coq_type list -> 'a) -> (ty_param -> 'a) -> coq_type -> 'a
val fold_ty' : ('a -> coq_type -> 'a) -> 'a -> coq_type -> 'a 

val dep_fold_ty  : ('a -> dep_type -> 'a) -> ('a -> var -> dep_type -> 'a) ->
                   (ty_ctr * dep_type list -> 'a) -> (constructor * dep_type list -> 'a) -> 
                   (ty_param -> 'a) -> (var -> 'a) -> dep_type -> 'a

(* Generate Type Names *)
val generate_names_from_type : string -> coq_type -> string list 
val fold_ty_vars : (var list -> var -> coq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> coq_type -> var list -> 'a

(* val defineConstant : string -> coq_expr -> var
   val defineTypedConstant : string -> coq_expr -> coq_expr -> var *)
val declare_class_instance : ?global:bool -> ?priority:int -> arg list -> string -> (var list -> coq_expr) -> (var list -> coq_expr) -> unit 

(* List utils *)
val list_last : 'a list -> 'a 
val list_init : 'a list -> 'a list 
val list_drop_every : int -> 'a list -> 'a list
val take_last : 'a list -> 'a list -> ('a list * 'a)
val list_insert_nth : 'a -> 'a list -> int -> 'a list

val sameTypeCtr  : ty_ctr -> coq_type -> bool
val isBaseBranch : ty_ctr -> coq_type -> bool
                                                
