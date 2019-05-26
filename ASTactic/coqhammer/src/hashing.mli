open Coqterms

type namesubst = (string (* new name *) * string (* old name *)) list

(* takes a context and term and returns them in canonical form, along
   with a list of free variable substitutions made. *)
val canonical : coqcontext -> coqterm -> coqcontext * coqterm * namesubst

type 'a lift_fun = (coqterm -> coqterm) -> ('a -> 'a)

(* a hash table for coqterms which hashes up to alpha-equivalence; 'a
   = f coqterm for some functor f; the second element of the pair is
   the functor lifting function (fmap) *)
type 'a coqterms_hash = (coqcontext * coqterm, 'a) Hashtbl.t * ('a lift_fun)

val create : 'a lift_fun -> 'a coqterms_hash
val clear : 'a coqterms_hash -> unit
(* find_or_insert h ctx tm mk *)
val find_or_insert : 'a coqterms_hash -> coqcontext -> coqterm ->
  (coqcontext -> coqterm -> 'a) (* function creating new value, called if tm not found *) ->
  'a
