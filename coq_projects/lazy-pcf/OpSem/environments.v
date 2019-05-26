(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  environments.v                                                          *)
(*                                                                          *)
(*  This file contains the definitions of type environments,                *)
(*  operational semantics environments, and configurations.                 *)
(*  It also contains the function mapsto which interprets                   *)
(*  type environments as partial mappings, and functions that               *)
(*  return the domains of environments.                                     *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              environments.v                              *)
(****************************************************************************)

Require Import syntax.

Require Import List.

(******************************)
(* (member x L)               *)
(*                            *)
(*  Defines when an element x *)
(*  is contained in a list L. *)
(*                            *)
(******************************)
Fixpoint member (A : Set) (b : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | a :: m => a = b \/ member A b m
  end.
(*
Definition member :=                                  
 [A:Set][b:A][l:(list A)] (<Prop>Match l with
                  (* nil *)      False 
                  (* cons a m *) [a:A][m:(list A)][P:Prop]
                                      (a=b) \/ P end).
*)

(******************************************************)
(*                                                    *)
(*  ty_env:  type environment, variable-type list.    *)
(*  OS_env:  Operational semantics environment,       *)
(*           variable-type-term list.                 *)
(*                                                    *)
(******************************************************)

Definition VT := (vari * ty)%type.
Definition ty_env := list VT.

Definition VTT := (VT * tm)%type.
Definition OS_env := list VTT.


(****************************************)
(*   Mapsto - 				*)
(*      Implements type environments as	*)
(*      partial mappings.		*)
(*					*)
(*   (mapsto x t H) -> H(x) = t		*)
(****************************************)

Definition mapsto (indx : vari) (val : ty) (l : list VT) :=
  (fix F (l0 : list VT) : Prop :=
     match l0 with
     | nil => False
     | v :: l1 => IF fst v = indx :>vari then snd v = val :>ty else F l1
     end) l.
(* Nil *) 
(* cons a m *) 



(******************************************)
(*   Configurations and their destructors *)
(******************************************)

Inductive config : Set :=
    cfg : tm -> OS_env -> config.

Definition cfgexp (c : config) := let (e, A) return tm := c in e.

Definition cfgenv (c : config) := let (e, A) return OS_env := c in A.



(**************************************************)
(*  Domain functions for type and OS environments *)
(*						  *)
(*  TE_Dom    : ty_env -> var list                *)
(*  OS_Dom    : OS_env -> var list                *)
(*  OS_Dom_ty : OS_env -> VT list                 *)
(* 						  *)
(**************************************************)

Definition TE_Dom (H : ty_env) :=
  (fix F (l : list VT) : list vari :=
     match l with
     | nil => nil (A:=vari)
     | v :: l0 => cons (fst v) (F l0)
     end) H.
(* nil *) 
(* cons vt H' *) 

Definition OS_Dom (A : OS_env) :=
  (fix F (l : list VTT) : list vari :=
     match l with
     | nil => nil (A:=vari)
     | v :: l0 => cons (fst (fst v)) (F l0)
     end) A.
(* nil *) 
(* cons vtt A' *) 

Definition OS_Dom_ty (A : OS_env) :=
  (fix F (l : list VTT) : list VT :=
     match l with
     | nil => nil (A:=VT)
     | v :: l0 => cons (fst v) (F l0)
     end) A.
(* nil *) 
(* cons vtt A' *) 

