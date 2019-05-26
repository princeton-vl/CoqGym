(* File: Derivable_Def.v  (last edited on 1/11/2000) (c) Klaus Weich  *)


Require Export Derivations.

(*******************************************************************)

Inductive Derivable (context : flist) (a : form) : Prop :=
    Derivable_Intro :
      forall t : proof_term, derives context t a -> Derivable context a.


Inductive Derivable2 (context : flist) (a b : form) : Prop :=
    Derivable2_Intro :
      Derivable context a -> Derivable context b -> Derivable2 context a b.
