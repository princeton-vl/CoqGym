(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          InterChange Law                                                  *)
(*                                                                           *)
(*          Ge'rard Huet and Amokrane Saibi,  June 1994                      *)
(*                                                                           *)
(*****************************************************************************)

Require Export CatFunct. 

Set Implicit Arguments.
Unset Strict Implicit.

Section horz_comp.

Variables (A B C : Category) (F G : Functor A B) (F' G' : Functor B C)
  (T : NT F G) (T' : NT F' G').

Definition Ast (a : A) : (F o_F F') a --> (G o_F G') a :=
  T' (F a) o FMor G' (T a).

Lemma Ast_eq :
 forall a : A, FMor F' (T a) o T' (G a) =_S T' (F a) o FMor G' (T a).
Proof.
intro a; apply NatCond.
Qed.

Lemma Ast_nt_law : NT_law Ast.
Proof.
unfold NT_law, Ast, Comp_Functor in |- *.
unfold FMor at 1 in |- *; simpl in |- *.
unfold FMor at 3 in |- *; simpl in |- *.
unfold Comp_FMor in |- *.
intros a b f.
(* *) apply Trans with ((FMor F' (T a) o T' (G a)) o FMor G' (FMor G f)).
(* *) apply Trans with (FMor F' (FMor F f) o FMor F' (T b) o T' (G b)).
apply Comp_l; apply Sym; apply (Ast_eq b).
(* *) apply Trans with (FMor F' (T a) o FMor F' (FMor G f) o T' (G b)).
(* *) apply Trans with ((FMor F' (FMor F f) o FMor F' (T b)) o T' (G b)).
apply Ass.
(* *) apply Trans with ((FMor F' (T a) o FMor F' (FMor G f)) o T' (G b)).
apply Comp_r.
(* commutation du diagramme de gauche par fonctorialite' de F'
   et Naturalite' de T (p.18) *)
(* *) apply Trans with (FMor F' (FMor F f o T b)).
apply FComp1.
(* *) apply Trans with (FMor F' (T a o FMor G f)).
(* Fonctorialite' de F' *)
(* T Naturelle *)
apply FPres; apply NatCond.
apply FComp.
apply Ass1.
(* *) apply Trans with (FMor F' (T a) o T' (G a) o FMor G' (FMor G f)).
apply Comp_l; apply NatCond.
apply Ass.
apply Comp_r.
apply (Ast_eq a).
Qed.

Canonical Structure CompH_NT := Build_NT Ast_nt_law.

End horz_comp.

Infix "o_NTh" := CompH_NT (at level 20, right associativity).

Section interchangelaw.

Variables (A B C : Category) (F G H : Functor A B) (F' G' H' : Functor B C).
Variables (T : NT F G) (T' : NT F' G') (U : NT G H) (U' : NT G' H').

Lemma InterChange_law :
 (T o_NTh T') o_NTv U o_NTh U' =_NT (T o_NTv U) o_NTh T' o_NTv U'.
Proof.
unfold Equal_NT in |- *; intro a; simpl in |- *.
unfold CompH_NT, Comp_Functor in |- *; simpl in |- *.
unfold Ast, Comp_tau in |- *; simpl in |- *.
unfold Comp_tau in |- *.
(* *) apply
       Trans with ((T' (F a) o U' (F a)) o FMor H' (T a) o FMor H' (U a)).
(* *) apply Trans with (T' (F a) o FMor G' (T a) o U' (G a) o FMor H' (U a)).
apply Ass1.
(* *) apply Trans with (T' (F a) o U' (F a) o FMor H' (T a) o FMor H' (U a)).
apply Comp_l.
(* *) apply Trans with ((FMor G' (T a) o U' (G a)) o FMor H' (U a)).
apply Ass.
(* *) apply Trans with ((U' (F a) o FMor H' (T a)) o FMor H' (U a)).
apply Comp_r; apply NatCond.
apply Ass1.
apply Ass.
apply Comp_l; apply FComp1.
Qed.
                                           
End interchangelaw.


(* o_NTh is associative *)

Definition EqualH_NT (C D : Category) (F G F' G' : Functor C D) 
  (T : NT F G) (T' : NT F' G') := forall a : C, T a =_H T' a.

Infix "=_NTH" := EqualH_NT (at level 70).

Section assoc_horz_comp.

Variables (A B C D : Category) (F G : Functor A B) 
  (F' G' : Functor B C) (F'' G'' : Functor C D).
Variables (T : NT F G) (T' : NT F' G') (T'' : NT F'' G'').

Lemma CompH_NT_assoc : (T o_NTh T') o_NTh T'' =_NTH T o_NTh T' o_NTh T''.
Proof.
unfold EqualH_NT, CompH_NT in |- *; simpl in |- *.
unfold Ast in |- *; simpl in |- *.
unfold Comp_FOb in |- *.
unfold FMor at 4 in |- *; simpl in |- *.
unfold Comp_FMor in |- *.
intro a.
apply Build_Equal_hom.
(* *) apply
       Trans
        with
          (T'' (F' (F a)) o FMor G'' (T' (F a)) o FMor G'' (FMor G' (T a))).
apply Comp_l; apply FComp.
apply Ass.
Qed.

End assoc_horz_comp.

