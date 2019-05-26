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
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*	      A Functor which is a Right Adjoint is Continuous		     *)
(*                      (part of Freyd's Theorem)             		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Adj_UA.
Require Export Pres_Limits.

Set Implicit Arguments.
Unset Strict Implicit.

(* *)

Section ladj_pres.

Variables (C D : Category) (G : Functor C D) (la : LeftAdj G) 
  (J : Category) (H : Functor J C) (l : Limit H).

(* pour tout d : D et tau : Delta(d) -> T o G,
   sigma(i) = phi_1<d,Ti>(tau(i)) *)

 Section lp_diese.

 Variables (d : D) (tau : Cone d (H o_F G)).

 Definition Lp_sigma_tau (i : J) := ApAphi_inv la (tau i:d --> G (H i)).

 (* sigma est en fait un cone(T,Fd) ou` F est l'adjoint de G *)

 Lemma Lp_sigma_tau_cone_law : Cone_law Lp_sigma_tau.
 Proof.
 unfold Cone_law, Lp_sigma_tau in |- *.
 intros i j g.
 (* *) apply Trans with (ApAphi_inv la (tau i o FMor G (FMor H g))).
 apply Aphi_invPres.
 apply (Eq_cone tau g).
 apply (Adj_eq5 la (FMor H g) (tau i)).
 Qed.

 Definition Lp_sigma := Build_Cone Lp_sigma_tau_cone_law.

 (* construction de tau# *)
 (* tau# = phi<d,limT>(sigma#) *)

 Definition Lp_diese : d --> G (Lim l) := ApAphi la (Lim_diese l Lp_sigma).
 
 End lp_diese.
 
Lemma Lp_coUAlaw1 : Limit_law1 (Limiting_cone l o_C G) Lp_diese.
Proof.
unfold Limit_law1, Limit_eq in |- *; simpl in |- *; intros d tau i.
unfold Comp_cone_tau, Lp_diese in |- *.
(* *) apply
       Trans
        with (ApAphi la (Lim_diese l (Lp_sigma tau) o Limiting_cone l i)).
apply Sym.
apply (Adj_eq3 la (Limiting_cone l i) (Lim_diese l (Lp_sigma tau))).
(* *) apply Trans with (ApAphi la (ApAphi_inv (c:=H i) la (tau i))).
unfold Comp_FOb in |- *; apply AphiPres.
apply (Prf_limit1 l (Lp_sigma tau) i).
apply (Idl_inv (NTa_areIso la (Build_POb1 d (H i))) (tau i)).
Qed.

Lemma Lp_coUAlaw2 : Limit_law2 (Limiting_cone l o_C G) Lp_diese.
Proof.
unfold Limit_law2, Limit_eq in |- *; simpl in |- *; intros d tau t.
unfold Comp_cone_tau, Lp_diese in |- *.
intro H'.
(* *) apply Trans with (ApAphi la (ApAphi_inv la t)).
apply Sym.
apply (Idl_inv (NTa_areIso la (Build_POb1 d (Lim l))) t).
apply AphiPres; apply (Prf_limit2 l).
unfold Limit_eq in |- *; intro i.
(* *) apply Trans with (ApAphi_inv la (t o FMor G (Limiting_cone l i))).
apply Sym.
apply (Adj_eq5 la (Limiting_cone l i) t).
simpl in |- *; unfold Lp_sigma_tau in |- *; apply Aphi_invPres; apply (H' i).
Qed.

Lemma Ladj_Pres1 : Preserves_1limit G l.
Proof.
apply (Build_IsLimit Lp_coUAlaw1 Lp_coUAlaw2).
Defined.

End ladj_pres.

(* Si G admet un adjoint, alors il Preserve toutes les Limites *)

Lemma Ladj_continuous :
 forall (C D : Category) (G : Functor C D), LeftAdj G -> Continuous G.
Proof.
unfold Continuous, Preserves_limits in |- *; intros C D G la J H l.
apply (Ladj_Pres1 la l).
Defined.





