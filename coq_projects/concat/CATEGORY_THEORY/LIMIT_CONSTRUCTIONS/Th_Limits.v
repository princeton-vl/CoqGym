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
(*									     *)
(*	    Limits by Producys and equalizers              		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                        A.SAIBI         May 95			     *)
(*									     *)
(*****************************************************************************)

Require Export Equalizers1.
Require Export Products1.

Set Implicit Arguments.
Unset Strict Implicit.

Section thl.

Variables (C J : Category) (H1 : forall k : J -> C, Product1 k)
  (H2 : forall k : Arrs J -> C, Product1 k)
  (H3 : forall (a b : C) (f g : a --> b), Equalizer1_fg f g)
  (F : Functor J C).

Let Limit2_fg (a b : C) (f g : a --> b) := Build_Equalizer2 (H3 f g) Elt1.

(* IIi Fi *)

Definition Thl_k_Fi (i : J) := F i.

Definition Thl_l_Fi := H1 Thl_k_Fi.

Definition Thl_PI_Fi := Pi1 Thl_l_Fi.

(* ||u F(codomu) *)

Definition Thl_k_Fu (u : Arrs J) := F (Codom u).

Definition Thl_l_Fu := H2 Thl_k_Fu.

Definition Thl_PI_Fu := Pi1 Thl_l_Fu.

(* qq u. fu : IIi Fi -> ku (= F(codomu)) *)

Definition Thl_fu (u : Arrs J) := Proj1 Thl_l_Fi (Codom u).

(* donc E! f : IIi Fi -> ||u F(codomu) tq ... *)

Definition Thl_f : Thl_PI_Fi --> Thl_PI_Fu := Pd1_diese Thl_l_Fu Thl_fu.

Lemma Thl_diag1 : forall u : Arrs J, Thl_fu u =_S Thl_f o Proj1 Thl_l_Fu u.
Proof.
exact (Prf_pd1_law1 Thl_l_Fu Thl_fu).
Qed.

(* qq u. gu : IIi Fi --p(domu)--> F(domu) --Fu--> ku (= F(codomu)) *)

Definition Thl_gu (u : Arrs J) := Proj1 Thl_l_Fi (Dom u) o FMor F (Arrow u).

(* donc E! g : IIi Fi -> ||u F(codomu) tq ... *)

Definition Thl_g := Pd1_diese Thl_l_Fu Thl_gu.

Lemma Thl_diag2 : forall u : Arrs J, Thl_gu u =_S Thl_g o Proj1 Thl_l_Fu u.
Proof.
exact (Prf_pd1_law1 Thl_l_Fu Thl_gu).
Qed.

(* equalizer de f et g *)

Definition Thl_l_fg := Limit2_fg Thl_f Thl_g.

Definition Thl_d := E1_ob Thl_l_fg.
  
Definition Thl_e := E1_mor Thl_l_fg.
 
(* construction du limiting cone *)

Definition Thl_mu_tau (j : J) := Thl_e o Proj1 Thl_l_Fi j.

Lemma Thl_mu_cone_law : Cone_law Thl_mu_tau.
Proof.
unfold Cone_law in |- *; intros j k u; unfold Thl_mu_tau in |- *.
(* *) apply Trans with (Thl_e o Thl_f o Proj1 Thl_l_Fu (Build_Arrs u)).
apply Comp_l.
apply (Thl_diag1 (Build_Arrs u)).
(* *) apply Trans with (Thl_e o Proj1 Thl_l_Fi j o FMor F u).
(* *) apply Trans with (Thl_e o Thl_g o Proj1 Thl_l_Fu (Build_Arrs u)).
(* *) apply Trans with ((Thl_e o Thl_f) o Proj1 Thl_l_Fu (Build_Arrs u)).
apply Ass.
(* *) apply Trans with ((Thl_e o Thl_g) o Proj1 Thl_l_Fu (Build_Arrs u)).
apply Comp_r.
apply (Prf_E1_law1 Thl_l_fg Elt1 Elt2).
apply Ass1.
apply Comp_l.
apply Sym.
exact (Thl_diag2 (Build_Arrs u)).
apply Ass.
Qed.
 
Definition Thl_mu := Build_Cone Thl_mu_cone_law.

 Section taudiese.

 (* construction de l'ope'ration # *)

 Variables (c : C) (tau : Cone c F).

 (* Bug trad *)

 Definition Thl_h := Pd1_diese Thl_l_Fi (c:=c) (fun i : J => tau i).

 Lemma Thl_diag3 : forall i : J, tau i =_S Thl_h o Proj1 Thl_l_Fi i.
 Proof.
 intro i; apply (Prf_pd1_law1 Thl_l_Fi (r:=c) (fun i : J => tau i) i).
 Qed.

 (* hof = hog *)
 (* hof = (IIFcodu)# (+) *)
 (* tau(codu) = h o p(codu)   Thl_diag3 *)
 (*           = h o f o p(u)  Thl_diag1 *)
 (* on a (+) par unicite' de IIFcodu *)

 (* hog = (IIFcodu)# (**) *)
 (* p(domu) o Fu = g o p(u) Thl_diag2 *)
 (* h o p(domu) o Fu = h o g o p(u) *)
 (* tau(domu)   o Fu = h o g o p(u) Thl_diag3 *)
 (* tau(codomu)      = h o f o p(u) tau est un cone *)
	
 Lemma Thl_diag4 : Thl_h o Thl_f =_S Thl_h o Thl_g.
 Proof.
 (* *) apply
        Trans
         with (Pd1_diese Thl_l_Fu (c:=c) (fun u : Arrs J => tau (Codom u))).
 apply
  (Prf_pd1_law2 (l:=Thl_l_Fu) (r:=c) (h:=fun u : Arrs J => tau (Codom u))).
 unfold Product_eq in |- *; intro u.
 (* *) apply Trans with (Thl_h o Proj1 Thl_l_Fi (Codom u)).
 apply (Thl_diag3 (Codom u)).
 (* *) apply Trans with (Thl_h o Thl_f o Proj1 Thl_l_Fu u).
 apply Comp_l.
 apply (Thl_diag1 u).
 apply Ass.
 apply Sym.
 apply
  (Prf_pd1_law2 (l:=Thl_l_Fu) (r:=c) (h:=fun u : Arrs J => tau (Codom u))).
 unfold Product_eq in |- *; intro u.
 (* *) apply Trans with (tau (Dom u) o FMor F (Arrow u)).
 apply (Eq_cone tau (Arrow u)).
 (* *) apply Trans with ((Thl_h o Proj1 Thl_l_Fi (Dom u)) o FMor F (Arrow u)).
 apply Comp_r.
 apply (Thl_diag3 (Dom u)).
 (* *) apply Trans with (Thl_h o Proj1 Thl_l_Fi (Dom u) o FMor F (Arrow u)).
 apply Ass1.
 (* *) apply Trans with (Thl_h o Thl_g o Proj1 Thl_l_Fu u).
 apply Comp_l.
 apply (Thl_diag2 u).
 apply Ass.
 Qed.

 (* posons tau# = h# *)

 Definition Thl_diese := E1_diese Thl_l_fg (Prf_law1_fg Thl_diag4).

 End taudiese.

(* universalite' *)

Lemma Thl_limit1 : Limit_law1 Thl_mu Thl_diese.
Proof.
unfold Limit_law1, Limit_eq in |- *; intros c tau; simpl in |- *; intro i.
(* *) apply Trans with ((Thl_diese tau o Thl_e) o Proj1 Thl_l_Fi i).
(* *) apply Trans with (Thl_diese tau o Thl_e o Proj1 Thl_l_Fi i).
apply Refl.
apply Ass.
(* *) apply
       Trans
        with
          (Pd1_diese Thl_l_Fi (c:=c) (fun i : J => tau i) o Proj1 Thl_l_Fi i).
apply Comp_r.
apply Sym.
apply (Prf_E1_law2 Thl_l_fg (Prf_law1_fg (Thl_diag4 tau))).
apply Sym.
apply (Thl_diag3 tau i).
Qed.

(* hyp: t o mu(i) = tau(i) *)
(* s` prouver: t = tau# (=h#) *)
(* par universalite' de e, revient a` prouver:
   h = t o e 
   or, (rappel) h =def (i|->tau(i))# pour ||Fi
   donc par universalite' de IIFi, revient a` prouver:
   qq i:Ob(J). tau(i) = t o e o p(i) 
   vrai par hyp car mu(i) =def e o p(i) *)

Lemma Thl_limit2 : Limit_law2 Thl_mu Thl_diese.
Proof.
unfold Limit_law2, Limit_eq in |- *; intros c tau t H.
unfold Thl_diese in |- *; apply (Prf_E1_law3 (l:=Thl_l_fg)).
apply Sym.
unfold Thl_h in |- *.
apply (Prf_pd1_law2 (l:=Thl_l_Fi)); unfold Product_eq in |- *; intro i.
apply Trans with (t o Thl_e o Proj1 Thl_l_Fi i).
apply Sym.
exact (H i).
apply Ass.
Qed.

Definition Thl_islimit := Build_IsLimit Thl_limit1 Thl_limit2.

Definition Thl_limit := Build_Limit Thl_islimit.

End thl.







