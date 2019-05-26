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
(*	                       Adjunctions                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export NatIso.
Require Export HomFunctor2.

Set Implicit Arguments.
Unset Strict Implicit.

Section adj_def.

Variables (C D : Category) (F : Functor D C) (G : Functor C D).

SubClass Adj := NatIso (FunSET2_r F) (FunSET2_l G).

Variables (phi : NT (FunSET2_r F) (FunSET2_l G))
  (phi_1 : NT (FunSET2_l G) (FunSET2_r F)).
Variable phi_iso : AreNatIsos phi phi_1.

Definition Build_Adj : Adj := Build_NatIso phi_iso.

Variables (d : D) (c : C) (ad : Adj).
 
Definition ApAphi (f : F d --> c) : d --> G c := ad (Build_POb1 d c) f.

Definition ApAphi_inv (g : d --> G c) : F d --> c :=
  NatIso_inv ad (Build_POb1 d c) g.

(* rewrite rules *)

Lemma AphiPres : forall f g : F d --> c, f =_S g -> ApAphi f =_S ApAphi g.
Proof.
intros; unfold ApAphi in |- *; apply (Pres (ad (Build_POb1 d c))); assumption.
Qed.

Lemma Aphi_invPres :
 forall f g : d --> G c, f =_S g -> ApAphi_inv f =_S ApAphi_inv g.
Proof.
intros; unfold ApAphi_inv in |- *;
 apply (Pres (NatIso_inv ad (Build_POb1 d c))); assumption.
Qed.

End adj_def.


(* Left Adjunction *)

Structure LeftAdj (C D : Category) (G : Functor C D) : Type := 
  {Adjoint : Functor D C; Adj_l :> Adj Adjoint G}.

(* Right Adjunction *)

Structure RightAdj (C D : Category) (F : Functor D C) : Type := 
  {CoAdjoint : Functor C D; Adj_r :> Adj F CoAdjoint}.


Section adj_eqs.

Variables (C D : Category) (F : Functor D C) (G : Functor C D) (ad : Adj F G).
Variables (d d' : D) (c c' : C) (h : d' --> d) (k : c --> c') (f : F d --> c).

Lemma Adj_eq1 :
 ApAphi ad ((FMor F h o f) o k) =_S (h o ApAphi ad f) o FMor G k.
Proof.
apply (Prf_NT_law ad (Build_Pmor1 h k) f).
Qed.

Variable g : d --> G c.

Lemma Adj_eq2 :
 ApAphi_inv ad ((h o g) o FMor G k) =_S (FMor F h o ApAphi_inv ad g) o k.
Proof.
apply (Prf_NT_law (NatIso_inv ad) (Build_Pmor1 h k) g).      
Qed.
       
End adj_eqs.


Section adj_eqs1.

Variables (C D : Category) (F : Functor D C) (G : Functor C D) (ad : Adj F G).
Variables (d d' : D) (c c' : C) (h : d' --> d) (k : c --> c') 
  (f : F d --> c) (g : d --> G c).

Lemma Adj_eq3 : ApAphi ad (f o k) =_S ApAphi ad f o FMor G k.
Proof.
apply Trans with (ApAphi ad ((FMor F (Id d) o f) o k)).
apply AphiPres.
apply Comp_r.
(* *) apply Trans with (Id (F d) o f).
apply Idl1.
apply Comp_r.
apply FId1.
(* *) apply Trans with ((Id d o ApAphi ad f) o FMor G k).
apply (Adj_eq1 ad (Id d) k f).
apply Comp_r.
apply Idl.
Qed.

Lemma Adj_eq4 : ApAphi ad (FMor F h o f) =_S h o ApAphi ad f.
Proof.
(* *) apply Trans with (ApAphi ad ((FMor F h o f) o Id c)).
apply AphiPres.
apply Idr.
(* *) apply Trans with ((h o ApAphi ad f) o FMor G (Id c)).
apply (Adj_eq1 ad h (Id c) f).
(* *) apply Trans with ((h o ApAphi ad f) o Id (G c)).
apply Comp_l.
apply FId.
apply Idr1.
Qed.

Lemma Adj_eq5 : ApAphi_inv ad (g o FMor G k) =_S ApAphi_inv ad g o k.
Proof.
(* *) apply Trans with (ApAphi_inv ad ((Id d o g) o FMor G k)).
apply Aphi_invPres.
apply Comp_r.
apply Idl1.
(* *) apply Trans with ((FMor F (Id d) o ApAphi_inv ad g) o k).
apply (Adj_eq2 ad (Id d) k g).
apply Comp_r.
(* *) apply Trans with (Id (F d) o ApAphi_inv ad g).
apply Comp_r.
apply FId.
apply Idl.
Qed.
        
Lemma Adj_eq6 : ApAphi_inv ad (h o g) =_S FMor F h o ApAphi_inv ad g.
Proof.
(* *) apply Trans with (ApAphi_inv ad ((h o g) o FMor G (Id c))).
apply Aphi_invPres.
(* *) apply Trans with ((h o g) o Id (G c)).
apply Idr.
apply Comp_l.
apply FId1.
(* *) apply Trans with ((FMor F h o ApAphi_inv ad g) o Id c).
apply (Adj_eq2 ad h (Id c) g).
apply Idr1.
Qed.

End adj_eqs1.

