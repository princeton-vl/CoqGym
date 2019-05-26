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
(*            2nd definition (Equational) of Adjunctions       		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export IdCAT.
Require Export Adj_UA.

Set Implicit Arguments.
Unset Strict Implicit.

(* lois des NT: eta et epsilon *)

Section adj1_def.

Variables (C D : Category) (F : Functor D C) (G : Functor C D).

 Section adj1_laws.

 Variables (eta : NT (Id_CAT D) (F o_F G)) (eps : NT (G o_F F) (Id_CAT C)).

 (* Rmq: on utilise idCAT, qui de'finit Id_CAT sans parler
    de Functor_Setoid. Evitant ainsi l'inconsistance des
    univers *)

 Definition Adj1_law1 :=
   forall c : C, eta (G c) o FMor G (eps c) =_S Id (G c).

 Definition Adj1_law2 :=
   forall d : D, FMor F (eta d) o eps (F d) =_S Id (F d).

 End adj1_laws.

 Structure Adj1 : Type := 
   {A_eta : NT (Id_CAT D) (F o_F G);
    A_eps : NT (G o_F F) (Id_CAT C);
    Prf_Adj1_law1 : Adj1_law1 A_eta A_eps;
    Prf_Adj1_law2 : Adj1_law2 A_eta A_eps}.

End adj1_def.

Section adj_to_adj1.

Variables (C D : Category) (F : Functor D C) (G : Functor C D) (ad : Adj F G).

(* *)

Definition Unit_tau (d : D) := UA_mor (Unit ad d).

Lemma Unit_nt_law : NT_law (F:=Id_CAT D) (G:=F o_F G) Unit_tau.
Proof.
unfold NT_law, Unit_tau in |- *; simpl in |- *.
unfold Unit_arrow in |- *.
unfold FMor at 1 2 in |- *; simpl in |- *.
unfold Comp_FMor, Comp_FOb, Id_CAT_ob in |- *; intros d1 d2 f.
(* *) apply Trans with (ApAphi ad (FMor F f o Id (F d2))).
apply Sym; apply (Adj_eq4 ad f (Id (F d2))).
(* *) apply Trans with (ApAphi ad (Id (F d1) o FMor F f)).
apply AphiPres; apply Idrl.
apply (Adj_eq3 ad (FMor F f) (Id (F d1))).
Qed.

Canonical Structure Unit_NT := Build_NT Unit_nt_law.

(* *)

Definition CoUnit_tau (c : C) := CoUA_mor (CoUnit ad c).

Lemma CoUnit_nt_law : NT_law (F:=G o_F F) (G:=Id_CAT C) CoUnit_tau.
Proof.
unfold NT_law, CoUnit_tau in |- *; simpl in |- *.
unfold CoUnit_arrow in |- *.
unfold FMor at 1 2 in |- *; simpl in |- *.
unfold Comp_FMor, Comp_FOb, Id_CAT_ob in |- *.
intros c1 c2 f.
(* *) apply Trans with (ApAphi_inv ad (FMor G f o Id (G c2))).
apply Sym; apply (Adj_eq6 ad (FMor G f) (Id (G c2))). 
(* *) apply Trans with (ApAphi_inv ad (Id (G c1) o FMor G f)).
apply Aphi_invPres; apply Idrl.
apply (Adj_eq5 ad f (Id (G c1))).
Qed.
 
Canonical Structure CoUnit_NT := Build_NT CoUnit_nt_law.

(* Unit et CoUnit verifient ces deux lois *)

Lemma Unit_and_CoUnit_law1 : Adj1_law1 Unit_NT CoUnit_NT.
Proof.
unfold Adj1_law1, Unit_NT, CoUnit_NT in |- *; simpl in |- *.
unfold Unit_tau, CoUnit_tau in |- *; simpl in |- *.
unfold Unit_arrow, CoUnit_arrow, Id_CAT_ob in |- *.
intro c.
(* *) apply Trans with (ApAphi ad (Id (F (G c)) o ApAphi_inv ad (Id (G c)))).
apply Sym; apply (Adj_eq3 ad (ApAphi_inv ad (Id (G c))) (Id (F (G c)))).
(* *) apply Trans with (ApAphi ad (ApAphi_inv ad (Id (G c)))).
apply AphiPres; apply Idl.
apply (Idl_inv (NTa_areIso ad (Build_POb1 (G c) c)) (Id (G c))).
Qed.

Lemma Unit_and_CoUnit_law2 : Adj1_law2 Unit_NT CoUnit_NT.
Proof.
unfold Adj1_law2, Unit_NT, CoUnit_NT in |- *; simpl in |- *.
unfold Unit_tau, CoUnit_tau in |- *; simpl in |- *.
unfold Unit_arrow, CoUnit_arrow, Id_CAT_ob in |- *.
intro d.
(* *) apply Trans with (ApAphi_inv ad (ApAphi ad (Id (F d)) o Id (G (F d)))).
apply Sym; apply (Adj_eq6 ad (ApAphi ad (Id (F d))) (Id (G (F d)))).
(* *) apply Trans with (ApAphi_inv ad (ApAphi ad (Id (F d)))).
apply Aphi_invPres; apply Idr1.
apply (Idr_inv (NTa_areIso ad (Build_POb1 d (F d))) (Id (F d))).
Qed.

Canonical Structure Adj_to_Adj1 :=
  Build_Adj1 Unit_and_CoUnit_law1 Unit_and_CoUnit_law2.

End adj_to_adj1.

Coercion Adj_to_Adj1 : Adj >-> Adj1.

(* *)

Section adj1_to_adj.

Variables (C D : Category) (F : Functor D C) (G : Functor C D)
  (ad : Adj1 F G).

(* a` partir de ces elements, construisons une adjunction, i.e.
   un iso teta : C(F-,-) -> D(-,G-) *)

 Section teta_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition Teta_arrow (f : F (OB_l dxc) --> Ob_r dxc) :=
   A_eta ad (OB_l dxc) o FMor G f.

 Lemma Teta_arrow_map_law : Map_law Teta_arrow.
 Proof.
 unfold Map_law, Teta_arrow in |- *.
 intros f g H.
 unfold FOb at 1 in |- *; simpl in |- *; unfold Id_CAT_ob in |- *.
 apply Comp_l.
 unfold Comp_FOb in |- *; apply FPres; assumption.
 Qed.

 Canonical Structure Teta_tau := Build_Map Teta_arrow_map_law.

 End teta_tau_def.

Lemma Teta_tau_NT_law : NT_law (F:=FunSET2_r F) (G:=FunSET2_l G) Teta_tau.
Proof.
unfold NT_law, Teta_tau, Teta_arrow in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold FunSET2_r_mor1, FunSET2_l_mor1 in |- *.
unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_l_ob in |- *.
(* *) apply
       Trans
        with
          (A_eta ad (OB_l d2xc2)
           o FMor G (FMor F (HOM_l fxg) o h) o FMor G (Hom_r fxg)).
apply Comp_l; unfold FOb at 1 in |- *; simpl in |- *; unfold Comp_FOb in |- *;
 apply FComp.
(* *) apply
       Trans
        with
          ((A_eta ad (OB_l d2xc2) o FMor G (FMor F (HOM_l fxg) o h))
           o FMor G (Hom_r fxg)).
apply Ass.
apply Comp_r.
(* *) apply
       Trans
        with (A_eta ad (OB_l d2xc2) o FMor G (FMor F (HOM_l fxg)) o FMor G h).
apply Comp_l.
unfold FOb at 1 in |- *; simpl in |- *; unfold Comp_FOb in |- *; apply FComp.
(* *) apply
       Trans
        with
          ((A_eta ad (OB_l d2xc2) o FMor G (FMor F (HOM_l fxg))) o FMor G h).
apply Ass.
(* *) apply Trans with ((HOM_l fxg o A_eta ad (OB_l d1xc1)) o FMor G h).
apply Comp_r; apply Sym.
apply (Prf_NT_law (A_eta ad) (HOM_l fxg)).
apply Ass1.
Qed.

Canonical Structure Teta := Build_NT Teta_tau_NT_law.

(* Construisons maintenant Teta_1 *)

 Section teta_1_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition Teta_1_arrow (g : OB_l dxc --> G (Ob_r dxc)) :=
   FMor F g o A_eps ad (Ob_r dxc).

 Lemma Teta_1_arrow_Map_law : Map_law Teta_1_arrow.
 Proof.
 unfold Map_law, Teta_1_arrow in |- *.
 intros f g H.
 apply Comp_r; apply FPres; assumption.
 Qed.

 Canonical Structure Teta_1_tau := Build_Map Teta_1_arrow_Map_law.

 End teta_1_tau_def.

Lemma Teta_1_tau_NT_law : NT_law (F:=FunSET2_l G) (G:=FunSET2_r F) Teta_1_tau.
Proof.
unfold NT_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold Teta_1_arrow, FunSET2_r_mor1, FunSET2_l_mor1 in |- *.
unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_r_ob in |- *.
(* *) apply
       Trans
        with
          ((FMor F (HOM_l fxg o h) o FMor F (FMor G (Hom_r fxg)))
           o A_eps ad (Ob_r d2xc2)).
apply Comp_r; apply FComp.
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg o h)
           o FMor F (FMor G (Hom_r fxg)) o A_eps ad (Ob_r d2xc2)).
apply Ass1.
(* *) apply
       Trans
        with
          ((FMor F (HOM_l fxg) o FMor F h)
           o FMor F (FMor G (Hom_r fxg)) o A_eps ad (Ob_r d2xc2)).
apply Comp_r; apply FComp. 
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg)
           o FMor F h o FMor F (FMor G (Hom_r fxg)) o A_eps ad (Ob_r d2xc2)).
apply Ass1.
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg)
           o (FMor F h o A_eps ad (Ob_r d1xc1)) o Hom_r fxg).
apply Comp_l.
(* *) apply Trans with (FMor F h o A_eps ad (Ob_r d1xc1) o Hom_r fxg).
apply Comp_l; apply (Prf_NT_law (A_eps ad) (Hom_r fxg)).
apply Ass.
apply Ass.
Qed.

Canonical Structure Teta_1 := Build_NT Teta_1_tau_NT_law.

(* dem. que Teta et Teta_1 sont iso *)

(* a` prouver: eta(d) o G(Ff o eps(c)) = f *)
(* f o eta(Gc) o G(eps(c)) =f (car eta NT) *)
(* f o Id(Gc) = f                 (car C1)     *)

 Section teta_iso.

 Variable dxc : POb (Dual D) C.

 Lemma Teta_1_o_Teta : AreIsos (Teta dxc) (Teta_1 dxc).
 Proof.
 unfold AreIsos, RIso_law in |- *; split; simpl in |- *; unfold Ext in |- *;
  simpl in |- *.
 unfold Teta_arrow, Id_fun, Teta_1_arrow in |- *.
 unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_l_ob in |- *.
 intros f.
 (* *) apply
        Trans
         with
           (A_eta ad (OB_l dxc)
            o FMor G (FMor F f) o FMor G (A_eps ad (Ob_r dxc))).
 apply Comp_l.
 unfold Comp_Functor in |- *; simpl in |- *; unfold Comp_FOb in |- *;
  apply FComp.
 (* *) apply
        Trans
         with
           ((A_eta ad (OB_l dxc) o FMor G (FMor F f))
            o FMor G (A_eps ad (Ob_r dxc))).
 apply Ass.
 (* *) apply
        Trans
         with ((f o A_eta ad (G (Ob_r dxc))) o FMor G (A_eps ad (Ob_r dxc))).
 apply Comp_r; apply Sym; apply (Prf_NT_law (A_eta ad) f).
 (* *) apply
        Trans
         with (f o A_eta ad (G (Ob_r dxc)) o FMor G (A_eps ad (Ob_r dxc))).
 apply Ass1.
 (* *) apply Trans with (f o Id (G (Ob_r dxc))).
 apply Comp_l; apply (Prf_Adj1_law1 ad (Ob_r dxc)).
 apply Idr1.
 (**)
 unfold Teta_1_arrow, Teta_arrow, Id_fun in |- *.
 unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_r_ob in |- *; intro f.
 (* *) apply
        Trans
         with
           ((FMor F (A_eta ad (OB_l dxc)) o FMor F (FMor G f))
            o A_eps ad (Ob_r dxc)).
 apply Comp_r; apply FComp.
 (* *) apply
        Trans
         with
           (FMor F (A_eta ad (OB_l dxc))
            o FMor F (FMor G f) o A_eps ad (Ob_r dxc)).
 apply Ass1.
 (* *) apply
        Trans
         with (FMor F (A_eta ad (OB_l dxc)) o A_eps ad (F (OB_l dxc)) o f).
 apply Comp_l; apply (Prf_NT_law (A_eps ad) f).
 (* *) apply
        Trans
         with ((FMor F (A_eta ad (OB_l dxc)) o A_eps ad (F (OB_l dxc))) o f).
 apply Ass.
 (* *) apply Trans with (Id (F (OB_l dxc)) o f).
 apply Comp_r; apply (Prf_Adj1_law2 ad (OB_l dxc)).
 apply Idl.
 Qed.

 End teta_iso.

Definition Adj1_to_Adj := Build_Adj (NT_Iso Teta_1_o_Teta).

End adj1_to_adj.
 
Coercion Adj1_to_Adj : Adj1 >-> Adj.

(* Les deux defs sont e'quivalentes: a faire *)

Section adj_equiv.

Variables (C D : Category) (F : Functor D C) (G : Functor C D).

Definition Eq_Adj (ad ad' : Adj F G) := ad =_NT ad'.

Definition Eq_Adj1 (ad ad' : Adj1 F G) :=
  A_eta ad =_NT A_eta ad' /\ A_eps ad =_NT A_eps ad'.

End adj_equiv.

