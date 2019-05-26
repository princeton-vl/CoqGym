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
(*	            Existence of Right Adjoint                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Adj_UA. 

Set Implicit Arguments.
Unset Strict Implicit.

Section ua_to_radj.

Variables (C D : Category) (F : Functor D C).

Hypothesis UA_of : forall c : C, CoUA c F.

(* construction de l'adj droit *)

Definition CoadjointUA_ob (c : C) := CoUA_ob (UA_of c).
 
 Section coadjoint_ua_map_def.

 Variable c c' : C.

 Definition CoadjointUA_mor (f : c --> c') :=
   CoUA_diese (UA_of c') (CoUA_mor (UA_of c) o f).

 Lemma CoadjointUA_map_law : Map_law CoadjointUA_mor.
 Proof.
 unfold Map_law, CoadjointUA_mor in |- *; intros f g H.
 apply
  (Codiese_map (UA_of c') (x:=CoUA_mor (UA_of c) o f)
     (y:=CoUA_mor (UA_of c) o g)).
 apply Comp_l; assumption.
 Qed.

 Canonical Structure CoadjointUA_map :
   Map (c --> c') (CoadjointUA_ob c --> CoadjointUA_ob c') :=
   CoadjointUA_map_law.

 End coadjoint_ua_map_def.

Lemma CoadjointUA_id_law : Fid_law CoadjointUA_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold CoadjointUA_mor, CoadjointUA_ob in |- *.
intro c.
apply CoUA_unic1.
(* *) apply Trans with (Id (F (CoUA_ob (UA_of c))) o CoUA_mor (UA_of c)).
apply Comp_r; apply FId.
(* *) apply Trans with (CoUA_mor (UA_of c)).
apply Idl.
apply Idr.
Qed.

Lemma CoadjointUA_comp_law : Fcomp_law CoadjointUA_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
unfold CoadjointUA_mor, CoadjointUA_ob in |- *; intros c1 c2 c3 f g.
apply CoUA_unic1.
(* *) apply
       Trans
        with
          ((FMor F (CoUA_diese (UA_of c2) (CoUA_mor (UA_of c1) o f))
            o FMor F (CoUA_diese (UA_of c3) (CoUA_mor (UA_of c2) o g)))
           o CoUA_mor (UA_of c3)).
apply Comp_r; apply FComp.
(* *) apply
       Trans
        with
          (FMor F (CoUA_diese (UA_of c2) (CoUA_mor (UA_of c1) o f))
           o FMor F (CoUA_diese (UA_of c3) (CoUA_mor (UA_of c2) o g))
             o CoUA_mor (UA_of c3)).
apply Ass1.
(* *) apply
       Trans
        with
          (FMor F (CoUA_diese (UA_of c2) (CoUA_mor (UA_of c1) o f))
           o CoUA_mor (UA_of c2) o g).
apply Comp_l; apply CoUA_diag.

(* *) apply
       Trans
        with
          ((FMor F (CoUA_diese (UA_of c2) (CoUA_mor (UA_of c1) o f))
            o CoUA_mor (UA_of c2)) o g).
apply Ass.

(* *) apply Trans with ((CoUA_mor (UA_of c1) o f) o g).
apply Comp_r; apply CoUA_diag.
apply Ass1.
Qed.

Canonical Structure CoadjointUA :=
  Build_Functor CoadjointUA_comp_law CoadjointUA_id_law.

(* *)

(* definition de PhiUA':C(F-,-) -> D(-,G-) *)

 Section psi_ua_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition PsiUA_arrow (f : F (Ob_l dxc) --> Ob_r dxc) :=
   CoUA_diese (UA_of (Ob_r dxc)) f.

 Lemma PsiUA_arrow_map_law : Map_law PsiUA_arrow.
 Proof.
 unfold Map_law, PsiUA_arrow in |- *.
 intros f g H.
 apply (Codiese_map (UA_of (Ob_r dxc)) (x:=f) (y:=g)).
 assumption.
 Qed.

 Canonical Structure PsiUA_tau := Build_Map PsiUA_arrow_map_law.

 End psi_ua_tau_def.

Lemma PsiUA_tau_nt_law :
 NT_law (F:=FunSET2_r F) (G:=FunSET2_l CoadjointUA) PsiUA_tau.
Proof.
unfold NT_law, PsiUA_tau, PsiUA_arrow in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold FunSET2_r_mor1, FunSET2_l_mor1, FunSET2_l_ob in |- *; simpl in |- *;
 unfold CoadjointUA_ob in |- *.
apply CoUA_unic1.
(* *) apply
       Trans
        with
          ((FMor F (HOM_l fxg o CoUA_diese (UA_of (Ob_r d1xc1)) h)
            o FMor F (FMor CoadjointUA (Hom_r fxg)))
           o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Comp_r; apply FComp.
(* *) apply
       Trans
        with
          (((FMor F (HOM_l fxg) o FMor F (CoUA_diese (UA_of (Ob_r d1xc1)) h))
            o FMor F (FMor CoadjointUA (Hom_r fxg)))
           o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Comp_r; apply Comp_r; apply FComp.
(* *) apply
       Trans
        with
          ((FMor F (HOM_l fxg) o FMor F (CoUA_diese (UA_of (Ob_r d1xc1)) h))
           o FMor F (FMor CoadjointUA (Hom_r fxg))
             o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Ass1.
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg)
           o FMor F (CoUA_diese (UA_of (Ob_r d1xc1)) h)
             o FMor F (FMor CoadjointUA (Hom_r fxg))
               o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Ass1.
(* *) apply Trans with (FMor F (HOM_l fxg) o h o Hom_r fxg).
apply Comp_l.
(* *) apply
       Trans
        with
          (FMor F (CoUA_diese (UA_of (Ob_r d1xc1)) h)
           o CoUA_mor (UA_of (Ob_r d1xc1)) o Hom_r fxg).
apply Comp_l.
unfold FMor at 2 in |- *; simpl in |- *;
 unfold CoadjointUA_mor, CoadjointUA_ob in |- *.
apply CoUA_diag.
(* *) apply
       Trans
        with
          ((FMor F (CoUA_diese (UA_of (Ob_r d1xc1)) h)
            o CoUA_mor (UA_of (Ob_r d1xc1))) o Hom_r fxg).
apply Ass.
apply Comp_r; apply CoUA_diag.
apply Ass.
Qed.

Canonical Structure PsiUA := Build_NT PsiUA_tau_nt_law.
               
(* PsiUA_1 *)

 Section psi_ua_1_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition PsiUA_1_arrow (f : OB_l dxc --> CoadjointUA (Ob_r dxc)) :=
   FMor F f o CoUA_mor (UA_of (Ob_r dxc)).

 Lemma PsiUA_1_arrow_map_law : Map_law PsiUA_1_arrow.                     
 Proof.
 unfold Map_law, PsiUA_1_arrow in |- *.
 intros f g H.
 apply Comp_r; apply FPres; assumption. 
 Qed.

 Canonical Structure PsiUA_1_tau := Build_Map PsiUA_1_arrow_map_law.
 
 End psi_ua_1_tau_def.
      
Lemma PsiUA_1_tau_nt_law :
 NT_law (F:=FunSET2_l CoadjointUA) (G:=FunSET2_r F) PsiUA_1_tau.
Proof.
unfold NT_law, PsiUA_1_tau, PsiUA_1_arrow in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold FunSET2_r_mor1, FunSET2_l_mor1 in |- *.
unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_r_ob in |- *.
(* *) apply
       Trans
        with
          (((FMor F (HOM_l fxg) o FMor F h)
            o FMor F (FMor CoadjointUA (Hom_r fxg)))
           o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Comp_r.
(* *) apply
       Trans
        with (FMor F (HOM_l fxg o h) o FMor F (FMor CoadjointUA (Hom_r fxg))).
apply FComp.
apply Comp_r; apply FComp.
(* *) apply
       Trans
        with
          ((FMor F (HOM_l fxg) o FMor F h)
           o FMor F (FMor CoadjointUA (Hom_r fxg))
             o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Ass1.
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg)
           o FMor F h
             o FMor F (FMor CoadjointUA (Hom_r fxg))
               o CoUA_mor (UA_of (Ob_r d2xc2))).
apply Ass1.
(* *) apply
       Trans
        with
          (FMor F (HOM_l fxg)
           o (FMor F h o CoUA_mor (UA_of (Ob_r d1xc1))) o Hom_r fxg).
apply Comp_l.
(* *) apply Trans with (FMor F h o CoUA_mor (UA_of (Ob_r d1xc1)) o Hom_r fxg).
apply Comp_l.
unfold FMor at 2 in |- *; simpl in |- *;
 unfold CoadjointUA_mor, CoadjointUA_ob in |- *.
apply CoUA_diag.
apply Ass.
apply Ass.
Qed.

Canonical Structure PsiUA_1 := Build_NT PsiUA_1_tau_nt_law.

(* PsiUA et PsiUA_1 sont iso *)

 Section psi_ua_iso.

 Variable dxc : POb (Dual D) C.

 Lemma PsiUA_1_o_PsiUA : AreIsos (PsiUA dxc) (PsiUA_1 dxc).
 Proof.
 unfold AreIsos, RIso_law in |- *; simpl in |- *; split.
 unfold Ext in |- *; simpl in |- *.
 unfold PsiUA_arrow, Id_fun, PsiUA_1_arrow in |- *.
 intro f.
 unfold FunSET2_l_ob in |- *; simpl in |- *; unfold CoadjointUA_ob in |- *.
 apply CoUA_unic1; apply Refl.
 (**)
 unfold Ext in |- *; simpl in |- *.
 unfold PsiUA_arrow, Id_fun, PsiUA_1_arrow in |- *.
 intro f.
 unfold FunSET2_r_ob in |- *; apply (CoUA_diag (UA_of (Ob_r dxc))). 
 Qed.

 End psi_ua_iso.

Definition CoAdjUA := Build_Adj (NT_Iso PsiUA_1_o_PsiUA).

Canonical Structure RightAdjUA := Build_RightAdj CoAdjUA.

End ua_to_radj.
