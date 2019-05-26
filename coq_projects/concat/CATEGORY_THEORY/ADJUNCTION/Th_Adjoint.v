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
(*	            Existence of Left Adjoint                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Adj_UA.

Set Implicit Arguments.
Unset Strict Implicit.

(* Maintenant a` partir d'un UA unit (pour tout d:D), *)
(* construire une adj *)

Section ua_to_ladj.

Variables (C D : Category) (G : Functor C D).

Hypothesis UA_of : forall d : D, UA d G.

Definition AdjointUA_ob (d : D) := UA_ob (UA_of d).

 Section adjoint_ua_map_def.

 Variable d d' : D.

 Definition AdjointUA_mor (f : d --> d') :=
   UA_diese (UA_of d) (f o UA_mor (UA_of d')).

 Lemma AdjointUA_map_law : Map_law AdjointUA_mor.
 Proof.
 unfold Map_law, AdjointUA_mor in |- *; intros f g H.
 apply
  (Diese_map (UA_of d) (x:=f o UA_mor (UA_of d')) (y:=g o UA_mor (UA_of d'))).
 apply Comp_r; assumption.
 Qed.

 Canonical Structure AdjointUA_map :
   Map (d --> d') (AdjointUA_ob d --> AdjointUA_ob d') := AdjointUA_map_law.

 End adjoint_ua_map_def.
 
(* unicite' de # pour <cd,ud> : *)
(* qq a':C. qq f':d->Ga'. qq g:cd->a'. *)
(* ud o Gg = f' => g=f'# *)

(* appliquer unicite' pour (Id(d) o ud) et Id(cd) *)

Lemma AdjointUA_id_law : Fid_law AdjointUA_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold AdjointUA_mor, AdjointUA_ob in |- *.
intro d.
apply UA_unic1.
(* *) apply Trans with (UA_mor (UA_of d) o Id (G (UA_ob (UA_of d)))).
apply Comp_l; apply FId.
(* *) apply Trans with (UA_mor (UA_of d)).
apply Idr1.
apply Idl1.
Qed.

(* revient a` prouver: ((f o g) o ud3)#1 = (f o ud2)#1 o (g o ud3)#2 *)
(* unicite' ud1 avec ((f o g) o ud3) et (f o ud2)#1 o (g o ud3)#2 *)
(* revient a` dem: ud1 o G((f o ud2)#1 o (g o ud3)#2) = (f o g) o ud3 *)
(*                            (1)   *)
(* (1) = (ud1 o G((f o ud2)#1)) o G((g o ud3)#2) (Fcomplaw) *) 
(*     = (f o ud2) o G((g o ud3)#2)              (loi #1) *)
(*     = f o (g o ud3)                           (loi #2) *) 
(* cqfd *)

Lemma AdjointUA_comp_law : Fcomp_law AdjointUA_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
unfold AdjointUA_mor, AdjointUA_ob in |- *; intros d1 d2 d3 f g.
apply UA_unic1.
(* *) apply
       Trans
        with
          (UA_mor (UA_of d1)
           o FMor G (UA_diese (UA_of d1) (f o UA_mor (UA_of d2)))
             o FMor G (UA_diese (UA_of d2) (g o UA_mor (UA_of d3)))). 
apply Comp_l; apply FComp.
(* *) apply
       Trans
        with
          ((UA_mor (UA_of d1)
            o FMor G (UA_diese (UA_of d1) (f o UA_mor (UA_of d2))))
           o FMor G (UA_diese (UA_of d2) (g o UA_mor (UA_of d3)))). 
apply Ass.
(* *) apply
       Trans
        with
          ((f o UA_mor (UA_of d2))
           o FMor G (UA_diese (UA_of d2) (g o UA_mor (UA_of d3)))).
apply Comp_r; apply UA_diag.
(* *) apply
       Trans
        with
          (f
           o UA_mor (UA_of d2)
             o FMor G (UA_diese (UA_of d2) (g o UA_mor (UA_of d3)))).
apply Ass1.
(* *) apply Trans with (f o g o UA_mor (UA_of d3)).
apply Comp_l; apply UA_diag.
apply Ass.
Qed.

Canonical Structure AdjointUA :=
  Build_Functor AdjointUA_comp_law AdjointUA_id_law.

(* definition de phi:C(F-,-) -> D(-,G-) *)

(* construction de phi *)
(* soit f: Fd ->c, phi(f)=ud o Gf : d -> G(Fd) *)

 Section phi_ua_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition PhiUA_arrow (f : UA_ob (UA_of (OB_l dxc)) --> Ob_r dxc) :=
   UA_mor (UA_of (OB_l dxc)) o FMor G f.

 Lemma PhiUA_arrow_map_law : Map_law PhiUA_arrow.
 Proof.
 unfold Map_law, PhiUA_arrow in |- *.
 intros f g H.
 apply Comp_l; apply FPres; assumption.
 Qed.

 Canonical Structure PhiUA_tau := Build_Map PhiUA_arrow_map_law.

 End phi_ua_tau_def.

(* on a a` prouver: ud2 o G(F(fo) o h o g) = fo o ud1 o Gh o Gg *)
(* => ud2 o G(Ffo) = fo o ud1 *)
(* or Ffo = (fo o ud1)#2 *)
(* donc: ud2 o G((fo o ud1)#2) = fo o ud *)
(* vrai car c'est #2 law *)

Lemma PhiUA_tau_nt_law :
 NT_law (F:=FunSET2_r AdjointUA) (G:=FunSET2_l G) PhiUA_tau.
Proof.
unfold NT_law, PhiUA_tau, PhiUA_arrow in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold FunSET2_r_mor1, FunSET2_l_mor1 in |- *.
unfold FOb at 1 in |- *; simpl in |- *; unfold FunSET2_l_ob in |- *.
(* *) apply
       Trans
        with
          (UA_mor (UA_of (OB_l d2xc2))
           o FMor G (FMor AdjointUA (HOM_l fxg) o h) o FMor G (Hom_r fxg)).
apply Comp_l; apply FComp.
(* *) apply
       Trans
        with
          ((UA_mor (UA_of (OB_l d2xc2))
            o FMor G (FMor AdjointUA (HOM_l fxg) o h)) o 
           FMor G (Hom_r fxg)).
apply Ass.
apply Comp_r.
(* *) apply
       Trans
        with
          (UA_mor (UA_of (OB_l d2xc2))
           o FMor G (FMor AdjointUA (HOM_l fxg)) o FMor G h).
apply Comp_l; apply FComp.
(* *) apply
       Trans
        with
          ((UA_mor (UA_of (OB_l d2xc2)) o FMor G (FMor AdjointUA (HOM_l fxg)))
           o FMor G h).
apply Ass.
(* *) apply Trans with ((HOM_l fxg o UA_mor (UA_of (OB_l d1xc1))) o FMor G h).
apply Comp_r; unfold FMor at 2 in |- *; simpl in |- *;
 unfold AdjointUA_mor, AdjointUA_ob in |- *.
apply UA_diag.
apply Ass1.
Qed.

Canonical Structure PhiUA := Build_NT PhiUA_tau_nt_law.

(* de'finissons PhiUA_1 *)

 Section phi_ua_1_tau_def.

 Variable dxc : POb (Dual D) C.

 Definition PhiUA_1_arrow (f : OB_l dxc --> G (Ob_r dxc)) :=
   UA_diese (UA_of (OB_l dxc)) f.

 Lemma PhiUA_1_arrow_map_law : Map_law PhiUA_1_arrow.
 Proof.
 unfold Map_law, PhiUA_1_arrow in |- *.
 intros f g H.
 apply (Diese_map (UA_of (OB_l dxc)) (x:=f) (y:=g)).
 assumption.
 Qed.

 Canonical Structure PhiUA_1_tau := Build_Map PhiUA_1_arrow_map_law.

 End phi_ua_1_tau_def.

(* On doit prouver: ((fo o h) o Gg)#2 = ((fo o ud1)#2 o h#1) o g *)
(* unicite' de #2 avec (fo o h) o Gg et (fo o ud1)#2 o h#1 o g *)
(* reste a` prouver: ud2 o G((fo o ud1)#2 o h#1 o g) = (fo o h) o Gg *)
(*                        (1)         *)
(* (1) = ud2 o G((fo o ud1)#2) o G(h#1) o Gg (Fcomp) *)
(*     = fo o ud1 o G(h#1) o Gg              (loi #2) *)
(*     = fo o h o Gg                         (loi #1) *)

Lemma PhiUA_1_tau_nt_law :
 NT_law (F:=FunSET2_l G) (G:=FunSET2_r AdjointUA) PhiUA_1_tau.
Proof.
unfold NT_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intros d1xc1 d2xc2 fxg h.
unfold PhiUA_1_arrow, FunSET2_r_mor1 in |- *. 
unfold FMor at 1 in |- *; simpl in |- *.
unfold AdjointUA_mor, FunSET2_r_ob in |- *; simpl in |- *;
 unfold AdjointUA_ob in |- *.
apply UA_unic1.
apply
 Trans
  with
    (UA_mor (UA_of (OB_l d2xc2))
     o FMor G
         (UA_diese (UA_of (OB_l d2xc2))
            (HOM_l fxg o UA_mor (UA_of (OB_l d1xc1)))
          o UA_diese (UA_of (OB_l d1xc1)) h) o FMor G (Hom_r fxg)).
apply Comp_l; apply FComp.
apply
 Trans
  with
    ((UA_mor (UA_of (OB_l d2xc2))
      o FMor G
          (UA_diese (UA_of (OB_l d2xc2))
             (HOM_l fxg o UA_mor (UA_of (OB_l d1xc1)))
           o UA_diese (UA_of (OB_l d1xc1)) h)) o FMor G (Hom_r fxg)).
apply Ass.
apply
 Trans
  with
    ((UA_mor (UA_of (OB_l d2xc2))
      o FMor G
          (UA_diese (UA_of (OB_l d2xc2))
             (HOM_l fxg o UA_mor (UA_of (OB_l d1xc1))))
        o FMor G (UA_diese (UA_of (OB_l d1xc1)) h)) o 
     FMor G (Hom_r fxg)).
apply Comp_r; apply Comp_l; apply FComp.
apply
 Trans
  with
    (((UA_mor (UA_of (OB_l d2xc2))
       o FMor G
           (UA_diese (UA_of (OB_l d2xc2))
              (HOM_l fxg o UA_mor (UA_of (OB_l d1xc1)))))
      o FMor G (UA_diese (UA_of (OB_l d1xc1)) h)) o 
     FMor G (Hom_r fxg)).
apply Comp_r; apply Ass.
apply
 Trans
  with
    (((HOM_l fxg o UA_mor (UA_of (OB_l d1xc1)))
      o FMor G (UA_diese (UA_of (OB_l d1xc1)) h)) o 
     FMor G (Hom_r fxg)).
apply Comp_r; apply Comp_r; apply UA_diag.
unfold FunSET2_l_mor1 in |- *; apply Comp_r.
apply
 Trans
  with
    (HOM_l fxg
     o UA_mor (UA_of (OB_l d1xc1)) o FMor G (UA_diese (UA_of (OB_l d1xc1)) h)).
apply Ass1.
apply Comp_l; apply UA_diag.
Qed.

Canonical Structure PhiUA_1 := Build_NT PhiUA_1_tau_nt_law.


(* PhiUA et PhiUA_1 sont iso *)

 Section phi_ua_iso.

 Variable dxc : POb (Dual D) C.

 Lemma PhiUA_1_o_PhiUA : AreIsos (PhiUA dxc) (PhiUA_1 dxc).
 Proof.
 unfold AreIsos in |- *; unfold RIso_law in |- *; simpl in |- *; split.
 unfold Ext in |- *; simpl in |- *.
 unfold PhiUA_arrow, Id_fun, PhiUA_1_arrow in |- *.
 intro f.
 unfold FunSET2_l_ob in |- *; apply UA_diag.
 (**)
 unfold Ext in |- *; simpl in |- *.
 unfold PhiUA_arrow, Id_fun, PhiUA_1_arrow in |- *.
 intro f.
 unfold FunSET2_r_ob in |- *; simpl in |- *; unfold AdjointUA_ob in |- *.
 apply UA_unic1.
 apply Refl.
 Qed.

 End phi_ua_iso.

Definition AdjUA := Build_Adj (NT_Iso PhiUA_1_o_PhiUA).

Canonical Structure LeftAdjUA := Build_LeftAdj AdjUA.

End ua_to_ladj.
                     
