Require Import FcEtt.sigs.

Require Import FcEtt.imports.

Require Import FcEtt.ett_ind.

Set Bullet Behavior "Strict Subproofs".

Module fc_dec_fuel (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig) (unique: fc_unique_sig).

Inductive fuel_tpg : tm -> Type :=
 | FT_Star :
    fuel_tpg a_Star
 | FT_Var_f : ∀ (x:tmvar),
    fuel_tpg (a_Var_f x)
 | FT_Pi : ∀ (rho:relflag) (A B:tm),
    (∀ x , x \notin  (fv_tm_tm_tm B) ->
      fuel_tpg (open_tm_wrt_tm B (a_Var_f x)))  ->
    fuel_tpg A ->
    fuel_tpg (a_Pi rho A B)
 | FT_Abs : ∀ (rho:relflag) (a A:tm),
    (∀ x , x \notin  (fv_tm_tm_tm a) ->
      fuel_tpg  (open_tm_wrt_tm a (a_Var_f x))) ->
    fuel_tpg A ->
    fuel_tpg (a_Abs rho A a)
 | FT_App : ∀ (rho:relflag) (b a:tm),
    fuel_tpg b ->
    fuel_tpg a ->
    fuel_tpg (a_App b rho a)
 | FT_Conv : ∀ (a:tm) g,
    fuel_tpg a ->
    fuel_deq g ->
    fuel_tpg (a_Conv a g)
 | FT_CPi : ∀ (phi:constraint) (B:tm),
    (∀ c, c \notin  (fv_co_co_tm B) -> fuel_tpg (open_tm_wrt_co B (g_Var_f c))) ->
    fuel_pwf phi ->
    fuel_tpg (a_CPi phi B)
 | FT_CAbs : ∀ (a:tm) (phi:constraint),
    (∀ c, c \notin (fv_co_co_constraint phi \u fv_co_co_tm a) -> fuel_tpg (open_tm_wrt_co a (g_Var_f c))) ->
    fuel_pwf phi ->
    fuel_tpg (a_CAbs phi a)
 | FT_CApp : ∀ (b:tm) g,
    fuel_tpg b ->
    fuel_deq g ->
    fuel_tpg (a_CApp b g)
 | FT_Const : ∀ (T:atom),
    fuel_tpg (a_Const T)
 | FT_Fam : forall (F:tyfam),
    fuel_tpg (a_Fam F)

 (* No typing rule for these cases --- they immediately fail. *)
 | FT_Var_b : forall n0,
     fuel_tpg (a_Var_b n0)
 | FT_UAbs : forall rho a,
     fuel_tpg (a_UAbs rho a)
 | FT_UCAbs : forall a,
     fuel_tpg (a_UCAbs a)
 | FT_DataCon : forall K,
     fuel_tpg (a_DataCon K)
 | FT_Case : forall a brs5,
     fuel_tpg (a_Case a brs5)
 | FT_Bullet :
     fuel_tpg a_Bullet

with fuel_pwf : constraint -> Type :=
  | FP_fuel_pwf : ∀ a b A,
    fuel_tpg a ->
    fuel_tpg b ->
    fuel_pwf (Eq a b A)


with fuel_iso : co -> Type :=
  | FI_Cong : ∀ (g1:co) (A:tm) (g2:co),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_iso (g_EqCong g1 A g2)
  | FI_CPiFst : ∀ (g:co),
    fuel_deq g ->
    fuel_iso (g_CPiFst g)
  | FI_IsoSym : ∀ (g:co),
    fuel_iso g ->
    fuel_iso (g_Sym g)
  | FI_IsoConv : ∀ (g:co) phi1 phi2,
    fuel_deq g ->
    fuel_pwf phi1 ->
    fuel_pwf phi2 ->
    fuel_iso (g_IsoConv phi1 phi2 g)


  (* Trivial cases *)
  | FI_Triv :
    fuel_iso g_Triv
  | FI_Var_b : forall n0,
    fuel_iso (g_Var_b n0)
  | FI_Var_f : ∀ (c:covar),
    fuel_iso (g_Var_f c)
  | FI_Refl : ∀ (a:tm),
    fuel_iso (g_Refl a)
  | FI_Refl2 : ∀ (a b:tm) (g:co),
    fuel_iso (g_Refl2 a b g)
  | FI_Trans : ∀ (g1 g2: co),
    fuel_iso (g_Trans g1 g2)
  | FI_Beta : ∀ (a1 a2:tm),
    fuel_iso (g_Beta a1 a2)
  | FI_PiCong : ∀ (rho:relflag) (g1 g2:co),
    fuel_iso (g_PiCong rho g1 g2)
  | FI_AbsCong : ∀ (rho:relflag) (g1 g2:co),
    fuel_iso ((g_AbsCong rho g1 g2))
  | FI_AppCong : ∀ (g1:co) (g2:co) (rho:relflag),
    fuel_iso (g_AppCong g1 rho g2)
  | FI_PiFst : ∀ (g:co),
    fuel_iso (g_PiFst g)
  | FI_PiSnd : ∀ (g1 g2:co),
    fuel_iso (g_PiSnd g1 g2)
  | FI_CPiCong : ∀ (g1 g3:co),
    fuel_iso ((g_CPiCong g1 g3))
  | FI_CAbsCong : ∀ (g1 g3 g4:co),
    fuel_iso ((g_CAbsCong g1 g3 g4))
  | FI_CAppCong : ∀  (g1 g2 g3:co),
    fuel_iso (g_CAppCong g1 g2 g3)
  | FI_CPiSnd : ∀  (g1 g2 g3:co),
    fuel_iso (g_CPiSnd g1 g2 g3)
  | FI_Cast : ∀  (g1 g2:co),
    fuel_iso (g_Cast g1 g2)
  | FI_IsoSnd : ∀  (g:co),
    fuel_iso (g_IsoSnd g)

  | FI_Eta : forall a,
    fuel_iso (g_Eta a)


  | FI_Left : forall g1 g2,
      fuel_iso (g_Left g1 g2)
  | FI_Right : forall g1 g2,
      fuel_iso (g_Right g1 g2)


with fuel_deq : co -> Type :=
  | FD_Assn : ∀ (c:covar),
    fuel_deq (g_Var_f c)
  | FD_Refl : ∀ (a:tm),
    fuel_tpg a ->
    fuel_deq (g_Refl a)
  | FD_Refl2 : ∀ (a b:tm) (g:co),
    fuel_tpg a ->
    fuel_tpg b ->
    fuel_deq g ->
    fuel_deq (g_Refl2 a b g)
  | FD_Sym : ∀ (g:co),
    fuel_deq g ->
    fuel_deq (g_Sym g)
  | FD_Trans : ∀ (g1 g2: co),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_deq (g_Trans g1 g2)
  | FD_Beta : ∀ (a1 a2:tm),
    fuel_tpg a1 ->
    fuel_tpg a2 ->
    fuel_deq (g_Beta a1 a2)

  | FD_PiCong : ∀ (rho:relflag) (g1 g2:co),
    fuel_deq g1 ->
    (∀ x, x \notin (fv_tm_tm_co g1 \u fv_tm_tm_co g2) ->
      fuel_deq (open_co_wrt_tm g2 (a_Var_f x))) ->
    fuel_deq (g_PiCong rho g1 g2)
  | FD_AbsCong : ∀ (rho:relflag) (g1 g2:co),
    fuel_deq g1 ->
    (∀ x,
      x \notin (fv_tm_tm_co g1 \u fv_tm_tm_co g2) ->
      fuel_deq (open_co_wrt_tm g2 (a_Var_f x))) ->
    fuel_deq ((g_AbsCong rho g1 g2))
  | FD_AppCong : ∀ (g1:co) (g2:co) (rho:relflag),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_deq (g_AppCong g1 rho g2)
  | FD_PiFst : ∀ (g:co),
    fuel_deq g ->
    fuel_deq (g_PiFst g)
  | FD_PiSnd : ∀ (g1 g2:co),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_deq (g_PiSnd g1 g2)
  | FD_CPiCong : ∀ (g1 g3:co),
    fuel_iso g1 ->
    (∀ c,
      c \notin  (fv_co_co_co g1 \u fv_co_co_co g3) ->
      fuel_deq (open_co_wrt_co g3 (g_Var_f c))) ->
    fuel_deq ((g_CPiCong g1 g3))
  | FD_CAbsCong : ∀ (g1 g3 g4:co),
    fuel_iso g1 ->
    (∀ c,
      c \notin (fv_co_co_co g1 \u fv_co_co_co g3) ->
      fuel_deq (open_co_wrt_co g3 (g_Var_f c))) ->
    fuel_deq g4 ->
    fuel_deq ((g_CAbsCong g1 g3 g4))
  | FD_CAppCong : ∀  (g1 g2 g3:co),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_deq g3 ->
    fuel_deq (g_CAppCong g1 g2 g3)
  | FD_CPiSnd : ∀  (g1 g2 g3:co),
    fuel_deq g1 ->
    fuel_deq g2 ->
    fuel_deq g3 ->
    fuel_deq (g_CPiSnd g1 g2 g3)
  | FD_Cast : ∀  (g1 g2:co),
    fuel_deq g1 ->
    fuel_iso g2 ->
    fuel_deq (g_Cast g1 g2)
  | FD_IsoSnd : ∀  (g:co),
    fuel_iso g ->
    fuel_deq (g_IsoSnd g)

  | FD_Triv :
      fuel_deq g_Triv
  | FD_Var_b : forall n0,
      fuel_deq (g_Var_b n0)
  | FD_CPiFst : ∀ (g:co),
    fuel_deq (g_CPiFst g)
  | FD_Cong : ∀ (g1:co) (A:tm) (g2:co),
    fuel_deq (g_EqCong g1 A g2)
  | FD_IsoConv : ∀ (g:co) phi1 phi2,
      fuel_deq (g_IsoConv phi1 phi2 g)

  | FD_Eta : forall a,
      fuel_tpg a ->
      fuel_deq (g_Eta a)

  | FD_Left : forall g1 g2,
      fuel_deq g1 ->
      fuel_deq g2 ->
      fuel_deq (g_Left g1 g2)

  | FD_Right : forall g1 g2,
      fuel_deq g1 ->
      fuel_deq g2 ->
      fuel_deq (g_Right g1 g2)

.

Hint Constructors fuel_deq fuel_iso fuel_pwf fuel_tpg.

Scheme
     ind_fuel_tpg := Induction for fuel_tpg Sort Prop
with ind_fuel_pwf := Induction for fuel_pwf Sort Prop
with ind_fuel_iso := Induction for fuel_iso Sort Prop
with ind_fuel_deq := Induction for fuel_deq Sort Prop.

Combined Scheme fuel_mutind from ind_fuel_tpg, ind_fuel_pwf, ind_fuel_iso, ind_fuel_deq.

End fc_dec_fuel.
