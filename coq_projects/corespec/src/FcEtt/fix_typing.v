Require Import Metalib.Metatheory.
Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(*

This module proves the following results:

     Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
     Lemma Sig_toplevel: Sig toplevel.


It *should* be the only place in the development that
unfolds the definition of an_toplevel. That way, if we change the
definition of the signature in ett.ott, we only need to change this file.

In this case, it uses the fact that an_toplevel (defined in ett.ott)
contains the following definitions:

Definition Fix : atom.
  pick fresh F.
  exact F.
Qed.

Definition FixDef : tm :=
  (a_Abs Irrel a_Star
         (a_Abs Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
                (a_App (a_Var_b 0) Rel
                       (a_App (a_App (a_Fam Fix) Irrel (a_Var_b 1)) Rel (a_Var_b 0))))).

Definition FixTy : tm :=
  a_Pi Irrel a_Star
       (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
             (a_Var_b 1)).
 *)

Lemma AxFix : binds Fix (Ax FixDef FixTy) an_toplevel.
  unfold an_toplevel.
  eauto.
Qed.

Ltac an_use_binder f x :=
  pick fresh x and apply f; eauto;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- AnnTyping ?ctx ?a ?A ] =>
    assert (AnnCtx ctx); [econstructor; eauto|idtac]
  end.

Lemma An_App_intro :
  forall (G : context) (b : tm) (rho : relflag) (a B A C : tm),
       AnnTyping G b (a_Pi rho A B) -> (open_tm_wrt_tm B a) = C ->
       AnnTyping G a A -> AnnTyping G (a_App b rho a) C.
Proof.
  intros. subst. eapply An_App; eauto.
Qed.

Lemma FixTy_Star :
  AnnTyping nil FixTy a_Star.
Proof.
  an_use_binder An_Pi X.
  an_use_binder An_Pi Z.
  an_use_binder An_Pi W.
  eauto.
  eauto.
  an_use_binder An_Pi W.
  eauto.
Qed.

Lemma FixDef_FixTy :
  AnnTyping nil FixDef FixTy.
Proof.
  an_use_binder An_Abs X.
  an_use_binder An_Abs x.
  { an_use_binder An_Pi Z. eauto. }
  { an_use_binder An_Pi Z. eauto. }
  { eapply An_App_intro; eauto.
    { eapply An_App_intro; simpl; eauto.
      { eapply An_App_intro; simpl; eauto.
        econstructor; eauto.
        eapply AxFix.
        an_use_binder An_Pi Z.
        an_use_binder An_Pi W; eauto.
        an_use_binder An_Pi M; eauto.
        an_use_binder An_Pi N; eauto.
        unfold open_tm_wrt_tm. simpl. eauto. }
      unfold open_tm_wrt_tm. simpl. eauto.
    }
  }
Qed.

Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
Proof.
  unfold an_toplevel.
  econstructor; eauto.
(*  eapply AxFix. *)
  eapply FixTy_Star. eauto.
  eapply FixDef_FixTy.
Qed.

(* ---------------------------------------------------------- *)

Ltac use_binder f x :=
  pick fresh x and apply f;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- Typing ?ctx ?a ?A ] =>
    assert (Ctx ctx); [econstructor; eauto|idtac]
  end.

Lemma E_App_intro :
  forall (G : context) (b : tm) (a B A C : tm),
       Typing G b (a_Pi Rel A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G a A -> Typing G (a_App b Rel a) C.
Proof.
  intros. subst.  eapply E_App; eauto.
Qed.

Lemma E_IApp_intro :
  forall (G : context) (b : tm) (a B A C : tm),
       Typing G b (a_Pi Irrel A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G a A -> Typing G (a_App b Irrel a_Bullet) C.
Proof.
  intros. subst.  eapply E_IApp; eauto.
Qed.

Lemma FixTy_erase :
  Typing nil (erase_tm FixTy) a_Star.
Proof.
  use_binder E_Pi X.
  use_binder E_Pi Z.
  use_binder E_Pi W.
  eauto.
  eauto.
  use_binder E_Pi W.
  eauto.
Qed.

Lemma FixDef_FixTy_erase :
  Typing nil (erase_tm FixDef) (erase_tm FixTy).
Proof.
  pose (H := AxFix). clearbody H.
  unfold FixDef,FixTy; simpl.
  use_binder E_Abs X.
  use_binder E_Abs x.
  { use_binder E_Pi Z. eauto. }
  { eapply E_App_intro; eauto.
    { eapply E_App_intro; simpl; eauto.
      { eapply E_IApp_intro with (a := (a_Var_f X)); simpl; eauto.

        pose (K := @E_Fam _ Fix  (erase_tm FixTy) (erase_tm FixDef) H1).
        unfold toplevel, erase_sig in K.
        apply binds_map with (f:=erase_csort) in H.
        apply K in H.
        clear K.
        simpl in H.
        apply H.

        { simpl.
        use_binder E_Pi Z; eauto.
        use_binder E_Pi W; eauto.
        use_binder E_Pi M; eauto.
        use_binder E_Pi N; eauto. }

        { unfold open_tm_wrt_tm. simpl. eauto. }
      }
      unfold open_tm_wrt_tm. simpl. eauto.
    }
  }
  use_binder E_Pi Z; eauto.
Qed.


Lemma Sig_toplevel: Sig toplevel.
Proof.
  unfold toplevel, erase_sig.
  unfold an_toplevel.
  econstructor; eauto.
(*  unfold toplevel, erase_sig.
  pose (K := AxFix).
  eapply binds_map with (f:= erase_csort) in K.
  apply K. *)
  eapply FixTy_erase.
  eapply FixDef_FixTy_erase.
Qed.
