(* File: Le_Ks.v  (last edited on 27/10/2000) (c) Klaus Weich  *)



Require Export Rev_App.



(*****************************************************************)



Inductive le_ni : nested_imps -> nested_imps -> Prop :=
  | Le_NI_Nil : le_ni NNil NNil
  | Le_NI_Cons_NN :
      forall (x : nimp) (ni1 ni2 : nested_imps),
      le_ni ni1 ni2 -> le_ni (Undecorated x :: ni1) (Undecorated x :: ni2)
  | Le_NI_Cons_DN :
      forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
      le_ni ni1 ni2 -> le_ni (Decorated x k :: ni1) (Undecorated x :: ni2)
  | Le_NI_Cons_DD :
      forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
      le_ni ni1 ni2 -> le_ni (Decorated x k :: ni1) (Decorated x k :: ni2).






Lemma in_k_le :
 forall (ni1 ni2 : nested_imps) (x : nimp) (k : kripke_tree),
 le_ni ni1 ni2 -> In (Decorated x k) ni2 -> In (Decorated x k) ni1.
intros ni1 ni2 x k le12.
elim le12; clear le12 ni1 ni2.
intros; assumption.

intros x' ni1 ni2 le12 ih in_k.
right.
apply ih.
inversion_clear in_k.
 discriminate H.
assumption.

intros x' k' ni1 ni2 le12 ih in_k.
right.
apply ih.
inversion_clear in_k.
 discriminate H.
assumption.

intros x' k' ni1 ni2 le12 ih in_k.
inversion_clear in_k.
left; assumption.
right; apply ih; assumption.
Qed.




Lemma le_ni_refl : forall ni : nested_imps, le_ni ni ni.
intros ni; elim ni; clear ni.
apply Le_NI_Nil.
intros a; case a; clear a.
intros x N ih.
apply Le_NI_Cons_NN; assumption.
intros x k ni ih.
apply Le_NI_Cons_DD; assumption.
Qed.




Lemma le_ni_trans :
 forall ni1 ni2 ni3 : nested_imps,
 le_ni ni1 ni2 -> le_ni ni2 ni3 -> le_ni ni1 ni3.
intros ni1 ni2 ni3 le12.
generalize ni3; clear ni3.
elim le12; clear le12 ni1 ni2.
intros; assumption.
intros x ni1 ni2 le12 ih ni3 le23.
inversion_clear le23.
apply Le_NI_Cons_NN.
apply ih; assumption.
intros x k ni1 ni2 le12 ih ni3 le23.
inversion_clear le23.
apply Le_NI_Cons_DN.
apply ih; assumption.
intros x k ni1 ni2 le12 ih ni3 le23.
inversion_clear le23.
apply Le_NI_Cons_DN.
apply ih; assumption.
apply Le_NI_Cons_DD.
apply ih; assumption.
Qed.





(*****************************************************************)


Inductive filter_deco_spec (i : Int) (N : nested_imps) : Set :=
    Filter_Deco_Spec_Intro :
      forall ni1 : nested_imps,
      le_ni N ni1 ->
      (forall (x : nimp) (k : kripke_tree),
       In (Decorated x k) ni1 -> forces_t k (Atom i)) -> 
      filter_deco_spec i N.


Lemma filter_deco :
 forall (i : Int) (ni : nested_imps), filter_deco_spec i ni.
intros i ni.
elim ni; clear ni.
fold NNil in |- *.
apply Filter_Deco_Spec_Intro with NNil.
apply Le_NI_Nil.
intros x k in_k.
inversion_clear in_k. 

intros a; case a; clear a.
intros x ni ih.
elim ih; clear ih.
intros ni1 le1 forces_i.
apply Filter_Deco_Spec_Intro with (Undecorated x :: ni1).
apply Le_NI_Cons_NN; assumption.
intros x' k' in_k0.
apply forces_i with x'.
inversion_clear in_k0.
 discriminate H.
assumption.

intros x k ni ih.
elim ih; clear ih.
intros ni1 le1 forces_i.
case k; clear k.
intros Atms succs.
case Atms; clear Atms.
intros t avl_t.
elim (lookup_dec unit i t avl_t).
intros d; case d; clear d.
intros lookup.
apply
 Filter_Deco_Spec_Intro
  with (Decorated x (node atoms (AVL_intro unit t avl_t) succs) :: ni1).
apply Le_NI_Cons_DD; assumption.
intros x' k' in_k0.
inversion_clear in_k0.
 injection H; clear H; intros.
 rewrite <- H; assumption.
apply forces_i with x'; assumption.

intros notlookup.
apply Filter_Deco_Spec_Intro with (Undecorated x :: ni1).
apply Le_NI_Cons_DN; assumption.
simpl in |- *; intros x' k' in_k0.
inversion_clear in_k0.
 discriminate H.
apply forces_i with x'; assumption.
Qed.


(*****************************************************************)


Inductive eqv_ni : nested_imps -> nested_imps -> Prop :=
  | Eqv_NI_Nil : eqv_ni NNil NNil
  | Eqv_NI_Cons_NN :
      forall (x : nimp) (ni1 ni2 : nested_imps),
      eqv_ni ni1 ni2 -> eqv_ni (Undecorated x :: ni1) (Undecorated x :: ni2)
  | Eqv_NI_Cons_DN :
      forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
      eqv_ni ni1 ni2 -> eqv_ni (Decorated x k :: ni1) (Undecorated x :: ni2)
  | Eqv_NI_Cons_DD :
      forall (x : nimp) (k k' : kripke_tree) (ni1 ni2 : nested_imps),
      eqv_ni ni1 ni2 -> eqv_ni (Decorated x k :: ni1) (Decorated x k' :: ni2)
  | Eqv_NI_Cons_ND :
      forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
      eqv_ni ni1 ni2 -> eqv_ni (Undecorated x :: ni1) (Decorated x k :: ni2).



Lemma eqv_ni_trans :
 forall ni1 ni2 ni3 : nested_imps,
 eqv_ni ni1 ni2 -> eqv_ni ni2 ni3 -> eqv_ni ni1 ni3.
intros ni1 ni2 ni3 eqv12.
generalize ni3; clear ni3.
elim eqv12; clear eqv12 ni1 ni2.
intros; assumption.
intros x ni1 ni2 eqv12 ih ni3 eqv23.
inversion_clear eqv23.
apply Eqv_NI_Cons_NN.
apply ih; assumption.
apply Eqv_NI_Cons_ND.
apply ih; assumption.
intros x k ni1 ni2 eqv12 ih ni3 eqv23.
inversion_clear eqv23.
apply Eqv_NI_Cons_DN.
apply ih; assumption.
apply Eqv_NI_Cons_DD.
apply ih; assumption.
intros x k k' ni1 ni2 eqv12 ih ni3 eqv23.
inversion_clear eqv23.
apply Eqv_NI_Cons_DN.
apply ih; assumption.
apply Eqv_NI_Cons_DD.
apply ih; assumption.
intros x k ni1 ni2 eqv12 ih ni3 eqv23.
inversion_clear eqv23.
apply Eqv_NI_Cons_NN.
apply ih; assumption.
apply Eqv_NI_Cons_ND.
apply ih; assumption.
Qed.


Lemma le_eqv : forall ni1 ni2 : nested_imps, le_ni ni1 ni2 -> eqv_ni ni1 ni2.
intros ni1 ni2 le12; elim le12; clear le12 ni1 ni2.
apply Eqv_NI_Nil.
intros x ni1 ni2 le12 ih; apply Eqv_NI_Cons_NN; assumption.
intros x k ni1 ni2 le12 ih; apply Eqv_NI_Cons_DN; assumption.
intros x k ni1 ni2 le12 ih; apply Eqv_NI_Cons_DD; assumption.
Qed.


Lemma eqv_sym :
 forall ni1 ni2 : nested_imps, eqv_ni ni1 ni2 -> eqv_ni ni2 ni1.
intros ni1 ni2 eqv12; elim eqv12; clear eqv12 ni1 ni2.
apply Eqv_NI_Nil.
intros x ni1 ni2 eqv12 ih; apply Eqv_NI_Cons_NN; assumption.
intros x k ni1 ni2 eqv12 ih; apply Eqv_NI_Cons_ND; assumption.
intros x k k' ni1 ni2 eqv12 ih; apply Eqv_NI_Cons_DD; assumption.
intros x k ni1 ni2 eqv12 ih; apply Eqv_NI_Cons_DN; assumption.
Qed.


Lemma ge_eqv : forall ni1 ni2 : nested_imps, le_ni ni2 ni1 -> eqv_ni ni1 ni2.
intros ni1 ni2 le21.
apply eqv_sym.
apply le_eqv; assumption.
Qed.

(*****************************************************************)

Lemma eqv_ni_rec :
 forall P : nested_imps -> nested_imps -> Set,
 P NNil NNil ->
 (forall (x : nimp) (ni1 ni2 : nested_imps),
  eqv_ni ni1 ni2 ->
  P ni1 ni2 -> P (Undecorated x :: ni1) (Undecorated x :: ni2)) ->
 (forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
  eqv_ni ni1 ni2 ->
  P ni1 ni2 -> P (Decorated x k :: ni1) (Undecorated x :: ni2)) ->
 (forall (x : nimp) (k k' : kripke_tree) (ni1 ni2 : nested_imps),
  eqv_ni ni1 ni2 ->
  P ni1 ni2 -> P (Decorated x k :: ni1) (Decorated x k' :: ni2)) ->
 (forall (x : nimp) (k : kripke_tree) (ni1 ni2 : nested_imps),
  eqv_ni ni1 ni2 ->
  P ni1 ni2 -> P (Undecorated x :: ni1) (Decorated x k :: ni2)) ->
 forall ni1 ni2 : nested_imps, eqv_ni ni1 ni2 -> P ni1 ni2.
intros P base step_nn step_rn step_rr step_nr ni1.
elim ni1; clear ni1.
intros ni2; case ni2; clear ni2.
intros; apply base.
intros a ni2 eqv; elimtype False; inversion_clear eqv.


intros a; case a; clear a.
intros x ni1 ih ni2.
case ni2; clear ni2.
intros eqv; elimtype False; inversion_clear eqv.
intros a; case a; clear a.
intros x' ni2 eqv.
cut (x = x').
intro eq_x;  rewrite eq_x; clear eq_x.
apply step_nn.
inversion_clear eqv; assumption.
apply ih.
inversion_clear eqv; assumption.
inversion_clear eqv; trivial.
intros x' k' ni2 eqv.
cut (x = x').
intro eq_x;  rewrite eq_x; clear eq_x.
apply step_nr.
inversion_clear eqv; assumption.
apply ih.
inversion_clear eqv; assumption.
inversion_clear eqv; trivial.

intros x k ni1 ih ni2.
case ni2; clear ni2.
intros eqv; elimtype False; inversion_clear eqv.
intros a; case a; clear a.
intros x' ni2 eqv.
cut (x = x').
intro eq_x;  rewrite eq_x; clear eq_x.
apply step_rn.
inversion_clear eqv; assumption.
apply ih.
inversion_clear eqv; assumption.
inversion_clear eqv; trivial.
intros x' k' ni2 eqv.
cut (x = x').
intro eq_x;  rewrite eq_x; clear eq_x.
apply step_rr.
inversion_clear eqv; assumption.
apply ih.
inversion_clear eqv; assumption.
inversion_clear eqv; trivial.
Qed.

(*****************************************************************)


Inductive inf_deco_spec (ni1 ni2 : nested_imps) : Set :=
    Inf_Deco_Spec_Intro :
      forall ni : nested_imps,
      le_ni ni ni1 ->
      eqv_ni ni ni2 ->
      (forall (x : nimp) (k : kripke_tree),
       In (Decorated x k) ni ->
       In (Decorated x k) ni1 \/ In (Decorated x k) ni2) ->
      inf_deco_spec ni1 ni2.


Lemma inf_deco :
 forall ni1 ni2 : nested_imps, eqv_ni ni1 ni2 -> inf_deco_spec ni1 ni2.
intros ni1 ni2 eqv12. 
elim eqv12; clear eqv12 ni1 ni2.
apply Inf_Deco_Spec_Intro with NNil.
apply Le_NI_Nil.
apply Eqv_NI_Nil.
intros; left; assumption.

intros x ni1 ni2 eqv12 ih.
elim ih; clear ih.
intros ni le eqv inf.
apply Inf_Deco_Spec_Intro with (Undecorated x :: ni).
apply Le_NI_Cons_NN; assumption.
apply Eqv_NI_Cons_NN; assumption.
intros x' k' in_k0.
inversion_clear in_k0.
left; left; assumption.
elim (inf x' k' H); clear inf H.
intros in_ni1; left; right; assumption.
intros in_ni2; right; right; assumption.

intros x k ni1 ni2 eqv12 ih.
elim ih; clear ih.
intros ni le eqv inf.
apply Inf_Deco_Spec_Intro with (Decorated x k :: ni).
apply Le_NI_Cons_DD; assumption.
apply Eqv_NI_Cons_DN; assumption.
intros x' k' in_k0.
inversion_clear in_k0.
left; left; assumption.
elim (inf x' k' H); clear inf H.
intros in_ni1; left; right; assumption.
intros in_ni2; right; right; assumption.

intros x k k' ni1 ni2 eqv12 ih.
elim ih; clear ih.
intros ni le eqv inf.
apply Inf_Deco_Spec_Intro with (Decorated x k :: ni).
apply Le_NI_Cons_DD; assumption.
apply Eqv_NI_Cons_DD; assumption.
intros x0 k0 in_k0.
inversion_clear in_k0.
left; left; assumption.
elim (inf x0 k0 H); clear inf H.
intros in_ni1; left; right; assumption.
intros in_ni2; right; right; assumption.


intros x k ni1 ni2 eqv12 ih.
elim ih; clear ih.
intros ni le eqv inf.
apply Inf_Deco_Spec_Intro with (Decorated x k :: ni).
apply Le_NI_Cons_DN; assumption.
apply Eqv_NI_Cons_DD; assumption.
intros x0 k0 in_k0.
inversion_clear in_k0.
right; left; assumption.
elim (inf x0 k0 H); clear inf H.
intros in_ni1; left; right; assumption.
intros in_ni2; right; right; assumption.
Qed.


(************************************************************************)

Remark eqv_nimps_eq :
 forall ni1 ni2 : nested_imps,
 eqv_ni ni1 ni2 -> nested_imps2nimps ni1 = nested_imps2nimps ni2.
intros ni1 ni2 eqv.
elim eqv; clear eqv ni1 ni2; simpl in |- *.
trivial.
intros x ni1 ni2 eqv ih;  rewrite ih; trivial.
intros x k ni1 ni2 eqv ih;  rewrite ih; trivial.
intros x k1 k2 ni1 ni2 eqv ih;  rewrite ih; trivial.
intros x k ni1 ni2 eqv ih;  rewrite ih; trivial.
Qed.


Lemma in_ngamma_eqv :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 eqv_ni ni1 ni2 ->
 in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
intros work ds ni1 ni2 ai a c eqv12 ini1.
apply in_ngamma_ni_eq with ni1; try assumption.
apply eqv_nimps_eq; assumption.
Qed.



Lemma in_ngamma_le :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 le_ni ni1 ni2 ->
 in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
intros work ds ni1 ni2 ai a c le12 in_ngamma.
apply in_ngamma_eqv with ni1.
apply le_eqv; assumption.
assumption.
Qed.

Lemma in_ngamma_ge :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 le_ni ni2 ni1 ->
 in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
intros work ds ni1 ni2 ai a c le21 in_ngamma.
apply in_ngamma_eqv with ni1.
apply ge_eqv; assumption.
assumption.
Qed.


(***********************************************************************)


Inductive le_app_spec (ni1 : nested_imps) (n : nat) : Set :=
    Le_App_Spec_Intro :
      forall ni11 ni12 : nested_imps,
      ni1 = ni11 ++ ni12 -> length ni11 = n -> le_app_spec ni1 n.

Lemma le_app0 :
 forall ni1 ni21 ni22 : nested_imps,
 le_ni ni1 (ni21 ++ ni22) -> le_app_spec ni1 (length ni21).
intros ni1 ni21 ni22.
generalize ni1; clear ni1.
elim ni21; clear ni21.
simpl in |- *; intros ni1 le.
exists NNil ni1.
trivial.
trivial.
intros x ni21 ih ni1.
case ni1; clear ni1.
intros le; elimtype False; inversion_clear le.
simpl in |- *; intros x' ni1 le1.
elim (ih ni1); clear ih.
intros ni11 ni12 eq len.
exists (x' :: ni11) ni12.
 rewrite eq.
trivial.
simpl in |- *.
 rewrite len; trivial.
inversion_clear le1; assumption.
Qed.





Lemma le_ni_app_nn :
 forall (ni1 ni2 ni3 ni4 : nested_imps) (x : nimp),
 length ni1 = length ni3 ->
 le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
 le_ni (ni1 ++ Undecorated x :: ni2) (ni3 ++ Undecorated x :: ni4).
intros ni1 ni2 ni3 ni4 x.
generalize ni3; clear ni3.
elim ni1; clear ni1.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le.
apply Le_NI_Cons_NN; assumption.
intros y ni3 len le.
inversion_clear len.
intros y ni1 ih.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le; inversion_clear len.
simpl in |- *; intros y' ni3 len le.
inversion_clear le.
apply Le_NI_Cons_NN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DD.
apply ih.
 injection len; intros; assumption.
assumption.
Qed.



Lemma le_ni_app_dn :
 forall (ni1 ni2 ni3 ni4 : nested_imps) (x : nimp) (k : kripke_tree),
 length ni1 = length ni3 ->
 le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
 le_ni (ni1 ++ Decorated x k :: ni2) (ni3 ++ Undecorated x :: ni4).
intros ni1 ni2 ni3 ni4 x k.
generalize ni3; clear ni3.
elim ni1; clear ni1.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le.
apply Le_NI_Cons_DN; assumption.
intros y ni3 len le.
inversion_clear len.
intros y ni1 ih.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le; inversion_clear len.
simpl in |- *; intros y' ni3 len le.
inversion_clear le.
apply Le_NI_Cons_NN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DD.
apply ih.
 injection len; intros; assumption.
assumption.
Qed.




Lemma le_ni_app_dd :
 forall (ni1 ni2 ni3 ni4 : nested_imps) (x : nimp) (k : kripke_tree),
 length ni1 = length ni3 ->
 le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
 le_ni (ni1 ++ Decorated x k :: ni2) (ni3 ++ Decorated x k :: ni4).
intros ni1 ni2 ni3 ni4 x k.
generalize ni3; clear ni3.
elim ni1; clear ni1.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le.
apply Le_NI_Cons_DD; assumption.
intros y ni3 len le.
inversion_clear len.
intros y ni1 ih.
intros ni3; case ni3; clear ni3.
simpl in |- *; intros len le; inversion_clear len.
simpl in |- *; intros y' ni3 len le.
inversion_clear le.
apply Le_NI_Cons_NN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DN.
apply ih.
 injection len; intros; assumption.
assumption.
apply Le_NI_Cons_DD.
apply ih.
 injection len; intros; assumption.
assumption.
Qed.



