(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_comprehension.v                                               *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_parties.

(***************************************************************************)
(* Schema d'axiome de comprehension                                        *)
(***************************************************************************)
Parameter subset : (E -> Prop) -> E -> E.
Axiom
  axs_comprehension :
    forall (F : E -> Prop) (a v0 : E), In v0 (subset F a) <-> In v0 a /\ F v0.

(***************************************************************************)
(* Pour les tactiques, on splite l'axiome precedent en deux lemmes orientes*)
(***************************************************************************)
Lemma lem_comprehension_lr :
 forall (F : E -> Prop) (a v0 : E), In v0 (subset F a) -> In v0 a /\ F v0.
(* Proof of lem_comprehension_lr                                           *)
intros; elim (axs_comprehension F a v0); intros; exact (H0 H).

Qed.
(* End of proof of lem_comprehension_lr                                    *)

Lemma lem_comprehension_rl :
 forall (F : E -> Prop) (a v0 : E), In v0 a /\ F v0 -> In v0 (subset F a).
(* Proof of lem_comprehension_rl                                           *)
intros; elim (axs_comprehension F a v0); intros; exact (H1 H).

Qed.
(* End of proof of lem_comprehension_rl                                    *)

(***************************************************************************)
(* Consequences                                                            *)
(***************************************************************************)

(***************************************************************************)
(* Existence de l'ensemble vide                                            *)
(***************************************************************************)
Definition def_F_vide (v0 : E) := v0 <> v0.

Definition vide (a : E) := subset def_F_vide a.

Lemma lem_vide_propertie : forall v0 v1 : E, ~ In v0 (vide v1).
(* Proof of lem_vide_propertie                                             *)
intros; unfold vide in |- *; unfold def_F_vide in |- *; unfold not in |- *;
 intros.
elim (axs_comprehension def_F_vide v1 v0); unfold def_F_vide in |- *;
 unfold not in |- *; intros.
elim H0; clear H0; intros.
clear H; clear H1; clear H0; apply H2; clear H2; reflexivity.

apply H1; clear H1.
split.
elim (axs_comprehension def_F_vide v1 v0); unfold def_F_vide in |- *;
 unfold not in |- *; intros.
elim H0; clear H0; intros; assumption.

elim (axs_comprehension def_F_vide v1 v0); unfold def_F_vide in |- *;
 unfold not in |- *; intros.
elim H0; clear H0; intros.
apply H3; reflexivity.

assumption.

Qed.
(* End of proof of lem_vide_existence                                      *)

Lemma lem_vide_unicite : forall v0 v1 : E, vide v0 = vide v1.
(* Proof of lem_vide_unicite                                               *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
generalize (lem_vide_propertie v2 v0); intros; elim H0; assumption.

generalize (lem_vide_propertie v2 v1); intros; elim H0; assumption.

Qed.
(* End of proof of lem_vide_unicite                                        *)

Parameter var_vide : E.
Definition Vide := vide var_vide.

Lemma lem_x_inc_vide : forall x : E, inc x Vide -> x = Vide.
(* Proof of lem_x_inc_vide                                                 *)
intros.
unfold inc in H.
apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
exact (H v2 H0).

generalize (lem_vide_propertie v2 var_vide); intros.
unfold Vide in H0.
absurd (In v2 (vide var_vide)); auto with zfc.

Qed.
(* End of proof of lem_x_inc_vide                                          *)

Lemma lem_x_noteq_vide : forall x y : E, In y x -> x <> Vide.
(* Proof of lem_x_noteq_vide                                               *)
intros.
unfold not in |- *; intros.
generalize H; clear H; rewrite H0; intros.
generalize (lem_vide_propertie y var_vide); intros; unfold Vide in H.
absurd (In y (vide var_vide)); auto with zfc.

Qed.
(* End of proof of lem_x_noteq_vide                                        *)

Lemma lem_paire_not_empty : forall a b : E, paire a b <> Vide.
(* Proof of lem_paire_not_empty                                            *)
intros.
cut (In a (paire a b)); intros.
unfold not in |- *; intros.
generalize H; clear H; rewrite H0; intros.
generalize (lem_vide_propertie a var_vide); intros; unfold Vide in H.
absurd (In a (vide var_vide)); auto with zfc.

elim (axs_paire a b a); intros; apply H0; left; reflexivity.

Qed.
(* End of proof of lem_paire_not_empty                                     *)

Lemma lem_not_vide_in_vide : ~ In Vide Vide.
(* Proof of lem_not_vide_in_vide                                           *)
unfold not in |- *; intros.
absurd (Vide = Vide); [ unfold not in |- *; intros | reflexivity ].
generalize (lem_x_noteq_vide Vide Vide H); intros.
tauto.

Qed.
(* End of proof of lem_not_vide_in_vide                                    *)

(***************************************************************************)
(* Intersection de deux ensembles                                          *)
(***************************************************************************)
Definition def_F_inter (s x : E) := In x s.

Definition inter (a b : E) := subset (def_F_inter b) a.

Lemma lem_inter_propertie :
 forall a b x : E, In x (inter a b) <-> In x a /\ In x b.
(* Proof of lem_inter_propertie                                            *)
intros; unfold iff in |- *; unfold inter in |- *; unfold def_F_inter in |- *;
 split; intros.
elim (axs_comprehension (def_F_inter b) a x); unfold def_F_inter in |- *;
 intros; auto with zfc.

elim (axs_comprehension (def_F_inter b) a x); unfold def_F_inter in |- *;
 intros; auto with zfc.

Qed.
(* End of proof of lem_inter_propertie                                     *)

Lemma lem_inter_propertie_lr :
 forall a b x : E, In x (inter a b) -> In x a /\ In x b.
(* Proof of lem_inter_propertie_lr                                         *)
intros; elim (lem_inter_propertie a b x); intros; exact (H0 H).

Qed.
(* End of proof of lem_inter_propertie_lr                                  *)

Lemma lem_inter_propertie_rl :
 forall a b x : E, In x a /\ In x b -> In x (inter a b).
(* Proof of lem_inter_propertie_rl                                         *)
intros; elim (lem_inter_propertie a b x); intros; exact (H1 H).

Qed.
(* End of proof of lem_inter_propertie_rl                                  *)

Lemma lem_inter_unicite :
 forall a b i : E,
 (forall x : E, In x i <-> In x a /\ In x b) -> i = inter a b.
(* Proof of lem_inter_unicite                                              *)
intros; apply axs_extensionnalite; intros.
elim (H v2); clear H; intros.
elim (lem_inter_propertie a b v2); intros; split; intros; auto with zfc.

Qed.
(* End of proof of lem_inter_unicite                                       *)

Lemma lem_inter_vide_prop : forall x : E, inter x Vide = Vide.
(* Proof of lem_inter_vide_prop                                            *)
intros; unfold inter in |- *; apply axs_extensionnalite; intros;
 unfold iff in |- *; split; intros.
elim (axs_comprehension (def_F_inter Vide) x v2); intros; generalize (H0 H);
 clear H H0 H1; intros.
elim H; clear H; unfold def_F_inter in |- *; intros; auto with zfc.

elim (axs_comprehension (def_F_inter Vide) x v2); intros; apply H1;
 clear H0 H1; intros.
unfold def_F_inter in |- *.
split; [ idtac | auto with zfc ].
generalize (lem_vide_propertie v2 var_vide); intros.
unfold Vide in H.
absurd (In v2 (vide var_vide)); auto with zfc.

Qed.
(* End of proof of lem_inter_vide_prop                                     *)

(***************************************************************************)
(* L'ensemble de tous les ensembles ... n'existe pas !!!                   *)
(***************************************************************************)
Theorem notEEexists : ~ (exists v0 : E, (forall v1 : E, In v1 v0)).
(* Proof of notEEexists                                                    *)
unfold not in |- *; intros; elim H; clear H; intros.
elim
 (axs_comprehension (fun v0 : E => ~ In v0 v0) x
    (subset (fun v0 : E => ~ In v0 v0) x)); intros.
generalize (H (subset (fun v0 : E => ~ In v0 v0) x)); intros.
absurd
 (In (subset (fun v0 : E => ~ In v0 v0) x)
    (subset (fun v0 : E => ~ In v0 v0) x)); tauto.

Qed.
(* End of proof of notEEexists                                             *)

(***************************************************************************)
(* Intersection d'un ensemble a                                            *)
(* a est un ensemble non vide. On recherche l'ensemble dont tous les       *)
(* elements sont elements des elements de a.                               *)
(***************************************************************************)
Definition Einter (a : E) (Ine : a <> Vide) :=
  subset (fun v0 : E => forall v3 : E, In v3 a -> In v0 v3) (reunion a).

Lemma lem_Einter_propertie :
 forall (a v0 : E) (Ine : a <> Vide),
 In v0 (Einter a Ine) -> forall v3 : E, In v3 a -> In v0 v3.
(* Proof of lem_Einter_propertie                                           *)
unfold Einter in |- *; intros.
elim
 (axs_comprehension (fun v1 : E => forall v3 : E, In v3 a -> In v1 v3)
    (reunion a) v0); intros; generalize (H1 H); clear H H1 H2; 
 intros.
elim H; clear H; intros.
exact (H1 v3 H0).

Qed.
(* End of proof of lem_Einter_propertie                                    *)

Lemma lem_Einter_sing :
 forall a : E, Einter (singleton a) (lem_paire_not_empty a a) = a.
(* Proof of lem_Einter_sing                                                *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold Einter in H.
elim
 (axs_comprehension
    (fun v0 : E => forall v3 : E, In v3 (singleton a) -> In v0 v3)
    (reunion (singleton a)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
elim (axs_reunion (singleton a) v2); intros; generalize (H1 H); clear H H1 H2;
 intros.
elim H; clear H; intros; elim H; clear H; intros.
unfold singleton in H.
elim (axs_paire a a x); intros; generalize (H2 H); clear H H2 H3; intros.
elim H; clear H; intros; generalize H1; rewrite H; tauto.

unfold Einter in |- *.
elim
 (axs_comprehension
    (fun v0 : E => forall v3 : E, In v3 (singleton a) -> In v0 v3)
    (reunion (singleton a)) v2); intros; apply H1; 
 clear H0 H1; intros.
split; intros.
elim (axs_reunion (singleton a) v2); intros; apply H1; clear H0 H1; intros.
exists a; split; [ apply lem_x_in_sing_x | idtac ]; auto with zfc.

unfold singleton in H0.
elim (axs_paire a a v3); intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; rewrite H0; auto with zfc.

Qed.
(* End of proof of lem_Einter_sing                                         *)

Lemma lem_Einter_paire :
 forall a b : E, Einter (paire a b) (lem_paire_not_empty a b) = inter a b.
(* Proof of lem_Einter_paire                                               *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold Einter in H.
elim
 (axs_comprehension
    (fun v0 : E => forall v3 : E, In v3 (paire a b) -> In v0 v3)
    (reunion (paire a b)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
elim (axs_reunion (paire a b) v2); intros; generalize (H1 H); clear H H1 H2;
 intros.
elim H; clear H; intros; elim H; clear H; intros.
generalize (H0 a); generalize (H0 b); clear H0; intros.
cut (In a (paire a b)); cut (In b (paire a b)); intros.
generalize (H0 H3) (H2 H4); clear H0 H2 H3 H4; intros.
unfold inter in |- *.
elim (axs_comprehension (def_F_inter b) a v2); intros; apply H4; clear H3 H4;
 intros.
unfold def_F_inter in |- *; split; auto with zfc.

elim (axs_paire a b b); intros; apply H4; right; reflexivity.

elim (axs_paire a b a); intros; apply H5; left; reflexivity.

elim (axs_paire a b b); intros; apply H4; right; reflexivity.

unfold inter in H; unfold def_F_inter in H.
elim (axs_comprehension (fun x : E => In x b) a v2); intros;
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
unfold Einter in |- *.
elim
 (axs_comprehension
    (fun v0 : E => forall v3 : E, In v3 (paire a b) -> In v0 v3)
    (reunion (paire a b)) v2); intros; apply H2; clear H1 H2; 
 intros.
split; intros.
elim (lem_union_propertie a b v2); unfold union in |- *; intros; apply H2;
 clear H1 H2; intros.
left; auto with zfc.

elim (axs_paire a b v3); intros; generalize (H2 H1); clear H1 H2 H3; intros.
elim H1; clear H1; intros; rewrite H1; auto with zfc.

Qed.
(* End of proof of lem_Einter_paire                                        *)

Lemma lem_Einter_vide :
 forall (x : E) (Nv : x <> Vide), In Vide x -> Einter x Nv = Vide.
(* Proof of lem_Einter_vide                                                *)
intros.
apply lem_x_inc_vide; intros.
unfold inc in |- *; unfold Einter in |- *; intros.
elim
 (axs_comprehension (fun v1 : E => forall v3 : E, In v3 x -> In v1 v3)
    (reunion x) v0); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
exact (H1 Vide H).

Qed.
(* End of proof of lem_Einter_vide                                         *)
(***************************************************************************)
(* Complementaire d'un ensemble                                            *)
(***************************************************************************)
Definition Comp (a b : E) := subset (fun y : E => ~ In y b) a.

Parameter OComp : E -> E -> E.

Axiom def_OComp : forall a b y : E, In y (OComp a b) <-> In y a /\ ~ In y b.

Lemma lem_Comp_eq_OComp : forall a b : E, OComp a b = Comp a b.
(* Proof of lem_Comp_eq_OComp                                              *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
elim (def_OComp a b v2); intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
unfold Comp in |- *.
elim (axs_comprehension (fun y : E => ~ In y b) a v2); intros; apply H2;
 clear H1 H2; intros.
split; auto with zfc.

unfold Comp in H.
elim (axs_comprehension (fun y : E => ~ In y b) a v2); intros;
 generalize (H0 H); clear H H0 H1; intros.
elim (def_OComp a b v2); intros; apply H1; clear H0 H1; intros;
 auto with zfc.

Qed.
(* End of proof of lem_Comp_eq_OComp                                       *)

(***************************************************************************)
(* Difference symetrique de deux ensembles                                 *)
(***************************************************************************)
Definition Delta (a b : E) := union (Comp a b) (Comp b a).

(***************************************************************************)
(* Quelques proprietes agreables                                           *)
(***************************************************************************)
Lemma lem_inter_commut : forall a b : E, inter a b = inter b a.
(* Proof of lem_inter_commut                                               *)
intros; apply axs_extensionnalite; intros.
elim (lem_inter_propertie a b v2); intros.
elim (lem_inter_propertie b a v2); intros.
unfold iff in |- *; split; intros.
clear H0; clear H1; apply H2; apply lem_and_sym; apply H; auto with zfc.

clear H; clear H2; apply H0; apply lem_and_sym; apply H1; auto with zfc.

Qed.
(* End of proof of lem_inter_commut                                        *)

Lemma lem_inter_assoc :
 forall a b c : E, inter (inter a b) c = inter a (inter b c).
(* Proof of lem_inter_assoc                                                *)
intros; apply axs_extensionnalite; intros.
elim (lem_inter_propertie (inter a b) c v2); intros.
elim (lem_inter_propertie a (inter b c) v2); intros.
elim (lem_and_rew_l (In v2 c) (In v2 (inter a b)) (In v2 a /\ In v2 b));
 intros.
elim (lem_and_rew_r (In v2 a) (In v2 (inter b c)) (In v2 b /\ In v2 c));
 intros.
elim (lem_and_assoc_l (In v2 a) (In v2 b) (In v2 c)); intros.
unfold iff in |- *; split; intros.
clear H0; clear H1; clear H4; clear H5; clear H8.
apply H2; clear H2; apply H6; clear H6; apply H7; clear H7.
apply H3; clear H3; apply H; clear H; auto with zfc.

clear H; clear H2; clear H3; clear H6; clear H7.
apply H0; clear H0; apply H4; clear H4; apply H8; clear H8.
apply H5; clear H5; apply H1; clear H1; auto with zfc.

apply (lem_inter_propertie b c v2).

apply (lem_inter_propertie a b v2).

Qed.
(* End of proof of lem_inter_assoc                                         *)

Lemma lem_union_commut : forall a b : E, union a b = union b a.
(* Proof of lem_union_commut                                               *)
intros; apply axs_extensionnalite; intros.
elim (lem_union_propertie a b v2); intros.
elim (lem_union_propertie b a v2); intros.
unfold iff in |- *; split; intros.
clear H0; clear H1.
apply H2; clear H2; apply lem_or_sym; apply H; clear H; auto with zfc.

clear H; clear H2.
apply H0; clear H0; apply lem_or_sym; apply H1; clear H1; auto with zfc.

Qed.
(* End of proof of lem_union_commut                                        *)

Lemma lem_union_assoc :
 forall a b c : E, union (union a b) c = union a (union b c).
(* Proof of lem_union_assoc                                                *)
intros; apply axs_extensionnalite; intros.
elim (lem_union_propertie (union a b) c v2); intros.
elim (lem_union_propertie a (union b c) v2); intros.
elim (lem_or_rew_l (In v2 c) (In v2 (union a b)) (In v2 a \/ In v2 b));
 intros.
elim (lem_or_rew_r (In v2 a) (In v2 (union b c)) (In v2 b \/ In v2 c));
 intros.
elim (lem_or_assoc_l (In v2 a) (In v2 b) (In v2 c)); intros.
unfold iff in |- *; split; intros.
clear H0; clear H1; clear H4; clear H5; clear H8.
apply H2; clear H2; apply H6; clear H6; apply H7; clear H7.
apply H3; clear H3; apply H; clear H; auto with zfc.

clear H; clear H2; clear H3; clear H6; clear H7.
apply H0; clear H0; apply H4; clear H4; apply H8; clear H8.
apply H5; clear H5; apply H1; clear H1; auto with zfc.

apply (lem_union_propertie b c v2).

apply (lem_union_propertie a b v2).

Qed.
(* End of proof of lem_union_assoc                                         *)

Lemma lem_inter_dist :
 forall a b c : E, inter a (union b c) = union (inter a b) (inter a c).
(* Proof of lem_inter_dist                                                 *)
intros; apply axs_extensionnalite; intros.
elim (lem_inter_propertie a (union b c) v2); intros.
elim (lem_union_propertie (inter a b) (inter a c) v2); intros.
elim
 (lem_or_rew_lr (In v2 (inter a b)) (In v2 (inter a c)) 
    (In v2 a /\ In v2 b) (In v2 a /\ In v2 c)); intros.
elim
 (lem_or_rew_lr (In v2 a /\ In v2 b) (In v2 a /\ In v2 c)
    (In v2 b /\ In v2 a) (In v2 c /\ In v2 a)); intros.
elim (lem_and_rew_r (In v2 a) (In v2 (union b c)) (In v2 b \/ In v2 c));
 intros.
unfold iff in |- *; split; intros.
clear H0; clear H1; clear H3; clear H5; clear H8.
apply H2; clear H2; apply H4; clear H4.
apply H6; clear H6; apply lem_and_fact.
apply lem_and_sym; apply H7; clear H7; apply H; clear H; auto with zfc.

clear H; clear H2; clear H4; clear H6; clear H7.
apply H0; clear H0; apply H8; clear H8.
apply lem_and_sym; apply lem_and_dist.
apply H5; clear H5; apply H3; clear H3; apply H1; clear H1; auto with zfc.

apply lem_union_propertie.

unfold iff in |- *; split; intros; apply lem_and_sym; auto with zfc.

unfold iff in |- *; split; intros; apply lem_and_sym; auto with zfc.

apply lem_inter_propertie.

apply lem_inter_propertie.

Qed.
(* End of proof of lem_inter_dist                                          *)

Lemma lem_union_dist :
 forall a b c : E, union a (inter b c) = inter (union a b) (union a c).
(* Proof of lem_union_dist                                                 *)
intros; apply axs_extensionnalite; intros.
elim (lem_union_propertie a (inter b c) v2); intros.
elim (lem_inter_propertie (union a b) (union a c) v2); intros.
elim
 (lem_and_rew_lr (In v2 (union a b)) (In v2 (union a c)) 
    (In v2 a \/ In v2 b) (In v2 a \/ In v2 c)); intros;
 [ idtac | apply lem_union_propertie | apply lem_union_propertie ].
elim (lem_or_rew_r (In v2 a) (In v2 (inter b c)) (In v2 b /\ In v2 c));
 intros; [ idtac | apply lem_inter_propertie ].
unfold iff in |- *; split; intros.
apply H2; clear H2; apply H4; clear H4.
elim
 (lem_and_rew_lr (In v2 a \/ In v2 b) (In v2 a \/ In v2 c)
    (In v2 b \/ In v2 a) (In v2 c \/ In v2 a)); intros;
 [ idtac
 | unfold iff in |- *; split; intros; apply lem_or_sym; auto with zfc
 | unfold iff in |- *; split; intros; apply lem_or_sym; auto with zfc ].
apply H4; clear H4; apply lem_or_fact; apply lem_or_sym; apply H5; clear H5;
 apply H; clear H; auto with zfc.

apply H0; clear H0; apply H6; clear H6; apply lem_or_sym; apply lem_or_dist.
elim
 (lem_and_rew_lr (In v2 b \/ In v2 a) (In v2 c \/ In v2 a)
    (In v2 a \/ In v2 b) (In v2 a \/ In v2 c)); intros;
 [ idtac
 | unfold iff in |- *; split; intros; apply lem_or_sym; auto with zfc
 | unfold iff in |- *; split; intros; apply lem_or_sym; auto with zfc ].
apply H6; clear H6; apply H3; clear H3; apply H1; clear H1; auto with zfc.

Qed.
(* End of proof of lem_union_dist                                          *)

(***************************************************************************)
(* Quelques proprietes de l'ensemble Vide                                  *)
(***************************************************************************)
Lemma lem_reunion_vide : reunion Vide = Vide.
(* Proof of lem_reunion_vide                                               *)
apply axs_extensionnalite; intros.
unfold iff in |- *; split; intros.
elim (axs_reunion Vide v2); intros.
elim H0; clear H0 H1; intros; [ idtac | auto with zfc ].
elim H0; clear H0; intros; unfold Vide in |- *; unfold Vide in H;
 elim (lem_vide_propertie x var_vide); auto with zfc.

unfold Vide in H; elim (lem_vide_propertie v2 var_vide); auto with zfc.

Qed.
(* End of proof of lem_reunion_vide                                        *)

Lemma lem_union_vide : forall a : E, union a Vide = a.
(* Proof of lem_union_vide                                                 *)
intros; apply axs_extensionnalite; intros.
elim (lem_union_propertie a Vide v2); intros.
unfold iff in |- *; split; intros.
elim H; clear H H0; intros;
 [ auto with zfc
 | unfold Vide in H1; elim (lem_vide_propertie v2 var_vide);
    auto with zfc
 | auto with zfc ].

apply H0; clear H H0; left; auto with zfc.

Qed.
(* End of proof of lem_union_vide                                          *)

Lemma lem_inter_vide : forall a : E, inter a Vide = Vide.
(* Proof of lem_inter_vide                                                 *)
intros; apply axs_extensionnalite; intros.
elim (lem_inter_propertie a Vide v2); intros.
unfold iff in |- *; split; intros.
elim H; clear H H0; intros; auto with zfc.

apply H0; clear H H0; unfold Vide in H1;
 elim (lem_vide_propertie v2 var_vide); auto with zfc.

Qed.
(* End of proof of lem_inter_vide                                          *)

(***************************************************************************)
(* Proprietes de l'inclusion                                               *)
(***************************************************************************)
Lemma lem_vide_is_inc : forall a : E, inc Vide a.
(* Proof of lem_vide_is_inc                                                *)
unfold inc in |- *; intros.
unfold Vide in H; elim (lem_vide_propertie v0 var_vide); auto with zfc.

Qed.
(* End of proof of lem_vide_is_inc                                         *)

(***************************************************************************)
(* Definition de l'inclusion stricte                                       *)
(***************************************************************************)
Definition incNotEq (a b : E) : Prop :=
  (forall v0 : E, In v0 a -> In v0 b) /\ (exists y : E, In y b /\ ~ In y a).

(***************************************************************************)
(*                     Next : axs_remplacement.v                           *)
(***************************************************************************)