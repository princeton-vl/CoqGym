(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_fundation.v                                                   *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_choice.

Axiom axs_vide_or_not : forall x : E, x = Vide \/ x <> Vide.

Axiom
  axs_fundation :
    forall x : E, x <> Vide -> exists y : E, In y x /\ inter y x = Vide.
(***************************************************************************)
(* Un ensemble ne s'appartient pas.                                        *)
(***************************************************************************)
Lemma lem_sing_not_empty : forall x : E, singleton x <> Vide.
(* Proof of lem_sing_not_empty                                             *)
unfold not in |- *; intros.
unfold Vide in H; generalize (lem_vide_propertie x var_vide); rewrite <- H;
 intros.
generalize (lem_x_in_sing_x x); intros.
absurd (In x (singleton x)); auto with zfc.

Qed.
(* End of proof of lem_sing_not_empty                                      *)

Lemma lem_x_not_in_x : forall x : E, ~ In x x.
(* Proof of lem_x_not_in_x                                                 *)
unfold not in |- *; intros.
elim (axs_vide_or_not x); intros.
generalize H; clear H; rewrite H0; clear H0; intros.
generalize lem_not_vide_in_vide; intros.
absurd (In Vide Vide); auto with zfc.

generalize (axs_fundation (singleton x) (lem_sing_not_empty x)); intros.
elim H1; clear H1; intros; elim H1; clear H1; intros.
elim (axs_paire x x x0); intros; generalize (H3 H1); clear H1 H3 H4; intros.
generalize (lem_or_contract (x0 = x) H1); clear H1; intros.
generalize H2; clear H2; rewrite H1; clear H1; intros.
cut (In x (inter x (singleton x))); intros.
generalize H1; clear H1; rewrite H2; unfold Vide in |- *; intros.
generalize (lem_vide_propertie x var_vide); intros.
absurd (In x (vide var_vide)); auto with zfc.

unfold inter in |- *; unfold def_F_inter in |- *.
elim (axs_comprehension (fun x0 : E => In x0 (singleton x)) x x); intros;
 apply H3; clear H1 H3; intros.
split; [ auto with zfc | apply lem_x_in_sing_x ].

Qed.
(* End of proof of lem_x_not_in_x                                          *)

(***************************************************************************)
(* Une propriete sur les intersections vides                               *)
(***************************************************************************)
Lemma lem_inter_is_empty :
 forall a b : E,
 (forall x : E, In x a -> ~ In x b) ->
 (forall y : E, In y b -> ~ In y a) -> inter a b = Vide.
(* Proof of lem_inter_is_empty                                             *)
intros.
apply lem_x_inc_vide; unfold inc in |- *; intros.
unfold inter in H1.
unfold def_F_inter in H1.
elim (axs_comprehension (fun x : E => In x b) a v0); intros;
 generalize (H2 H1); clear H1 H2 H3; intros.
elim H1; clear H1; intros.
generalize (H v0 H1) (H0 v0 H2); clear H H0; intros.
absurd (In v0 a); auto with zfc.

Qed.
(* End of proof of lem_inter_is_empty                                      *)
(***************************************************************************)