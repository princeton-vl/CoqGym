(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_paire.v                                                       *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_extensionnalite.

(***************************************************************************)
(* Axiome de la paire                                                      *)
(***************************************************************************)
Parameter paire : E -> E -> E.
Axiom
  axs_paire : forall v0 v1 v3 : E, In v3 (paire v0 v1) <-> v3 = v0 \/ v3 = v1.

(***************************************************************************)
(* Etant donne a et b, {a,b} est unique.                                   *)
(***************************************************************************)
Lemma lem_paire_unique :
 forall a b p : E, (forall y : E, In y p <-> y = a \/ y = b) -> p = paire a b.
(* Proof of lem_paire_unique                                               *)
intros.
apply axs_extensionnalite; intros.
generalize (H v2); clear H; unfold iff in |- *; intros.
elim H; clear H; intros.
generalize (axs_paire a b); unfold iff in |- *; intros.
generalize (H1 v2); clear H1; intros.
elim H1; clear H1; intros.
split; intros.
clear H0; clear H1; auto.

clear H; clear H2; auto.

Qed.
(* End of proof of lem_paire_unique                                        *)

(***************************************************************************)
(* {a,b} = {b,a}                                                           *)
(***************************************************************************)
Lemma lem_paire_sym : forall a b : E, paire a b = paire b a.
(* Proof of lem_paire_sym                                                  *)
intros.
apply axs_extensionnalite; intros; unfold iff in |- *; intros.
elim (axs_paire b a v2); intros.
elim (axs_paire a b v2); intros.
split; intros.
clear H; clear H2; apply H0; clear H0; apply lem_or_sym; auto.

clear H0; clear H1; apply H2; clear H2; apply lem_or_sym; auto.

Qed.
(* End of proof of lem_paire_sym                                           *)

(***************************************************************************)
(* Propriete de la paire                                                   *)
(***************************************************************************)
Lemma lem_paire_propertie :
 forall a0 b0 a1 b1 : E,
 paire a0 b0 = paire a1 b1 <-> a0 = a1 /\ b0 = b1 \/ a0 = b1 /\ b0 = a1.
(* Proof of lem_paire_propertie                                            *)
intros; split; intros.
apply lem_or_and_conv_r.
generalize axs_paire; intros.
split.
elim (H0 a1 b1 a0); intros.
clear H0; clear H2; apply H1; clear H1.
rewrite <- H.
elim (axs_paire a0 b0 a0); intros.
clear H0; apply H1; clear H1; left; reflexivity.

split.
apply lem_or_sym.
elim (H0 a0 b0 b1); clear H0; intros.
clear H1.
elim (lem_eq_or a0 b0 b1); intros.
clear H1; apply H2; clear H2.
apply H0; clear H0.
rewrite H.
elim (axs_paire a1 b1 b1); intros.
clear H0; apply H1; clear H1; right; reflexivity.

split.
elim (lem_eq_or a0 b0 a1); intros.
clear H1; apply H2; clear H2.
elim (H0 a0 b0 a1); clear H0; intros.
clear H1; apply H0; clear H0; rewrite H.
elim (axs_paire a1 b1 a1); intros.
clear H0; apply H1; clear H1; left; reflexivity.

apply lem_or_sym.
elim (H0 a1 b1 b0); clear H0; intros.
clear H1; apply H0; clear H0; rewrite <- H; clear H.
elim (axs_paire a0 b0 b0); intros.
clear H; apply H0; clear H0; right; reflexivity.

elim H; clear H; intros.
elim H; clear H; intros.
rewrite H; clear H; rewrite H0; clear H0; reflexivity.

elim H; clear H; intros.
rewrite H; clear H; rewrite H0; clear H0; elim (lem_paire_sym a1 b1); intros;
 reflexivity.

Qed.
(* End of proof of lem_paire_propertie                                     *)

(***************************************************************************)
(* Singleton                                                               *)
(***************************************************************************)
Definition singleton (a : E) := paire a a.

Hint Unfold singleton: zfc.

(***************************************************************************)
(* {a} = {a'} <=> a = a'                                                   *)
(***************************************************************************)
Lemma lem_singleton_propertie :
 forall a b : E, singleton a = singleton b <-> a = b.
(* Proof of lem_singleton_propertie                                        *)
intros; unfold singleton in |- *.
elim (lem_paire_propertie a a b b); intros.
unfold iff in |- *; split; intros.
apply lem_and_contract; apply lem_or_contract; auto with zfc.

rewrite H1; reflexivity.

Qed.
(* End of proof of lem_singleton_propertie                                 *)

Lemma lem_in_singleton : forall a x : E, In x (singleton a) <-> x = a.
(* Proof of lem_in_singleton                                               *)
intros; elim (axs_paire a a x); intros.
unfold singleton in |- *; unfold iff in |- *; split; intros;
 [ elim H; intros; auto with zfc | apply H0; left; auto with zfc ].

Qed.
(* End of proof of lem_in_singleton                                        *)

Lemma lem_x_in_sing_x : forall x : E, In x (singleton x).
(* Proof of lem_x_in_sing_x                                                *)
intros; unfold singleton in |- *; elim (axs_paire x x x); intros; apply H0;
 clear H0 H; left; reflexivity.

Qed.
(* End of proof of lem_x_in_sing_x                                         *)

(***************************************************************************)
(*                        Next : axs_reunion.v                             *)
(***************************************************************************)