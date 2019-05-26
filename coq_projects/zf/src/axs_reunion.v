(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: axs_reunion.v                                                     *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_paire.

(***************************************************************************)
(* Axiome de la reunion                                                    *)
(***************************************************************************)
Parameter reunion : E -> E.
Axiom
  axs_reunion :
    forall v0 v2 : E,
    In v2 (reunion v0) <-> (exists v3 : E, In v3 v0 /\ In v2 v3).

(***************************************************************************)
(* Unicite de la reunion de d'ensemble                                     *)
(* a est la reunion de b                                                   *)
(***************************************************************************)
Lemma lem_reunion_unique :
 forall v0 v1 : E,
 (forall v2 : E, In v2 v1 <-> (exists v3 : E, In v3 v0 /\ In v2 v3)) ->
 v1 = reunion v0.

(* Preuve de lem_reunion_unique                                            *)
intros.
generalize (axs_reunion v0); intros.
apply axs_extensionnalite; intros.
generalize (H v2); clear H; unfold iff in |- *; intros.
elim H; clear H; intros.
generalize (H0 v2); clear H0; unfold iff in |- *; intros.
elim H0; clear H0; intros.
split; intros.
clear H0; clear H1; auto with zfc.

clear H; clear H2; auto with zfc.

Qed.
(* Fin de la preuve de lem_reunion_unique                                  *)

(* Autre version                                                           *)


(***************************************************************************)
(* Notion d'union de deux ensembles                                        *)
(***************************************************************************)
Definition union (a b : E) := reunion (paire a b).

Hint Unfold union: zfc.

Lemma lem_union_propertie :
 forall a b v0 : E, In v0 (union a b) <-> In v0 a \/ In v0 b.

(* Proof of lem_union_propertie                                            *)
intros; unfold union in |- *.
elim (axs_reunion (paire a b) v0); intros.
unfold iff in |- *; split; intros.
elim H; clear H; intros.
clear H0; clear H1.
elim (axs_paire a b x); unfold iff in |- *; intros.
elim H; clear H; intros.
clear H1; elim H0; clear H0; intros.
clear H; rewrite <- H0; left; assumption.

clear H; rewrite <- H0; right; assumption.

clear H2; assumption.

clear H0; assumption.

apply H0; elim H1; clear H1; intros.
clear H; clear H0; exists a; split.
clear H1; elim (axs_paire a b a); intros; auto with zfc.

assumption.

clear H; clear H0; exists b; split.
clear H1; elim (axs_paire a b b); intros; auto with zfc.

assumption.

Qed.
(* End of proof of lem_union_propertie                                     *)

Lemma lem_union_propertie_lr :
 forall a b v0 : E, In v0 (union a b) -> In v0 a \/ In v0 b.
(* Proof of lem_union_propertie_lr                                         *)
intros; elim (lem_union_propertie a b v0); intros; exact (H0 H).

Qed.
(* End of proof of lem_union_propertie_lr                                  *)

Lemma lem_union_propertie_rl :
 forall a b v0 : E, In v0 a \/ In v0 b -> In v0 (union a b).
(* Proof of lem_union_propertie_rl                                         *)
intros; elim (lem_union_propertie a b v0); intros; exact (H1 H).

Qed.
(* End of proof of lem_union_propertie_rl                                  *)

(***************************************************************************)
(*                        Next : axs_parties.v                             *)
(***************************************************************************)