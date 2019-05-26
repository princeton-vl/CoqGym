(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: couples.v                                                         *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_remplacement.

Definition couple (a b : E) := paire (singleton a) (paire a b).

(***************************************************************************)
(* Un lemme intermediaire sur les paires : {a,b}={a,c} ==> b=c             *)
(***************************************************************************)
Lemma lem_paire_prop2 : forall a b c : E, paire a b = paire a c <-> b = c.
(* Proof of lem_paire_prop2                                                *)
intros; unfold iff in |- *; split; intros.
elim (lem_paire_propertie a b a c); intros.
elim H0; intros; [ idtac | idtac | auto with zfc ]; elim H2; intros;
 [ auto with zfc | rewrite <- H3; rewrite H4; reflexivity ].

rewrite H; reflexivity.

Qed.
(* End of proof of lem_paire_prop2                                         *)

(***************************************************************************)
(* {a} = {b,c} <==> (a=b) /\ (a=c)                                         *)
(***************************************************************************)
Lemma lem_sing_eq_paire :
 forall a b c : E, singleton a = paire b c <-> a = b /\ a = c.
(* Proof of lem_sing_eq_paire                                              *)
intros; unfold singleton in |- *; unfold iff in |- *; split; intros.
elim (lem_paire_propertie a a b c); intros.
elim H0; intros;
 [ auto with zfc
 | elim H2; intros; split; auto with zfc
 | auto with zfc ].

elim H; intros; rewrite <- H0; rewrite <- H1; reflexivity.

Qed.
(* End of proof of lem_sing_eq_paire                                       *)

(***************************************************************************)
(* (a,b)=(c,d) <==> (a=c /\ b=d)                                           *)
(***************************************************************************)
Lemma lem_couple_propertie :
 forall al ar bl br : E, couple al bl = couple ar br <-> al = ar /\ bl = br.
(* Proof of lem_couple_propertie                                           *)
unfold couple in |- *; intros.
unfold iff in |- *; split; intros.
elim
 (lem_paire_propertie (singleton al) (paire al bl) 
    (singleton ar) (paire ar br)); intros.
clear H1; elim H0; clear H0; intros; [ idtac | idtac | auto with zfc ];
 elim H0; clear H0; intros.
elim (lem_singleton_propertie al ar); intros.
generalize H1; clear H1; elim H2; clear H2; intros;
 [ idtac | auto with zfc ].
elim (lem_paire_prop2 al bl br); intros.
split; [ reflexivity | auto with zfc ].

elim (lem_sing_eq_paire al ar br); intros.
elim (lem_sing_eq_paire ar al bl); intros.
cut (singleton ar = paire al bl); intros;
 [ idtac | symmetry  in |- *; auto with zfc ].
elim H2; intros; [ idtac | auto with zfc ].
elim H4; intros; [ idtac | auto with zfc ].
rewrite <- H10; rewrite <- H7; rewrite <- H8; split; reflexivity.

elim H; clear H; intros.
rewrite H; rewrite H0; reflexivity.

Qed.
(* End of proof of lem_couple_propertie                                    *)

Lemma lem_couple_propertie_lr :
 forall al ar bl br : E, couple al bl = couple ar br -> al = ar /\ bl = br.
(* Proof of lem_couple_propertie_lr                                        *)
intros; elim (lem_couple_propertie al ar bl br); intros; exact (H0 H).

Qed.
(* End of proof of lem_couple_propertie_lr                                 *)

Lemma lem_couple_propertie_rl :
 forall al ar bl br : E, al = ar /\ bl = br -> couple al bl = couple ar br.
(* Proof of lem_couple_propertie_rl                                        *)
intros; elim (lem_couple_propertie al ar bl br); intros; exact (H1 H).

Qed.
(* End of proof of lem_couple_propertie_rl                                 *)

(***************************************************************************)
(* Produit cartesien de deux ensembles                                     *)
(***************************************************************************)
Definition cartesien (a b : E) :=
  subset
    (fun u : E =>
     exists x : E, (exists y : E, In x a /\ In y b /\ u = couple x y))
    (parties (parties (union a b))).

Lemma lem_cartesian_propertie :
 forall a b x : E,
 In x (cartesien a b) <->
 (exists v1 : E, (exists v2 : E, In v1 a /\ In v2 b /\ x = couple v1 v2)).
(* Proof of lem_cartesian_propertie                                        *)
intros; unfold cartesien in |- *.
elim
 (axs_comprehension
    (fun u : E =>
     exists x0 : E, (exists y : E, In x0 a /\ In y b /\ u = couple x0 y))
    (parties (parties (union a b))) x); intros.
unfold iff in |- *; split; intros.
elim H; clear H; clear H0; intros; [ idtac | auto with zfc ].
do 2 (elim H0; clear H0; intros); exists x0; exists x1; auto with zfc.

do 2 (elim H1; clear H1; intros); clear H; apply H0; clear H0.
split; [ idtac | exists x0; exists x1; auto with zfc ].
elim H1; clear H1; intros; elim H0; clear H0; intros.
elim (axs_parties (parties (union a b)) x); intros.
clear H2; apply H3; clear H3; intros.
elim (axs_parties (union a b) v3); intros.
clear H3; apply H4; clear H4; intros.
elim (lem_union_propertie a b v0); intros.
clear H4; apply H5; clear H5; intros.
unfold couple in H1.
elim (axs_paire (singleton x0) (paire x0 x1) v3); intros.
generalize H2; rewrite H1; intros.
clear H5; elim H4; clear H4; intros; [ idtac | idtac | auto with zfc ].
generalize H3; rewrite H4; intros.
elim (lem_in_singleton x0 v0); intros.
generalize H; clear H8; elim H7; clear H7; intros;
 [ idtac | auto with zfc ]; left; auto with zfc.

generalize H3; rewrite H4; intros.
elim (axs_paire x0 x1 v0); intros.
clear H8; elim H7; clear H7; intros;
 [ rewrite H7; left; auto with zfc
 | rewrite H7; right; auto with zfc
 | auto with zfc ].

Qed.
(* End of proof of lem_cartesian_propertie                                 *)

Lemma lem_cartesian_cons :
 forall x y a b : E, In x a -> In y b -> In (couple x y) (cartesien a b).
(* Proof of lem_cartesian_cons                                             *)
intros; unfold cartesien in |- *.
elim
 (axs_comprehension
    (fun u : E =>
     exists x0 : E, (exists y0 : E, In x0 a /\ In y0 b /\ u = couple x0 y0))
    (parties (parties (union a b))) (couple x y)); 
 intros; apply H2; clear H1 H2; intros.
split;
 [ idtac
 | exists x; exists y; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ] ].
elim (axs_parties (parties (union a b)) (couple x y)); intros; apply H2;
 clear H1 H2; intros.
elim (axs_parties (union a b) v3); intros; apply H3; clear H2 H3; intros.
unfold couple in H1; generalize (axs_paire (singleton x) (paire x y) v3);
 unfold iff in |- *; intros.
elim H3; clear H3; intros.
generalize (H3 H1); clear H3 H4; intros.
elim H3; clear H3; intros.
generalize H2; clear H2; rewrite H3; clear H3; intros.
elim (lem_in_singleton x v0); intros.
generalize (H3 H2); clear H2 H3 H4; intros; rewrite H2.
elim (lem_union_propertie a b x); intros.
apply H4; left; auto with zfc.

generalize H2; clear H2; rewrite H3; clear H3; intros.
elim (axs_paire x y v0); intros.
generalize (H3 H2); clear H2 H3 H4; intros; elim H2; clear H2; intros.
rewrite H2; clear H2; elim (lem_union_propertie a b x); intros.
apply H3; left; auto with zfc.

rewrite H2; clear H2; elim (lem_union_propertie a b y); intros.
apply H3; right; auto with zfc.

Qed.
(* End of proof of lem_cartesian_cons                                      *)

(***************************************************************************)
(* Somme disjointe de deux ensembles                                       *)
(***************************************************************************)
(* Old Release                                                             *)
Parameter Odisj_l : E -> E.
Axiom
  axs_Odisj_l :
    forall a x : E,
    In x (Odisj_l a) <-> (exists y : E, In y a /\ x = couple y Vide).
Parameter Odisj_r : E -> E.
Axiom
  axs_Odisj_r :
    forall a x : E,
    In x (Odisj_r a) <->
    (exists y : E, In y a /\ x = couple y (singleton Vide)).

Definition Osomme_disj (a b : E) := union (Odisj_l a) (Odisj_r b).

(* New Release                                                             *)
Definition disj_l (a : E) :=
  subset (fun y : E => exists x : E, y = couple x Vide /\ In x a)
    (cartesien a (singleton Vide)).

Definition disj_r (a : E) :=
  subset (fun y : E => exists x : E, y = couple x (singleton Vide) /\ In x a)
    (cartesien a (singleton (singleton Vide))).

Definition somme_disj (a b : E) := union (disj_l a) (disj_r b).

(* Old and New                                                             *)
Lemma lem_OaN : forall a b : E, somme_disj a b = Osomme_disj a b.
(* Proof of lem_OaN                                                        *)
intros; apply axs_extensionnalite; intros.
unfold somme_disj in |- *; unfold Osomme_disj in |- *.
elim (lem_union_propertie (disj_l a) (disj_r b) v2); intros.
elim (lem_union_propertie (Odisj_l a) (Odisj_r b) v2); intros.
elim (axs_Odisj_l a v2); intros.
elim (axs_Odisj_r b v2); intros.
elim
 (axs_comprehension (fun y : E => exists x : E, y = couple x Vide /\ In x a)
    (cartesien a (singleton Vide)) v2); intros.
elim
 (axs_comprehension
    (fun y : E => exists x : E, y = couple x (singleton Vide) /\ In x b)
    (cartesien b (singleton (singleton Vide))) v2); 
 intros.
unfold iff in |- *; split; intros.
elim H; clear H H0; intros;
 [ clear H11; apply H2; clear H1 H2; intros
 | clear H11; apply H2; clear H1 H2; intros
 | auto with zfc ].
unfold disj_l in H.
elim H7; clear H7 H8; intros; [ clear H | auto with zfc ].
elim H1; clear H1; intros.
elim H; clear H; intros.
left; apply H4; clear H3 H4; intros.
exists x; split; auto with zfc.

unfold disj_r in H.
elim H9; clear H9 H10; intros; [ clear H | auto with zfc ].
elim H1; clear H1; intros.
elim H; clear H; intros.
right; apply H6; clear H5 H6; intros.
exists x; split; auto with zfc.

apply H0; clear H H0; intros.
elim H1; clear H1 H2; intros; [ clear H11 | clear H11 | auto with zfc ].
left; unfold disj_l in |- *; apply H8; clear H7 H8; intros.
apply lem_and_sym; elim H3; clear H3 H4; intros;
 [ clear H | auto with zfc ].
elim H0; clear H0; intros.
split; [ exists x; split; auto with zfc | idtac ].
elim (lem_cartesian_propertie a (singleton Vide) v2); intros.
apply H2; clear H1 H2; exists x; exists Vide; split;
 [ auto with zfc
 | apply lem_and_sym; split; [ auto with zfc | idtac ] ].
unfold singleton in |- *; elim (axs_paire Vide Vide Vide); intros.
apply H2; clear H1 H2; left; reflexivity.

right; unfold disj_r in |- *; apply H10; clear H9 H10; intros.
apply lem_and_sym; elim H5; clear H5 H6; intros;
 [ clear H | auto with zfc ].
elim H0; clear H0; intros.
split; [ exists x; split; auto with zfc | idtac ].
elim (lem_cartesian_propertie b (singleton (singleton Vide)) v2); intros.
apply H2; clear H1 H2; exists x; exists (singleton Vide); split;
 [ auto with zfc
 | apply lem_and_sym; split; [ auto with zfc | idtac ] ].
unfold singleton in |- *;
 elim (axs_paire (paire Vide Vide) (paire Vide Vide) (paire Vide Vide));
 intros.
apply H2; left; reflexivity.

Qed.
(* End of proof of lem_OaN                                                 *)

(***************************************************************************)
(* Extension des constructions d'ensembles                                 *)
(***************************************************************************)
(*
Lemma lem_ext_set :
  (f:E->E)(P:E->Prop)
  (Ex[ns:E]((y:E)((In y ns) <-> (Ex[t:E]((y=(f t)) /\ (P t))))))
.
(* Proof of lem_ext_set                                                    *)
????
(* End of proof of lem_ext_set                                             *)
*)
(***************************************************************************)
(*                     Projections et couples                              *)
(***************************************************************************)
(* Un lemme auxiliaire: La reunion d'un couple (a,b) est la paire {a,b}    *)
Lemma lem_reunion_couple : forall a b : E, reunion (couple a b) = paire a b.
(* Proof of lem_reunion_couple                                             *)
intros; apply axs_extensionnalite; intros.
unfold couple in |- *.
elim (axs_reunion (paire (singleton a) (paire a b)) v2); intros.
elim (axs_paire a b v2); intros.
unfold iff in |- *; split; intros.
elim H; clear H H0; intros; [ clear H3 | auto with zfc ].
elim H; clear H; intros.
apply H2; clear H1 H2; intros.
elim (axs_paire (singleton a) (paire a b) x); intros.
elim H1; clear H1 H2; intros; [ clear H | clear H | auto with zfc ].
left; generalize H0; rewrite H1; clear H1 H0; intros.
unfold singleton in H0.
elim (axs_paire a a v2); intros.
apply lem_or_contract; apply H; auto with zfc.

generalize H0; rewrite H1; clear H1 H0; intros.
elim (axs_paire a b v2); auto with zfc.

apply H0; clear H0 H; intros.
exists (paire a b); split; [ idtac | auto with zfc ].
clear H1 H2 H3; elim (axs_paire (singleton a) (paire a b) (paire a b));
 auto with zfc.

Qed.
(* End of proof of lem_reunion_couple                                      *)

(* Definitions des projections par comprehension                           *)
Definition first (c : E) :=
  subset
    (fun x : E => exists a : E, (exists b : E, c = couple a b /\ In x a))
    (reunion (reunion c)).
Definition second (c : E) :=
  subset
    (fun x : E => exists a : E, (exists b : E, c = couple a b /\ In x b))
    (reunion (reunion c)).

Lemma lem_first_propertie : forall a b : E, first (couple a b) = a.
(* Proof of lem_first_propertie                                            *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold first in H.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E, (exists b0 : E, couple a b = couple a0 b0 /\ In x a0))
    (reunion (reunion (couple a b))) v2); intros.
elim H0; clear H0 H1; intros; [ clear H | auto with zfc ].
elim H1; clear H1; intros.
elim H; clear H; intros.
elim H; clear H; intros.
elim (lem_couple_propertie a x b x0); intros.
elim H2; clear H2 H3; intros; [ clear H | auto with zfc ].
rewrite H2; auto with zfc.

unfold first in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E, (exists b0 : E, couple a b = couple a0 b0 /\ In x a0))
    (reunion (reunion (couple a b))) v2); intros.
apply H1; clear H1 H0; intros.
rewrite (lem_reunion_couple a b).
split;
 [ idtac | exists a; exists b; split; [ reflexivity | auto with zfc ] ].
elim (lem_union_propertie a b v2); intros.
clear H0; unfold union in H1; apply H1; clear H1; intros.
left; auto with zfc.

Qed.
(* End of proof of lem_first_prop                                          *)

Lemma lem_second_propertie : forall a b : E, second (couple a b) = b.
(* Proof of lem_second_propertie                                           *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold second in H.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E, (exists b0 : E, couple a b = couple a0 b0 /\ In x b0))
    (reunion (reunion (couple a b))) v2); intros.
elim H0; clear H0 H1; intros; [ clear H | auto with zfc ].
elim H1; clear H1; intros.
elim H; clear H; intros.
elim H; clear H; intros.
elim (lem_couple_propertie a x b x0); intros.
elim H2; clear H2 H3; intros; [ clear H | auto with zfc ].
rewrite H3; auto with zfc.

unfold second in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E, (exists b0 : E, couple a b = couple a0 b0 /\ In x b0))
    (reunion (reunion (couple a b))) v2); intros.
apply H1; clear H1 H0; intros.
rewrite (lem_reunion_couple a b).
split;
 [ idtac | exists a; exists b; split; [ reflexivity | auto with zfc ] ].
elim (lem_union_propertie a b v2); intros.
clear H0; unfold union in H1; apply H1; clear H1; intros.
right; auto with zfc.

Qed.
(* End of proof of lem_second_propertie                                    *)

(***************************************************************************)
(* Couples et reunion                                                      *)
(***************************************************************************)
Lemma lem_couple_reunion_prop :
 forall x y z : E,
 In (couple x y) z ->
 In x (reunion (reunion z)) /\ In y (reunion (reunion z)).
(* Proof of lem_couple_reunion_prop                                        *)
intros.
split.
elim (axs_reunion (reunion z) x); intros; apply H1; clear H0 H1; intros.
exists (singleton x); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion z (singleton x)); intros; apply H1; clear H0 H1; intros.
exists (couple x y); split;
 [ auto with zfc
 | elim (axs_paire (singleton x) (paire x y) (singleton x)); intros; apply H1;
    left; reflexivity ].

elim (axs_reunion (reunion z) y); intros; apply H1; clear H0 H1; intros.
exists (paire x y); split;
 [ idtac | elim (axs_paire x y y); intros; apply H1; right; reflexivity ].
elim (axs_reunion z (paire x y)); intros; apply H1; clear H0 H1; intros.
exists (couple x y); split;
 [ auto with zfc
 | elim (axs_paire (singleton x) (paire x y) (paire x y)); intros; apply H1;
    right; reflexivity ].

Qed.
(* End of proof of lem_couple_reunion_prop                                 *)

(***************************************************************************)
(*                        Les n-uplets                                     *)
(***************************************************************************)
Inductive isTupple : nat -> E -> Prop :=
  | c_0_tupple : isTupple 0 Vide
  | c_1_tupple : forall a : E, isTupple 1 a
  | c_2_tupple : forall a b : E, isTupple 2 (couple a b)
  | c_n_tupple :
      forall (a b : E) (n : nat),
      isTupple (S (S n)) b -> isTupple (S (S (S n))) (couple a b).

Fixpoint cart_power (m : nat) : E -> E :=
  fun a : E =>
  match m with
  | O => Vide
  | S O => a
  | S (S n as N) => cartesien a (cart_power N a)
  end.

Lemma cart_power_eq1 : forall a : E, cart_power 0 a = Vide. 
Proof.
 auto with zfc.
Qed.

Lemma cart_power_eq2 : forall a : E, cart_power 1 a = a.
Proof.
 auto with zfc.
Qed.

Lemma cart_power_eq3 :
 forall (n : nat) (a : E),
 cart_power (S (S n)) a = cartesien a (cart_power (S n) a).
Proof.
 auto with zfc.
Qed.

Lemma lem_eq_cart_power : forall a : E, cart_power 2 a = cartesien a a.
(* Proof of lem_eq_cart_power                                              *)
intros; rewrite (cart_power_eq3 0 a); rewrite (cart_power_eq2 a); reflexivity.

Qed.
(* End of proof of lem_eq_cart_power                                       *)

(***************************************************************************)
(*                     Next : relations.v                                  *)
(***************************************************************************)