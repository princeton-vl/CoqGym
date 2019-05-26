(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: ZFrelations.v                                                     *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export axs_fundation.

(***************************************************************************)
(***************************************************************************)
(* Une relation est un ensemble de couples                                 *)
(* Nous nous interessons ici aux relations binaires.                       *)
(***************************************************************************)
(***************************************************************************)
Definition rel (r : E) :=
  forall c : E, In c r -> exists x : E, (exists y : E, c = couple x y).

Definition rel_sig (r a b : E) := inc r (cartesien a b).

Lemma lem_rel_sig_to_rel : forall r a b : E, rel_sig r a b -> rel r.
(* Proof of lem_rel_sig_is_rel                                             *)
unfold rel_sig in |- *; unfold inc in |- *; intros.
unfold rel in |- *; intros.
generalize (H c H0); clear H H0; intros.
elim (lem_cartesian_propertie a b c); intros; generalize (H0 H);
 clear H H0 H1; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
exists x; exists x0; auto with zfc.

Qed.
(* End of proof of lem_rel_sig_is_rel                                      *)

Lemma lem_rel_to_rel_sig :
 forall r : E, rel r -> exists a : E, (exists b : E, rel_sig r a b).
(* Proof of lem_rel_to_rel_sig                                             *)
intros.
unfold rel in H.
exists
 (subset (fun z : E => exists t : E, In (couple z t) r) (reunion (reunion r))).
exists
 (subset (fun t : E => exists z : E, In (couple z t) r) (reunion (reunion r))).
unfold rel_sig in |- *; unfold inc in |- *; intros.
generalize (H v0 H0); intros.
elim H1; clear H1; intros; elim H1; clear H1; intros.
elim
 (lem_cartesian_propertie
    (subset (fun z : E => exists t : E, In (couple z t) r)
       (reunion (reunion r)))
    (subset (fun t : E => exists z : E, In (couple z t) r)
       (reunion (reunion r))) v0); intros; apply H3; 
 clear H2 H3; intros.
exists x; exists x0; split; [ idtac | split; [ idtac | auto with zfc ] ].
elim
 (axs_comprehension (fun z : E => exists t : E, In (couple z t) r)
    (reunion (reunion r)) x); intros; apply H3; clear H2 H3; 
 intros.
generalize H0; rewrite H1; intros.
split; [ idtac | exists x0; auto with zfc ].
elim (axs_reunion (reunion r) x); intros; apply H4; clear H3 H4; intros.
exists (singleton x); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion r (singleton x)); intros; apply H4; clear H3 H4; intros.
exists (couple x x0); split; [ auto with zfc | idtac ].
unfold couple in |- *;
 elim (axs_paire (singleton x) (paire x x0) (singleton x)); 
 intros; apply H4; left; reflexivity.

generalize H0; rewrite H1; intros.
elim
 (axs_comprehension (fun t : E => exists z : E, In (couple z t) r)
    (reunion (reunion r)) x0); intros; apply H4; clear H3 H4; 
 intros.
split; [ idtac | exists x; auto with zfc ].
elim (axs_reunion (reunion r) x0); intros; apply H4; clear H3 H4; intros.
exists (paire x x0); split;
 [ idtac | elim (axs_paire x x0 x0); intros; apply H4; right; reflexivity ].
elim (axs_reunion r (paire x x0)); intros; apply H4; clear H3 H4; intros.
exists (couple x x0); split;
 [ auto with zfc
 | elim (axs_paire (singleton x) (paire x x0) (paire x x0)); intros; apply H4;
    right; reflexivity ].

Qed.
(* End of proof of lem_rel_to_rel_sig                                      *)

(***************************************************************************)
(***************************************************************************)
(* Notions de domaine et d'image d'une relation binaire                    *)
(***************************************************************************)
(***************************************************************************)
Definition rdom (r a b : E) (rRel : rel_sig r a b) :=
  subset (fun x : E => exists y : E, In (couple x y) r) a.

Definition rImg (r a b : E) (rRel : rel_sig r a b) :=
  subset (fun y : E => exists x : E, In (couple x y) r) b.

Definition rdom2 (r : E) (rRel : rel r) :=
  subset (fun x : E => exists y : E, In (couple x y) r) (reunion (reunion r)).

Definition rImg2 (r : E) (rRel : rel r) :=
  subset (fun y : E => exists x : E, In (couple x y) r) (reunion (reunion r)).

Lemma lem_rdom_eq_rdom2 :
 forall (r a b : E) (rRel : rel_sig r a b),
 rdom r a b rRel = rdom2 r (lem_rel_sig_to_rel r a b rRel).
(* Proof of lem_rdom_eq_rdom2                                              *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold rdom in H.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
elim H0; clear H0; intros.
unfold rdom2 in |- *.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) r)
    (reunion (reunion r)) v2); intros; apply H2; clear H1 H2; 
 intros.
split; [ idtac | exists x; auto with zfc ].
elim (axs_reunion (reunion r) v2); intros; apply H2; clear H1 H2; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion r (singleton v2)); intros; apply H2; clear H1 H2; intros.
exists (couple v2 x); split;
 [ auto with zfc
 | unfold couple in |- *;
    elim (axs_paire (singleton v2) (paire v2 x) (singleton v2)); 
    intros; apply H2; left; reflexivity ].

unfold rdom2 in H.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) r)
    (reunion (reunion r)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros.
unfold rdom in |- *.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; apply H2; clear H1 H2; intros.
split; [ idtac | exists x; auto with zfc ].
unfold rel_sig in rRel; unfold inc in rRel.
generalize (rRel (couple v2 x) H0); intros.
elim (lem_cartesian_propertie a b (couple v2 x)); intros; generalize (H2 H1);
 clear H1 H2 H3; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
generalize H1; rewrite H3; tauto.

Qed.
(* End of proof of lem_rdom_eq_rdom2                                       *)

Lemma lem_rImg_eq_rImg2 :
 forall (r a b : E) (rRel : rel_sig r a b),
 rImg r a b rRel = rImg2 r (lem_rel_sig_to_rel r a b rRel).
(* Proof of lem_rImg_eq_rImg2                                              *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold rImg in H.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) b v2);
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros.
unfold rImg2 in |- *.
elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) r)
    (reunion (reunion r)) v2); intros; apply H2; clear H1 H2; 
 intros.
split; [ idtac | exists x; auto with zfc ].
elim (axs_reunion (reunion r) v2); intros; apply H2; clear H1 H2; intros.
exists (paire x v2); split;
 [ idtac | elim (axs_paire x v2 v2); intros; apply H2; right; reflexivity ].
elim (axs_reunion r (paire x v2)); intros; apply H2; clear H1 H2; intros.
exists (couple x v2); split;
 [ auto with zfc
 | unfold couple in |- *;
    elim (axs_paire (singleton x) (paire x v2) (paire x v2)); 
    intros; apply H2; right; reflexivity ].

unfold rImg2 in H.
elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) r)
    (reunion (reunion r)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros.
unfold rImg in |- *.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) b v2);
 intros; apply H2; clear H1 H2; intros.
split; [ idtac | exists x; auto with zfc ].
unfold rel_sig in rRel; unfold inc in rRel.
generalize (rRel (couple x v2) H0); clear rRel H H0; intros.
elim (lem_cartesian_propertie a b (couple x v2)); intros; generalize (H0 H);
 clear H H0 H1; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H2 H1);
 clear H1 H2 H3; intros.
elim H1; clear H1; intros; generalize H0; rewrite H2; tauto.

Qed.
(* End of proof of lem_rImg_eq_rImg2                                       *)

(***************************************************************************)
(* Si (x,y) est dans r alors x est dans le domaine de r.                   *)
(***************************************************************************)
Lemma lem_rel_and_rdom :
 forall (r a b : E) (rRel : rel_sig r a b) (x y : E),
 In (couple x y) r -> In x (rdom r a b rRel).
(* Proof of lem_rel_and_rdom                                               *)
intros; unfold rdom in |- *.
elim (axs_comprehension (fun x0 : E => exists y : E, In (couple x0 y) r) a x);
 intros; apply H1; clear H0 H1; intros.
split; [ idtac | exists y; auto with zfc ].
unfold rel_sig in rRel; unfold inc in rRel.
generalize (rRel (couple x y) H); intros.
elim (lem_cartesian_propertie a b (couple x y)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H3 H2);
 clear H2 H3 H4; intros.
elim H2; clear H2; intros; generalize H0; rewrite H2; tauto.

Qed.
(* End of proof of lem_rel_and_rdom                                        *)

Lemma lem_rel_and_rdom2 :
 forall (r : E) (rRel : rel r) (x y : E),
 In (couple x y) r -> In x (rdom2 r rRel).
(* Proof of lem_rel_and_rdom2                                              *)
unfold rdom2 in |- *; intros.
elim
 (axs_comprehension (fun x0 : E => exists y : E, In (couple x0 y) r)
    (reunion (reunion r)) x); intros; apply H1; clear H0 H1; 
 intros.
split; [ idtac | exists y; auto with zfc ].
elim (axs_reunion (reunion r) x); intros; apply H1; clear H0 H1; intros.
exists (singleton x); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion r (singleton x)); intros; apply H1; clear H0 H1; intros.
exists (couple x y); split; [ auto with zfc | idtac ].
elim (axs_paire (singleton x) (paire x y) (singleton x)); intros; apply H1;
 clear H0 H1; intros.
left; reflexivity.

Qed.
(* End of proof of lem_rel_and_rdom2                                       *)

(***************************************************************************)
(* Si (x,y) est dans r alors y est dans l'image de r.                      *)
(***************************************************************************)
Lemma lem_rel_and_rImg :
 forall (r a b : E) (rRel : rel_sig r a b) (x y : E),
 In (couple x y) r -> In y (rImg r a b rRel).
(* Proof of lem_rel_and_rImg                                               *)
unfold rImg in |- *; intros.
elim (axs_comprehension (fun y0 : E => exists x : E, In (couple x y0) r) b y);
 intros; apply H1; clear H0 H1; intros.
split; [ idtac | exists x; auto with zfc ].
generalize (rRel (couple x y) H); intros.
elim (lem_cartesian_propertie a b (couple x y)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros.
rewrite H3; auto with zfc.

Qed.
(* End of proof of lem_rel_and_rImg                                        *)

Lemma lem_rel_and_rImg2 :
 forall (r : E) (rRel : rel r) (x y : E),
 In (couple x y) r -> In y (rImg2 r rRel).
(* Proof of lem_rel_and_rImg2                                              *)
unfold rImg2 in |- *; intros.
elim
 (axs_comprehension (fun y0 : E => exists x : E, In (couple x y0) r)
    (reunion (reunion r)) y); intros; apply H1; clear H0 H1; 
 intros.
split; [ idtac | exists x; auto with zfc ].
elim (axs_reunion (reunion r) y); intros; apply H1; clear H0 H1; intros.
exists (paire x y); split;
 [ idtac
 | elim (axs_paire x y y); intros; apply H1; intros; right; reflexivity ].
elim (axs_reunion r (paire x y)); intros; apply H1; clear H0 H1; intros.
exists (couple x y); split;
 [ auto with zfc
 | elim (axs_paire (singleton x) (paire x y) (paire x y)); intros; apply H1;
    right; reflexivity ].

Qed.
(* End of proof of lem_rel_and_rImg2                                       *)

(***************************************************************************)
(***************************************************************************)
(* Relation partielle vs relation totale                                   *)
(* Nous considerons ici qu'une relation est totale si tous les elements de *)
(* son domaine sont "consommes" par la relation.                           *)
(***************************************************************************)
(***************************************************************************)
Definition rel_total (r a b : E) (rRel : rel_sig r a b) :=
  rdom r a b rRel = a.

Definition rel_partiel (r a b : E) (rRel : rel_sig r a b) :=
  exists x : E, In x a -> forall y : E, ~ In (couple x y) r.

(***************************************************************************)
(***************************************************************************)
(* Proprietes de base des relations                                        *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Toute application est une relation                                      *)
(***************************************************************************)

Lemma lem_fun_is_rel : forall (f : E) (Af : fun_ f), rel f.
(* Proof of lem_fun_is_rel                                                 *)
unfold rel in |- *; intros.
unfold fun_ in Af.
elim Af; clear Af; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros.
unfold inc in H0.
generalize (H0 c H); clear H H0 H1; intros.
elim (lem_cartesian_propertie x x0 c); intros; generalize (H0 H);
 clear H H0 H1; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
exists x1; exists x2; auto with zfc.

Qed.
(* End of proof of lem_fun_is_rel                                          *)


(***************************************************************************)
(* Le domaine et l'image d'une relation non vide sont non vides            *)
(***************************************************************************)
(*
Lemma lem_rel_not_empty_so_rdom_not_empty :
  (r:E)(rRel:(rel r))
    ~(r=Vide)
    ->
    ~((rdom2 r rRel)=Vide)
.
(* Proof of lem_rel_not_empty_so_rdom_not_empty                            *)
Save.
(* End of proof of lem_rel_not_empty_so_rdom_not_empty                     *)
*)
(***************************************************************************)
(* Considerons maintenant des relations dont l'image est tout ou partie du *)
(* domaine.                                                                *)
(***************************************************************************)

(***************************************************************************)
(* Reflexivite & irreflexivite                                             *)
(***************************************************************************)
Definition reflexivity (r a : E) (rRel : rel_sig r a a) :=
  forall x : E, In x (rdom r a a rRel) -> In (couple x x) r.

Definition irreflexivity (r a : E) (rRel : rel_sig r a a) :=
  forall x : E, In x (rdom r a a rRel) -> ~ In (couple x x) r.

(***************************************************************************)
(* Le domaine d'une relation reflexive est inclus dans l'image             *)
(***************************************************************************)
Lemma lem_refl_dom_inc_img :
 forall (r a : E) (rRel : rel_sig r a a),
 reflexivity r a rRel -> inc (rdom r a a rRel) (rImg r a a rRel).
(* Proof of lem_refl_dom_inc_img                                           *)
unfold inc in |- *; intros.
unfold reflexivity in H.
generalize (H v0 H0); clear H; intros.
unfold rImg in |- *.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) a v0);
 intros; apply H2; clear H1 H2; intros.
split; [ idtac | exists v0; auto with zfc ].
unfold rdom in H0.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v0);
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; auto with zfc.

Qed.
(* End of proof of lem_refl_dom_inc_img                                    *)

(***************************************************************************)
(* Si le domaine d'une relation n'est pas inclus dans l'image, alors la    *)
(* relation n'est pas reflexive.                                           *)
(***************************************************************************)
Lemma lem_refl_dom_inc_img_recip :
 forall (r a : E) (rRel : rel_sig r a a),
 ~ inc (rdom r a a rRel) (rImg r a a rRel) -> ~ reflexivity r a rRel.
(* Proof of lem_refl_dom_inc_img_recip                                     *)
intros.
unfold not in |- *; intros.
generalize (lem_refl_dom_inc_img r a rRel H0); intros.
absurd (inc (rdom r a a rRel) (rImg r a a rRel)); auto with zfc.

Qed.
(* End of proof of lem_refl_dom_inc_img_recip                              *)

(***************************************************************************)
(* Une relation non vide reflexive n'est pas irreflexive                   *)
(***************************************************************************)

Lemma lem_refl_not_irrefl :
 forall (r a : E) (rNe : r <> Vide) (rRel : rel_sig r a a),
 reflexivity r a rRel -> ~ irreflexivity r a rRel.
(* Proof of lem_refl_not_irrefl                                            *)
unfold reflexivity in |- *; unfold irreflexivity in |- *; unfold not in |- *;
 intros.
generalize (axs_fundation r rNe); intros.
elim H1; clear H1; intros; elim H1; clear H1; intros.
generalize rRel; intros; unfold rel_sig in rRel0; unfold inc in rRel0; intros.
generalize (rRel0 x H1); clear rRel0; intros.
elim (lem_cartesian_propertie a a x); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H4; clear H4; intros.
generalize H1; rewrite H5; intros.
cut (In x0 (rdom r a a rRel)); intros.
generalize (H x0 H7) (H0 x0 H7); intros.
absurd (In (couple x0 x0) r); auto with zfc.

unfold rdom in |- *.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a x0);
 intros; apply H8; clear H7 H8; intros.
split; [ auto with zfc | exists x1; auto with zfc ].

Qed.
(* End of proof of lem_refl_not_irrefl                                     *)

(***************************************************************************)
(* Une relation non vide irreflexive n'est pas reflexivive                 *)
(***************************************************************************)
Lemma lem_irrefl_not_refl :
 forall (r a : E) (rNe : r <> Vide) (rRel : rel_sig r a a),
 irreflexivity r a rRel -> ~ reflexivity r a rRel.
(* Proof of lem_irrefl_not_refl                                            *)
unfold reflexivity in |- *; unfold irreflexivity in |- *; unfold not in |- *;
 intros.
generalize (axs_fundation r rNe); intros; elim H1; clear H1; intros; elim H1;
 clear H1; intros.
generalize rRel; intros; unfold rel_sig in rRel0; unfold inc in rRel0;
 generalize (rRel0 x H1); clear rRel0; intros.
elim (lem_cartesian_propertie a a x); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H4; clear H4; intros.
generalize H1; clear H1; rewrite H5; intros.
cut (In x0 (rdom r a a rRel)); intros.
generalize (H x0 H6) (H0 x0 H6); intros.
absurd (In (couple x0 x0) r); auto with zfc.

unfold rdom in |- *.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a x0);
 intros; apply H7; clear H6 H7; intros.
split; [ auto with zfc | exists x1; auto with zfc ].

Qed.
(* End of proof of lem_irrefl_not_refl                                     *)


(***************************************************************************)
(* Symmetrie & antisymetrie                                                *)
(***************************************************************************)
Definition symmetry (r a : E) (rRel : rel_sig r a a) :=
  forall x y : E, In (couple x y) r -> In (couple y x) r.
Definition antisymmetry (r a : E) (rRel : rel_sig r a a) :=
  forall x y : E, In (couple x y) r -> In (couple y x) r -> x = y.

(***************************************************************************)
(* Propriete de la symetrie                                                *)
(***************************************************************************)
Lemma lem_sym_so_rdom_eq_rImg :
 forall (r a : E) (rRel : rel_sig r a a),
 symmetry r a rRel -> rdom r a a rRel = rImg r a a rRel.
(* Proof of lem_sym_so_rdom_eq_rImg                                        *)
unfold symmetry in |- *; intros.
apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold rdom in H0.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros.
generalize (H v2 x H1); clear H; intros.
unfold rImg in |- *.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) a v2);
 intros; apply H3; clear H2 H3; intros.
split; [ auto with zfc | exists x; auto with zfc ].

unfold rImg in H0.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) a v2);
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros.
generalize (H x v2 H1); clear H H1; intros.
unfold rdom in |- *.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; apply H2; clear H1 H2; intros.
split; [ auto with zfc | exists x; auto with zfc ].

Qed.
(* End of proof of lem_sym_so_rdom_eq_rImg                                 *)

(***************************************************************************)
(* Transitivite                                                            *)
(***************************************************************************)
Definition transitivity (r a : E) (rRel : rel_sig r a a) :=
  forall x y z : E,
  In (couple x y) r -> In (couple y z) r -> In (couple x z) r.

(***************************************************************************)
(***************************************************************************)
(* Autres relations                                                        *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Trois relations sur un ensemble donne                                   *)
(***************************************************************************)

(***************************************************************************)
(* La relation vide                                                        *)
(***************************************************************************)
Lemma lem_Vide_rel_sig : forall a : E, rel_sig Vide a a.
(* Proof of lem_Vide_rel_sig                                               *)
unfold rel_sig in |- *; intros.
exact (lem_vide_is_inc (cartesien a a)).

Qed.
(* End of proof of lem_Vide_rel_sig                                        *)

(***************************************************************************)
(* Le domaine de la relation vide est l'ensemble vide                      *)
(***************************************************************************)
Lemma lem_Vide_dom : forall a : E, rdom Vide a a (lem_Vide_rel_sig a) = Vide.
(* Proof of lem_Vide_dom                                                   *)
intros; apply (lem_x_inc_vide (rdom Vide a a (lem_Vide_rel_sig a)));
 unfold inc in |- *; intros.
unfold rdom in H.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) Vide) a v0);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
generalize (lem_vide_propertie (couple v0 x) var_vide); intros;
 absurd (In (couple v0 x) Vide); auto with zfc.

Qed.
(* End of proof of lem_Vide_dom                                            *)

(***************************************************************************)
(* L'image de la relation vide est l'ensemble vide                         *)
(***************************************************************************)
Lemma lem_Vide_Img : forall a : E, rImg Vide a a (lem_Vide_rel_sig a) = Vide.
(* Proof of lem_Vide_Img                                                   *)
intros; apply (lem_x_inc_vide (rImg Vide a a (lem_Vide_rel_sig a)));
 unfold inc in |- *; unfold rImg in |- *; intros.
elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) Vide) a v0);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
generalize (lem_vide_propertie (couple x v0) var_vide); intros;
 absurd (In (couple x v0) Vide); auto with zfc.

Qed.
(* End of proof of lem_Vide_Img                                            *)

(***************************************************************************)
(* La relation pleine                                                      *)
(***************************************************************************)
Definition rfull (a : E) :=
  subset (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a).

(***************************************************************************)
(* rfull est une relation sur a                                            *)
(***************************************************************************)
Lemma lem_rfull_rel_sig : forall a : E, rel_sig (rfull a) a a.
(* Proof of lem_rfull_rel_sig                                              *)
unfold rel_sig in |- *; unfold inc in |- *; unfold rfull in |- *; intros.
elim
 (axs_comprehension
    (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_rfull_rel_sig                                       *)

(***************************************************************************)
(* Le domaine de la relation pleine est a                                  *)
(***************************************************************************)
Lemma lem_rfull_dom :
 forall a : E, rdom (rfull a) a a (lem_rfull_rel_sig a) = a.
(* Proof of lem_rfull_dom                                                  *)
unfold rdom in |- *; intros; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) (rfull a)) a
    v2); intros; generalize (H0 H); clear H H0 H1; 
 intros; elim H; clear H; intros; auto with zfc.

elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) (rfull a)) a
    v2); intros; apply H1; clear H0 H1; split; [ auto with zfc | idtac ].
exists v2; unfold rfull in |- *.
elim
 (axs_comprehension
    (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a) (couple v2 v2)); intros; apply H1; 
 clear H0 H1; intros; split; [ idtac | exists v2; exists v2; reflexivity ].
elim (lem_cartesian_propertie a a (couple v2 v2)); intros; apply H1;
 clear H0 H1; exists v2; exists v2; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_rfull_dom                                           *)

(***************************************************************************)
(* L'image de la relation pleine est a                                     *)
(***************************************************************************)
Lemma lem_rfull_Img :
 forall a : E, rImg (rfull a) a a (lem_rfull_rel_sig a) = a.
(* Proof of lem_rfull_Img                                                  *)
unfold rImg in |- *; intros; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) (rfull a)) a
    v2); intros; generalize (H0 H); clear H H0 H1; 
 intros; elim H; clear H; intros; auto with zfc.

elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) (rfull a)) a
    v2); intros; apply H1; clear H0 H1; intros; split;
 [ auto with zfc | unfold rfull in |- *; exists v2 ].
elim
 (axs_comprehension
    (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a) (couple v2 v2)); intros; apply H1; 
 clear H0 H1; intros.
split;
 [ elim (lem_cartesian_propertie a a (couple v2 v2)); intros; apply H1;
    exists v2; exists v2; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ]
 | exists v2; exists v2; reflexivity ].

Qed.
(* End of proof of lem_rfull_Img                                           *)

(***************************************************************************)
(* La relation pleine sur a n'est autre que a x a                          *)
(***************************************************************************)
Lemma lem_rfull_eq_cart : forall a : E, rfull a = cartesien a a.
(* Proof of lem_rfull_eq_cart                                              *)
unfold rfull in |- *; intros; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension
    (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros; elim H; clear H; intros; auto with zfc.

elim
 (axs_comprehension
    (fun c : E => exists x : E, (exists y : E, c = couple x y))
    (cartesien a a) v2); intros; apply H1; clear H0 H1; 
 intros; split; [ auto with zfc | idtac ].
elim (lem_cartesian_propertie a a v2); intros; generalize (H0 H);
 clear H H0 H1; intros; elim H; clear H; intros; elim H; 
 clear H; intros; elim H; clear H; intros; elim H0; 
 clear H0; intros.
exists x; exists x0; auto with zfc.

Qed.
(* End of proof of lem_rfull_eq_cart                                       *)

(***************************************************************************)
(* La propriete de la relation pleine                                      *)
(***************************************************************************)
Lemma lem_rfull_prop :
 forall a x y : E, In x a -> In y a -> In (couple x y) (rfull a).
(* Proof of lem_rfull_prop                                                 *)
unfold rfull in |- *; intros.
elim
 (axs_comprehension
    (fun c : E => exists x0 : E, (exists y0 : E, c = couple x0 y0))
    (cartesien a a) (couple x y)); intros; apply H2; 
 clear H1 H2; intros.
split;
 [ elim (lem_cartesian_propertie a a (couple x y)); intros; apply H2;
    exists x; exists y; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ]
 | exists x; exists y; reflexivity ].

Qed.
(* End of proof of lem_rfull_prop                                          *)

(***************************************************************************)
(* La relation identite                                                    *)
(***************************************************************************)
Definition rId (a : E) :=
  subset (fun c : E => exists x : E, c = couple x x) (cartesien a a).

(***************************************************************************)
(* L'identite est une relation                                             *)
(***************************************************************************)
Lemma lem_rId_rel_sig : forall a : E, rel_sig (rId a) a a.
(* Proof of lem_rId_rel_sig                                                *)
unfold rel_sig in |- *; unfold inc in |- *; unfold rId in |- *; intros.
elim
 (axs_comprehension (fun c : E => exists x : E, c = couple x x)
    (cartesien a a) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros; elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_rId_rel_sig                                         *)

(***************************************************************************)
(* Le domaine de l'identite est a                                          *)
(***************************************************************************)
Lemma lem_rId_dom : forall a : E, rdom (rId a) a a (lem_rId_rel_sig a) = a.
(* Proof of lem_rId_dom                                                    *)
unfold rdom in |- *; intros; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) (rId a)) a v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; auto with zfc.

elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) (rId a)) a v2);
 intros; apply H1; clear H0 H1; split;
 [ auto with zfc | exists v2; unfold rId in |- * ].
elim
 (axs_comprehension (fun c : E => exists x : E, c = couple x x)
    (cartesien a a) (couple v2 v2)); intros; apply H1; 
 clear H0 H1; intros.
split;
 [ elim (lem_cartesian_propertie a a (couple v2 v2)); intros; apply H1;
    exists v2; exists v2; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ]
 | exists v2; reflexivity ].

Qed.
(* End of proof of lem_rId_dom                                             *)

(***************************************************************************)
(* L'image de l'identite est a                                             *)
(***************************************************************************)
(*
Lemma lem_rId_Img :
  (a:E)(rImg (rId a) a a (lem_rId_rel_sig a))=a
.
*)
(***************************************************************************)
(* Complementaire d'une relation                                           *)
(***************************************************************************)
Definition rel_Comp (r a b : E) (rRel : rel_sig r a b) :=
  Comp (cartesien a b) r.

Lemma lem_rel_Comp_rel_sig :
 forall (r a b : E) (rRel : rel_sig r a b), rel_sig (rel_Comp r a b rRel) a b.
(* Proof of lem_rel_Comp_rel_sig                                           *)
unfold rel_sig in |- *; unfold rel_Comp in |- *; unfold Comp in |- *;
 unfold inc in |- *; intros.
elim (axs_comprehension (fun y : E => ~ In y r) (cartesien a b) v0); intros;
 generalize (H0 H); clear H H0 H1; intros; elim H; 
 clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_rel_Comp_rel_sig                                    *)

(***************************************************************************)
(* Reunion de relations                                                    *)
(***************************************************************************)
Definition rel_union (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
  (rRel2 : rel_sig r2 a2 b2) := union r1 r2.

Lemma lem_rel_union_rel_sig :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 rel_sig (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2) 
   (union a1 a2) (union b1 b2).
(* Proof of lem_rel_union_rel_sig                                          *)
unfold rel_union in |- *; unfold rel_sig in |- *; unfold inc in |- *; intros.
elim (lem_union_propertie r1 r2 v0); intros; generalize (H0 H); clear H H0 H1;
 intros.
elim (lem_cartesian_propertie (union a1 a2) (union b1 b2) v0); intros;
 apply H1; clear H0 H1; intros.
elim H; clear H; intros.
generalize (rRel1 v0 H); intros.
elim (lem_cartesian_propertie a1 b1 v0); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
exists x; exists x0; split;
 [ elim (lem_union_propertie a1 a2 x); intros; apply H4; left;
    auto with zfc
 | split;
    [ elim (lem_union_propertie b1 b2 x0); intros; apply H4; left;
       auto with zfc
    | auto with zfc ] ].

generalize (rRel2 v0 H); intros.
elim (lem_cartesian_propertie a2 b2 v0); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
exists x; exists x0; split;
 [ elim (lem_union_propertie a1 a2 x); intros; apply H4; right;
    auto with zfc
 | split;
    [ elim (lem_union_propertie b1 b2 x0); intros; apply H4; right;
       auto with zfc
    | auto with zfc ] ].

Qed.
(* End of proof of lem_rel_union_rel_sig                                   *)

(***************************************************************************)
(* Le domaine de l'union de deux relations est l'union des deux domaines   *)
(***************************************************************************)
Lemma lem_rel_union_dom :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 rdom (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2) (union a1 a2) 
   (union b1 b2) (lem_rel_union_rel_sig r1 a1 b1 r2 a2 b2 rRel1 rRel2) =
 union (rdom r1 a1 b1 rRel1) (rdom r2 a2 b2 rRel2).
(* Proof of lem_rel_union_dom                                              *)
intros; unfold rdom in |- *; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists y : E, In (couple x y) (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (union a1 a2) v2); intros; generalize (H0 H); clear H H0 H1; 
 intros.
elim H; clear H; intros; elim H0; clear H0; intros.
unfold rel_union in H0.
elim (lem_union_propertie a1 a2 v2); intros; generalize (H1 H); clear H H1 H2;
 intros.
elim (lem_union_propertie r1 r2 (couple v2 x)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim
 (lem_union_propertie
    (subset (fun x : E => exists y : E, In (couple x y) r1) a1)
    (subset (fun x : E => exists y : E, In (couple x y) r2) a2) v2); 
 intros; apply H2; clear H1 H2; intros.
elim H; elim H0; clear H H0; intros.
left;
 elim
  (axs_comprehension (fun x : E => exists y : E, In (couple x y) r1) a1 v2);
 intros; apply H2; clear H1 H2; split;
 [ auto with zfc | exists x; auto with zfc ].

generalize (rRel2 (couple v2 x) H); intros.
elim (lem_cartesian_propertie a2 b2 (couple v2 x)); intros;
 generalize (H2 H1); clear H1 H2 H3; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x1; intros.
right;
 elim
  (axs_comprehension (fun x : E => exists y : E, In (couple x y) r2) a2 v2);
 intros; apply H4; split; [ auto with zfc | exists x; auto with zfc ].

generalize (rRel1 (couple v2 x) H); intros.
elim (lem_cartesian_propertie a1 b1 (couple v2 x)); intros;
 generalize (H2 H1); clear H1 H2 H3; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x1; intros.
left;
 elim
  (axs_comprehension (fun x : E => exists y : E, In (couple x y) r1) a1 v2);
 intros; apply H4; split; [ auto with zfc | exists x; auto with zfc ].

right;
 elim
  (axs_comprehension (fun x : E => exists y : E, In (couple x y) r2) a2 v2);
 intros; apply H2; split; [ auto with zfc | exists x; auto with zfc ].

elim
 (lem_union_propertie
    (subset (fun x : E => exists y : E, In (couple x y) r1) a1)
    (subset (fun x : E => exists y : E, In (couple x y) r2) a2) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists y : E, In (couple x y) (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (union a1 a2) v2); intros; apply H1; clear H0 H1; 
 intros.
elim H; clear H; intros.
elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) r1) a1 v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
split;
 [ elim (lem_union_propertie a1 a2 v2); intros; apply H2; left;
    auto with zfc
 | exists x; unfold rel_union in |- * ].
elim (lem_union_propertie r1 r2 (couple v2 x)); intros; apply H2; left;
 auto with zfc.

elim
 (axs_comprehension (fun x : E => exists y : E, In (couple x y) r2) a2 v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
split;
 [ elim (lem_union_propertie a1 a2 v2); intros; apply H2; right;
    auto with zfc
 | unfold rel_union in |- * ].
exists x; elim (lem_union_propertie r1 r2 (couple v2 x)); intros; apply H2;
 right; auto with zfc.

Qed.
(* End of proof of lem_rel_union_dom                                       *)

(***************************************************************************)
(* L'image de l'union de deux relations est l'union des deux images        *)
(***************************************************************************)
Lemma lem_rel_union_Img :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 rImg (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2) (union a1 a2) 
   (union b1 b2) (lem_rel_union_rel_sig r1 a1 b1 r2 a2 b2 rRel1 rRel2) =
 union (rImg r1 a1 b1 rRel1) (rImg r2 a2 b2 rRel2).
(* Proof of lem_rel_union_Img                                              *)
unfold rImg in |- *; intros; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension
    (fun y : E =>
     exists x : E, In (couple x y) (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (union b1 b2) v2); intros; generalize (H0 H); clear H H0 H1; 
 intros.
elim H; clear H; intros; elim H0; clear H0; intros.
elim (lem_union_propertie r1 r2 (couple x v2)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim (lem_union_propertie b1 b2 v2); intros; generalize (H1 H); clear H H1 H2;
 intros.
elim
 (lem_union_propertie
    (subset (fun y : E => exists x : E, In (couple x y) r1) b1)
    (subset (fun y : E => exists x : E, In (couple x y) r2) b2) v2); 
 intros; apply H2; clear H1 H2; intros.
elim H0; elim H; clear H H0; intros.
left;
 elim
  (axs_comprehension (fun y : E => exists x : E, In (couple x y) r1) b1 v2);
 intros; apply H2; split; [ auto with zfc | exists x; auto with zfc ].

generalize (rRel1 (couple x v2) H0); intros.
elim (lem_cartesian_propertie a1 b1 (couple x v2)); intros;
 generalize (H2 H1); clear H1 H2 H3; intros; elim H1; 
 clear H1; intros; elim H1; clear H1; intros; elim H1; 
 clear H1; intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x1; intros.
left;
 elim
  (axs_comprehension (fun y : E => exists x : E, In (couple x y) r1) b1 v2);
 intros; apply H4; split; [ auto with zfc | exists x; auto with zfc ].

generalize (rRel2 (couple x v2) H0); intros.
elim (lem_cartesian_propertie a2 b2 (couple x v2)); intros;
 generalize (H2 H1); clear H1 H2 H3; intros; elim H1; 
 clear H1; intros; elim H1; clear H1; intros; elim H1; 
 clear H1; intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x1; intros.
right;
 elim
  (axs_comprehension (fun y : E => exists x : E, In (couple x y) r2) b2 v2);
 intros; apply H4; split; [ auto with zfc | exists x; auto with zfc ].

right;
 elim
  (axs_comprehension (fun y : E => exists x : E, In (couple x y) r2) b2 v2);
 intros; apply H2; split; [ auto with zfc | exists x; auto with zfc ].

elim
 (lem_union_propertie
    (subset (fun y : E => exists x : E, In (couple x y) r1) b1)
    (subset (fun y : E => exists x : E, In (couple x y) r2) b2) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim
 (axs_comprehension
    (fun y : E =>
     exists x : E, In (couple x y) (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (union b1 b2) v2); intros; apply H1; clear H0 H1; 
 intros.
elim H; clear H; intros.
elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) r1) b1 v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
split;
 [ elim (lem_union_propertie b1 b2 v2); intros; apply H2; left;
    auto with zfc
 | exists x; elim (lem_union_propertie r1 r2 (couple x v2)); intros; apply H2;
    left; auto with zfc ].

elim
 (axs_comprehension (fun y : E => exists x : E, In (couple x y) r2) b2 v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
split;
 [ elim (lem_union_propertie b1 b2 v2); intros; apply H2; right;
    auto with zfc
 | exists x; elim (lem_union_propertie r1 r2 (couple x v2)); intros; apply H2;
    right; auto with zfc ].

Qed.
(* End of proof of lem_rel_union_Img                                       *)

(***************************************************************************)
(* Des evidences                                                           *)
(***************************************************************************)
Lemma lem_rel_union_prop :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2) (c : E),
 In c (rel_union r1 a1 b1 r2 a2 b2 rRel1 rRel2) <-> In c r1 \/ In c r2.
(* Proof of lem_rel_union_prop                                             *)
intros; unfold iff in |- *; unfold rel_union in |- *; split; intros.
elim (lem_union_propertie r1 r2 c); intros; exact (H0 H).

elim (lem_union_propertie r1 r2 c); intros; exact (H1 H).

Qed.
(* End of proof of lem_rel_union_prop                                      *)

(***************************************************************************)
(* Intersection de deux relations                                          *)
(***************************************************************************)
Definition rel_inter (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
  (rRel2 : rel_sig r2 a2 b2) := inter r1 r2.

Lemma lem_rel_inter_rel_sig :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 rel_sig (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2) 
   (inter a1 a2) (inter b1 b2).
(* Proof of lem_rel_inter_rel_sig                                          *)
unfold rel_sig in |- *; unfold inc in |- *; unfold rel_inter in |- *; intros.
elim (lem_inter_propertie r1 r2 v0); intros; generalize (H0 H); clear H H0 H1;
 intros; elim H; clear H; intros.
elim (lem_cartesian_propertie (inter a1 a2) (inter b1 b2) v0); intros;
 apply H2; clear H1 H2; intros.
generalize (rRel1 v0 H) (rRel2 v0 H0); clear rRel1 rRel2 H H0; intros.
elim (lem_cartesian_propertie a1 b1 v0); intros; generalize (H1 H);
 clear H H1 H2; intros; elim H; clear H; intros; elim H; 
 clear H; intros; elim H; clear H; intros; elim H1; 
 clear H1; intros.
elim (lem_cartesian_propertie a2 b2 v0); intros; generalize (H3 H0);
 clear H0 H3 H4; intros; elim H0; clear H0; intros; 
 elim H0; clear H0; intros; elim H0; clear H0; intros; 
 elim H3; clear H3; intros.
generalize H4; rewrite H2; clear H2 H4; intros.
elim (lem_couple_propertie x x1 x0 x2); intros; generalize (H2 H4);
 clear H2 H4 H5; intros; elim H2; clear H2; intros; 
 generalize H0 H3; rewrite <- H2; rewrite <- H4; clear H0 H3 H2 H4;
 clear x1 x2; intros.
exists x; exists x0; split;
 [ elim (lem_inter_propertie a1 a2 x); intros; apply H4; split;
    auto with zfc
 | split;
    [ elim (lem_inter_propertie b1 b2 x0); intros; apply H4; split;
       auto with zfc
    | reflexivity ] ].

Qed.
(* End of proof of lem_rel_inter_rel_sig                                   *)

(***************************************************************************)
(* Le domaine de l'intersection de deux relations est inclus dans          *)
(* l'intersection des deux domaines.                                       *)
(***************************************************************************)
Lemma lem_rel_inter_dom :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 inc
   (rdom (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2) 
      (inter a1 a2) (inter b1 b2)
      (lem_rel_inter_rel_sig r1 a1 b1 r2 a2 b2 rRel1 rRel2))
   (inter (rdom r1 a1 b1 rRel1) (rdom r2 a2 b2 rRel2)).
(* Proof of lem_rel_inter_dom                                              *)
unfold inc in |- *; intros.
unfold rdom in H.
elim
 (axs_comprehension
    (fun x : E =>
     exists y : E, In (couple x y) (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (inter a1 a2) v0); intros; generalize (H0 H); clear H H0 H1; 
 intros.
elim H; clear H; intros; elim H0; clear H0; intros.
elim (lem_inter_propertie r1 r2 (couple v0 x)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros; elim H0; clear H0; intros.
generalize (lem_rel_and_rdom r1 a1 b1 rRel1 v0 x H0)
 (lem_rel_and_rdom r2 a2 b2 rRel2 v0 x H1); clear H0 H1; 
 intros.
elim (lem_inter_propertie (rdom r1 a1 b1 rRel1) (rdom r2 a2 b2 rRel2) v0);
 intros; apply H3; split; auto with zfc.

Qed.
(* End of proof of lem_rel_inter_dom                                       *)

(***************************************************************************)
(* L'image de l'intersection de deux relations est incluse dans            *)
(* l'intersection des deux images.                                         *)
(***************************************************************************)
Lemma lem_rel_inter_Img :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2),
 inc
   (rImg (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2) 
      (inter a1 a2) (inter b1 b2)
      (lem_rel_inter_rel_sig r1 a1 b1 r2 a2 b2 rRel1 rRel2))
   (inter (rImg r1 a1 b1 rRel1) (rImg r2 a2 b2 rRel2)).
(* Proof of lem_rel_inter_Img                                              *)
unfold inc in |- *; intros.
unfold rImg in H.
elim
 (axs_comprehension
    (fun y : E =>
     exists x : E, In (couple x y) (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2))
    (inter b1 b2) v0); intros; generalize (H0 H); clear H H0 H1; 
 intros; elim H; clear H; intros; elim H0; clear H0; 
 intros.
elim (lem_inter_propertie r1 r2 (couple x v0)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros; elim H0; clear H0; intros.
generalize (lem_rel_and_rImg r1 a1 b1 rRel1 x v0 H0)
 (lem_rel_and_rImg r2 a2 b2 rRel2 x v0 H1); clear H0 H1; 
 intros;
 elim (lem_inter_propertie (rImg r1 a1 b1 rRel1) (rImg r2 a2 b2 rRel2) v0);
 intros; apply H3; split; auto with zfc.

Qed.
(* End of proof of lem_rel_inter_Img                                       *)

(***************************************************************************)
(* Une evidence                                                            *)
(***************************************************************************)
Lemma lem_rel_inter_prop :
 forall (r1 a1 b1 r2 a2 b2 : E) (rRel1 : rel_sig r1 a1 b1)
   (rRel2 : rel_sig r2 a2 b2) (c : E),
 In c (rel_inter r1 a1 b1 r2 a2 b2 rRel1 rRel2) <-> In c r1 /\ In c r2.
(* Proof of lem_rel_inter_prop                                             *)
unfold rel_inter in |- *; unfold iff in |- *; intros; split; intros.
elim (lem_inter_propertie r1 r2 c); intros; generalize (H0 H); clear H H0;
 intros; auto with zfc.

elim (lem_inter_propertie r1 r2 c); intros; apply H1; auto with zfc.

Qed.
(* End of proof of lem_rel_inter_prop                                      *)

(***************************************************************************)
(* Relation inverse                                                        *)
(***************************************************************************)
Definition rel_inverse (r a b : E) (rRel : rel_sig r a b) :=
  subset
    (fun c : E =>
     exists x : E, (exists y : E, In (couple x y) r /\ c = couple y x))
    (cartesien b a).

Lemma lem_rel_inv_is_rel_sig :
 forall (r a b : E) (rRel : rel_sig r a b),
 rel_sig (rel_inverse r a b rRel) b a.
(* Proof of lem_rel_inv_is_rel_sig                                         *)
unfold rel_sig in |- *; unfold inc in |- *; unfold rel_inverse in |- *;
 intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E, (exists y : E, In (couple x y) r /\ c = couple y x))
    (cartesien b a) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros; elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_rel_inv_is_rel_sig                                  *)

(***************************************************************************)
(* Le domaine de la relation inverse est l'image de la relation initiale   *)
(***************************************************************************)
Lemma lem_rel_inv_dom :
 forall (r a b : E) (rRel : rel_sig r a b),
 rdom (rel_inverse r a b rRel) b a (lem_rel_inv_is_rel_sig r a b rRel) =
 rImg r a b rRel.
(* Proof of lem_rel_inv_dom                                                *)
unfold rdom in |- *; unfold rImg in |- *; intros; apply axs_extensionnalite;
 unfold iff in |- *; split; intros.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In (couple x y) (rel_inverse r a b rRel)) b
    v2); intros; generalize (H0 H); clear H H0 H1; 
 intros; elim H; clear H; intros.
elim H0; clear H0; unfold rel_inverse in |- *; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) r /\ c = couple y x0))
    (cartesien b a) (couple v2 x)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie v2 x1 x x0); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros.
generalize H1; rewrite <- H2; rewrite <- H3; clear H1 H2 H3; clear x0 x1;
 intros.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) b v2);
 intros; apply H3; clear H2 H3; intros.
split; [ auto with zfc | exists x; auto with zfc ].

elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r) b v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In (couple x y) (rel_inverse r a b rRel)) b
    v2); intros; apply H2; clear H1 H2; intros.
split; [ auto with zfc | unfold rel_inverse in |- *; exists x ].
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) r /\ c = couple y x0))
    (cartesien b a) (couple v2 x)); intros; apply H2; 
 clear H1 H2; intros.
split;
 [ idtac | exists x; exists v2; split; [ auto with zfc | reflexivity ] ].
generalize (rRel (couple x v2) H0); intros.
elim (lem_cartesian_propertie a b (couple x v2)); intros; generalize (H2 H1);
 clear H1 H2 H3; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x1; intros.
elim (lem_cartesian_propertie b a (couple v2 x)); intros; apply H4;
 clear H3 H4; intros.
exists v2; exists x; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_rel_inv_dom                                         *)

(***************************************************************************)
(* L'image de la relation inverse est le domaine de la relation initiale   *)
(***************************************************************************)
Lemma lem_rel_inv_Img :
 forall (r a b : E) (rRel : rel_sig r a b),
 rImg (rel_inverse r a b rRel) b a (lem_rel_inv_is_rel_sig r a b rRel) =
 rdom r a b rRel.
(* Proof of lem_rel_inv_Img                                                *)
unfold rImg in |- *; unfold rdom in |- *; intros; apply axs_extensionnalite;
 unfold iff in |- *; split; intros.
elim
 (axs_comprehension
    (fun y : E => exists x : E, In (couple x y) (rel_inverse r a b rRel)) a
    v2); intros; generalize (H0 H); clear H H0 H1; 
 intros; elim H; clear H; intros; elim H0; clear H0;
 unfold rel_inverse in |- *; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) r /\ c = couple y x0))
    (cartesien b a) (couple x v2)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros; elim H0; clear H0; intros; 
 elim H1; clear H1; intros; elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim (lem_couple_propertie x x1 v2 x0); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros; 
 generalize H1; rewrite <- H2; rewrite <- H3; clear H1 H2 H3; 
 clear x0 x1; intros.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; apply H3; clear H2 H3; intros.
split; [ auto with zfc | exists x; auto with zfc ].

elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r) a v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; intros.
generalize (rRel (couple v2 x) H0); intros.
elim (lem_cartesian_propertie a b (couple v2 x)); intros; generalize (H2 H1);
 clear H2 H3; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H3; clear H3; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H5 H4);
 clear H4 H5 H6; intros; elim H4; clear H4; intros; 
 generalize H2 H3; rewrite <- H4; rewrite <- H5; clear H2 H3 H4 H5;
 clear x0 x1; intros.
elim
 (axs_comprehension
    (fun y : E => exists x : E, In (couple x y) (rel_inverse r a b rRel)) a
    v2); intros; apply H5; clear H4 H5; intros.
split; [ auto with zfc | exists x; unfold rel_inverse in |- * ].
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) r /\ c = couple y x0))
    (cartesien b a) (couple x v2)); intros; apply H5; 
 clear H4 H5; intros.
split;
 [ elim (lem_cartesian_propertie b a (couple x v2)); intros; apply H5;
    exists x; exists v2; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ]
 | exists v2; exists x; split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_rel_inv_Img                                         *)

(***************************************************************************)
(* Produit de relations                                                    *)
(***************************************************************************)
Definition rel_prod (r1 r2 a : E) (rRel1 : rel_sig r1 a a)
  (rRel2 : rel_sig r2 a a) :=
  subset
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r1 /\ In (couple y z) r2 /\ c = couple x z)))
    (cartesien a a).

Lemma lem_rel_prod_rel_sig :
 forall (r1 r2 a : E) (rRel1 : rel_sig r1 a a) (rRel2 : rel_sig r2 a a),
 rel_sig (rel_prod r1 r2 a rRel1 rRel2) a a.
(* Proof of lem_rel_prod_rel_sig                                           *)
unfold rel_sig in |- *; unfold inc in |- *; unfold rel_prod in |- *; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r1 /\ In (couple y z) r2 /\ c = couple x z)))
    (cartesien a a) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_rel_prod_rel_sig                                    *)

(***************************************************************************)
(* Le domaine de r1.r2 est inclus dans le domaine de r1                    *)
(***************************************************************************)
Lemma lem_rel_prod_dom :
 forall (r1 r2 a : E) (rRel1 : rel_sig r1 a a) (rRel2 : rel_sig r2 a a),
 inc
   (rdom (rel_prod r1 r2 a rRel1 rRel2) a a
      (lem_rel_prod_rel_sig r1 r2 a rRel1 rRel2)) (rdom r1 a a rRel1).
(* Proof of lem_rel_prod_dom                                               *)
unfold inc in |- *; unfold rdom in |- *; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists y : E, In (couple x y) (rel_prod r1 r2 a rRel1 rRel2)) a v0);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; unfold rel_prod in |- *; 
 intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E,
       (exists y : E,
          (exists z : E,
             In (couple x0 y) r1 /\ In (couple y z) r2 /\ c = couple x0 z)))
    (cartesien a a) (couple v0 x)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H1; clear H1; intros; elim H1; clear H1; 
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie v0 x0 x x2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x2; intros.
elim (axs_comprehension (fun x : E => exists y : E, In (couple x y) r1) a v0);
 intros; apply H4; clear H3 H4; intros.
split; [ auto with zfc | exists x1; auto with zfc ].

Qed.
(* End of proof of lem_rel_prod_dom                                        *)

(***************************************************************************)
(* L'image de r1.r2 est incluse dans l'image de r2                         *)
(***************************************************************************)
Lemma lem_rel_prod_Img :
 forall (r1 r2 a : E) (rRel1 : rel_sig r1 a a) (rRel2 : rel_sig r2 a a),
 inc
   (rImg (rel_prod r1 r2 a rRel1 rRel2) a a
      (lem_rel_prod_rel_sig r1 r2 a rRel1 rRel2)) (rImg r2 a a rRel2).
(* Proof of lem_rel_prod_Img                                               *)
unfold rImg in |- *; unfold inc in |- *; intros.
elim
 (axs_comprehension
    (fun y : E =>
     exists x : E, In (couple x y) (rel_prod r1 r2 a rRel1 rRel2)) a v0);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; elim H0; clear H0; unfold rel_prod in |- *; 
 intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E,
       (exists y : E,
          (exists z : E,
             In (couple x0 y) r1 /\ In (couple y z) r2 /\ c = couple x0 z)))
    (cartesien a a) (couple x v0)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H1; clear H1; intros; elim H1; clear H1; 
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 v0 x2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H1 H2; rewrite <- H3; rewrite <- H4; clear H1 H2 H3 H4;
 clear x0 x2; intros.
elim (axs_comprehension (fun y : E => exists x : E, In (couple x y) r2) a v0);
 intros; apply H4; clear H3 H4; intros.
split; [ auto with zfc | exists x1; auto with zfc ].

Qed.
(* End of proof of lem_rel_prod_Img                                        *)

(***************************************************************************)
(* Le produit est associatif                                               *)
(***************************************************************************)
Lemma lem_rel_prod_assoc :
 forall (r1 r2 r3 a : E) (rRel1 : rel_sig r1 a a) (rRel2 : rel_sig r2 a a)
   (rRel3 : rel_sig r3 a a),
 rel_prod (rel_prod r1 r2 a rRel1 rRel2) r3 a
   (lem_rel_prod_rel_sig r1 r2 a rRel1 rRel2) rRel3 =
 rel_prod r1 (rel_prod r2 r3 a rRel2 rRel3) a rRel1
   (lem_rel_prod_rel_sig r2 r3 a rRel2 rRel3).
(* Proof of lem_rel_prod_assoc                                             *)
unfold rel_prod at 1 3 in |- *; intros; apply axs_extensionnalite;
 unfold iff in |- *; split; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) (rel_prod r1 r2 a rRel1 rRel2) /\
             In (couple y z) r3 /\ c = couple x z))) 
    (cartesien a a) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros;
 elim H0; clear H0; intros; elim H0; clear H0; intros; 
 elim H1; clear H1; intros.
unfold rel_prod in H0.
elim
 (axs_comprehension
    (fun c : E =>
     exists x1 : E,
       (exists y : E,
          (exists z : E,
             In (couple x1 y) r1 /\ In (couple y z) r2 /\ c = couple x1 z)))
    (cartesien a a) (couple x x0)); intros; generalize (H3 H0);
 clear H0 H3 H4; intros.
elim H0; clear H0; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H3; clear H3; intros; elim H3; clear H3; 
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie x x2 x0 x4); intros; generalize (H6 H5);
 clear H5 H6 H7; intros; elim H5; clear H5; intros; 
 generalize H3 H4; rewrite <- H5; rewrite <- H6; clear H3 H4 H5 H6;
 clear x2 x4; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r1 /\
             In (couple y z) (rel_prod r2 r3 a rRel2 rRel3) /\ c = couple x z)))
    (cartesien a a) v2); intros; apply H6; clear H5 H6; 
 intros.
split;
 [ auto with zfc
 | exists x; exists x3; exists x1; split;
    [ auto with zfc
    | unfold rel_prod in |- *; split; [ idtac | auto with zfc ] ] ].
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r2 /\ In (couple y z) r3 /\ c = couple x z)))
    (cartesien a a) (couple x3 x1)); intros; apply H6; 
 clear H5 H6; intros.
split;
 [ idtac
 | exists x3; exists x0; exists x1; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ] ].
generalize (rRel3 (couple x0 x1) H1) (rRel1 (couple x x3) H3);
 clear H H0 H1 H2 H3 H4; intros.
elim (lem_cartesian_propertie a a (couple x0 x1)); intros; generalize (H1 H);
 clear H H1 H2; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H1; clear H1; intros.
elim (lem_couple_propertie x0 x2 x1 x4); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros; 
 generalize H H1; rewrite <- H2; rewrite <- H3; clear H H1 H2 H3; 
 clear x2 x4; intros.
elim (lem_cartesian_propertie a a (couple x x3)); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x2 x3 x4); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H0 H2; rewrite <- H3; rewrite <- H4; clear H0 H2 H3 H4;
 clear x2 x4; intros.
elim (lem_cartesian_propertie a a (couple x3 x1)); intros; apply H4;
 clear H3 H4; exists x3; exists x1; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r1 /\
             In (couple y z) (rel_prod r2 r3 a rRel2 rRel3) /\ c = couple x z)))
    (cartesien a a) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros;
 elim H0; clear H0; intros; elim H0; clear H0; intros; 
 elim H1; clear H1; intros.
unfold rel_prod in H1.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) r2 /\ In (couple y z) r3 /\ c = couple x z)))
    (cartesien a a) (couple x0 x1)); intros; generalize (H3 H1);
 clear H1 H3 H4; intros.
elim H1; clear H1; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H3; clear H3; intros; elim H3; clear H3; 
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie x0 x2 x1 x4); intros; generalize (H6 H5);
 clear H5 H6 H7; intros; elim H5; clear H5; intros; 
 generalize H3 H4; rewrite <- H5; rewrite <- H6; clear H3 H4 H5 H6;
 clear x2 x4; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E,
          (exists z : E,
             In (couple x y) (rel_prod r1 r2 a rRel1 rRel2) /\
             In (couple y z) r3 /\ c = couple x z))) 
    (cartesien a a) v2); intros; apply H6; clear H5 H6; 
 intros.
split;
 [ auto with zfc
 | exists x; exists x3; exists x1; split;
    [ unfold rel_prod in |- * | split; auto with zfc ] ].
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E,
       (exists y : E,
          (exists z : E,
             In (couple x0 y) r1 /\ In (couple y z) r2 /\ c = couple x0 z)))
    (cartesien a a) (couple x x3)); intros; apply H6; 
 clear H5 H6; intros.
split;
 [ idtac
 | exists x; exists x0; exists x3; split;
    [ auto with zfc | split; [ auto with zfc | reflexivity ] ] ].
generalize (rRel1 (couple x x0) H0) (rRel2 (couple x0 x3) H3);
 clear H H0 H1 H2 H3 H4; intros.
elim (lem_cartesian_propertie a a (couple x x0)); intros; generalize (H1 H);
 clear H H1 H2; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H1; clear H1; intros.
elim (lem_couple_propertie x x2 x0 x4); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros; 
 generalize H H1; rewrite <- H2; rewrite <- H3; clear H H1 H2 H3; 
 clear x2 x4; intros.
elim (lem_cartesian_propertie a a (couple x0 x3)); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x0 x2 x3 x4); intros; generalize (H4 H3);
 clear H3 H4 H5; intros; elim H3; clear H3; intros; 
 generalize H0 H2; rewrite <- H3; rewrite <- H4; clear H0 H2 H3 H4;
 clear x2 x4; intros.
elim (lem_cartesian_propertie a a (couple x x3)); intros; apply H4; exists x;
 exists x3; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_rel_prod_assoc                                      *)

(***************************************************************************)
(* L'identite est un element neutre pour le produit                        *)
(***************************************************************************)

(***************************************************************************)
(***************************************************************************)
(* Relations d'equivalence                                                 *)
(***************************************************************************)
(***************************************************************************)
Definition equivalence (r a : E) (rRel : rel_sig r a a) :=
  reflexivity r a rRel /\ symmetry r a rRel /\ transitivity r a rRel.

(***************************************************************************)
(* Classe d'equivalence                                                    *)
(***************************************************************************)
Definition equivClass (r a : E) (rRel : rel_sig r a a)
  (rEqv : equivalence r a rRel) (x : E) :=
  subset (fun y : E => In (couple x y) r) a.

(***************************************************************************)
(* Si x est en relation avec y alors ils ont meme classe d'equivalence     *)
(***************************************************************************)
Lemma lem_equivClass_eq :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (x y : E),
 In (couple x y) r -> equivClass r a rRel rEqv x = equivClass r a rRel rEqv y.
(* Proof of lem_equivClass_eq                                              *)
intros; unfold equivClass in |- *; apply axs_extensionnalite;
 unfold iff in |- *; split; intros.
elim (axs_comprehension (fun y : E => In (couple x y) r) a v2); intros;
 generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros.
elim (axs_comprehension (fun y0 : E => In (couple y y0) r) a v2); intros;
 apply H3; clear H2 H3; intros.
split; [ auto with zfc | idtac ].
unfold equivalence in rEqv.
elim rEqv; clear rEqv; intros; elim H3; clear H3; intros.
unfold symmetry in H3.
generalize (H3 x y H); clear H H3; intros.
unfold transitivity in H4.
exact (H4 y x v2 H H1).

elim (axs_comprehension (fun y0 : E => In (couple y y0) r) a v2); intros;
 generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros.
elim (axs_comprehension (fun y : E => In (couple x y) r) a v2); intros;
 apply H3; clear H2 H3; intros.
split; [ auto with zfc | idtac ].
elim rEqv; clear rEqv; intros; elim H3; clear H3; intros;
 unfold transitivity in H4.
exact (H4 x y v2 H H1).

Qed.
(* End of proof of lem_equivClass_eq                                       *)

(***************************************************************************)
(* Si x et y ne sont pas en relation, l'intersection de leurs classes      *)
(* d'equivalence respectives est vide.                                     *)
(***************************************************************************)
Lemma lem_inter_equivClass_empty :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (x y : E),
 ~ In (couple x y) r ->
 inter (equivClass r a rRel rEqv x) (equivClass r a rRel rEqv y) = Vide.
(* Proof of lem_inter_equivClass_empty                                     *)
intros.
apply lem_inter_is_empty; unfold not in |- *; intros.
unfold equivClass in H0; unfold equivClass in H1.
elim (axs_comprehension (fun y : E => In (couple x y) r) a x0); intros;
 generalize (H2 H0); clear H0 H2 H3; intros.
elim (axs_comprehension (fun y0 : E => In (couple y y0) r) a x0); intros;
 generalize (H2 H1); clear H1 H2 H3; intros.
elim H0; elim H1; clear H0 H1; intros; clear H2.
elim rEqv; clear rEqv; intros.
elim H4; clear H4; unfold symmetry in |- *; unfold transitivity in |- *;
 intros.
generalize (H4 y x0 H1); clear H1 H4; intros.
generalize (H5 x x0 y H3 H1); clear H1 H3 H5; intros.
absurd (In (couple x y) r); auto with zfc.

unfold equivClass in H0; unfold equivClass in H1.
elim (axs_comprehension (fun y1 : E => In (couple y y1) r) a y0); intros;
 generalize (H2 H0); clear H0 H2 H3; intros.
elim (axs_comprehension (fun y : E => In (couple x y) r) a y0); intros;
 generalize (H2 H1); clear H1 H2 H3; intros.
elim H0; elim H1; clear H0 H1; intros; clear H2.
elim rEqv; clear rEqv; unfold symmetry in |- *; unfold transitivity in |- *;
 intros; elim H4; clear H4; intros.
generalize (H4 y y0 H3); clear H3 H4; intros.
generalize (H5 x y0 y H1 H3); clear H1 H3 H5; intros.
absurd (In (couple x y) r); auto with zfc.

Qed.
(* End of proof of lem_inter_equivClass_empty                              *)

Lemma lem_equivClass_in_parties_a :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (x : E), In (equivClass r a rRel rEqv x) (parties a).
(* Proof of lem_equivClass_in_parties_a                                    *)
intros.
elim (axs_parties a (equivClass r a rRel rEqv x)); intros; apply H0;
 clear H H0; intros.
unfold equivClass in H.
elim (axs_comprehension (fun y : E => In (couple x y) r) a v3); intros;
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_equivClass_in_parties_a                             *)

(***************************************************************************)
(* Quotient d'un ensemble par une relation d'equivalence                   *)
(***************************************************************************)
Definition quotient (r a : E) (rRel : rel_sig r a a)
  (rEqv : equivalence r a rRel) (rD : rdom r a a rRel = a) :=
  subset
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a).


(***************************************************************************)
(* Toute application induit une relation d'equivalence sur son domaine     *)
(* equiv_fun sera le "noyau d'equivalence" de l'application                *)
(***************************************************************************)
Definition equiv_fun (f : E) (Af : fun_ f) :=
  subset
    (fun x : E =>
     exists a : E, (exists b : E, x = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)).

Lemma lem_fun_equiv_is_rel :
 forall (f : E) (Af : fun_ f), rel_sig (equiv_fun f Af) (dom f) (dom f).
(* Proof of lem_fun_equiv_is_rel                                           *)
unfold rel_sig in |- *; unfold inc in |- *; unfold equiv_fun in |- *; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists a : E, (exists b : E, x = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_equiv_is_rel                                    *)

Lemma lem_sig_fun_equiv_is_rel :
 forall (f a s : E) (Afs : fun_sig f a s),
 rel_sig (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a a.
(* Proof of lem_sig_fun_equiv_is_rel                                       *)
unfold rel_sig in |- *; unfold inc in |- *; unfold equiv_fun in |- *; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E,
       (exists b : E,
          x = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros;
 elim H0; clear H0; intros.
elim Afs; intros; elim H3; clear H3; intros.
generalize H; rewrite H3; tauto.

Qed.
(* End of proof of lem_sig_fun_equiv_is_rel                                *)

Lemma lem_fun_equiv_is_equiv :
 forall (f : E) (Af : fun_ f),
 equivalence (equiv_fun f Af) (dom f) (lem_fun_equiv_is_rel f Af).
(* Proof of lem_fun_equiv_is_equiv                                         *)
unfold equivalence in |- *; intros.
split;
 [ unfold reflexivity in |- *; intros
 | split;
    [ unfold symmetry in |- *; intros | unfold transitivity in |- *; intros ] ].
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x x)); intros; 
 apply H1; clear H0 H1; intros.
split; [ idtac | exists x; exists x; split; reflexivity ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x x)); intros; apply H1;
 clear H0 H1; intros.
exists x; exists x.
unfold rdom in H.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In (couple x0 y) (equiv_fun f Af)) 
    (dom f) x); intros; generalize (H0 H); clear H H0 H1; 
 intros.
elim H; clear H; intros.
split; [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold equiv_fun in H.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros;
 elim H0; clear H0; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H2 H0);
 clear H0 H2 H3; intros; elim H0; clear H0; intros.
generalize H; rewrite H0; rewrite H2; clear H H0 H2; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple x0 x1)); intros;
 generalize (H0 H); clear H H0 H2; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
elim (lem_couple_propertie x0 x2 x1 x3); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros.
generalize H H0; rewrite <- H2; rewrite <- H3; clear H H0 H2 H3; intros.
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists a : E, (exists b : E, x = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x1 x0)); intros; 
 apply H3; clear H2 H3; intros.
split;
 [ idtac
 | exists x1; exists x0; split;
    [ reflexivity | symmetry  in |- *; auto with zfc ] ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x1 x0)); intros;
 apply H3; clear H2 H3; intros.
exists x1; exists x0; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold equiv_fun in H.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 generalize (H1 H); clear H H1 H2; intros.
elim H; clear H; intros; elim H1; clear H1; intros; elim H1; clear H1; intros;
 elim H1; clear H1; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H3 H1);
 clear H1 H3 H4; intros.
elim H1; clear H1; intros.
generalize H2; rewrite <- H1; rewrite <- H3; clear H1 H2 H3; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple x y)); intros;
 generalize (H1 H); clear H H1 H3; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H1; clear H1; intros.
elim (lem_couple_propertie x x2 y x3); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
generalize H H1; rewrite <- H3; rewrite <- H4; clear H H1 H3 H4; intros.
unfold equiv_fun in H0.
elim
 (axs_comprehension
    (fun x : E =>
     exists a : E, (exists b : E, x = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple y z)); intros; 
 generalize (H3 H0); clear H0 H3 H4; intros.
elim H0; clear H0; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H3; clear H3; intros.
elim (lem_couple_propertie y x4 z x5); intros; generalize (H5 H3);
 clear H3 H5 H6; intros.
elim H3; clear H3; intros.
generalize H4; rewrite <- H3; rewrite <- H5; clear H3 H4 H5; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple y z)); intros;
 generalize (H3 H0); clear H0 H3 H5; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H3; clear H3; intros.
elim (lem_couple_propertie y x6 z x7); intros; generalize (H6 H5);
 clear H5 H6 H7; intros.
elim H5; clear H5; intros.
generalize H0 H3; rewrite <- H5; rewrite <- H6; clear H0 H3 H5 H6; intros.
clear H1; unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x z)); intros; 
 apply H5; clear H1 H5; intros.
split;
 [ idtac
 | exists x; exists z; split;
    [ reflexivity | rewrite <- H4; auto with zfc ] ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x z)); intros; apply H5;
 clear H1 H5; intros.
exists x; exists z; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_fun_equiv_is_equiv                                  *)

Lemma lem_sig_fun_equiv_is_equiv :
 forall (f a s : E) (Afs : fun_sig f a s),
 equivalence (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
   (lem_sig_fun_equiv_is_rel f a s Afs).
(* Proof of lem_sig_fun_equiv_is_equiv                                     *)
intros.
elim Afs; intros; elim H0; clear H0; intros.
generalize (lem_fun_equiv_is_equiv f H); intros.
unfold equivalence in |- *.
elim H2; unfold reflexivity, symmetry, transitivity in |- *; clear H2; intros;
 elim H3; clear H3; intros.
split; [ intros | split; intros ].
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple x x)); intros; 
 apply H7; clear H6 H7; intros.
split; [ idtac | exists x; exists x; split; reflexivity ].
unfold rdom in H5.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists y : E,
       In (couple x0 y) (equiv_fun f (lem_fun_sig_is_fun f a s Afs))) a x);
 intros; generalize (H6 H5); clear H5 H6 H7; intros.
elim H5; clear H5; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple x x)); intros; apply H8;
 clear H7 H8; intros.
exists x; exists x; rewrite H0; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold equiv_fun in H5.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 generalize (H6 H5); clear H5 H6 H7; intros.
elim H5; clear H5; intros; elim H6; clear H6; intros; elim H6; clear H6;
 intros; elim H6; clear H6; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H8 H6);
 clear H6 H8 H9; intros.
elim H6; clear H6; intros.
generalize H7; rewrite <- H6; rewrite <- H8; clear H6 H7 H8; intros.
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple y x)); intros; 
 apply H8; clear H6 H8; intros.
split;
 [ idtac
 | exists y; exists x; split;
    [ reflexivity | symmetry  in |- *; auto with zfc ] ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x y)); intros;
 generalize (H6 H5); clear H5 H6 H8; intros.
elim H5; clear H5; intros; elim H5; clear H5; intros; elim H5; clear H5;
 intros; elim H6; clear H6; intros.
elim (lem_couple_propertie x x2 y x3); intros; generalize (H9 H8);
 clear H8 H9 H10; intros; elim H8; clear H8; intros.
rewrite H8; rewrite H9;
 elim (lem_cartesian_propertie (dom f) (dom f) (couple x3 x2)); 
 intros; apply H11; clear H10 H11; intros.
exists x3; exists x2; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold equiv_fun in H5; unfold equiv_fun in H6.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 generalize (H7 H5); clear H5 H7 H8; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E,
       (exists b : E,
          x = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple y z)); intros; 
 generalize (H7 H6); clear H6 H7 H8; intros.
elim H5; clear H5; intros; elim H7; clear H7; intros; elim H7; clear H7;
 intros; elim H7; clear H7; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H9 H7);
 clear H7 H9 H10; intros; elim H7; clear H7; intros.
generalize H8; rewrite <- H7; rewrite <- H9; clear H7 H8 H9; intros.
elim H6; clear H6; intros; elim H7; clear H7; intros; elim H7; clear H7;
 intros; elim H7; clear H7; intros.
elim (lem_couple_propertie y x2 z x3); intros; generalize (H10 H7);
 clear H7 H10 H11; intros; elim H7; clear H7; intros.
generalize H9; rewrite <- H7; rewrite <- H10; clear H7 H9 H10; intros.
generalize H9; rewrite <- H8; clear H8 H9; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple x y)); intros;
 generalize (H7 H5); clear H5 H7 H8; intros.
elim H5; clear H5; intros; elim H5; clear H5; intros; elim H5; clear H5;
 intros; elim H7; clear H7; intros.
elim (lem_couple_propertie x x4 y x5); intros; generalize (H10 H8);
 clear H8 H10 H11; intros; elim H8; clear H8; intros.
generalize H5; rewrite <- H8; clear H5 H7 H8 H10; intros.
elim (lem_cartesian_propertie (dom f) (dom f) (couple y z)); intros;
 generalize (H7 H6); clear H6 H7 H8; intros.
elim H6; clear H6; intros; elim H6; clear H6; intros; elim H6; clear H6;
 intros; elim H7; clear H7; intros.
elim (lem_couple_propertie y x6 z x7); intros; generalize (H10 H8);
 clear H8 H10 H11; intros; elim H8; clear H8; intros.
generalize H7; rewrite <- H10; clear H6 H7 H8 H10; intros.
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple x z)); intros; 
 apply H8; clear H6 H8; intros.
split;
 [ idtac | exists x; exists z; split; [ reflexivity | auto with zfc ] ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x z)); intros; apply H8;
 clear H6 H8; intros.
exists x; exists z; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_sig_fun_equiv_is_equiv                              *)

Lemma lem_fun_equiv_dom :
 forall (f : E) (Af : fun_ f),
 rdom (equiv_fun f Af) (dom f) (dom f) (lem_fun_equiv_is_rel f Af) = dom f.
(* Proof of lem_fun_equiv_dom                                              *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold rdom in H.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In (couple x y) (equiv_fun f Af)) 
    (dom f) v2); intros; generalize (H0 H); clear H H0 H1; 
 intros.
elim H; clear H; intros; auto with zfc.

unfold rdom in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In (couple x y) (equiv_fun f Af)) 
    (dom f) v2); intros; apply H1; clear H0 H1; intros.
split; [ auto with zfc | exists v2; unfold equiv_fun in |- * ].
elim
 (axs_comprehension
    (fun x : E =>
     exists a : E, (exists b : E, x = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple v2 v2)); intros; 
 apply H1; clear H0 H1; intros.
split; [ idtac | exists v2; exists v2; split; reflexivity ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple v2 v2)); intros;
 apply H1; clear H0 H1; intros.
exists v2; exists v2; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_fun_equiv_dom                                       *)

Lemma lem_sig_fun_equiv_dom :
 forall (f a s : E) (Afs : fun_sig f a s),
 rdom (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a a
   (lem_sig_fun_equiv_is_rel f a s Afs) = a.
(* Proof of lem_sig_fun_equiv_dom                                          *)
intros; unfold rdom in |- *; apply axs_extensionnalite; unfold iff in |- *;
 split; intros.
elim
 (axs_comprehension
    (fun x : E =>
     exists y : E,
       In (couple x y) (equiv_fun f (lem_fun_sig_is_fun f a s Afs))) a v2);
 intros; generalize (H0 H); clear H H0 H1; intros; 
 elim H; clear H; intros; auto with zfc.

elim
 (axs_comprehension
    (fun x : E =>
     exists y : E,
       In (couple x y) (equiv_fun f (lem_fun_sig_is_fun f a s Afs))) a v2);
 intros; apply H1; clear H0 H1; intros.
split; [ auto with zfc | idtac ].
exists v2; unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E,
       (exists b : E,
          x = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple v2 v2)); intros; 
 apply H1; clear H0 H1; intros.
split; [ idtac | exists v2; exists v2; split; reflexivity ].
elim Afs; intros; elim H1; clear H1; intros; rewrite H1.
elim (lem_cartesian_propertie a a (couple v2 v2)); intros; apply H4;
 clear H3 H4; intros.
exists v2; exists v2; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_sig_fun_equiv_dom                                   *)

Lemma lem_fun_equiv_prop :
 forall (f : E) (Af : fun_ f) (x y : E),
 In (couple x y) (equiv_fun f Af) -> App f Af x = App f Af y.
(* Proof of lem_fun_equiv_prop                                             *)
unfold equiv_fun in |- *; intros.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros;
 elim H0; clear H0; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros.
rewrite H0; rewrite H2; auto with zfc.

Qed.
(* End of proof of lem_fun_equiv_prop                                      *)

Lemma lem_equiv_fun_make :
 forall (f : E) (Af : fun_ f) (x y : E),
 In x (dom f) ->
 In y (dom f) -> App f Af x = App f Af y -> In (couple x y) (equiv_fun f Af).
(* Proof of lem_equiv_fun_make                                             *)
intros; unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a : E, (exists b : E, x0 = couple a b /\ App f Af a = App f Af b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 apply H3; clear H2 H3; intros.
split;
 [ idtac | exists x; exists y; split; [ reflexivity | auto with zfc ] ].
elim (lem_cartesian_propertie (dom f) (dom f) (couple x y)); intros; apply H3;
 clear H2 H3; intros.
exists x; exists y; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_equiv_fun_make                                      *)

Lemma lem_sig_equiv_fun_make :
 forall (f a s : E) (Afs : fun_sig f a s) (x y : E),
 In x a ->
 In y a ->
 App f (lem_fun_sig_is_fun f a s Afs) x =
 App f (lem_fun_sig_is_fun f a s Afs) y ->
 In (couple x y) (equiv_fun f (lem_fun_sig_is_fun f a s Afs)).
(* Proof of lem_sig_equiv_fun_make                                         *)
intros.
elim Afs; intros; elim H3; clear H3; intros.
unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists a0 : E,
       (exists b : E,
          x0 = couple a0 b /\
          App f (lem_fun_sig_is_fun f a s Afs) a0 =
          App f (lem_fun_sig_is_fun f a s Afs) b))
    (cartesien (dom f) (dom f)) (couple x y)); intros; 
 apply H6; clear H5 H6; intros.
split;
 [ idtac | exists x; exists y; split; [ reflexivity | auto with zfc ] ].
rewrite H3.
elim (lem_cartesian_propertie a a (couple x y)); intros; apply H6;
 clear H5 H6; intros.
exists x; exists y; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_sig_equiv_fun_make                                  *)

(***************************************************************************)
(* Projection sur le quotient                                              *)
(***************************************************************************)
Definition projQuotient (r a : E) (rRel : rel_sig r a a)
  (rEqv : equivalence r a rRel) (rD : rdom r a a rRel = a) :=
  subset
    (fun x : E =>
     exists z : E,
       (exists t : E, x = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)).

(***************************************************************************)
(* projQuotient est une application                                        *)
(***************************************************************************)
Lemma lem_projQuotient_is_fun :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a), fun_ (projQuotient r a rRel rEqv rD).
(* Proof of lem_projQuotient_is_fun                                        *)
unfold fun_ in |- *; intros.
split; intros.
exists a; exists (quotient r a rRel rEqv rD); unfold inc in |- *; intros.
unfold projQuotient in H.
elim
 (axs_comprehension
    (fun x : E =>
     exists z : E,
       (exists t : E, x = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) v0); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; clear H0; auto with zfc.

unfold projQuotient in H.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x y)); 
 intros; generalize (H1 H); clear H H1 H2; intros.
unfold projQuotient in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z0 : E,
       (exists t : E, x0 = couple z0 t /\ t = equivClass r a rRel rEqv z0))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x z)); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H; clear H; intros; elim H1; clear H1; intros; elim H1; clear H1; intros;
 elim H1; clear H1; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H3 H1);
 clear H1 H3 H4; intros.
elim H1; clear H1; intros.
generalize H2; rewrite <- H1; rewrite <- H3; clear H1 H2 H3; intros.
rewrite H2; clear H H2.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H0; clear H0; intros.
elim (lem_couple_propertie x x2 z x3); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros.
generalize H1; rewrite <- H0; rewrite <- H2; clear H0 H1 H2; intros.
rewrite H1; reflexivity.

Qed.
(* End of proof of lem_projQuotient_is_fun                                 *)

(***************************************************************************)
(* Le domaine de projQuotient est a                                        *)
(***************************************************************************)
Lemma lem_projQuotient_dom :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a), dom (projQuotient r a rRel rEqv rD) = a.
(* Proof of lem_projQuotient_dom                                           *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (projQuotient r a rRel rEqv rD) ->
     exists v1 : E, In (couple v0 v1) (projQuotient r a rRel rEqv rD))
    (reunion (reunion (projQuotient r a rRel rEqv rD))) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_projQuotient_is_fun r a rRel rEqv rD)); clear H0; intros.
elim H0; clear H0; intros.
unfold projQuotient in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple v2 x)); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros.
clear H1;
 elim (lem_cartesian_propertie a (quotient r a rRel rEqv rD) (couple v2 x));
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H3 H2);
 clear H2 H3 H4; intros; elim H2; clear H2; intros.
rewrite H2; auto with zfc.

unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (projQuotient r a rRel rEqv rD) ->
     exists v1 : E, In (couple v0 v1) (projQuotient r a rRel rEqv rD))
    (reunion (reunion (projQuotient r a rRel rEqv rD))) v2); 
 intros; apply H1; clear H0 H1; intros.
split; intros.
elim (axs_reunion (reunion (projQuotient r a rRel rEqv rD)) v2); intros;
 apply H1; clear H0 H1; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion (projQuotient r a rRel rEqv rD) (singleton v2)); intros;
 apply H1; clear H0 H1; intros.
exists (couple v2 (equivClass r a rRel rEqv v2)); split;
 [ idtac
 | elim
    (axs_paire (singleton v2) (paire v2 (equivClass r a rRel rEqv v2))
       (singleton v2)); intros; apply H1; left; reflexivity ].
unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists z : E,
       (exists t : E, x = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD))
    (couple v2 (equivClass r a rRel rEqv v2))); intros; 
 apply H1; clear H0 H1; intros.
split;
 [ idtac
 | exists v2; exists (equivClass r a rRel rEqv v2); split; reflexivity ].
elim
 (lem_cartesian_propertie a (quotient r a rRel rEqv rD)
    (couple v2 (equivClass r a rRel rEqv v2))); intros; 
 apply H1; clear H0 H1; intros.
exists v2; exists (equivClass r a rRel rEqv v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) (equivClass r a rRel rEqv v2)); intros; 
 apply H1; clear H0 H1; intros.
split;
 [ exact (lem_equivClass_in_parties_a r a rRel rEqv v2)
 | exists v2; split; [ auto with zfc | reflexivity ] ].

exists (equivClass r a rRel rEqv v2); unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists z : E,
       (exists t : E, x = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD))
    (couple v2 (equivClass r a rRel rEqv v2))); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ idtac
 | exists v2; exists (equivClass r a rRel rEqv v2); split; reflexivity ].
elim
 (lem_cartesian_propertie a (quotient r a rRel rEqv rD)
    (couple v2 (equivClass r a rRel rEqv v2))); intros; 
 apply H2; clear H1 H2; intros.
exists v2; exists (equivClass r a rRel rEqv v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) (equivClass r a rRel rEqv v2)); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ exact (lem_equivClass_in_parties_a r a rRel rEqv v2)
 | exists v2; split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_projQuotient_dom                                    *)

(***************************************************************************)
(* L'image de projQuotient est l'ensemble quotient                         *)
(***************************************************************************)
Lemma lem_projQuotient_img :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a),
 Img (projQuotient r a rRel rEqv rD) = quotient r a rRel rEqv rD.
(* Proof of lem_projQuotient_img                                           *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (projQuotient r a rRel rEqv rD) ->
     exists v0 : E, In (couple v0 v1) (projQuotient r a rRel rEqv rD))
    (reunion (reunion (projQuotient r a rRel rEqv rD))) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_projQuotient_is_fun r a rRel rEqv rD)); clear H0; intros;
 elim H0; clear H0; intros.
unfold projQuotient in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x v2)); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; clear H1.
elim (lem_cartesian_propertie a (quotient r a rRel rEqv rD) (couple x v2));
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H3 H2);
 clear H2 H3 H4; intros.
elim H2; clear H2; intros; generalize H1; rewrite H3; tauto.

generalize H; unfold quotient in |- *; intros.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
unfold Img in |- *.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (projQuotient r a rRel rEqv rD) ->
     exists v0 : E, In (couple v0 v1) (projQuotient r a rRel rEqv rD))
    (reunion (reunion (projQuotient r a rRel rEqv rD))) v2); 
 intros; apply H4; clear H3 H4; intros.
split; intros.
elim (axs_reunion (reunion (projQuotient r a rRel rEqv rD)) v2); intros;
 apply H4; clear H3 H4; intros.
exists (paire x v2); split;
 [ idtac | elim (axs_paire x v2 v2); intros; apply H4; right; reflexivity ].
elim (axs_reunion (projQuotient r a rRel rEqv rD) (paire x v2)); intros;
 apply H4; clear H3 H4; intros.
exists (couple x v2); split;
 [ idtac
 | elim (axs_paire (singleton x) (paire x v2) (paire x v2)); intros; apply H4;
    right; reflexivity ].
unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x v2)); 
 intros; apply H4; clear H3 H4; intros.
split;
 [ idtac | exists x; exists v2; split; [ reflexivity | auto with zfc ] ].
elim (lem_cartesian_propertie a (quotient r a rRel rEqv rD) (couple x v2));
 intros; apply H4; clear H3 H4; intros.
exists x; exists v2; split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; apply H4; clear H3 H4; 
 intros.
split; [ auto with zfc | exists x; split; auto with zfc ].

exists x.
unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x v2)); 
 intros; apply H5; clear H4 H5; intros.
split;
 [ idtac | exists x; exists v2; split; [ reflexivity | auto with zfc ] ].
elim (lem_cartesian_propertie a (quotient r a rRel rEqv rD) (couple x v2));
 intros; apply H5; clear H4 H5; intros.
exists x; exists v2; split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; apply H5; clear H4 H5; 
 intros.
split; [ auto with zfc | exists x; split; auto with zfc ].

Qed.
(* End of proof of lem_projQuotient_img                                    *)

(***************************************************************************)
(* La projection sur l'ensemble quotient est une surjection                *)
(***************************************************************************)
Lemma lem_projQuotient_is_surj :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a),
 fun_surj (projQuotient r a rRel rEqv rD) a (quotient r a rRel rEqv rD).
(* Proof of lem_projQuotient_is_surj                                       *)
intros; unfold fun_surj in |- *.
split;
 [ exact (lem_projQuotient_is_fun r a rRel rEqv rD)
 | split;
    [ exact (lem_projQuotient_dom r a rRel rEqv rD)
    | exact (lem_projQuotient_img r a rRel rEqv rD) ] ].

Qed.
(* End of proof of lem_projQuotient_is_surj                                *)

(***************************************************************************)
(* Le resultat de l'evaluation de x par projQuotient est la classe         *)
(* d'equivalence de x.                                                     *)
(***************************************************************************)
Lemma lem_projQuotient_eval :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (x : E),
 In x a ->
 App (projQuotient r a rRel rEqv rD)
   (lem_projQuotient_is_fun r a rRel rEqv rD) x = equivClass r a rRel rEqv x.
(* Proof of lem_projQuotient_eval                                          *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold App in H0.
elim
 (axs_comprehension
    (fun z : E =>
     exists y : E, In (couple x y) (projQuotient r a rRel rEqv rD) /\ In z y)
    (reunion (Img (projQuotient r a rRel rEqv rD))) v2); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
generalize H0; clear H0; rewrite (lem_projQuotient_img r a rRel rEqv rD);
 intros.
unfold projQuotient in H1.
elim
 (axs_comprehension
    (fun x1 : E =>
     exists z : E,
       (exists t : E, x1 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple x x0)); 
 intros; generalize (H3 H1); clear H1 H3 H4; intros.
elim H1; clear H1; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H3; clear H3; intros.
elim (lem_couple_propertie x x1 x0 x2); intros; generalize (H5 H3);
 clear H3 H5 H6; intros; elim H3; clear H3; intros.
generalize H2; rewrite H5; rewrite H4; rewrite <- H3; tauto.

unfold App in |- *.
rewrite (lem_projQuotient_img r a rRel rEqv rD).
elim
 (axs_comprehension
    (fun z : E =>
     exists y : E, In (couple x y) (projQuotient r a rRel rEqv rD) /\ In z y)
    (reunion (quotient r a rRel rEqv rD)) v2); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ idtac
 | exists (equivClass r a rRel rEqv x); split; [ idtac | auto with zfc ] ].
elim (axs_reunion (quotient r a rRel rEqv rD) v2); intros; apply H2;
 clear H1 H2; intros.
exists (equivClass r a rRel rEqv x); split;
 [ unfold quotient in |- * | auto with zfc ].
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In y a /\ x0 = equivClass r a rRel rEqv y)
    (parties a) (equivClass r a rRel rEqv x)); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ exact (lem_equivClass_in_parties_a r a rRel rEqv x)
 | exists x; split; [ auto with zfc | reflexivity ] ].

unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD))
    (couple x (equivClass r a rRel rEqv x))); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ idtac
 | exists x; exists (equivClass r a rRel rEqv x); split;
    [ reflexivity | auto with zfc ] ].
elim
 (lem_cartesian_propertie a (quotient r a rRel rEqv rD)
    (couple x (equivClass r a rRel rEqv x))); intros; 
 apply H2; clear H1 H2; intros.
exists x; exists (equivClass r a rRel rEqv x); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In y a /\ x0 = equivClass r a rRel rEqv y)
    (parties a) (equivClass r a rRel rEqv x)); intros; 
 apply H2; clear H1 H2; intros.
split;
 [ exact (lem_equivClass_in_parties_a r a rRel rEqv x)
 | exists x; split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_projQuotient_eval                                   *)

(***************************************************************************)
(* Le couple compose d'un element et de sa classe d'equivalence funartient *)
(* au graphe de projQuotient                                               *)
(***************************************************************************)
Lemma lem_x_equiv_in_projQ :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (x : E),
 In x a ->
 In (couple x (equivClass r a rRel rEqv x)) (projQuotient r a rRel rEqv rD).
(* Proof of lem_x_equiv_in_projQ                                           *)
intros.
unfold projQuotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD))
    (couple x (equivClass r a rRel rEqv x))); intros; 
 apply H1; clear H0 H1; intros.
split;
 [ idtac
 | exists x; exists (equivClass r a rRel rEqv x); split; reflexivity ].
elim
 (lem_cartesian_propertie a (quotient r a rRel rEqv rD)
    (couple x (equivClass r a rRel rEqv x))); intros; 
 apply H1; clear H0 H1; intros.
exists x; exists (equivClass r a rRel rEqv x); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In y a /\ x0 = equivClass r a rRel rEqv y)
    (parties a) (equivClass r a rRel rEqv x)); intros; 
 apply H1; clear H0 H1; intros.
split;
 [ exact (lem_equivClass_in_parties_a r a rRel rEqv x)
 | exists x; split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_x_equiv_in_projQ                                    *)

(***************************************************************************)
(* Encore un lemme a la XXX: x est membre de sa classe d'equivalence       *)
(***************************************************************************)
Lemma lem_x_in_equivClass_x :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (x : E),
 In x a -> In x (equivClass r a rRel rEqv x).
(* Proof of lem_x_in_equivClass_x                                          *)
intros; unfold equivClass in |- *.
elim (axs_comprehension (fun y : E => In (couple x y) r) a x); intros;
 apply H1; clear H0 H1; split; [ auto with zfc | idtac ].
elim rEqv; clear rEqv; intros.
unfold reflexivity in H0.
generalize H; rewrite <- rD; clear H; intros.
exact (H0 x H).

Qed.
(* End of proof of lem_x_in_equivClass_x                                   *)

(***************************************************************************)
(* Le noyau d'equivalence de projQuotient est r                            *)
(***************************************************************************)
Lemma lem_projQuotient_equiv_fun :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a),
 equiv_fun (projQuotient r a rRel rEqv rD)
   (lem_projQuotient_is_fun r a rRel rEqv rD) = r.
(* Proof of lem_projQuotient_equiv_fun                                     *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold equiv_fun in H.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E,
       (exists b : E,
          x = couple a0 b /\
          App (projQuotient r a rRel rEqv rD)
            (lem_projQuotient_is_fun r a rRel rEqv rD) a0 =
          App (projQuotient r a rRel rEqv rD)
            (lem_projQuotient_is_fun r a rRel rEqv rD) b))
    (cartesien (dom (projQuotient r a rRel rEqv rD))
       (dom (projQuotient r a rRel rEqv rD))) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; rewrite (lem_projQuotient_dom r a rRel rEqv rD); intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros.
generalize H; rewrite H0; clear H H0; intros.
elim (lem_cartesian_propertie a a (couple x x0)); intros; generalize (H0 H);
 clear H H0 H2; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
elim (lem_couple_propertie x x1 x0 x2); intros; generalize (H3 H2);
 clear H2 H3 H4; intros.
elim H2; clear H2; intros.
generalize H H0; rewrite <- H2; rewrite <- H3; clear H H0 H2 H3; intros.
generalize H1; rewrite (lem_projQuotient_eval r a rRel rEqv rD x H);
 rewrite (lem_projQuotient_eval r a rRel rEqv rD x0 H0); 
 clear H1; intros.
generalize (lem_x_in_equivClass_x r a rRel rEqv rD x0 H0); intros.
generalize H2; rewrite <- H1; clear H1 H2; intros.
unfold equivClass in H2.
elim (axs_comprehension (fun y : E => In (couple x y) r) a x0); intros;
 generalize (H1 H2); clear H1 H2 H3; intros.
elim H1; clear H1; intros; auto with zfc.

unfold equiv_fun in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     exists a0 : E,
       (exists b : E,
          x = couple a0 b /\
          App (projQuotient r a rRel rEqv rD)
            (lem_projQuotient_is_fun r a rRel rEqv rD) a0 =
          App (projQuotient r a rRel rEqv rD)
            (lem_projQuotient_is_fun r a rRel rEqv rD) b))
    (cartesien (dom (projQuotient r a rRel rEqv rD))
       (dom (projQuotient r a rRel rEqv rD))) v2); 
 intros; apply H1; clear H0 H1; intros.
elim rEqv; intros.
elim H1; clear H1; intros.
split.
rewrite (lem_projQuotient_dom r a rRel rEqv rD).
unfold rel_sig in rRel; unfold inc in rRel.
exact (rRel v2 H).

generalize rRel; intros.
unfold rel_sig in rRel0; unfold inc in rRel0.
generalize (rRel v2 H); intros.
elim (lem_cartesian_propertie a a v2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H4; clear H4; intros.
exists x; exists x0; split; [ auto with zfc | idtac ].
rewrite (lem_projQuotient_eval r a rRel0 rEqv rD x H3).
rewrite (lem_projQuotient_eval r a rRel0 rEqv rD x0 H4).
generalize H; rewrite H5; intros.
exact (lem_equivClass_eq r a rRel rEqv x x0 H6).

Qed.
(* End of proof of lem_projQuotient_equiv_fun                              *)

(***************************************************************************)
(* D'ou la signature de projQuotient                                       *)
(***************************************************************************)
Lemma lem_projQuotient_sig :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a),
 fun_sig (projQuotient r a rRel rEqv rD) a (quotient r a rRel rEqv rD).
(* Proof of lem_projQuotient_sig                                           *)
intros; unfold fun_sig in |- *.
split;
 [ exact (lem_projQuotient_is_fun r a rRel rEqv rD)
 | split;
    [ exact (lem_projQuotient_dom r a rRel rEqv rD)
    | unfold inc in |- *; intros ] ].
generalize H; rewrite (lem_projQuotient_img r a rRel rEqv rD); tauto.

Qed.
(* End of proof of lem_projQuotient_sig                                    *)

(***************************************************************************)
(***************************************************************************)
(* Theoreme 6 page 25 Algebre Tome 1 (Mac LANE & BIRKHOFF)                 *)
(* Propriete fondamentale de l'ensemble quotient                           *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Si x et y ont meme classe d'equivalence, alors ils sont en relation     *)
(***************************************************************************)
Lemma lem_equivClass_is_same :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (x y : E),
 In x a ->
 In y a ->
 equivClass r a rRel rEqv x = equivClass r a rRel rEqv y -> In (couple x y) r.
(* Proof of lem_equivClass_is_same                                         *)
intros.
generalize (lem_x_in_equivClass_x r a rRel rEqv rD x H)
 (lem_x_in_equivClass_x r a rRel rEqv rD y H0); intros.
generalize H3; clear H3; rewrite <- H1; intros.
unfold equivClass in H3.
elim (axs_comprehension (fun y0 : E => In (couple x y0) r) a y); intros;
 generalize (H4 H3); clear H3 H4 H5; intros.
elim H3; clear H3; intros; auto with zfc.

Qed.
(* End of proof of lem_equivClass_is_same                                  *)

Definition equiv_comp (r a : E) (rRel : rel_sig r a a)
  (rEqv : equivalence r a rRel) (rD : rdom r a a rRel = a) 
  (s f : E) (Afs : fun_sig f a s)
  (Pr : forall x y : E,
        In (couple x y) r ->
        App f (lem_fun_sig_is_fun f a s Afs) x =
        App f (lem_fun_sig_is_fun f a s Afs) y) :=
  subset
    (fun z : E =>
     exists x : E,
       In x a /\
       z =
       couple (equivClass r a rRel rEqv x)
         (App f (lem_fun_sig_is_fun f a s Afs) x))
    (cartesien (quotient r a rRel rEqv rD) s).

(***************************************************************************)
(* equiv_comp est une application                                          *)
(***************************************************************************)
Lemma lem_equiv_comp_is_fun :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 fun_ (equiv_comp r a rRel rEqv rD s f Afs Pr).
(* Proof of lem_equiv_comp_is_fun                                          *)
intros; unfold fun_ in |- *; intros.
split; intros.
exists (quotient r a rRel rEqv rD); exists s; unfold inc in |- *; intros.
unfold equiv_comp in H.
elim
 (axs_comprehension
    (fun z : E =>
     exists x : E,
       In x a /\
       z =
       couple (equivClass r a rRel rEqv x)
         (App f (lem_fun_sig_is_fun f a s Afs) x))
    (cartesien (quotient r a rRel rEqv rD) s) v0); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

unfold equiv_comp in H.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s) (couple x y)); 
 intros; generalize (H1 H); clear H H1 H2; intros.
elim H; clear H; intros; elim H1; clear H1; intros; elim H1; clear H1; intros.
elim
 (lem_couple_propertie x (equivClass r a rRel rEqv x0) y
    (App f (lem_fun_sig_is_fun f a s Afs) x0)); intros; 
 generalize (H3 H2); clear H2 H3 H4; intros.
elim H2; clear H2; intros.
unfold equiv_comp in H0.
elim
 (axs_comprehension
    (fun z0 : E =>
     exists x0 : E,
       In x0 a /\
       z0 =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s) (couple x z)); 
 intros; generalize (H4 H0); clear H0 H4 H5; intros.
elim H0; clear H0; intros; elim H4; clear H4; intros; elim H4; clear H4;
 intros.
elim
 (lem_couple_propertie x (equivClass r a rRel rEqv x1) z
    (App f (lem_fun_sig_is_fun f a s Afs) x1)); intros; 
 generalize (H6 H5); clear H5 H6 H7; intros; elim H5; 
 clear H5; intros.
generalize H5; clear H5; rewrite H2; intros.
generalize (lem_equivClass_is_same r a rRel rEqv rD x0 x1 H1 H4 H5); intros.
generalize (Pr x0 x1 H7); intros.
rewrite H3; rewrite H6; rewrite H8; reflexivity.

Qed.
(* End of proof of lem_equiv_comp_is_fun                                   *)

(***************************************************************************)
(* Le domaine de equiv_comp est l'ensemble quotient                        *)
(***************************************************************************)
Lemma lem_equiv_comp_dom :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 dom (equiv_comp r a rRel rEqv rD s f Afs Pr) = quotient r a rRel rEqv rD.
(* Proof of lem_equiv_comp_dom                                             *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (equiv_comp r a rRel rEqv rD s f Afs Pr) ->
     exists v1 : E,
       In (couple v0 v1) (equiv_comp r a rRel rEqv rD s f Afs Pr))
    (reunion (reunion (equiv_comp r a rRel rEqv rD s f Afs Pr))) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
elim (H0 (lem_equiv_comp_is_fun r a rRel rEqv rD s f Afs Pr)); clear H0;
 intros.
unfold equiv_comp in H0.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s) (couple v2 x)); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; clear H1.
elim (lem_cartesian_propertie (quotient r a rRel rEqv rD) s (couple v2 x));
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H1; clear H1; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H3 H2);
 clear H2 H3 H4; intros.
elim H2; clear H2; intros.
generalize H0; rewrite <- H2; tauto.

unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (equiv_comp r a rRel rEqv rD s f Afs Pr) ->
     exists v1 : E,
       In (couple v0 v1) (equiv_comp r a rRel rEqv rD s f Afs Pr))
    (reunion (reunion (equiv_comp r a rRel rEqv rD s f Afs Pr))) v2); 
 intros; apply H1; clear H0 H1; intros.
generalize H; unfold quotient in |- *; intros.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
split; intros.
elim (axs_reunion (reunion (equiv_comp r a rRel rEqv rD s f Afs Pr)) v2);
 intros; apply H4; clear H3 H4; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion (equiv_comp r a rRel rEqv rD s f Afs Pr) (singleton v2));
 intros; apply H4; clear H3 H4; intros.
exists (couple v2 (App f (lem_fun_sig_is_fun f a s Afs) x)); split;
 [ idtac
 | elim
    (axs_paire (singleton v2)
       (paire v2 (App f (lem_fun_sig_is_fun f a s Afs) x)) 
       (singleton v2)); intros; apply H4; left; reflexivity ].
unfold equiv_comp in |- *.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s)
    (couple v2 (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H4; clear H3 H4; intros.
split;
 [ idtac | exists x; split; [ auto with zfc | rewrite H2; reflexivity ] ].
elim
 (lem_cartesian_propertie (quotient r a rRel rEqv rD) s
    (couple v2 (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H4; clear H3 H4; intros.
exists v2; exists (App f (lem_fun_sig_is_fun f a s Afs) x); split;
 [ unfold quotient in |- * | split; [ idtac | reflexivity ] ].
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; apply H4; clear H3 H4; 
 intros.
split;
 [ rewrite H2; exact (lem_equivClass_in_parties_a r a rRel rEqv x)
 | exists x; split; auto with zfc ].

elim Afs; intros.
elim H4; clear H4; intros.
cut (In x (dom f)); intros; [ idtac | rewrite H4; auto with zfc ].
generalize (lem_eval_prop2 f x (lem_fun_sig_is_fun f a s Afs) H6); clear H6;
 intros.
generalize
 (lem_fun_and_img f x (App f (lem_fun_sig_is_fun f a s Afs) x)
    (lem_fun_sig_is_fun f a s Afs) H6); clear H6; intros.
unfold inc in H5.
exact (H5 (App f (lem_fun_sig_is_fun f a s Afs) x) H6).

exists (App f (lem_fun_sig_is_fun f a s Afs) x); unfold equiv_comp in |- *.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s)
    (couple v2 (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H5; clear H4 H5; intros.
split;
 [ idtac
 | exists x; split; [ auto with zfc | rewrite H2; auto with zfc ] ].
elim
 (lem_cartesian_propertie (quotient r a rRel rEqv rD) s
    (couple v2 (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H5; clear H4 H5; intros.
exists v2; exists (App f (lem_fun_sig_is_fun f a s Afs) x); split;
 [ idtac | split; [ idtac | reflexivity ] ].
unfold quotient in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, In y a /\ x = equivClass r a rRel rEqv y)
    (parties a) v2); intros; apply H5; clear H4 H5; 
 intros.
split;
 [ rewrite H2; exact (lem_equivClass_in_parties_a r a rRel rEqv x)
 | exists x; split; auto with zfc ].

elim Afs; intros.
elim H5; clear H5; intros.
cut (In x (dom f)); intros; [ idtac | rewrite H5; auto with zfc ].
generalize (lem_eval_prop2 f x (lem_fun_sig_is_fun f a s Afs) H7); intros.
generalize
 (lem_fun_and_img f x (App f (lem_fun_sig_is_fun f a s Afs) x)
    (lem_fun_sig_is_fun f a s Afs) H8); clear H8; intros.
exact (H6 (App f (lem_fun_sig_is_fun f a s Afs) x) H8).

Qed.
(* End of proof of lem_equiv_comp_dom                                      *)

(***************************************************************************)
(* L'image de equiv_comp est une partie de s                               *)
(***************************************************************************)
Lemma lem_equiv_comp_img :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 inc (Img (equiv_comp r a rRel rEqv rD s f Afs Pr)) s.
(* Proof of lem_equiv_comp_img                                             *)
unfold inc in |- *; intros.
elim Afs; intros; elim H1; clear H1; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (equiv_comp r a rRel rEqv rD s f Afs Pr) ->
     exists v2 : E,
       In (couple v2 v1) (equiv_comp r a rRel rEqv rD s f Afs Pr))
    (reunion (reunion (equiv_comp r a rRel rEqv rD s f Afs Pr))) v0); 
 intros; generalize (H3 H); clear H H3 H4; intros.
elim H; clear H; intros.
elim (H3 (lem_equiv_comp_is_fun r a rRel rEqv rD s f Afs Pr)); clear H3;
 intros.
unfold equiv_comp in H3.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s) (couple x v0)); 
 intros; generalize (H4 H3); clear H3 H4 H5; intros.
elim H3; clear H3; intros; clear H4.
elim (lem_cartesian_propertie (quotient r a rRel rEqv rD) s (couple x v0));
 intros; generalize (H4 H3); clear H3 H4 H5; intros.
elim H3; clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie x x0 v0 x1); intros; generalize (H6 H5);
 clear H5 H6 H7; intros; elim H5; clear H5; intros.
generalize H4; rewrite H6; tauto.

Qed.
(* End of proof of lem_equiv_comp_img                                      *)

(***************************************************************************)
(* D'ou la signature de equiv_comp ...                                     *)
(***************************************************************************)
Lemma lem_equiv_comp_sig :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 fun_sig (equiv_comp r a rRel rEqv rD s f Afs Pr) (quotient r a rRel rEqv rD)
   s.
(* Proof of lem_equiv_comp_sig                                             *)
intros; unfold fun_sig in |- *.
split;
 [ exact (lem_equiv_comp_is_fun r a rRel rEqv rD s f Afs Pr)
 | split;
    [ exact (lem_equiv_comp_dom r a rRel rEqv rD s f Afs Pr)
    | exact (lem_equiv_comp_img r a rRel rEqv rD s f Afs Pr) ] ].

Qed.
(* End of proof of lem_equiv_comp_sig                                      *)

(***************************************************************************)
(* Si x est dans a, le couple classe d'equivalence de x et (f x) est un    *)
(* element de equiv_comp.                                                  *)
(***************************************************************************)
Lemma lem_equiv_comp_elem :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y) (x : E),
 In x a ->
 In
   (couple (equivClass r a rRel rEqv x)
      (App f (lem_fun_sig_is_fun f a s Afs) x))
   (equiv_comp r a rRel rEqv rD s f Afs Pr).
(* Proof of lem_equiv_comp_elem                                            *)
intros.
generalize (lem_x_equiv_in_projQ r a rRel rEqv rD x H); intros.
generalize
 (lem_fun_and_img (projQuotient r a rRel rEqv rD) x
    (equivClass r a rRel rEqv x) (lem_projQuotient_is_fun r a rRel rEqv rD)
    H0); rewrite (lem_projQuotient_img r a rRel rEqv rD); 
 intros.
unfold equiv_comp in |- *.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s)
    (couple (equivClass r a rRel rEqv x)
       (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H3; clear H2 H3; intros.
split; [ idtac | exists x; split; [ auto with zfc | reflexivity ] ].
elim
 (lem_cartesian_propertie (quotient r a rRel rEqv rD) s
    (couple (equivClass r a rRel rEqv x)
       (App f (lem_fun_sig_is_fun f a s Afs) x))); 
 intros; apply H3; clear H2 H3; intros.
exists (equivClass r a rRel rEqv x);
 exists (App f (lem_fun_sig_is_fun f a s Afs) x); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
elim Afs; intros; elim H3; clear H3; intros.
cut (In x (dom f)); intros; [ idtac | rewrite H3; auto with zfc ].
generalize (lem_eval_prop2 f x (lem_fun_sig_is_fun f a s Afs) H5); intros.
generalize
 (lem_fun_and_img f x (App f (lem_fun_sig_is_fun f a s Afs) x)
    (lem_fun_sig_is_fun f a s Afs) H6); intros.
exact (H4 (App f (lem_fun_sig_is_fun f a s Afs) x) H7).

Qed.
(* End of proof of lem_equiv_comp_elem                                     *)

(***************************************************************************)
(* f = equiv_comp o projQuotient                                           *)
(***************************************************************************)
Lemma lem_equiv_comp_prop :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 f =
 comp (projQuotient r a rRel rEqv rD)
   (equiv_comp r a rRel rEqv rD s f Afs Pr) a (quotient r a rRel rEqv rD) s
   (lem_projQuotient_sig r a rRel rEqv rD)
   (lem_equiv_comp_sig r a rRel rEqv rD s f Afs Pr).
(* Proof of lem_equiv_comp_prop                                            *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
elim Afs; intros; elim H1; clear H1; intros.
generalize (lem_x_in_fun_form f H0 v2 H); intros; elim H3; clear H3; intros;
 elim H3; clear H3; intros.
generalize H; clear H; rewrite H3; clear H3; intros.
generalize (lem_fun_and_dom f x x0 H0 H) (lem_fun_and_img f x x0 H0 H);
 intros.
cut (In x a); intros; [ idtac | rewrite <- H1; auto with zfc ].
generalize (H2 x0 H4); intros.
generalize (lem_x_equiv_in_projQ r a rRel rEqv rD x H5); intros.
generalize
 (lem_fun_and_img (projQuotient r a rRel rEqv rD) x
    (equivClass r a rRel rEqv x) (lem_projQuotient_is_fun r a rRel rEqv rD)
    H7); rewrite (lem_projQuotient_img r a rRel rEqv rD); 
 intros.
generalize (lem_equiv_comp_elem r a rRel rEqv rD s f Afs Pr x H5); intros.
unfold comp in |- *.
elim
 (axs_comprehension
    (fun c : E =>
     exists y : E,
       In (couple (first c) y) (projQuotient r a rRel rEqv rD) /\
       In (couple y (second c)) (equiv_comp r a rRel rEqv rD s f Afs Pr))
    (cartesien a s) (couple x x0)); intros; apply H11; 
 clear H10 H11; intros.
split;
 [ idtac
 | exists (equivClass r a rRel rEqv x); rewrite (lem_first_propertie x x0);
    rewrite (lem_second_propertie x x0); split; [ auto with zfc | idtac ] ].
elim (lem_cartesian_propertie a s (couple x x0)); intros; apply H11;
 clear H10 H11; intros.
exists x; exists x0; split;
 [ auto with zfc | split; [ exact (H2 x0 H4) | reflexivity ] ].

rewrite (lem_eval_propertie f x x0 (lem_fun_sig_is_fun f a s Afs) H);
 auto with zfc.

unfold comp in H.
elim
 (axs_comprehension
    (fun c : E =>
     exists y : E,
       In (couple (first c) y) (projQuotient r a rRel rEqv rD) /\
       In (couple y (second c)) (equiv_comp r a rRel rEqv rD s f Afs Pr))
    (cartesien a s) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros.
unfold projQuotient in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     exists z : E,
       (exists t : E, x0 = couple z t /\ t = equivClass r a rRel rEqv z))
    (cartesien a (quotient r a rRel rEqv rD)) (couple (first v2) x)); 
 intros; generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie (first v2) x0 x x1); intros; generalize (H4 H2);
 clear H2 H4 H5; intros; elim H2; clear H2; intros.
generalize H3; rewrite <- H2; rewrite <- H4; clear H2 H3 H4; intros.
unfold equiv_comp in H1.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple (equivClass r a rRel rEqv x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien (quotient r a rRel rEqv rD) s) (couple x (second v2))); 
 intros; generalize (H2 H1); clear H1 H2 H4; intros.
elim H1; clear H1; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros.
elim
 (lem_couple_propertie x (equivClass r a rRel rEqv x2) 
    (second v2) (App f (lem_fun_sig_is_fun f a s Afs) x2)); 
 intros; generalize (H5 H4); clear H4 H5 H6; intros; 
 elim H4; clear H4; intros.
elim (lem_cartesian_propertie a s v2); intros; generalize (H6 H); clear H6 H7;
 intros.
elim H6; clear H6; intros; elim H6; clear H6; intros; elim H6; clear H6;
 intros; elim H7; clear H7; intros.
generalize H H0 H1 H3 H5; rewrite H8; rewrite (lem_first_propertie x3 x4);
 rewrite (lem_second_propertie x3 x4); clear H H0 H1 H3 H5; 
 intros.
generalize H4; rewrite H3; clear H3; intros.
generalize (lem_equivClass_is_same r a rRel rEqv rD x3 x2 H6 H2 H3); intros.
generalize (Pr x3 x2 H9); intros.
rewrite H5; rewrite <- H10.
elim Afs; intros; elim H12; clear H12; intros.
cut (In x3 (dom f)); intros; [ idtac | rewrite H12; auto with zfc ].
exact (lem_eval_prop2 f x3 (lem_fun_sig_is_fun f a s Afs) H14).

Qed.
(* End of proof of lem_equiv_comp_prop                                     *)

(***************************************************************************)
(* Si f = g o projQuotient alors g = equiv_comp                            *)
(***************************************************************************)
Lemma lem_equiv_comp_unicite :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y) (g : E)
   (Ags : fun_sig g (quotient r a rRel rEqv rD) s),
 f =
 comp (projQuotient r a rRel rEqv rD) g a (quotient r a rRel rEqv rD) s
   (lem_projQuotient_sig r a rRel rEqv rD) Ags ->
 g = equiv_comp r a rRel rEqv rD s f Afs Pr.
(* Proof of lem_equiv_comp_unicite                                         *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
elim Afs; elim Ags; intros.
elim H2; elim H4; clear H2 H4; intros.
generalize (lem_x_in_fun_form g H1 v2 H0); intros.
elim H7; clear H7; intros; elim H7; clear H7; intros.
generalize H0; rewrite H7; clear H0 H7; intros.
generalize (lem_fun_and_dom g x x0 H1 H0) (lem_fun_and_img g x x0 H1 H0);
 intros.
generalize H7; rewrite H5; intros.
unfold equiv_comp in |- *.
elim
 (axs_comprehension
    (fun z : E =>
     exists x1 : E,
       In x1 a /\
       z =
       couple (equivClass r a rRel rEqv x1)
         (App f (lem_fun_sig_is_fun f a s Afs) x1))
    (cartesien (quotient r a rRel rEqv rD) s) (couple x x0)); 
 intros; apply H11; clear H10 H11; intros.
generalize (H6 x0 H8); intros.
split.
elim (lem_cartesian_propertie (quotient r a rRel rEqv rD) s (couple x x0));
 intros; apply H12; clear H11 H12; intros.
exists x; exists x0; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold quotient in H9.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In y a /\ x0 = equivClass r a rRel rEqv y)
    (parties a) x); intros; generalize (H11 H9); clear H9 H11 H12; 
 intros.
elim H9; clear H9; intros; elim H11; clear H11; intros; elim H11; clear H11;
 intros.
exists x1; split; [ auto with zfc | idtac ].
elim
 (lem_couple_propertie x (equivClass r a rRel rEqv x1) x0
    (App f (lem_fun_sig_is_fun f a s Afs) x1)); intros; 
 apply H14; clear H13 H14; intros.
split; [ auto with zfc | idtac ].
generalize (lem_x_equiv_in_projQ r a rRel rEqv rD x1 H11); rewrite <- H12;
 intros.
generalize
 (lem_comp_make (projQuotient r a rRel rEqv rD) g a
    (quotient r a rRel rEqv rD) s x1 x x0
    (lem_projQuotient_sig r a rRel rEqv rD) Ags H13 H0); 
 rewrite <- H; intros.
exact (lem_eval_propertie f x1 x0 H3 H14).

unfold equiv_comp in H0.
elim
 (axs_comprehension
    (fun z : E =>
     exists x : E,
       In x a /\
       z =
       couple (equivClass r a rRel rEqv x)
         (App f (lem_fun_sig_is_fun f a s Afs) x))
    (cartesien (quotient r a rRel rEqv rD) s) v2); 
 intros; generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
elim (lem_cartesian_propertie (quotient r a rRel rEqv rD) s v2); intros;
 generalize (H3 H0); clear H0 H3 H4; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H3; clear H3; intros.
generalize H2; rewrite H4; clear H2 H4; intros.
elim
 (lem_couple_propertie x0 (equivClass r a rRel rEqv x) x1
    (App f (lem_fun_sig_is_fun f a s Afs) x)); intros; 
 generalize (H4 H2); clear H2 H4 H5; intros.
elim H2; clear H2; intros.
generalize (lem_x_equiv_in_projQ r a rRel rEqv rD x H1); rewrite <- H2;
 intros.
elim Afs; intros; elim H7; clear H7; intros.
generalize H1; rewrite <- H7; intros.
cut
 (In (couple x (App f (lem_fun_sig_is_fun f a s Afs) x))
    (comp (projQuotient r a rRel rEqv rD) g a (quotient r a rRel rEqv rD) s
       (lem_projQuotient_sig r a rRel rEqv rD) Ags)); 
 intros.
generalize
 (lem_comp_intermed (projQuotient r a rRel rEqv rD) g a
    (quotient r a rRel rEqv rD) s x (App f (lem_fun_sig_is_fun f a s Afs) x)
    (lem_projQuotient_sig r a rRel rEqv rD) Ags H10); 
 clear H10; intros.
elim H10; clear H10; intros; elim H10; clear H10; intros.
generalize (lem_projQuotient_is_fun r a rRel rEqv rD); intros.
elim H12; clear H12; intros.
generalize (H13 x x0 x2 H5 H10); clear H12 H13; intros.
generalize H11; rewrite <- H12; rewrite <- H4; tauto.

rewrite <- H.
exact (lem_eval_prop2 f x (lem_fun_sig_is_fun f a s Afs) H9).

Qed.
(* End of proof of lem_equiv_comp_unicite                                  *)

(***************************************************************************)
(* On propose un ennonce plus traditionnel du thm fondamental sur les      *)
(* ensembles quotients.                                                    *)
(***************************************************************************)
Theorem thm_ens_quotient_fond :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_sig f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s Afs) x =
         App f (lem_fun_sig_is_fun f a s Afs) y),
 exUniq _
   (fun g : E =>
    fun_sig g (quotient r a rRel rEqv rD) s /\
    f =
    comp2 (projQuotient r a rRel rEqv rD) g a (quotient r a rRel rEqv rD) s).
(* Proof of thm_ens_quotient_fond                                          *)
unfold exUniq in |- *; intros.
exists (equiv_comp r a rRel rEqv rD s f Afs Pr).
generalize (lem_equiv_comp_sig r a rRel rEqv rD s f Afs Pr); intros.
split; [ split; [ auto with zfc | idtac ] | intros; symmetry  in |- * ].
generalize (lem_projQuotient_sig r a rRel rEqv rD); intros.
rewrite <-
 (lem_comp2_eq_comp (projQuotient r a rRel rEqv rD)
    (equiv_comp r a rRel rEqv rD s f Afs Pr) a (quotient r a rRel rEqv rD) s
    H0 H).
exact (lem_equiv_comp_prop r a rRel rEqv rD s f Afs Pr).

elim H0; clear H0; intros.
generalize
 (lem_comp2_eq_comp (projQuotient r a rRel rEqv rD) y a
    (quotient r a rRel rEqv rD) s (lem_projQuotient_sig r a rRel rEqv rD) H0);
 intros.
generalize H1; rewrite <- H2; clear H1 H2; intros.
exact (lem_equiv_comp_unicite r a rRel rEqv rD s f Afs Pr y H0 H1).

Qed.
(* End of proof of thm_ens_quotient_fond                                   *)

(***************************************************************************)
(* La seconde partie du thm fondamental: si f est une surjection et si la  *)
(* reciproque de Pr est verifiee alors equiv_comp est une bijection        *)
(***************************************************************************)
Lemma lem_equiv_comp_bij_under :
 forall (r a : E) (rRel : rel_sig r a a) (rEqv : equivalence r a rRel)
   (rD : rdom r a a rRel = a) (s f : E) (Afs : fun_surj f a s)
   (Pr : forall x y : E,
         In (couple x y) r ->
         App f (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) x =
         App f (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) y)
   (Prinv : forall x y : E,
            App f (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) x =
            App f (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) y ->
            In (couple x y) r),
 fun_bij (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
   (quotient r a rRel rEqv rD) s.
(* Proof of lem_equiv_comp_bij_under                                       *)
unfold fun_bij in |- *; intros.
split;
 [ exact
    (lem_equiv_comp_is_fun r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs)
       Pr)
 | idtac ].
split;
 [ exact
    (lem_equiv_comp_dom r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
 | idtac ].
split;
 [ apply axs_extensionnalite; unfold iff in |- *; split; intros | intros ].
exact
 (lem_equiv_comp_img r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr v2 H).

elim Afs; intros; elim H1; clear H1; intros.
cut (In v2 (Img f)); intros; [ idtac | rewrite H2; auto with zfc ].
generalize (lem_App_rev f v2 H0 H3); intros.
elim H4; clear H4; intros; elim H4; clear H4; intros.
cut (In x a); intros; [ idtac | rewrite <- H1; auto with zfc ].
generalize (lem_eval_propertie f x v2 H0 H5); intros.
generalize H H3 H5; rewrite H7; clear H H3 H5 H7; intros.
generalize
 (lem_equiv_comp_prop r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr);
 intros.
cut
 (In (couple x (App f H0 x))
    (comp (projQuotient r a rRel rEqv rD)
       (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) a
       (quotient r a rRel rEqv rD) s (lem_projQuotient_sig r a rRel rEqv rD)
       (lem_equiv_comp_sig r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs)
          Pr))); intros; [ idtac | rewrite <- H7; auto with zfc ].
generalize
 (lem_comp_intermed (projQuotient r a rRel rEqv rD)
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) a
    (quotient r a rRel rEqv rD) s x (App f H0 x)
    (lem_projQuotient_sig r a rRel rEqv rD)
    (lem_equiv_comp_sig r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
    H8); clear H7 H8; intros.
elim H7; clear H7; intros; elim H7; clear H7; intros.
exact
 (lem_fun_and_img
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) x0
    (App f H0 x)
    (lem_equiv_comp_is_fun r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs)
       Pr) H8).

unfold exUniq in |- *; intros.
generalize
 (lem_App_rev
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) b
    (lem_equiv_comp_is_fun r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs)
       Pr) H); intros.
elim H0; clear H0; intros; elim H0; clear H0; intros.
exists x; split; [ auto with zfc | intros ].
generalize
 (lem_fun_and_dom
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) y b
    (lem_equiv_comp_is_fun r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs)
       Pr) H2); intros.
generalize H0 H3;
 rewrite
  (lem_equiv_comp_dom r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
  ; clear H0 H3; intros.
unfold quotient in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, In y a /\ x0 = equivClass r a rRel rEqv y)
    (parties a) x); intros; generalize (H4 H0); clear H0 H4 H5; 
 intros.
unfold quotient in H3.
elim
 (axs_comprehension
    (fun x : E => exists y0 : E, In y0 a /\ x = equivClass r a rRel rEqv y0)
    (parties a) y); intros; generalize (H4 H3); clear H3 H4 H5; 
 intros.
elim H0; clear H0; intros; clear H0; elim H4; clear H4; intros; elim H0;
 clear H0; intros.
elim H3; clear H3; intros; clear H3; elim H5; clear H5; intros; elim H3;
 clear H3; intros.
generalize H1 H2; rewrite H4; rewrite H5; clear H1 H2 H4 H5; intros.
generalize (lem_x_equiv_in_projQ r a rRel rEqv rD x0 H0)
 (lem_x_equiv_in_projQ r a rRel rEqv rD x1 H3); intros.
generalize
 (lem_comp_make (projQuotient r a rRel rEqv rD)
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) a
    (quotient r a rRel rEqv rD) s x0 (equivClass r a rRel rEqv x0) b
    (lem_projQuotient_sig r a rRel rEqv rD)
    (lem_equiv_comp_sig r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
    H4 H1); intros.
generalize
 (lem_comp_make (projQuotient r a rRel rEqv rD)
    (equiv_comp r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr) a
    (quotient r a rRel rEqv rD) s x1 (equivClass r a rRel rEqv x1) b
    (lem_projQuotient_sig r a rRel rEqv rD)
    (lem_equiv_comp_sig r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr)
    H5 H2); intros.
generalize
 (lem_equiv_comp_prop r a rRel rEqv rD s f (lem_surj_to_sig f a s Afs) Pr);
 intros.
generalize H6 H7; rewrite <- H8; clear H6 H7 H8; intros.
generalize
 (lem_eval_propertie f x0 b
    (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) H6)
 (lem_eval_propertie f x1 b
    (lem_fun_sig_is_fun f a s (lem_surj_to_sig f a s Afs)) H7); 
 intros.
generalize H9; rewrite H8; intros.
generalize (Prinv x0 x1 H10); intros.
exact (lem_equivClass_eq r a rRel rEqv x0 x1 H11).

Qed.
(* End of proof of lem_equiv_comp_bij_under                                *)

(***************************************************************************)
(***************************************************************************)
(* Deux corollaires au thm fondamental                                     *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Corollaire 1                                                            *)
(***************************************************************************)
(***************************************************************************)
(* On s'interesse a equiv_comp dans le cas ou la relation r est le noyau   *)
(* d'equivalence de f.                                                     *)
(***************************************************************************)
Definition equiv_comp_fun (f a s : E) (Afs : fun_sig f a s) :=
  equiv_comp (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs)).

(***************************************************************************)
(* Cette nouvelle "instance" de equiv_comp est une injection               *)
(***************************************************************************)
Lemma lem_equiv_comp_fun_is_inj :
 forall (f a s : E) (Afs : fun_sig f a s),
 fun_inj (equiv_comp_fun f a s Afs)
   (quotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
      (lem_sig_fun_equiv_is_rel f a s Afs)
      (lem_sig_fun_equiv_is_equiv f a s Afs)
      (lem_sig_fun_equiv_dom f a s Afs)) s.
(* Proof of lem_equiv_comp_fun_is_inj                                      *)
intros; unfold fun_inj in |- *.
split; [ idtac | split; intros ].
unfold equiv_comp_fun in |- *.
exact
 (lem_equiv_comp_is_fun (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))).

exact
 (lem_equiv_comp_dom (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))).

split; intros.
exact
 (lem_equiv_comp_img (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))).

unfold exUniq in |- *; intros.
generalize
 (lem_App_rev (equiv_comp_fun f a s Afs) b
    (lem_equiv_comp_is_fun (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
       (lem_sig_fun_equiv_is_rel f a s Afs)
       (lem_sig_fun_equiv_is_equiv f a s Afs)
       (lem_sig_fun_equiv_dom f a s Afs) s f Afs
       (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))) H); 
 intros.
elim H0; clear H0; intros; elim H0; clear H0; intros.
exists x; split; [ auto with zfc | intros ].
generalize
 (lem_equiv_comp_is_fun (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))); 
 intros.
unfold equiv_comp_fun in H1.
unfold equiv_comp in H1.
elim
 (axs_comprehension
    (fun z : E =>
     exists x0 : E,
       In x0 a /\
       z =
       couple
         (equivClass (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
            (lem_sig_fun_equiv_is_rel f a s Afs)
            (lem_sig_fun_equiv_is_equiv f a s Afs) x0)
         (App f (lem_fun_sig_is_fun f a s Afs) x0))
    (cartesien
       (quotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
          (lem_sig_fun_equiv_is_rel f a s Afs)
          (lem_sig_fun_equiv_is_equiv f a s Afs)
          (lem_sig_fun_equiv_dom f a s Afs)) s) (couple x b)); 
 intros; generalize (H4 H1); clear H1 H4 H5; intros.
elim H1; clear H1; intros; elim H4; clear H4; intros; elim H4; clear H4;
 intros.
elim
 (lem_couple_propertie x
    (equivClass (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
       (lem_sig_fun_equiv_is_rel f a s Afs)
       (lem_sig_fun_equiv_is_equiv f a s Afs) x0) b
    (App f (lem_fun_sig_is_fun f a s Afs) x0)); intros; 
 generalize (H6 H5); clear H5 H6 H7; intros.
elim H5; clear H5; intros.
clear H1; unfold equiv_comp_fun in H2; unfold equiv_comp in H2.
elim
 (axs_comprehension
    (fun z : E =>
     exists x : E,
       In x a /\
       z =
       couple
         (equivClass (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
            (lem_sig_fun_equiv_is_rel f a s Afs)
            (lem_sig_fun_equiv_is_equiv f a s Afs) x)
         (App f (lem_fun_sig_is_fun f a s Afs) x))
    (cartesien
       (quotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
          (lem_sig_fun_equiv_is_rel f a s Afs)
          (lem_sig_fun_equiv_is_equiv f a s Afs)
          (lem_sig_fun_equiv_dom f a s Afs)) s) (couple y b)); 
 intros; generalize (H1 H2); clear H1 H2 H7; intros.
elim H1; clear H1; intros; clear H1; elim H2; clear H2; intros; elim H1;
 clear H1; intros.
elim
 (lem_couple_propertie y
    (equivClass (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
       (lem_sig_fun_equiv_is_rel f a s Afs)
       (lem_sig_fun_equiv_is_equiv f a s Afs) x1) b
    (App f (lem_fun_sig_is_fun f a s Afs) x1)); intros; 
 generalize (H7 H2); clear H2 H7 H8; intros.
elim H2; clear H2; intros.
generalize H7; rewrite H6; clear H6 H7; intros.
generalize (lem_sig_equiv_fun_make f a s Afs x0 x1 H4 H1 H7); intros.
generalize
 (lem_equivClass_eq (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) x0 x1 H6); 
 intros.
rewrite H5; rewrite H2; auto with zfc.

Qed.
(* End of proof of lem_equiv_comp_fun_is_inj                               *)

(***************************************************************************)
(* La signature de equiv_comp_fun                                          *)
(***************************************************************************)
Lemma lem_equiv_comp_fun_sig :
 forall (f a s : E) (Afs : fun_sig f a s),
 fun_sig (equiv_comp_fun f a s Afs)
   (quotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
      (lem_sig_fun_equiv_is_rel f a s Afs)
      (lem_sig_fun_equiv_is_equiv f a s Afs)
      (lem_sig_fun_equiv_dom f a s Afs)) s.
(* Proof of lem_equiv_comp_fun_sig                                         *)
intros.
exact
 (lem_equiv_comp_sig (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))).

Qed.
(* End of proof of lem_equiv_comp_fun_sig                                  *)

(***************************************************************************)
(* Comme on pouvait s'y attendre, f = equiv_comp_fun o projQuotient        *)
(***************************************************************************)
Lemma lem_equiv_comp_fun_prop :
 forall (f a s : E) (Afs : fun_sig f a s),
 f =
 comp
   (projQuotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
      (lem_sig_fun_equiv_is_rel f a s Afs)
      (lem_sig_fun_equiv_is_equiv f a s Afs)
      (lem_sig_fun_equiv_dom f a s Afs)) (equiv_comp_fun f a s Afs) a
   (quotient (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
      (lem_sig_fun_equiv_is_rel f a s Afs)
      (lem_sig_fun_equiv_is_equiv f a s Afs)
      (lem_sig_fun_equiv_dom f a s Afs)) s
   (lem_projQuotient_sig (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
      (lem_sig_fun_equiv_is_rel f a s Afs)
      (lem_sig_fun_equiv_is_equiv f a s Afs)
      (lem_sig_fun_equiv_dom f a s Afs)) (lem_equiv_comp_fun_sig f a s Afs).
(* Proof of lem_equiv_comp_fun_prop                                        *)
intros.
exact
 (lem_equiv_comp_prop (equiv_fun f (lem_fun_sig_is_fun f a s Afs)) a
    (lem_sig_fun_equiv_is_rel f a s Afs)
    (lem_sig_fun_equiv_is_equiv f a s Afs) (lem_sig_fun_equiv_dom f a s Afs)
    s f Afs (lem_fun_equiv_prop f (lem_fun_sig_is_fun f a s Afs))).

Qed.
(* End of proof of lem_equiv_comp_fun_prop                                 *)

(***************************************************************************)
(***************************************************************************)
(* Resultats exotiques                                                     *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Une relation symmetrique dont le domaine contient au moins deux elements*)
(* distincts n'est pas antisymmetrique.                                    *)
(***************************************************************************)
Lemma lem_sym_not_antisym :
 forall (r a : E) (rRel : rel_sig r a a)
   (rNe : exists x : E, (exists y : E, x <> y /\ In (couple x y) r)),
 symmetry r a rRel -> ~ antisymmetry r a rRel.
(* Proof of lem_sym_not_antisym                                            *)
unfold not in |- *; unfold symmetry in |- *; unfold antisymmetry in |- *;
 intros.
elim rNe; clear rNe; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
generalize (H0 x x0 H2 (H x x0 H2)); intros.
absurd (x = x0); auto with zfc.

Qed.
(* End of proof of lem_sym_not_antisym                                     *)

(***************************************************************************)
(* Une relation antisymmetrique dont le domaine contient au moins deux     *)
(* elements distincts n'est pas symmetrique.                               *)
(***************************************************************************)
Lemma lem_antisym_not_sym :
 forall (r a : E) (rRel : rel_sig r a a)
   (rNe : exists x : E, (exists y : E, x <> y /\ In (couple x y) r)),
 antisymmetry r a rRel -> ~ symmetry r a rRel.
(* Proof of lem_antisym_not_sym                                            *)
unfold not in |- *; unfold symmetry in |- *; unfold antisymmetry in |- *;
 intros.
elim rNe; clear rNe; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
generalize (H x x0 H2 (H0 x x0 H2)); intros.
absurd (x = x0); auto with zfc.

Qed.
(* End of proof of lem_antisym_not_sym                                     *)

(***************************************************************************)
(* Une relation irreflexive et transitive est antisymmetrique              *)
(***************************************************************************)
Lemma lem_irrefl_trans_so_antisym :
 forall (r a : E) (rRel : rel_sig r a a) (rIrrefl : irreflexivity r a rRel)
   (rTrans : transitivity r a rRel), antisymmetry r a rRel.
(* Proof of lem_irrefl_trans_so_antisym                                    *)
unfold irreflexivity in |- *; unfold transitivity in |- *;
 unfold antisymmetry in |- *; intros.
unfold not in |- *; intros.
generalize (rTrans x y x H H0); clear rTrans H0; intros.
cut (In x (rdom r a a rRel)); intros.
generalize (rIrrefl x H1); intros; absurd (In (couple x x) r);
 auto with zfc.

unfold rdom in |- *.
elim (axs_comprehension (fun x0 : E => exists y : E, In (couple x0 y) r) a x);
 intros; apply H2; clear H1 H2; intros.
split;
 [ unfold rel_sig in rRel; unfold inc in rRel | exists y; auto with zfc ].
generalize (rRel (couple x y) H); intros.
elim (lem_cartesian_propertie a a (couple x y)); intros; generalize (H2 H1);
 clear H1 H2 H3; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; generalize H1; rewrite H3; tauto.

Qed.
(* End of proof of lem_irrefl_trans_so_antisym                             *)

(***************************************************************************)
(*                     End of module MSetBasis                             *)
(***************************************************************************)