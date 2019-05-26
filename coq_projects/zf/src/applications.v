(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(***************************************************************************)
(* File: applications.v                                                    *)
(* auteur: alex@sysal.ibp.fr                                               *)
(* date: 19/10/95                                                          *)
(***************************************************************************)
Require Export couples.

(***************************************************************************)
(***************************************************************************)
(* Relations n-aires                                                       *)
(***************************************************************************)
(***************************************************************************)
Definition n_aire (n : nat) (a : E) (F : E -> Prop) :=
  subset F (cart_power n a).

Lemma lem_subset :
 forall (a b y : E) (F : E -> Prop), a = subset F b -> In y a -> In y b.
(* Pas de reciproque (dixit pagano pb des ensembles non decidables)        *)
(* Proof of lem_subset                                                     *)
intros; elim (axs_comprehension F b y); intros.
generalize H1; rewrite <- H; clear H H1 H2; intros.
elim H1; intros; auto with zfc.

Qed.
(* End of proof of lem_subset                                              *)

(***************************************************************************)
(***************************************************************************)
(* applications                                                            *)
(***************************************************************************)
(***************************************************************************)
Definition fun_ (f : E) :=
  (exists a : E, (exists b : E, inc f (cartesien a b))) /\
  (forall x y z : E, In (couple x y) f -> In (couple x z) f -> y = z).

(***************************************************************************)
(* Domaine d'une application                                               *)
(***************************************************************************)
Definition dom (f : E) :=
  subset (fun v0 : E => fun_ f -> exists v1 : E, In (couple v0 v1) f)
    (reunion (reunion f)).

(***************************************************************************)
(* Image d'une application                                                 *)
(***************************************************************************)
Definition Img (f : E) :=
  subset (fun v1 : E => fun_ f -> exists v0 : E, In (couple v0 v1) f)
    (reunion (reunion f)).

(***************************************************************************)
(* f est une application de a vers b                                       *)
(***************************************************************************)
Definition fun_sig (f a b : E) := fun_ f /\ dom f = a /\ inc (Img f) b.

(***************************************************************************)
(* Trois lemmes evidents mais utiles                                       *)
(***************************************************************************)
Lemma lem_fun_sig_is_fun : forall f a b : E, fun_sig f a b -> fun_ f.
(* Proof of lem_fun_sig_is_fun                                             *)
unfold fun_sig in |- *; intros.
elim H; clear H; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_sig_is_fun                                      *)

Lemma lem_fun_sig_dom : forall f a b : E, fun_sig f a b -> dom f = a.
(* Proof of lem_fun_sig_dom                                                *)
intros; elim H; clear H; intros; elim H0; clear H0; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_sig_dom                                         *)

Lemma lem_fun_sig_img : forall f a b : E, fun_sig f a b -> inc (Img f) b.
(* Proof of lem_fun_sig_img                                                *)
intros; elim H; clear H; intros; elim H0; clear H0; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_sig_img                                         *)

(***************************************************************************)
(* f est une application surjective de a vers b                            *)
(***************************************************************************)
Definition fun_surj (f a b : E) := fun_ f /\ dom f = a /\ Img f = b.

(***************************************************************************)
(* f est une application injective                                         *)
(***************************************************************************)
Definition fun_inj (f a b : E) :=
  fun_ f /\
  dom f = a /\
  inc (Img f) b /\
  (forall b : E, In b (Img f) -> exUniq _ (fun a : E => In (couple a b) f)).

(***************************************************************************)
(* f est une bijection                                                     *)
(***************************************************************************)
Definition fun_bij (f a b : E) :=
  fun_ f /\
  dom f = a /\
  Img f = b /\
  (forall b : E, In b (Img f) -> exUniq _ (fun a : E => In (couple a b) f)).

(***************************************************************************)
(* Re-belote: Trois lemmes debiles ... mais utiles                         *)
(***************************************************************************)
Lemma lem_surj_to_sig : forall f a b : E, fun_surj f a b -> fun_sig f a b.
(* Proof of lem_surj_to_sig                                                *)
unfold fun_surj in |- *; unfold fun_sig in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros.
split;
 [ auto with zfc
 | split; [ auto with zfc | unfold inc in |- *; intros ] ].
generalize H2; rewrite H1; tauto.

Qed.
(* End of proof of lem_surj_to_sig                                         *)

Lemma lem_inj_to_sig : forall f a b : E, fun_inj f a b -> fun_sig f a b.
(* Proof of lem_inj_to_sig                                                 *)
unfold fun_inj in |- *; unfold fun_sig in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H1; clear H1; intros.
split; [ auto with zfc | split; auto with zfc ].

Qed.
(* End of proof of lem_inj_to_sig                                          *)

Lemma lem_bij_to_sig : forall f a b : E, fun_bij f a b -> fun_sig f a b.
(* Proof of lem_bij_to_sig                                                 *)
unfold fun_bij in |- *; unfold fun_sig in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H1; clear H1; intros.
split;
 [ auto with zfc
 | split; [ auto with zfc | unfold inc in |- *; intros ] ].
rewrite <- H1; auto with zfc.

Qed.
(* End of proof of lem_bij_to_sig                                          *)

(***************************************************************************)
(* Une bijection est une injection                                         *)
(***************************************************************************)
Lemma lem_bij_is_inj : forall f a b : E, fun_bij f a b -> fun_inj f a b.
(* Proof of lem_bij_is_inj                                                 *)
unfold fun_bij, fun_inj in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H1; clear H1; intros.
split;
 [ auto with zfc
 | split;
    [ auto with zfc
    | split;
       [ unfold inc in |- *; intros; rewrite <- H1; auto with zfc
       | auto with zfc ] ] ].

Qed.
(* End of proof of lem_bij_is_inj                                          *)

(***************************************************************************)
(* Une bijection est une surjection                                        *)
(***************************************************************************)
Lemma lem_bij_is_surj : forall f a b : E, fun_bij f a b -> fun_surj f a b.
(* Proof of lem_bij_is_inj                                                 *)
unfold fun_bij, fun_surj in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H1; clear H1; intros.
split; [ auto with zfc | split; auto with zfc ].

Qed.
(* End of proof of lem_bij_is_inj                                          *)

(***************************************************************************)
(* Une injection surjective est une bijection                              *)
(***************************************************************************)
Lemma lem_inj_surj_is_bij :
 forall f a b : E, fun_surj f a b -> fun_inj f a b -> fun_bij f a b.
(* Proof of lem_inj_surj_is_bij                                            *)
unfold fun_surj, fun_inj, fun_bij in |- *; intros.
elim H; clear H; intros; clear H; elim H1; clear H1; intros; clear H.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H2; clear H2;
 intros.
split;
 [ auto with zfc
 | split; [ auto with zfc | split; auto with zfc ] ].

Qed.
(* End of proof of lem_inj_surj_is_bij                                     *)

(***************************************************************************)
(***************************************************************************)
(* L'application Vide                                                      *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* Vide est une application                                                *)
(***************************************************************************)
Lemma lem_vide_application : fun_ Vide.
(* Proof of lem_vide_application                                           *)
unfold fun_ in |- *; split;
 [ exists Vide; exists Vide; exact (lem_vide_is_inc (cartesien Vide Vide))
 | intros ].
unfold Vide in H; elim (lem_vide_propertie (couple x y) var_vide);
 auto with zfc.

Qed.
(* End of proof of lem_vide_application                                    *)

(***************************************************************************)
(* Le domaine de l'application Vide est Vide                               *)
(***************************************************************************)
Lemma lem_dom_vide : dom Vide = Vide.
(* Proof of lem_dom_vide                                                   *)
apply axs_extensionnalite; intros; unfold iff in |- *; split; intros;
 unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E => fun_ Vide -> exists v1 : E, In (couple v0 v1) Vide)
    (reunion (reunion Vide)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
generalize H; rewrite lem_reunion_vide; rewrite lem_reunion_vide; tauto.

elim (lem_vide_propertie v2 var_vide); auto with zfc.

Qed.
(* End of proof of  lem_dom_vide                                           *)

(***************************************************************************)
(* L'image de l'application Vide est Vide                                  *)
(***************************************************************************)
Lemma lem_img_vide : Img Vide = Vide.
(* Proof of lem_img_vide                                                   *)
apply axs_extensionnalite; intros; unfold iff in |- *; split; intros;
 unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E => fun_ Vide -> exists v0 : E, In (couple v0 v1) Vide)
    (reunion (reunion Vide)) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
generalize H; rewrite lem_reunion_vide; rewrite lem_reunion_vide; tauto.

unfold Vide in H; elim (lem_vide_propertie v2 var_vide); auto with zfc.

Qed.
(* End of proof of lem_img_vide                                            *)

(***************************************************************************)
(* Pour tout ensemble a, Vide est une application de Vide vers a           *)
(***************************************************************************)
Lemma lem_fun_vide_sig : forall a : E, fun_sig Vide Vide a.
(* Proof of lem_fun_vide_sig                                               *)
unfold fun_sig in |- *; intros.
split;
 [ exact lem_vide_application
 | split;
    [ exact lem_dom_vide | rewrite lem_img_vide; exact (lem_vide_is_inc a) ] ].

Qed.
(* End of proof of lem_fun_vide_sig                                        *)

(***************************************************************************)
(***************************************************************************)
(* Quelques proprietes sur application, domaine et image                   *)
(***************************************************************************)
(***************************************************************************)
Lemma lem_fun_and_dom :
 forall f a b : E, fun_ f -> In (couple a b) f -> In a (dom f).
(* Proof of lem_fun_and_dom                                                *)
intros; unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E => fun_ f -> exists v1 : E, In (couple v0 v1) f)
    (reunion (reunion f)) a); intros; apply H2; clear H1 H2; 
 intros.
split; [ idtac | intros; exists b; auto with zfc ].
elim (axs_reunion (reunion f) a); intros; apply H2; clear H1 H2; intros.
exists (singleton a); split; [ idtac | exact (lem_x_in_sing_x a) ].
elim (axs_reunion f (singleton a)); intros; apply H2; clear H1 H2; intros.
exists (couple a b); split;
 [ auto with zfc
 | unfold couple in |- *;
    elim (axs_paire (singleton a) (paire a b) (singleton a)); 
    intros; apply H2; left; reflexivity ].

Qed.
(* End of proof of lem_fun_and_dom                                         *)

Lemma lem_fun_and_img :
 forall f a b : E, fun_ f -> In (couple a b) f -> In b (Img f).
(* Proof of lem_fun_and_img                                                *)
intros; unfold Img in |- *.
elim
 (axs_comprehension
    (fun v1 : E => fun_ f -> exists v0 : E, In (couple v0 v1) f)
    (reunion (reunion f)) b); intros; apply H2; clear H1 H2; 
 intros.
split; [ idtac | intros; exists a; auto with zfc ].
elim (axs_reunion (reunion f) b); intros; apply H2; clear H1 H2; intros;
 exists (paire a b).
split;
 [ idtac | elim (axs_paire a b b); intros; apply H2; right; reflexivity ].
elim (axs_reunion f (paire a b)); intros; apply H2; clear H1 H2; intros.
exists (couple a b); split;
 [ auto with zfc
 | unfold couple in |- *;
    elim (axs_paire (singleton a) (paire a b) (paire a b)); 
    intros; apply H2; right; reflexivity ].

Qed.
(* End of proof of lem_fun_and_img                                         *)

(***************************************************************************)
(* Si f est une application et x est un element du domaine de f alors il   *)
(* existe un y tel que (x,y) in f                                          *)
(***************************************************************************)
Lemma lem_App :
 forall f x : E,
 fun_ f -> In x (dom f) -> exists y : E, In y (Img f) /\ In (couple x y) f.
(* Proof of lem_App                                                   *)
intros; unfold dom in H0.
elim
 (axs_comprehension
    (fun v0 : E => fun_ f -> exists v1 : E, In (couple v0 v1) f)
    (reunion (reunion f)) x); intros; generalize (H1 H0); 
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; generalize (H1 H); clear H1; intros.
elim H1; clear H1; intros.
exists x0; split; [ exact (lem_fun_and_img f x x0 H H1) | auto with zfc ].

Qed.
(* End of proof of lem_App                                            *)

(***************************************************************************)
(* Si f est une application et que y est un element de l'image de f alors  *)
(* il existe au moins un x du domaine de f tel que (x,y) in f              *)
(***************************************************************************)
Lemma lem_App_rev :
 forall f y : E,
 fun_ f -> In y (Img f) -> exists x : E, In x (dom f) /\ In (couple x y) f.
(* Proof of lem_App_rev                                               *)
intros; unfold Img in H0.
elim
 (axs_comprehension
    (fun v1 : E => fun_ f -> exists v0 : E, In (couple v0 v1) f)
    (reunion (reunion f)) y); intros; generalize (H1 H0); 
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; generalize (H1 H); clear H1; intros; elim H1;
 clear H1; intros.
exists x; split; [ exact (lem_fun_and_dom f x y H H1) | auto with zfc ].

Qed.
(* End of proof of lem_App_rev                                        *)

(***************************************************************************)
(***************************************************************************)
(* Composition d'application                                               *)
(***************************************************************************)
(***************************************************************************)
Definition comp (f g a b c : E) (Af : fun_sig f a b) 
  (Ag : fun_sig g b c) :=
  subset
    (fun c : E =>
     exists y : E, In (couple (first c) y) f /\ In (couple y (second c)) g)
    (cartesien a c).

(***************************************************************************)
(* Il peut paraitre necessaire de reformuler la definition de la           *)
(* composition.                                                            *)
(***************************************************************************)
Definition comp2 (f g a b c : E) :=
  subset
    (fun x : E =>
     fun_sig f a b ->
     fun_sig g b c ->
     exists y : E, In (couple (first x) y) f /\ In (couple y (second x)) g)
    (cartesien a c).

Lemma lem_comp2_eq_comp :
 forall (f g a b c : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 comp f g a b c Af Ag = comp2 f g a b c.
(* Proof of lem_comp2_eq_comp                                              *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold comp in H.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros.
unfold comp2 in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     fun_sig f a b ->
     fun_sig g b c ->
     exists y : E, In (couple (first x) y) f /\ In (couple y (second x)) g)
    (cartesien a c) v2); intros; apply H3; clear H2 H3; 
 intros.
split; [ auto with zfc | intros; exists x; split; auto with zfc ].

unfold comp2 in H.
elim
 (axs_comprehension
    (fun x : E =>
     fun_sig f a b ->
     fun_sig g b c ->
     exists y : E, In (couple (first x) y) f /\ In (couple y (second x)) g)
    (cartesien a c) v2); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
elim (H0 Af Ag); clear H0; intros; elim H0; clear H0; intros.
unfold comp in |- *.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) v2); intros; apply H3; clear H2 H3; 
 intros.
split; [ auto with zfc | exists x; split; auto with zfc ].

Qed.
(* End of proof of lem_comp2_eq_comp                                       *)

(***************************************************************************)
(* comp est une application.                                               *)
(***************************************************************************)
Lemma lem_comp_is_fun :
 forall (f g a b c : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 fun_ (comp f g a b c Af Ag).
(* Proof of lem_comp_is_fun                                                *)
intros.
unfold fun_ in |- *; split; [ exists a; exists c | intros ].
unfold inc in |- *; intros.
unfold comp in H.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) v0); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros.
unfold fun_sig in Af; unfold fun_sig in Ag.
elim Af; clear Af; intros.
elim H3; clear H3; intros.
elim Ag; clear Ag; intros.
elim H6; clear H6; intros.
auto with zfc.

unfold comp in H; unfold comp in H0.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y0 : E,
       In (couple (first c0) y0) f /\ In (couple y0 (second c0)) g)
    (cartesien a c) (couple x y)); intros; generalize (H1 H); 
 clear H H1 H2; intros.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple x z)); intros; generalize (H1 H0); 
 clear H0 H1 H2; intros.
elim H; clear H; intros; elim H1; clear H1; intros; elim H1; clear H1; intros.
elim H0; clear H0; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros.
generalize H3; clear H3; rewrite (lem_first_propertie x z); intros.
generalize H4; clear H4; rewrite (lem_second_propertie x z); intros.
generalize H1; clear H1; rewrite (lem_first_propertie x y); intros.
generalize H2; clear H2; rewrite (lem_second_propertie x y); intros.
unfold fun_sig in Af; elim Af; intros.
unfold fun_sig in Ag; elim Ag; intros.
unfold fun_ in H5; unfold fun_ in H7; clear H6 H8.
elim H5; clear H5; intros; clear H5.
elim H7; clear H7; intros; clear H5.
generalize (H6 x x0 x1 H1 H3); clear H1 H3; intros.
generalize H4; clear H4; rewrite <- H1; clear H1; intros.
exact (H7 x0 y z H2 H4).

Qed.
(* End of proof of lem_comp_is_fun                                         *)

(***************************************************************************)
(* Le domaine de g o f est le domaine de f                                 *)
(***************************************************************************)
Lemma lem_comp_dom :
 forall (f g a b c : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 dom (comp f g a b c Af Ag) = dom f.
(* Proof of lem_comp_dom                                                   *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (comp f g a b c Af Ag) ->
     exists v1 : E, In (couple v0 v1) (comp f g a b c Af Ag))
    (reunion (reunion (comp f g a b c Af Ag))) v2); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_comp_is_fun f g a b c Af Ag)); clear H0; intros.
elim H0; clear H0; intros.
unfold comp in H0.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple v2 x)); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
generalize H1; clear H1 H2; rewrite (lem_first_propertie v2 x); intros.
unfold fun_sig in Af; elim Af; intros.
exact (lem_fun_and_dom f v2 x0 H2 H1).

generalize Af Ag; intros.
unfold fun_sig in Af0; unfold fun_sig in Ag0.
elim Af; clear Af; intros; elim H1; clear H1; intros.
elim Ag; clear Ag; intros; elim H4; clear H4; intros.
generalize (lem_App f v2 H0 H); intros; elim H6; clear H6; intros; elim H6;
 clear H6; intros.
unfold inc in H2.
generalize (H2 x); intros.
generalize (H8 H6); clear H6 H8; intros.
cut (In x (dom g)); [ intros | rewrite H4; auto with zfc ].
generalize (lem_App g x H3 H8); intros.
elim H9; clear H9; intros; elim H9; clear H9; intros.
unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (comp f g a b c Af0 Ag0) ->
     exists v1 : E, In (couple v0 v1) (comp f g a b c Af0 Ag0))
    (reunion (reunion (comp f g a b c Af0 Ag0))) v2); 
 intros; apply H12; clear H11 H12; intros.
split.
elim (axs_reunion (reunion (comp f g a b c Af0 Ag0)) v2); intros; apply H12;
 clear H11 H12; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion (comp f g a b c Af0 Ag0) (singleton v2)); intros; intros;
 apply H12; clear H11 H12; intros.
exists (couple v2 x0); split;
 [ idtac
 | unfold couple in |- *;
    elim (axs_paire (singleton v2) (paire v2 x0) (singleton v2)); 
    intros; apply H12; left; reflexivity ].
unfold comp in |- *.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple v2 x0)); intros; apply H12; 
 clear H11 H12; intros.
split; [ idtac | exists x ].
elim (lem_cartesian_propertie a c (couple v2 x0)); intros; apply H12;
 clear H11 H12; intros.
exists v2; exists x0.
rewrite <- H1; split; [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold inc in H5; generalize (H5 x0); intros; exact (H11 H9).

rewrite (lem_first_propertie v2 x0); rewrite (lem_second_propertie v2 x0);
 split; auto with zfc.

intros; exists x0.
unfold comp in |- *.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple v2 x0)); intros; apply H13; 
 clear H12 H13; intros.
split; [ idtac | exists x ].
elim (lem_cartesian_propertie a c (couple v2 x0)); intros; apply H13;
 clear H12 H13; intros.
exists v2; exists x0.
rewrite <- H1; split; [ auto with zfc | split; [ idtac | reflexivity ] ].
unfold inc in H5; generalize (H5 x0); intros; exact (H12 H9).

rewrite (lem_first_propertie v2 x0); rewrite (lem_second_propertie v2 x0);
 split; auto with zfc.

Qed.
(* End of proof of lem_comp_dom                                            *)

(***************************************************************************)
(* L'image de g o f est incluse dans l'image de f                          *)
(***************************************************************************)
Lemma lem_comp_img :
 forall (f g a b c : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 inc (Img (comp f g a b c Af Ag)) (Img g).
(* Proof of lem_comp_img                                                   *)
intros; unfold inc in |- *; intros.
elim Af; intros; elim H1; clear H1; intros.
elim Ag; intros; elim H4; clear H4; intros.
elim
 (lem_App_rev (comp f g a b c Af Ag) v0 (lem_comp_is_fun f g a b c Af Ag) H);
 intros.
elim H6; clear H6; intros.
unfold comp in H7.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple x v0)); intros; generalize (H8 H7);
 clear H7 H8 H9; intros.
elim H7; clear H7; intros; elim H8; clear H8; intros; elim H8; clear H8;
 intros.
generalize H9; clear H9; rewrite (lem_second_propertie x v0); intros.
exact (lem_fun_and_img g x0 v0 H3 H9).

Qed.
(* End of proof of lem_comp_img                                            *)

(***************************************************************************)
(* (x,y) in f et (y,z) in g -> (x,z) in g o f                              *)
(***************************************************************************)
Lemma lem_comp_make :
 forall (f g a b c x y z : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 In (couple x y) f ->
 In (couple y z) g -> In (couple x z) (comp f g a b c Af Ag).
(* Proof of lem_comp_make                                                  *)
intros; unfold comp in |- *.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple x z)); intros; apply H2; 
 clear H1 H2; intros.
split;
 [ idtac
 | exists y; rewrite (lem_first_propertie x z);
    rewrite (lem_second_propertie x z); split; auto with zfc ].
elim Af; clear Af; intros; elim H2; clear H2; intros.
elim Ag; clear Ag; intros; elim H5; clear H5; intros.
elim (lem_cartesian_propertie a c (couple x z)); intros; apply H8;
 clear H7 H8; intros.
exists x; exists z; split;
 [ rewrite <- H2; exact (lem_fun_and_dom f x y H1 H)
 | split; [ idtac | reflexivity ] ].
generalize (lem_fun_and_img g y z H4 H0); intros.
unfold inc in H6; exact (H6 z H7).

Qed.
(* End of proof of lem_comp_make                                           *)

(***************************************************************************)
(* (x,z) in g o f -> il existe un y tel que (x,y) in f et (y,z) in g       *)
(***************************************************************************)
Lemma lem_comp_intermed :
 forall (f g a b c x z : E) (Af : fun_sig f a b) (Ag : fun_sig g b c),
 In (couple x z) (comp f g a b c Af Ag) ->
 exists y : E, In (couple x y) f /\ In (couple y z) g.
(* Proof of lem_comp_intermed                                              *)
intros; unfold comp in H.
elim
 (axs_comprehension
    (fun c0 : E =>
     exists y : E, In (couple (first c0) y) f /\ In (couple y (second c0)) g)
    (cartesien a c) (couple x z)); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros; elim H0; clear H0; intros; elim H0; clear H0; intros.
generalize H0; clear H0; rewrite (lem_first_propertie x z); intros.
generalize H1; clear H1; rewrite (lem_second_propertie x z); intros.
exists x0; split; auto with zfc.

Qed.
(* End of proof of lem_comp_intermed                                       *)

(***************************************************************************)
(***************************************************************************)
(* Redefinissons maintenant une application dans le style f(x) = y         *)
(***************************************************************************)
(***************************************************************************)
Definition App (f : E) (Af : fun_ f) (x : E) :=
  subset (fun z : E => exists y : E, In (couple x y) f /\ In z y)
    (reunion (Img f)).

Lemma lem_eval_propertie :
 forall (f x y : E) (Af : fun_ f), In (couple x y) f -> y = App f Af x.
(* Proof of lem_eval_propertie                                             *)
intros; apply axs_extensionnalite; intros.
unfold iff in |- *; split; intros; unfold App in |- *.
elim
 (axs_comprehension (fun z : E => exists y : E, In (couple x y) f /\ In z y)
    (reunion (Img f)) v2); intros; apply H2; clear H1 H2; 
 intros.
split; [ idtac | exists y; split; auto with zfc ].
elim (axs_reunion (Img f) v2); intros; apply H2; clear H1 H2; intros.
exists y; split; [ exact (lem_fun_and_img f x y Af H) | auto with zfc ].

unfold App in H0.
elim
 (axs_comprehension (fun z : E => exists y : E, In (couple x y) f /\ In z y)
    (reunion (Img f)) v2); intros; generalize (H1 H0); 
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
elim Af; clear Af; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros.
generalize (H4 x x0 y H1 H); clear H4; intros.
rewrite <- H4; auto with zfc.

Qed.
(* End of proof of lem_eval_propertie                                      *)

Lemma lem_eval_prop2 :
 forall (f x : E) (Af : fun_ f), In x (dom f) -> In (couple x (App f Af x)) f.
(* Proof of lem_eval_prop2                                                 *)
unfold dom in |- *; intros.
elim
 (axs_comprehension
    (fun v0 : E => fun_ f -> exists v1 : E, In (couple v0 v1) f)
    (reunion (reunion f)) x); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 Af); clear H0; intros; elim H0; clear H0; intros.
generalize (lem_eval_propertie f x x0 Af H0); intros.
rewrite <- H1; auto with zfc.

Qed.
(* End of proof of lem_eval_prop2                                          *)

(***************************************************************************)
(* Si v2 est dans f, alors v2 est un couple ...                            *)
(***************************************************************************)
Lemma lem_x_in_fun_form :
 forall (f : E) (Af : fun_ f) (x : E),
 In x f -> exists a : E, (exists b : E, x = couple a b).
(* Proof of lem_x_in_fun_form                                              *)
intros.
elim Af; clear Af; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros.
generalize (H0 x H); clear H H0; intros.
elim (lem_cartesian_propertie x0 x1 x); intros; generalize (H0 H);
 clear H H0 H2; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H0; clear H0; intros.
exists x2; exists x3; auto with zfc.

Qed.
(* End of proof of lem_x_in_fun_form                                       *)

(***************************************************************************)
(***************************************************************************)
(* Image d'une partie du domaine d'une application f par f                 *)
(***************************************************************************)
(***************************************************************************)
Definition fun_img_directe (f : E) (Af : fun_ f) (c : E) :=
  subset
    (fun x : E =>
     In c (parties (dom f)) -> exists y : E, In y c /\ x = App f Af y)
    (Img f).

(***************************************************************************)
(* On peut definir l'image reciproque d'une partie de l'image d'une        *)
(* application f.                                                          *)
(***************************************************************************)
Definition fun_img_inverse (f : E) (Af : fun_ f) (d : E) :=
  subset (fun x : E => In d (parties (Img f)) -> In (App f Af x) d) (dom f).

(***************************************************************************)
(* Ces deux notions permettent de definir une application des parties de   *)
(* (dom f) dans les parties de (Img f)                                     *)
(***************************************************************************)
Definition fun_part (f : E) (Af : fun_ f) :=
  subset (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))).

(***************************************************************************)
(* fun_part est une application                                            *)
(***************************************************************************)
Lemma lem_fun_part_is_fun :
 forall (f : E) (Af : fun_ f), fun_ (fun_part f Af).
(* Proof of lem_fun_part_is_fun                                             *)
intros; unfold fun_ in |- *; split; intros.
exists (parties (dom f)); exists (parties (Img f)); unfold inc in |- *;
 intros.
unfold fun_part in H.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) v0); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

unfold fun_part in H; unfold fun_part in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y0 : E, x0 = couple y0 (fun_img_directe f Af y0))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple x y)); intros; generalize (H1 H); clear H H1 H2; 
 intros.
elim H; clear H; intros; elim H1; clear H1; intros.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple x z)); intros; generalize (H2 H0); clear H0 H2 H3; 
 intros.
elim H0; clear H0; intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 y (fun_img_directe f Af x0)); intros;
 generalize (H3 H1); clear H1 H3 H4; intros.
elim H1; clear H1; intros.
rewrite H3; clear H3; rewrite <- H1; clear H1.
elim (lem_couple_propertie x x1 z (fun_img_directe f Af x1)); intros;
 generalize (H1 H2); clear H2 H3 H1; intros.
elim H1; clear H1; intros.
rewrite H2; clear H2; rewrite <- H1; clear H1; reflexivity.

Qed.
(* End of proof of lem_fun_part_is_fun                                     *)

(***************************************************************************)
(* Le domaine de (fun_part f ?) est l'ensemble des parties du domaine de f *)
(***************************************************************************)
Lemma lem_fun_part_dom :
 forall (f : E) (Af : fun_ f), dom (fun_part f Af) = parties (dom f).
(* Proof of lem_fun_part_dom                                               *)
intros; apply axs_extensionnalite; intros.
unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (fun_part f Af) -> exists v1 : E, In (couple v0 v1) (fun_part f Af))
    (reunion (reunion (fun_part f Af))) v2); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_fun_part_is_fun f Af)); clear H0; intros.
elim H0; clear H0; intros.
unfold fun_part in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple v2 x)); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f)) (couple v2 x));
 intros; generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim H1; clear H1; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; rewrite H3; auto with zfc.

unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (fun_part f Af) -> exists v1 : E, In (couple v0 v1) (fun_part f Af))
    (reunion (reunion (fun_part f Af))) v2); intros; 
 apply H1; clear H0 H1; intros.
split; intros.
elim (axs_reunion (reunion (fun_part f Af)) v2); intros; apply H1;
 clear H0 H1; intros.
exists (singleton v2); split; [ idtac | apply lem_x_in_sing_x ].
elim (axs_reunion (fun_part f Af) (singleton v2)); intros; apply H1;
 clear H0 H1; intros.
exists (couple v2 (fun_img_directe f Af v2)); split;
 [ idtac
 | unfold couple in |- *;
    elim
     (axs_paire (singleton v2) (paire v2 (fun_img_directe f Af v2))
        (singleton v2)); intros; apply H1; left; reflexivity ].
unfold fun_part in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f)))
    (couple v2 (fun_img_directe f Af v2))); intros; 
 apply H1; clear H0 H1; intros.
split; [ idtac | exists v2; reflexivity ].
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f))
    (couple v2 (fun_img_directe f Af v2))); intros; 
 apply H1; clear H0 H1; intros.
exists v2; exists (fun_img_directe f Af v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
elim (axs_parties (Img f) (fun_img_directe f Af v2)); intros; apply H1;
 clear H0 H1; intros.
unfold fun_img_directe in H0.
elim
 (axs_comprehension
    (fun x : E =>
     In v2 (parties (dom f)) -> exists y : E, In y v2 /\ x = App f Af y)
    (Img f) v3); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; auto with zfc.

exists (fun_img_directe f Af v2); unfold fun_part in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f)))
    (couple v2 (fun_img_directe f Af v2))); intros; 
 apply H2; clear H1 H2; intros.
split; [ idtac | exists v2; reflexivity ].
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f))
    (couple v2 (fun_img_directe f Af v2))); intros; 
 apply H2; clear H1 H2; intros.
exists v2; exists (fun_img_directe f Af v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
elim (axs_parties (Img f) (fun_img_directe f Af v2)); intros; apply H2;
 clear H1 H2; intros.
unfold fun_img_directe in H1.
elim
 (axs_comprehension
    (fun x : E =>
     In v2 (parties (dom f)) -> exists y : E, In y v2 /\ x = App f Af y)
    (Img f) v3); intros; generalize (H2 H1); clear H1 H2 H3; 
 intros.
elim H1; clear H1; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_part_dom                                        *)

(***************************************************************************)
(* L'image de (fun_part f ?) est egale aux parties de (Img f)              *)
(***************************************************************************)
Lemma lem_fun_part_img :
 forall (f : E) (Af : fun_ f), Img (fun_part f Af) = parties (Img f).
(* Proof of lem_fun_part_img                                               *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (fun_part f Af) -> exists v0 : E, In (couple v0 v1) (fun_part f Af))
    (reunion (reunion (fun_part f Af))) v2); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_fun_part_is_fun f Af)); clear H0; intros; elim H0;
 clear H0; intros.
unfold fun_part in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple x v2)); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
elim H1; clear H1; intros.
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f)) (couple x v2));
 intros; generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x1 v2 x2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
rewrite H4; auto with zfc.

unfold Img in |- *.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (fun_part f Af) -> exists v0 : E, In (couple v0 v1) (fun_part f Af))
    (reunion (reunion (fun_part f Af))) v2); intros; 
 apply H1; clear H0 H1; intros.
split; intros.
elim (axs_reunion (reunion (fun_part f Af)) v2); intros; apply H1;
 clear H0 H1; intros.
exists (paire (fun_img_inverse f Af v2) v2); split;
 [ idtac
 | elim (axs_paire (fun_img_inverse f Af v2) v2 v2); intros; apply H1; right;
    reflexivity ].
elim (axs_reunion (fun_part f Af) (paire (fun_img_inverse f Af v2) v2));
 intros; apply H1; clear H0 H1; intros.
exists (couple (fun_img_inverse f Af v2) v2); split;
 [ idtac
 | unfold couple in |- *;
    elim
     (axs_paire (singleton (fun_img_inverse f Af v2))
        (paire (fun_img_inverse f Af v2) v2)
        (paire (fun_img_inverse f Af v2) v2)); intros; 
    apply H1; right; reflexivity ].
unfold fun_part in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f)))
    (couple (fun_img_inverse f Af v2) v2)); intros; 
 apply H1; clear H0 H1; intros.
split; [ idtac | exists (fun_img_inverse f Af v2) ].
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f))
    (couple (fun_img_inverse f Af v2) v2)); intros; 
 apply H1; clear H0 H1; intros.
exists (fun_img_inverse f Af v2); exists v2; split;
 [ idtac | split; [ auto with zfc | reflexivity ] ].
elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros; apply H1;
 clear H0 H1; intros.
unfold fun_img_inverse in H0.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; auto with zfc.

elim
 (lem_couple_propertie (fun_img_inverse f Af v2) (fun_img_inverse f Af v2) v2
    (fun_img_directe f Af (fun_img_inverse f Af v2))); 
 intros; apply H1; clear H0 H1; intros.
split;
 [ reflexivity
 | apply axs_extensionnalite; intros; unfold iff in |- *; split; intros ].
unfold fun_img_directe in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     In (fun_img_inverse f Af v2) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af v2) /\ x = App f Af y) 
    (Img f) v0); intros; apply H2; clear H1 H2; intros.
split; intros.
elim (axs_parties (Img f) v2); intros; generalize (H1 H); clear H1; intros.
exact (H1 v0 H0).

elim (axs_parties (Img f) v2); intros; generalize (H2 H); clear H2 H3; intros.
generalize (H2 v0 H0); clear H2; intros.
generalize (lem_App_rev f v0 Af H2); intros; elim H3; clear H3; intros;
 elim H3; clear H3; intros.
exists x; split.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x0 : E => In v2 (parties (Img f)) -> In (App f Af x0) v2) 
    (dom f) x); intros; apply H6; clear H5 H6; intros.
split; [ auto with zfc | intros ].
generalize (lem_eval_propertie f x v0 Af H4); intros.
rewrite <- H6; auto with zfc.

exact (lem_eval_propertie f x v0 Af H4).

unfold fun_img_directe in H0.
elim
 (axs_comprehension
    (fun x : E =>
     In (fun_img_inverse f Af v2) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af v2) /\ x = App f Af y) 
    (Img f) v0); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
cut (In (fun_img_inverse f Af v2) (parties (dom f))); intros.
generalize (H1 H2); clear H1 H2; intros.
elim H1; clear H1; intros; elim H1; clear H1; intros.
unfold fun_img_inverse in H1.
elim
 (axs_comprehension
    (fun x0 : E => In v2 (parties (Img f)) -> In (App f Af x0) v2) 
    (dom f) x); intros; generalize (H3 H1); clear H1 H3 H4; 
 intros.
elim H1; clear H1; intros; generalize (H3 H); clear H3; intros.
rewrite H2; auto with zfc.

clear H1; elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros;
 apply H2; clear H1 H2; intros.
unfold fun_img_inverse in H1.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H2 H1); clear H1 H2 H3; 
 intros.
elim H1; clear H1; intros; auto with zfc.

exists (fun_img_inverse f Af v2).
unfold fun_part in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f)))
    (couple (fun_img_inverse f Af v2) v2)); intros; 
 apply H2; clear H1 H2; intros.
split; [ idtac | exists (fun_img_inverse f Af v2) ].
elim
 (lem_cartesian_propertie (parties (dom f)) (parties (Img f))
    (couple (fun_img_inverse f Af v2) v2)); intros; 
 apply H2; clear H1 H2; intros.
exists (fun_img_inverse f Af v2); exists v2; split;
 [ idtac | split; [ auto with zfc | reflexivity ] ].
elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros; apply H2;
 clear H1 H2; intros.
unfold fun_img_inverse in H1.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H2 H1); clear H1 H2 H3; 
 intros.
elim H1; clear H1; intros; generalize (H2 H); clear H2; intros;
 auto with zfc.

elim
 (lem_couple_propertie (fun_img_inverse f Af v2) (fun_img_inverse f Af v2) v2
    (fun_img_directe f Af (fun_img_inverse f Af v2))); 
 intros; apply H2; clear H1 H2; intros.
split;
 [ reflexivity
 | apply axs_extensionnalite; unfold iff in |- *; split; intros ].
unfold fun_img_directe in |- *.
elim
 (axs_comprehension
    (fun x : E =>
     In (fun_img_inverse f Af v2) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af v2) /\ x = App f Af y) 
    (Img f) v0); intros; apply H3; clear H2 H3; intros.
split; elim (axs_parties (Img f) v2); intros.
exact (H2 H v0 H1).

elim (axs_parties (Img f) v2); intros.
generalize (H5 H v0 H1); clear H5 H6; intros.
generalize (lem_App_rev f v0 Af H5); intros.
elim H6; clear H6; intros; elim H6; clear H6; intros.
exists x; split.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x0 : E => In v2 (parties (Img f)) -> In (App f Af x0) v2) 
    (dom f) x); intros; apply H9; clear H8 H9; intros.
split; [ auto with zfc | intros ].
generalize (lem_eval_propertie f x v0 Af H7); intros.
rewrite <- H9; auto with zfc.

exact (lem_eval_propertie f x v0 Af H7).

unfold fun_img_directe in H1.
elim
 (axs_comprehension
    (fun x : E =>
     In (fun_img_inverse f Af v2) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af v2) /\ x = App f Af y) 
    (Img f) v0); intros; generalize (H2 H1); clear H1 H2 H3; 
 intros.
elim H1; clear H1; intros.
cut (In (fun_img_inverse f Af v2) (parties (dom f))); intros.
generalize (H2 H3); clear H2 H3; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros.
unfold fun_img_inverse in H2.
elim
 (axs_comprehension
    (fun x0 : E => In v2 (parties (Img f)) -> In (App f Af x0) v2) 
    (dom f) x); intros; generalize (H4 H2); clear H2 H4 H5; 
 intros.
elim H2; clear H2; intros; generalize (H4 H); clear H4; intros.
rewrite H3; auto with zfc.

clear H2; elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros;
 apply H3; clear H2 H3; intros.
unfold fun_img_inverse in H2.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H3 H2); clear H2 H3 H4; 
 intros.
elim H2; clear H2; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_part_img                                        *)

(***************************************************************************)
(* Les lemmes dont on avait besoin dans la preuve d'avant                  *)
(***************************************************************************)
(***************************************************************************)
(* (fun_img_inverse f Af x) est un element de (parties (dom f))            *)
(***************************************************************************)
Lemma lem_fun_img_inv_is_in_pdom :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (parties (Img f)) -> In (fun_img_inverse f Af x) (parties (dom f)).
(* Proof of lem_fun_img_inv_is_in_pdom                                     *)
intros.
elim (axs_parties (dom f) (fun_img_inverse f Af x)); intros; apply H1;
 clear H0 H1; intros.
unfold fun_img_inverse in H0.
elim
 (axs_comprehension
    (fun x0 : E => In x (parties (Img f)) -> In (App f Af x0) x) 
    (dom f) v3); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_img_inv_is_in_pdom                              *)

Lemma lem_fun_img_prop1 :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (parties (Img f)) -> fun_img_directe f Af (fun_img_inverse f Af x) = x.
(* Proof of lem_fun_img_prop1                                              *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold fun_img_directe in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     In (fun_img_inverse f Af x) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af x) /\ x0 = App f Af y) 
    (Img f) v2); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
generalize (H1 (lem_fun_img_inv_is_in_pdom f Af x H)); clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
unfold fun_img_inverse in H1.
elim
 (axs_comprehension
    (fun x1 : E => In x (parties (Img f)) -> In (App f Af x1) x) 
    (dom f) x0); intros; generalize (H3 H1); clear H1 H3 H4; 
 intros.
elim H1; clear H1; intros; generalize (H3 H); clear H3; intros.
rewrite H2; auto with zfc.

unfold fun_img_directe in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     In (fun_img_inverse f Af x) (parties (dom f)) ->
     exists y : E, In y (fun_img_inverse f Af x) /\ x0 = App f Af y) 
    (Img f) v2); intros; apply H2; clear H1 H2; intros.
split; intros.
elim (axs_parties (Img f) x); intros; generalize (H1 H); clear H1 H2; intros;
 auto with zfc.

elim (axs_parties (Img f) x); intros; generalize (H2 H); clear H2 H3; intros.
generalize (H2 v2 H0); clear H2; intros.
generalize (lem_App_rev f v2 Af H2); intros.
elim H3; clear H3; intros; elim H3; clear H3; intros.
exists x0; split.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x1 : E => In x (parties (Img f)) -> In (App f Af x1) x) 
    (dom f) x0); intros; apply H6; clear H5 H6; intros.
split; [ auto with zfc | intros; clear H5 ].
generalize (lem_eval_propertie f x0 v2 Af H4); intros.
rewrite <- H5; auto with zfc.

exact (lem_eval_propertie f x0 v2 Af H4).

Qed.
(* End of proof of lem_fun_img_prop1                                       *)

(***************************************************************************)
(* (fun_img_directe f Af x) est element de (parties (Img f))               *)
(***************************************************************************)
Lemma lem_fun_img_dir_is_in_pimg :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (parties (dom f)) -> In (fun_img_directe f Af x) (parties (Img f)).
(* Proof of lem_fun_img_dir_is_in_pimg                                     *)
intros.
elim (axs_parties (Img f) (fun_img_directe f Af x)); intros; apply H1;
 clear H0 H1; intros.
unfold fun_img_directe in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     In x (parties (dom f)) -> exists y : E, In y x /\ x0 = App f Af y)
    (Img f) v3); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_img_dir_is_in_pimg                              *)

Lemma lem_fun_img_prop2 :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (parties (dom f)) ->
 inc x (fun_img_inverse f Af (fun_img_directe f Af x)).
(* Proof of lem_fun_img_prop2                                              *)
intros; unfold inc in |- *; intros.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     In (fun_img_directe f Af x) (parties (Img f)) ->
     In (App f Af x0) (fun_img_directe f Af x)) (dom f) v0); 
 intros; apply H2; clear H1 H2; intros.
split; intros.
elim (axs_parties (dom f) x); intros; generalize (H1 H); clear H H1 H2;
 intros.
exact (H v0 H0).

unfold fun_img_directe in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     In x (parties (dom f)) -> exists y : E, In y x /\ x0 = App f Af y)
    (Img f) (App f Af v0)); intros; apply H3; clear H2 H3; 
 intros.
split; [ idtac | intros; clear H2 ].
elim (axs_parties (dom f) x); intros; generalize (H2 H); clear H2 H3; intros.
generalize (H2 v0 H0); clear H2; intros.
generalize (lem_eval_prop2 f v0 Af H2); intros.
exact (lem_fun_and_img f v0 (App f Af v0) Af H3).

exists v0; split; [ auto with zfc | reflexivity ].

Qed.
(* End of proof of lem_fun_img_prop2                                       *)

(***************************************************************************)
(* fun_img_directe est un evaluateur de fun_part                           *)
(***************************************************************************)
Lemma lem_fun_part_eval_prop :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (dom (fun_part f Af)) ->
 App (fun_part f Af) (lem_fun_part_is_fun f Af) x = fun_img_directe f Af x.
(* Proof of lem_fun_part_eval_prop                                         *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold App in H0.
elim
 (axs_comprehension
    (fun z : E => exists y : E, In (couple x y) (fun_part f Af) /\ In z y)
    (reunion (Img (fun_part f Af))) v2); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
unfold fun_part in H1.
elim
 (axs_comprehension
    (fun x1 : E => exists y : E, x1 = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple x x0)); intros; generalize (H3 H1); clear H1 H3 H4; 
 intros.
elim H1; clear H1; intros; elim H3; clear H3; intros.
elim (lem_couple_propertie x x1 x0 (fun_img_directe f Af x1)); intros;
 generalize (H4 H3); clear H3 H4 H5; intros.
elim H3; clear H3; intros; rewrite H3; rewrite <- H4; auto with zfc.

generalize H; rewrite (lem_fun_part_dom f Af); intros.
unfold fun_img_directe in H0.
elim
 (axs_comprehension
    (fun x0 : E =>
     In x (parties (dom f)) -> exists y : E, In y x /\ x0 = App f Af y)
    (Img f) v2); intros; generalize (H2 H0); clear H0 H2 H3; 
 intros.
elim H0; clear H0; intros; generalize (H2 H1); clear H2; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros.
unfold App in |- *.
elim
 (axs_comprehension
    (fun z : E => exists y : E, In (couple x y) (fun_part f Af) /\ In z y)
    (reunion (Img (fun_part f Af))) v2); intros; apply H5; 
 clear H4 H5; intros.
split.
rewrite (lem_fun_part_img f Af).
rewrite (lem_reunion_parties (Img f)).
auto with zfc.

generalize (lem_fun_part_is_fun f Af); intros.
generalize (lem_App (fun_part f Af) x H4 H); intros.
elim H5; clear H5; intros; elim H5; clear H5; intros.
exists x1; split; [ auto with zfc | idtac ].
unfold fun_part in H6.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_directe f Af y))
    (cartesien (parties (dom f)) (parties (Img f))) 
    (couple x x1)); intros; generalize (H7 H6); clear H6 H7 H8; 
 intros.
elim H6; clear H6; intros; elim H7; clear H7; intros.
elim (lem_couple_propertie x x2 x1 (fun_img_directe f Af x2)); intros;
 generalize (H8 H7); clear H7 H8 H9; intros.
elim H7; clear H7; intros.
rewrite H8; rewrite <- H7.
unfold fun_img_directe in |- *.
elim
 (axs_comprehension
    (fun x0 : E =>
     In x (parties (dom f)) -> exists y : E, In y x /\ x0 = App f Af y)
    (Img f) v2); intros; apply H10; clear H9 H10; intros.
split; [ auto with zfc | intros; exists x0; split; auto with zfc ].

Qed.
(* End of proof of lem_fun_part_eval_prop                                  *)

(***************************************************************************)
(***************************************************************************)
(* Reciproque: application des parties de l'image de f dans les parties du *)
(* domaine de f                                                            *)
(***************************************************************************)
(***************************************************************************)
Definition fun_part_inv (f : E) (Af : fun_ f) :=
  subset (fun x : E => exists y : E, x = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))).

(***************************************************************************)
(* fun_part_inv est une application                                        *)
(***************************************************************************)
Lemma lem_fun_part_inv_is_fun :
 forall (f : E) (Af : fun_ f), fun_ (fun_part_inv f Af).
(* Proof of lem_fun_part_inv_is_fun                                        *)
intros; unfold fun_ in |- *; split; intros.
exists (parties (Img f)); exists (parties (dom f)); unfold inc in |- *;
 intros.
unfold fun_part_inv in H.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) v0); 
 intros; generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros; auto with zfc.

unfold fun_part_inv in H; unfold fun_part_inv in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y0 : E, x0 = couple y0 (fun_img_inverse f Af y0))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x y)); intros; generalize (H1 H); clear H H1 H2; 
 intros.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x z)); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H; clear H; intros; elim H1; clear H1; intros.
elim H0; clear H0; intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x0 y (fun_img_inverse f Af x0)); intros;
 generalize (H3 H1); clear H1 H3 H4; intros.
elim (lem_couple_propertie x x1 z (fun_img_inverse f Af x1)); intros;
 generalize (H3 H2); clear H2 H3 H4; intros.
elim H1; clear H1; intros; elim H2; clear H2; intros.
rewrite H3; rewrite H4; rewrite <- H1; rewrite <- H2; reflexivity.

Qed.
(* End of proof of lem_fun_part_inv_is_fun                                 *)

(***************************************************************************)
(* Le domaine de fun_part_inv est l'ensemble des parties de f              *)
(***************************************************************************)
Lemma lem_fun_part_inv_dom :
 forall (f : E) (Af : fun_ f), dom (fun_part_inv f Af) = parties (Img f).
(* Proof of lem_fun_part_inv_dom                                           *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (fun_part_inv f Af) ->
     exists v1 : E, In (couple v0 v1) (fun_part_inv f Af))
    (reunion (reunion (fun_part_inv f Af))) v2); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_fun_part_inv_is_fun f Af)); clear H0; intros.
elim H0; clear H0; intros.
unfold fun_part_inv in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple v2 x)); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; elim H1; clear H1; intros.
elim
 (lem_cartesian_propertie (parties (Img f)) (parties (dom f)) (couple v2 x));
 intros; generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie v2 x1 x x2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
rewrite H3; auto with zfc.

elim (axs_parties (Img f) v2); intros; generalize (H0 H); clear H0 H1; intros.
unfold dom in |- *.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (fun_part_inv f Af) ->
     exists v1 : E, In (couple v0 v1) (fun_part_inv f Af))
    (reunion (reunion (fun_part_inv f Af))) v2); intros; 
 apply H2; clear H1 H2; intros.
split; intros.
elim (axs_reunion (reunion (fun_part_inv f Af)) v2); intros; apply H2;
 clear H1 H2; intros.
exists (paire v2 (fun_img_inverse f Af v2)).
split;
 [ idtac
 | elim (axs_paire v2 (fun_img_inverse f Af v2) v2); intros; apply H2; left;
    reflexivity ].
elim (axs_reunion (fun_part_inv f Af) (paire v2 (fun_img_inverse f Af v2)));
 intros; apply H2; clear H1 H2; intros.
exists (couple v2 (fun_img_inverse f Af v2)).
split;
 [ idtac
 | unfold couple in |- *;
    elim
     (axs_paire (singleton v2) (paire v2 (fun_img_inverse f Af v2))
        (paire v2 (fun_img_inverse f Af v2))); intros; 
    apply H2; right; reflexivity ].
unfold fun_part_inv in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f)))
    (couple v2 (fun_img_inverse f Af v2))); intros; 
 apply H2; clear H1 H2; intros.
split; [ idtac | exists v2; auto with zfc ].
elim
 (lem_cartesian_propertie (parties (Img f)) (parties (dom f))
    (couple v2 (fun_img_inverse f Af v2))); intros; 
 apply H2; clear H1 H2; intros.
exists v2; exists (fun_img_inverse f Af v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros; apply H2;
 clear H1 H2; intros.
unfold fun_img_inverse in H1.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H2 H1); clear H1 H2 H3; 
 intros.
elim H1; clear H1; intros; auto with zfc.

exists (fun_img_inverse f Af v2); unfold fun_part_inv in |- *.
elim
 (axs_comprehension
    (fun x : E => exists y : E, x = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f)))
    (couple v2 (fun_img_inverse f Af v2))); intros; 
 apply H3; clear H2 H3; intros.
split; [ idtac | exists v2; reflexivity ].
elim
 (lem_cartesian_propertie (parties (Img f)) (parties (dom f))
    (couple v2 (fun_img_inverse f Af v2))); intros; 
 apply H3; clear H2 H3; intros.
exists v2; exists (fun_img_inverse f Af v2); split;
 [ auto with zfc | split; [ idtac | reflexivity ] ].
elim (axs_parties (dom f) (fun_img_inverse f Af v2)); intros; apply H3;
 clear H2 H3; intros.
unfold fun_img_inverse in H2.
elim
 (axs_comprehension
    (fun x : E => In v2 (parties (Img f)) -> In (App f Af x) v2) 
    (dom f) v3); intros; generalize (H3 H2); clear H2 H3 H4; 
 intros.
elim H2; clear H2; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_part_inv_dom                                    *)

(***************************************************************************)
(* L'image de fun_img_inv est l'ensemble des parties du domaine de f       *)
(***************************************************************************)
Lemma lem_fun_part_inv_img :
 forall (f : E) (Af : fun_ f),
 inc (Img (fun_part_inv f Af)) (parties (dom f)).
(* Proof of lem_fun_part_inv_img                                           *)
intros; unfold inc in |- *; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (fun_part_inv f Af) ->
     exists v2 : E, In (couple v2 v1) (fun_part_inv f Af))
    (reunion (reunion (fun_part_inv f Af))) v0); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
generalize (H0 (lem_fun_part_inv_is_fun f Af)); clear H0; intros.
elim H0; clear H0; intros.
unfold fun_part_inv in H0.
elim
 (axs_comprehension
    (fun x0 : E => exists y : E, x0 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x v0)); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros; elim H1; clear H1; intros.
elim
 (lem_cartesian_propertie (parties (Img f)) (parties (dom f)) (couple x v0));
 intros; generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x1 v0 x2); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
rewrite H4; auto with zfc.

Qed.
(* End of proof of lem_fun_part_inv_img                                    *)

(***************************************************************************)
(* fun_img_inverse est un evaluateur de fun_part_inv                       *)
(***************************************************************************)
Lemma lem_fun_part_inv_eval_prop :
 forall (f : E) (Af : fun_ f) (x : E),
 In x (dom (fun_part_inv f Af)) ->
 App (fun_part_inv f Af) (lem_fun_part_inv_is_fun f Af) x =
 fun_img_inverse f Af x.
(* Proof of lem_fun_part_inv_eval_prop                                     *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold App in H0.
elim
 (axs_comprehension
    (fun z : E => exists y : E, In (couple x y) (fun_part_inv f Af) /\ In z y)
    (reunion (Img (fun_part_inv f Af))) v2); intros; 
 generalize (H1 H0); clear H0 H1 H2; intros.
elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1;
 intros.
unfold fun_part_inv in H1.
elim
 (axs_comprehension
    (fun x1 : E => exists y : E, x1 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x x0)); intros; generalize (H3 H1); clear H1 H3 H4; 
 intros.
elim H1; clear H1; intros; elim H3; clear H3; intros.
elim (lem_couple_propertie x x1 x0 (fun_img_inverse f Af x1)); intros;
 generalize (H4 H3); clear H3 H4 H5; intros.
elim H3; clear H3; intros.
rewrite H3; rewrite <- H4; auto with zfc.

unfold fun_img_inverse in H0.
elim
 (axs_comprehension
    (fun x0 : E => In x (parties (Img f)) -> In (App f Af x0) x) 
    (dom f) v2); intros; generalize (H1 H0); clear H0 H1 H2; 
 intros.
elim H0; clear H0; intros.
generalize H; rewrite (lem_fun_part_inv_dom f Af); intros.
generalize (H1 H2); clear H1 H2; intros.
unfold App in |- *.
elim
 (axs_comprehension
    (fun z : E => exists y : E, In (couple x y) (fun_part_inv f Af) /\ In z y)
    (reunion (Img (fun_part_inv f Af))) v2); intros; 
 apply H3; clear H2 H3; intros.
generalize (lem_fun_part_inv_is_fun f Af); intros.
elim (lem_App (fun_part_inv f Af) x H2 H); intros.
elim H3; clear H3; intros.
split.
elim (axs_reunion (Img (fun_part_inv f Af)) v2); intros; apply H6;
 clear H5 H6; intros.
exists x0.
split; [ auto with zfc | idtac ].
unfold fun_part_inv in H4.
elim
 (axs_comprehension
    (fun x1 : E => exists y : E, x1 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x x0)); intros; generalize (H5 H4); clear H4 H5 H6; 
 intros.
elim H4; clear H4; intros; elim H5; clear H5; intros.
elim (lem_couple_propertie x x1 x0 (fun_img_inverse f Af x1)); intros;
 generalize (H6 H5); clear H5 H6 H7; intros.
elim H5; clear H5; intros.
rewrite H6; rewrite <- H5; clear H5 H6.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x0 : E => In x (parties (Img f)) -> In (App f Af x0) x) 
    (dom f) v2); intros; apply H6; clear H5 H6; intros.
split; intros; auto with zfc.

exists x0; split; [ auto with zfc | idtac ].
unfold fun_part_inv in H4.
elim
 (axs_comprehension
    (fun x1 : E => exists y : E, x1 = couple y (fun_img_inverse f Af y))
    (cartesien (parties (Img f)) (parties (dom f))) 
    (couple x x0)); intros; generalize (H5 H4); clear H4 H5 H6; 
 intros.
elim H4; clear H4; intros; elim H5; clear H5; intros.
elim (lem_couple_propertie x x1 x0 (fun_img_inverse f Af x1)); intros;
 generalize (H6 H5); clear H5 H6 H7; intros.
elim H5; clear H5; intros.
rewrite H6; rewrite <- H5; clear H5 H6.
unfold fun_img_inverse in |- *.
elim
 (axs_comprehension
    (fun x0 : E => In x (parties (Img f)) -> In (App f Af x0) x) 
    (dom f) v2); intros; apply H6; clear H5 H6; intros.
split; intros; auto with zfc.

Qed.
(* End of proof of lem_fun_part_inv_eval_prop                              *)

(***************************************************************************)
(***************************************************************************)
(* Relation inverse d'une application et applications au cas des bijections*)
(***************************************************************************)
(***************************************************************************)
(***************************************************************************)
(* On peut definir la relation inverse d'une application                   *)
(***************************************************************************)
Definition fun_recip (f : E) (Af : fun_ f) :=
  subset
    (fun c : E =>
     exists x : E, (exists y : E, In (couple x y) f /\ c = couple y x))
    (cartesien (Img f) (dom f)).

(***************************************************************************)
(* fun_recip est une application ssi f est une injection                   *)
(***************************************************************************)
Lemma lem_fun_recip_is_fun_under_inj :
 forall (f : E) (Af : fun_ f),
 fun_inj f (dom f) (Img f) <-> fun_ (fun_recip f Af).
(* Proof of lem_fun_recip_is_fun_under_inj                                 *)
intros; unfold iff in |- *; split; intros.
unfold fun_inj in H.
elim H; clear H; intros; elim H0; clear H0; intros; clear H0; elim H1;
 clear H1; intros; clear H0.
unfold fun_ in |- *; split; intros.
exists (Img f); exists (dom f); unfold inc in |- *; intros.
unfold fun_recip in H0.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E, (exists y : E, In (couple x y) f /\ c = couple y x))
    (cartesien (Img f) (dom f)) v0); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros; auto with zfc.

unfold fun_recip in H0; unfold fun_recip in H2.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y0 : E, In (couple x0 y0) f /\ c = couple y0 x0))
    (cartesien (Img f) (dom f)) (couple x y)); intros; 
 generalize (H3 H0); clear H0 H3 H4; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) f /\ c = couple y x0))
    (cartesien (Img f) (dom f)) (couple x z)); intros; 
 generalize (H3 H2); clear H2 H3 H4; intros.
elim H0; clear H0; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H3; clear H3; intros.
elim H2; clear H2; intros; elim H5; clear H5; intros; elim H5; clear H5;
 intros; elim H5; clear H5; intros.
elim (lem_couple_propertie x x1 y x0); intros; generalize (H7 H4);
 clear H4 H7 H8; intros; elim H4; clear H4; intros.
generalize H3; rewrite <- H4; rewrite <- H7; clear H3 H4 H7; intros.
elim (lem_couple_propertie x x3 z x2); intros; generalize (H4 H6);
 clear H4 H6 H7; intros; elim H4; clear H4; intros.
generalize H5; rewrite <- H4; rewrite <- H6; clear H4 H5 H6; intros.
generalize (lem_fun_and_img f y x Af H3); intros.
generalize (H1 x H4); unfold exUniq in |- *; intros.
elim H6; clear H6; intros; elim H6; clear H6; intros;
 generalize (H7 y H3) (H7 z H5); intros.
rewrite <- H8; rewrite <- H9; reflexivity.

elim H; clear H; intros.
elim H; clear H; intros; elim H; clear H; intros.
unfold fun_inj in |- *.
split;
 [ auto with zfc
 | split;
    [ reflexivity
    | split;
       [ unfold inc in |- *; intros; auto with zfc
       | unfold exUniq in |- *; intros ] ] ].
generalize (lem_App_rev f b Af H1); intros; elim H2; clear H2; intros;
 elim H2; clear H2; intros.
exists x1; split; [ auto with zfc | intros ].
generalize (lem_fun_and_dom f y b Af H4); intros.
cut (In (couple b x1) (fun_recip f Af)); intros.
cut (In (couple b y) (fun_recip f Af)); intros.
exact (H0 b x1 y H6 H7).

unfold fun_recip in |- *.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E, (exists y0 : E, In (couple x y0) f /\ c = couple y0 x))
    (cartesien (Img f) (dom f)) (couple b y)); intros; 
 apply H8; clear H7 H8; intros.
split;
 [ idtac | exists y; exists b; split; [ auto with zfc | reflexivity ] ].
elim (lem_cartesian_propertie (Img f) (dom f) (couple b y)); intros; apply H8;
 clear H7 H8; intros.
exists b; exists y; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

unfold fun_recip in |- *.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E, (exists y : E, In (couple x y) f /\ c = couple y x))
    (cartesien (Img f) (dom f)) (couple b x1)); intros; 
 apply H7; clear H6 H7; intros.
split;
 [ idtac | exists x1; exists b; split; [ auto with zfc | reflexivity ] ].
elim (lem_cartesian_propertie (Img f) (dom f) (couple b x1)); intros;
 apply H7; clear H6 H7; intros.
exists b; exists x1; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_fun_recip_is_fun_under_inj                          *)

(***************************************************************************)
(* Si f est une application et que (x,y) est dans f alors (y,x) est dans   *)
(* (fun_recip f)                                                           *)
(***************************************************************************)
Lemma lem_xyinf_yxinrecipf :
 forall (f : E) (Af : fun_ f) (x y : E),
 In (couple x y) f -> In (couple y x) (fun_recip f Af).
(* Proof of lem_xyinf_yxinrecipf                                           *)
intros; unfold fun_recip in |- *.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y0 : E, In (couple x0 y0) f /\ c = couple y0 x0))
    (cartesien (Img f) (dom f)) (couple y x)); intros; 
 apply H1; clear H0 H1; intros.
split;
 [ idtac | exists x; exists y; split; [ auto with zfc | reflexivity ] ].
generalize (lem_fun_and_dom f x y Af H); intros.
generalize (lem_fun_and_img f x y Af H); intros.
elim (lem_cartesian_propertie (Img f) (dom f) (couple y x)); intros; apply H3;
 clear H2 H3; intros.
exists y; exists x; split;
 [ auto with zfc | split; [ auto with zfc | reflexivity ] ].

Qed.
(* End of proof of lem_xyinf_yxinrecipf                                    *)

(***************************************************************************)
(* Si f est une bijection alors fun_recip est une bijection                *)
(***************************************************************************)
Lemma lem_fun_recip_is_bij_under_bij :
 forall (f : E) (Af : fun_ f),
 fun_bij f (dom f) (Img f) -> fun_bij (fun_recip f Af) (Img f) (dom f).
(* Proof of lem_fun_recip_is_bij_under_bij                                 *)
intros.
generalize (lem_bij_is_inj f (dom f) (Img f) H); intros.
elim (lem_fun_recip_is_fun_under_inj f Af); intros; generalize (H1 H0);
 clear H0 H1 H2; intros.
unfold fun_bij in H.
elim H; clear H; intros; clear H; elim H1; clear H1; intros; clear H; elim H1;
 clear H1; intros; clear H.
unfold fun_bij in |- *.
split; [ auto with zfc | split ].
apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold dom in H.
elim
 (axs_comprehension
    (fun v0 : E =>
     fun_ (fun_recip f Af) ->
     exists v1 : E, In (couple v0 v1) (fun_recip f Af))
    (reunion (reunion (fun_recip f Af))) v2); intros; 
 generalize (H2 H); clear H H2 H3; intros.
elim H; clear H; intros; generalize (H2 H0); clear H2; intros; elim H2;
 clear H2; intros.
unfold fun_recip in H2.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) f /\ c = couple y x0))
    (cartesien (Img f) (dom f)) (couple v2 x)); intros; 
 generalize (H3 H2); clear H2 H3 H4; intros.
elim H2; clear H2; intros.
elim (lem_cartesian_propertie (Img f) (dom f) (couple v2 x)); intros;
 generalize (H4 H2); clear H2 H4 H5; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H6 H5);
 clear H5 H6 H7; intros.
elim H5; clear H5; intros.
rewrite H5; auto with zfc.

generalize (H1 v2 H); intros.
unfold exUniq in H2.
elim H2; clear H2; intros; elim H2; clear H2; intros.
generalize (lem_xyinf_yxinrecipf f Af x v2 H2); intros.
exact (lem_fun_and_dom (fun_recip f Af) v2 x H0 H4).

split.
apply axs_extensionnalite; unfold iff in |- *; split; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (fun_recip f Af) ->
     exists v0 : E, In (couple v0 v1) (fun_recip f Af))
    (reunion (reunion (fun_recip f Af))) v2); intros; 
 generalize (H2 H); clear H H2 H3; intros.
elim H; clear H; intros; generalize (H2 H0); clear H2; intros; elim H2;
 clear H2; intros.
unfold fun_recip in H2.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) f /\ c = couple y x0))
    (cartesien (Img f) (dom f)) (couple x v2)); intros; 
 generalize (H3 H2); clear H2 H3 H4; intros.
elim H2; clear H2; intros.
elim (lem_cartesian_propertie (Img f) (dom f) (couple x v2)); intros;
 generalize (H4 H2); clear H2 H4 H5; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie x x0 v2 x1); intros; generalize (H6 H5);
 clear H5 H6 H7; intros.
elim H5; clear H5; intros; rewrite H6; auto with zfc.

generalize (lem_App f v2 Af H); intros.
elim H2; clear H2; intros; elim H2; clear H2; intros.
generalize (lem_xyinf_yxinrecipf f Af v2 x H3); intros.
exact (lem_fun_and_img (fun_recip f Af) x v2 H0 H4).

intros.
unfold exUniq in |- *; intros.
unfold Img in H.
elim
 (axs_comprehension
    (fun v1 : E =>
     fun_ (fun_recip f Af) ->
     exists v0 : E, In (couple v0 v1) (fun_recip f Af))
    (reunion (reunion (fun_recip f Af))) b); intros; 
 generalize (H2 H); clear H H2 H3; intros.
elim H; clear H; intros; generalize (H2 H0); clear H2; intros; elim H2;
 clear H2; intros.
exists x; split; [ auto with zfc | intros ].
unfold fun_recip in H2; unfold fun_recip in H3.
elim
 (axs_comprehension
    (fun c : E =>
     exists x0 : E, (exists y : E, In (couple x0 y) f /\ c = couple y x0))
    (cartesien (Img f) (dom f)) (couple x b)); intros; 
 generalize (H4 H2); clear H2 H4 H5; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E, (exists y0 : E, In (couple x y0) f /\ c = couple y0 x))
    (cartesien (Img f) (dom f)) (couple y b)); intros; 
 generalize (H4 H3); clear H3 H4 H5; intros.
elim H2; clear H2; intros; elim H4; clear H4; intros; elim H4; clear H4;
 intros; elim H4; clear H4; intros.
elim H3; clear H3; intros; elim H6; clear H6; intros; elim H6; clear H6;
 intros; elim H6; clear H6; intros.
elim (lem_couple_propertie x x1 b x0); intros; generalize (H8 H5);
 clear H5 H8 H9; intros; elim H5; clear H5; intros.
elim (lem_couple_propertie y x3 b x2); intros; generalize (H9 H7);
 clear H7 H9 H10; intros; elim H7; clear H7; intros.
generalize H4 H6; clear H4 H6; rewrite <- H8; rewrite <- H9; rewrite <- H5;
 rewrite <- H7; clear H5 H7 H8 H9; intros.
generalize Af; intros.
elim Af0; clear Af0; intros.
exact (H7 b x y H4 H6).

Qed.
(* End of proof of lem_fun_recip_is_bij_under_bij                          *)

(***************************************************************************)
(* Si f est une injection de (dom f) dans (Img f) alors c'est une          *)
(* bijection de (dom f) dans (Img f)                                       *)
(***************************************************************************)
Lemma lem_fun_inj_dom_img_is_bij :
 forall (f : E) (Af : fun_ f),
 fun_inj f (dom f) (Img f) -> fun_bij f (dom f) (Img f).
(* Proof of lem_fun_inj_dom_img_is_bij                                     *)
unfold fun_inj, fun_bij in |- *; intros.
elim H; clear H Af; intros; elim H0; clear H0; intros; clear H0; elim H1;
 clear H1; intros; clear H0.
split;
 [ auto with zfc
 | split; [ reflexivity | split; [ reflexivity | auto with zfc ] ] ].

Qed.
(* End of proof of lem_fun_inj_dom_img_is_bij                              *)

(***************************************************************************)
(* Si f est une bijection alors fun_recip de fun_recip de f est egale a f  *)
(***************************************************************************)
Lemma lem_fun_recip_involutive_under_bij :
 forall (f : E) (Af : fun_ f) (Abijf : fun_bij f (dom f) (Img f))
   (Arec : fun_ (fun_recip f Af)), fun_recip (fun_recip f Af) Arec = f.
(* Proof of lem_fun_recip_involutive_under_bij                             *)
intros; apply axs_extensionnalite; unfold iff in |- *; split; intros.
elim
 (axs_comprehension
    (fun c : E =>
     exists x : E,
       (exists y : E, In (couple x y) (fun_recip f Af) /\ c = couple y x))
    (cartesien (Img (fun_recip f Af)) (dom (fun_recip f Af))) v2); 
 intros.
generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros.
unfold fun_recip in H0.
elim
 (axs_comprehension
    (fun c : E =>
     exists x1 : E, (exists y : E, In (couple x1 y) f /\ c = couple y x1))
    (cartesien (Img f) (dom f)) (couple x x0)); intros; 
 generalize (H2 H0); clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H2; clear H2; intros.
elim (lem_couple_propertie x x2 x0 x1); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros.
generalize H2; clear H2; rewrite <- H3; rewrite <- H4; rewrite <- H1;
 auto with zfc.

generalize Arec; clear Arec; generalize Af; intros.
elim Af; clear Af; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros.
unfold inc in H0.
generalize (H0 v2 H); clear H0; intros.
elim (lem_cartesian_propertie x x0 v2); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros; elim H2; clear H2; intros.
generalize H; rewrite H3; intros.
generalize (lem_xyinf_yxinrecipf f Af0 x1 x2 H4); intros.
exact (lem_xyinf_yxinrecipf (fun_recip f Af0) Arec x2 x1 H5); intros.

Qed.
(* End of proof of lem_fun_recip_involutive_under_bij                      *)

(***************************************************************************)
(***************************************************************************)
(* Exponantiation de a par b                                               *)
(***************************************************************************)
(***************************************************************************)

(***************************************************************************)
(* exp a b est l'ensemble des applications de b dans a                     *)
(***************************************************************************)
Definition exp (a b : E) :=
  subset
    (fun f : E =>
     forall x : E, In x b -> exUniq _ (fun y : E => In (couple x y) f))
    (parties (cartesien b a)).

(***************************************************************************)
(* Si f est un element de (exp a b) alors f est une application de b dans a*)
(***************************************************************************)
Lemma lem_exp_elem_is_fun : forall a b f : E, In f (exp a b) -> fun_ f.
(* Proof of lem_exp_is_fun                                                 *)
intros; unfold fun_ in |- *; split; intros.
unfold exp in H.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall x : E, In x b -> exUniq E (fun y : E => In (couple x y) f0))
    (parties (cartesien b a)) f); intros; generalize (H0 H); 
 clear H H0 H1; intros.
elim H; clear H; intros.
exists b; exists a; unfold inc in |- *; intros.
elim (axs_parties (cartesien b a) f); intros; generalize (H2 H);
 clear H H2 H3; intros.
exact (H v0 H1).

unfold exp in H.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall x : E, In x b -> exUniq E (fun y : E => In (couple x y) f0))
    (parties (cartesien b a)) f); intros; generalize (H2 H); 
 clear H H2 H3; intros.
elim H; clear H; intros.
elim (axs_parties (cartesien b a) f); intros; generalize (H3 H);
 clear H H3 H4; intros.
generalize (H (couple x y) H0); intros.
elim (lem_cartesian_propertie b a (couple x y)); intros; generalize (H4 H3);
 clear H3 H4 H5; intros.
elim H3; clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3;
 intros; elim H4; clear H4; intros.
elim (lem_couple_propertie x x0 y x1); intros; generalize (H6 H5);
 clear H5 H6 H7; intros.
elim H5; clear H5; intros.
generalize H3; clear H3; rewrite <- H5; intros.
generalize (H2 x H3); clear H2 H3; intros.
unfold exUniq in H2.
elim H2; clear H2; intros; elim H2; clear H2; intros.
generalize (H3 y H0); intros.
generalize (H3 z H1); intros.
rewrite <- H7; rewrite <- H8; reflexivity.

Qed.
(* End of proof of lem_exp_is_fun                                          *)

(***************************************************************************)
(* Le domaine d'un element de (exp a b) est b                              *)
(***************************************************************************)
Lemma lem_exp_elem_dom : forall a b f : E, In f (exp a b) -> dom f = b.
(* Proof of lem_exp_elem_dom                                               *)
intros.
generalize (lem_exp_elem_is_fun a b f H); intros; unfold exp in H.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall x : E, In x b -> exUniq E (fun y : E => In (couple x y) f0))
    (parties (cartesien b a)) f); intros; generalize (H1 H); 
 clear H H1 H2; intros.
elim H; clear H; intros.
generalize H; intros.
elim (axs_parties (cartesien b a) f); intros; generalize (H3 H2);
 clear H2 H3 H4; intros.
apply axs_extensionnalite; unfold iff in |- *; split; intros.
generalize (lem_App f v2 H0 H3); intros.
elim H4; clear H4; intros; elim H4; clear H4; intros.
generalize (H2 (couple v2 x) H5); clear H2 H5; intros.
elim (lem_cartesian_propertie b a (couple v2 x)); intros; generalize (H5 H2);
 clear H2 H5 H6; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros; elim H5; clear H5; intros.
elim (lem_couple_propertie v2 x0 x x1); intros; generalize (H7 H6);
 clear H6 H7 H8; intros.
elim H6; clear H6; intros.
rewrite H6; auto with zfc.

generalize (H1 v2 H3); clear H1 H3; intros.
unfold exUniq in H1.
elim H1; clear H1; intros; elim H1; clear H1; intros.
exact (lem_fun_and_dom f v2 x H0 H1).

Qed.
(* End of proof of lem_exp_elem_dom                                        *)

(***************************************************************************)
(* L'image d'un element de (exp a b) est incluse dans a                    *)
(***************************************************************************)
Lemma lem_exp_elem_img : forall a b f : E, In f (exp a b) -> inc (Img f) a.
(* Proof of lem_exp_elem_img                                               *)
intros; unfold inc in |- *; intros.
generalize (lem_exp_elem_is_fun a b f H); intros.
unfold exp in H.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall x : E, In x b -> exUniq E (fun y : E => In (couple x y) f0))
    (parties (cartesien b a)) f); intros; generalize (H2 H); 
 clear H H2 H3; intros.
elim H; clear H; intros.
elim (axs_parties (cartesien b a) f); intros; generalize (H3 H);
 clear H H3 H4; intros.
generalize (lem_App_rev f v0 H1 H0); intros.
elim H3; clear H3; intros; elim H3; clear H3; intros.
generalize (H (couple x v0) H4); clear H H4; intros.
elim (lem_cartesian_propertie b a (couple x v0)); intros; generalize (H4 H);
 clear H H4 H5; intros.
elim H; clear H; intros; elim H; clear H; intros; elim H; clear H; intros;
 elim H4; clear H4; intros.
elim (lem_couple_propertie x x0 v0 x1); intros; generalize (H6 H5);
 clear H5 H6 H7; intros.
elim H5; clear H5; intros.
rewrite H6; auto with zfc.

Qed.
(* End of proof of lem_exp_elem_img                                        *)

(***************************************************************************)
(* La conclusion: les elements de (exp a b) sont les applications de b     *)
(* dans a                                                                  *)
(***************************************************************************)
Lemma lem_exp_elem_prop : forall a b f : E, In f (exp a b) -> fun_sig f b a.
(* Proof of lem_exp_elem_prop                                              *)
intros.
generalize (lem_exp_elem_is_fun a b f H); intros.
generalize (lem_exp_elem_dom a b f H); intros.
generalize (lem_exp_elem_img a b f H); intros.
unfold fun_sig in |- *.
split; [ auto with zfc | split; auto with zfc ].

Qed.
(* End of proof of lem_exp_elem_prop                                       *)

(***************************************************************************)
(* Un lemme a la xxx: si f est une application et que c est un element de  *)
(* f alors il existe x et y tel que c=(x,y)                                *)
(***************************************************************************)
Lemma lem_fun_elem_is_2tupple :
 forall (f : E) (Af : fun_ f) (c : E),
 In c f -> exists x : E, (exists y : E, In (couple x y) f /\ c = couple x y).
(* Proof of lem_fun_elem_is_2tupple                                        *)
intros.
elim Af; clear Af; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros.
unfold inc in H0.
generalize (H0 c H); clear H0; intros.
elim (lem_cartesian_propertie x x0 c); intros; generalize (H2 H0);
 clear H0 H2 H3; intros.
elim H0; clear H0; intros; elim H0; clear H0; intros; elim H0; clear H0;
 intros.
elim H2; clear H2; intros.
exists x1; exists x2; rewrite <- H3; split;
 [ auto with zfc | reflexivity ].

Qed.
(* End of proof of lem_fun_elem_is_2tupple                                 *)

(***************************************************************************)
(* La reciproque : Si f est une application de b dans a alors f est un     *)
(* element de (exp a b).                                                   *)
(***************************************************************************)
Lemma lem_exp_elem_prop_recip :
 forall a b f : E, fun_sig f b a -> In f (exp a b).
(* Proof of lem_exp_elem_prop_recip                                        *)
unfold fun_sig in |- *; intros.
elim H; clear H; intros; elim H0; clear H0; intros.
unfold exp in |- *.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall x : E, In x b -> exUniq E (fun y : E => In (couple x y) f0))
    (parties (cartesien b a)) f); intros; apply H3; 
 clear H2 H3; intros.
split; intros.
elim (axs_parties (cartesien b a) f); intros; apply H3; clear H2 H3; intros.
generalize (lem_fun_elem_is_2tupple f H v3 H2); clear H2; intros.
elim H2; clear H2; intros; elim H2; clear H2; intros; elim H2; clear H2;
 intros.
generalize (lem_fun_and_dom f x x0 H H2); intros.
generalize (lem_fun_and_img f x x0 H H2); intros.
elim (lem_cartesian_propertie b a v3); intros; apply H7; clear H6 H7; intros.
exists x; exists x0; split.
rewrite <- H0; auto with zfc.

unfold inc in H1; generalize (H1 x0 H5); clear H1 H5; intros.
split; auto with zfc.

unfold exUniq in |- *; intros.
generalize H2; clear H2; rewrite <- H0; intros.
generalize (lem_App f x H H2); intros.
elim H3; clear H3; intros; elim H3; clear H3; intros.
exists x0; split; [ auto with zfc | intros ].
elim H; intros.
exact (H7 x x0 y H4 H5).

Qed.
(* End of proof of lem_exp_elem_prop_recip                                 *)

(***************************************************************************)
(***************************************************************************)
(* Famille d'ensembles indexee                                             *)
(***************************************************************************)
(***************************************************************************)
Definition index (a I : E) (funa : fun_ a) (doma : dom a = I) :=
  subset (fun x : E => True) (Img a).

Lemma lem_index_prop :
 forall (a I : E) (funa : fun_ a) (doma : dom a = I),
 index a I funa doma = Img a.
(* Proof of lem_index_prop                                                 *)
intros; apply axs_extensionnalite; intros; unfold iff in |- *; split; intros.
unfold index in H.
elim (axs_comprehension (fun _ : E => True) (Img a) v2); intros;
 generalize (H0 H); clear H H0 H1; intros; elim H; 
 clear H; intros; auto with zfc.

unfold index in |- *.
elim (axs_comprehension (fun _ : E => True) (Img a) v2); intros; apply H1;
 clear H0 H1; intros.
split; auto with zfc.

Qed.
(* End of proof of lem_index_prop                                          *)

Lemma lem_reunion_index_prop :
 forall (a I : E) (funa : fun_ a) (doma : dom a = I) (x : E),
 In x (reunion (index a I funa doma)) ->
 exists i : E, In i I /\ In x (App a funa i).
(* Proof of lem_reunion_index_prop                                         *)
intros.
generalize (lem_index_prop a I funa doma); intros.
generalize H; rewrite H0; clear H H0; intros.
elim (axs_reunion (Img a) x); intros; generalize (H0 H); clear H H0 H1;
 intros.
elim H; clear H; intros; elim H; clear H; intros.
generalize (lem_App_rev a x0 funa H); intros.
elim H1; clear H1; intros; elim H1; clear H1; intros.
generalize H1; clear H1; rewrite doma; intros.
generalize (lem_eval_propertie a x1 x0 funa H2); intros.
generalize H0; clear H0; rewrite H3; clear H3; intros.
exists x1; split; auto with zfc.

Qed.
(* End of proof of lem_reunion_index_prop                                  *)

Lemma lem_index_inter :
 forall (a I : E) (funa : fun_ a) (doma : dom a = I) 
   (Ine : I <> Vide) (x : E) (indNe : index a I funa doma <> Vide),
 In x (Einter (index a I funa doma) indNe) ->
 forall i : E, In i I -> In x (App a funa i).
(* Proof of lem_index_inter                                                *)
intros.
unfold App in |- *.
elim
 (axs_comprehension (fun z : E => exists y : E, In (couple i y) a /\ In z y)
    (reunion (Img a)) x); intros; apply H2; clear H1 H2; 
 intros.
unfold Einter in H.
elim
 (axs_comprehension
    (fun v0 : E => forall v3 : E, In v3 (index a I funa doma) -> In v0 v3)
    (reunion (index a I funa doma)) x); intros; generalize (H1 H);
 clear H H1 H2; intros.
elim H; clear H; intros.
generalize H; clear H; rewrite (lem_index_prop a I funa doma); intros.
split; [ auto with zfc | exists (App a funa i); split ].
generalize H0; rewrite <- doma; intros.
generalize (lem_App a i funa H2); intros.
elim H3; clear H3; intros; elim H3; clear H3; intros.
generalize (lem_eval_propertie a i x0 funa H4); intros.
rewrite <- H5; auto with zfc.

apply (H1 (App a funa i)); clear H1; intros.
unfold index in |- *.
elim (axs_comprehension (fun _ : E => True) (Img a) (App a funa i)); intros;
 apply H2; clear H1 H2; intros.
split; [ idtac | auto with zfc ].
generalize H0; rewrite <- doma; intros.
generalize (lem_eval_prop2 a i funa H1); intros.
exact (lem_fun_and_img a i (App a funa i) funa H2).

Qed.
(* End of proof of lem_index_inter                                         *)

(***************************************************************************)
(***************************************************************************)
(* Produit d'une famille d'ensembles                                       *)
(***************************************************************************)
(***************************************************************************)
Definition produit (a I : E) (funa : fun_ a) (doma : dom a = I) :=
  subset
    (fun f : E =>
     forall i : E,
     In i I ->
     exUniq _ (fun y : E => In (couple i y) f /\ In y (App a funa i)))
    (exp (reunion (index a I funa doma)) I).

Lemma lem_f_in_prod_is_fun :
 forall (a I : E) (funa : fun_ a) (doma : dom a = I) (f : E),
 In f (produit a I funa doma) -> fun_ f.
(* Proof of lem_f_in_prod_is_fun                                           *)
unfold produit in |- *; intros.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall i : E,
     In i I ->
     exUniq E (fun y : E => In (couple i y) f0 /\ In y (App a funa i)))
    (exp (reunion (index a I funa doma)) I) f); intros; 
 generalize (H0 H); clear H H0 H1; intros.
elim H; clear H; intros.
exact (lem_exp_elem_is_fun (reunion (index a I funa doma)) I f H).

Qed.
(* End of proof of lem_f_in_prod_is_fun                                    *)

Lemma lem_dom_of_f_in_prod_is_I :
 forall (a I : E) (funa : fun_ a) (doma : dom a = I) (f : E),
 In f (produit a I funa doma) -> dom f = I.
(* Proof of lem_dom_of_f_in_prod_is_I                                      *)
intros.
generalize (lem_f_in_prod_is_fun a I funa doma f H); intros.
unfold produit in H.
elim
 (axs_comprehension
    (fun f0 : E =>
     forall i : E,
     In i I ->
     exUniq E (fun y : E => In (couple i y) f0 /\ In y (App a funa i)))
    (exp (reunion (index a I funa doma)) I) f); intros; 
 generalize (H1 H); clear H H1 H2; intros.
elim H; clear H; intros.
exact (lem_exp_elem_dom (reunion (index a I funa doma)) I f H).

Qed.
(* End of proof of lem_dom_of_f_in_prod_is_I                               *)

(***************************************************************************)
(*                         Next : axs_choice.v                             *)
(***************************************************************************)