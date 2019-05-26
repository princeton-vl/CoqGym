Require Import Div2 Bool Even Setoid Min List Aux Field VectorSpace Grassmann.
Require Import Field_tac.

Section Vect.

(* Our Field *)
Variable F: fparams.

Hypothesis FT:
  @field_theory (Field.K F) (v0 F) (v1 F) (addK F) (multK F)
        (fun x y => (addK F) x (oppK F y)) (oppK F) 
        (fun x y => (multK F) x (invK F y)) (invK F) (@Logic.eq F).
Add Field Kfth : FT.


(******************************************************************************)
(*   Instanciation of Grassman for n = 3                                      *)
(******************************************************************************)

Definition Pp: params :=  {| dim := 3; K := F |}.
Variable HP : fparamsProp Pp.

SubClass point := Kn Pp.
SubClass vect := Vect Pp.

Definition Vjoin (x y : vect): vect := Vjoin Pp x y.
Notation "x '∨' y" := (Vjoin x y) (at level 40, left associativity).
Definition Vadd (x y : vect): vect := Vadd Pp x y.
Notation "x + y" := (Vadd x y).
Definition Vsub (x y : vect): vect := sub Pp Pp x y.
Notation "x - y" := (Vsub x y).
Definition Vscal (k : F) (x : vect): vect := Vscal Pp k x.
Notation "k .* x" := (Vscal k x).
Definition Vmeet (x y : vect): vect := Vmeet Pp x y.
Notation "x '∧' y" := (Vmeet x y) (at level 45, left associativity).
Definition Vdual (x : vect): vect := Vdual Pp x.
Notation "'@  x" := (Vdual x) (at level 9).
Definition Veq (x y : vect): bool := Veq Pp x y.
Notation "x ?= y" := (Veq x y).
Definition Vgenk (k : F): vect := (Vgenk Pp k).
Notation "0" := (Vgenk 0%f).
Notation "1" := (Vgenk 1%f).
Definition hom (n: nat) (x : vect) := (hom Pp Pp n x).
Notation "'dC[ x ]" := (dconst Pp 3 x).
Notation "'C[ x ]" := (const Pp 3 x).
Notation "'E'" := (all Pp 3: vect).

Coercion p2v (x : point) := (K2G Pp x): vect.

Let scal0l x : 0%f .*  x = 0.
Proof. apply (scalE0l _ (fn _ HP 3)). Qed.

Let scal1l x : 1%f .*  x = x.
Proof. apply (scalE1 _ (fn _ HP 3)). Qed.

Let scal_integral k x : k .* x = 0 -> {k = 0%f} + {x = 0}.
Proof. apply (scalE_integral _ (fn _ HP 3)). Qed.

Lemma sub_add x y : x - y = x + (-(1))%f .* y.
Proof. apply (@sub_add _ HP 3). Qed.

Lemma join1l x : 1 ∨ x = x.
Proof. apply (join1l _ HP). Qed.

Lemma join1r x : x ∨ 1 = x.
Proof. apply (join1r _ HP). Qed.

Lemma join_addl x y z : (x + y) ∨ z = x ∨ z + y ∨ z.
Proof. apply (@join_addl _ HP 3). Qed.

Lemma join_addr x y z : z ∨ (x + y) = z ∨ x + z ∨ y.
Proof. apply (@join_addr _ HP 3). Qed.

Lemma join_scall k x y : k .* x ∨ y = k .* (x ∨ y).
Proof. apply (@join_scall _ HP 3). Qed.

Lemma join_scalr k x y : x ∨ (k .* y) = k .* (x ∨ y).
Proof. apply (@join_scalr _ HP 3). Qed.

Theorem join_swap (x y : point) : x ∨ y = (-(1))%f .* (y ∨ x).
Proof.
replace ((-(1))%f: F) with (((-(1))^(1 * 1))%f: F) .
apply (join_hom_com _ HP 3); apply k2g_hom; auto.
simpl expK; Krm1.
Qed.

Let join_id: forall (x : point), x ∨ x = 0.
Proof.
intros x.
apply join_hom1_id; auto.
destruct x as (x1,(x2,(x3,u))); simpl; Krm0; rewrite eqKI; auto.
Qed.

Let add_com x y : x + y = y + x.
Proof. apply (addE_com _ (fn _ HP 3)). Qed.

Let add_assoc x y z : x + y + z = x + (y + z).
Proof. apply (addE_assoc _ (fn _ HP 3)). Qed.

Let add0l x : 0 + x = x.
Proof. apply (addE0l _ (fn _ HP 3)). Qed.

Let add0r x : x + 0 = x.
Proof. apply (addE0r _ (fn _ HP 3)). Qed.

Let scal_mul k1 k2 x : (k1 * k2)%f .* x = k1.* (k2 .* x).
Proof. apply (scal_multE _ (fn _ HP 3)). Qed.

Let scal0r k : k .*  0 = 0.
Proof. apply (scalE0r _ (fn _ HP 3)). Qed.

Let join0r x : x ∨ 0 = 0.
Proof. apply (join0r _ HP). Qed.

Let join0l x : 0 ∨ x = 0.
Proof. apply (join0l _ HP). Qed.

Let join_assoc x y z : (x ∨ y) ∨ z =  x ∨ (y ∨ z).
Proof. apply (join_assoc _ HP). Qed.

Let scal_addl k1 k2 x : (k1 + k2)%f .* x = k1.* x + (k2 .* x).
Proof. apply (scal_addEl _ (fn _ HP 3)). Qed.

Let scal_addr k x y : k .* (x + y) = k.* x + (k .* y).
Proof. apply (scal_addEr _ (fn _ HP 3)). Qed.

Let scal_mult k1 k2 x : (k1 * k2)%f .* x = k1 .* (k2 .* x).
Proof. apply (scal_multE _ (fn _ HP 3)). Qed.

Let meet_assoc x y z : (x ∧ y) ∧ z =  x ∧ (y ∧ z).
Proof. apply (meet_assoc _ HP). Qed.

Let meet_alll x : (E ∧ x) = x.
Proof. apply (meet_alll _ HP). Qed.

Let meet_allr x : (x ∧ E) = x.
Proof. apply (meet_allr _ HP). Qed.

Lemma meet_scall k x y : k .* x ∧ y = k .* (x ∧ y).
Proof. apply (@meet_scall _ HP 3). Qed.

Lemma meet_scalr k x y : x ∧ k .* y = k .* (x ∧ y).
Proof. apply (@meet_scalr _ HP 3). Qed.

Lemma meet_addr x y z : z ∧ (x + y) = z ∧ x + z ∧ y.
Proof. apply (@meet_addr _ HP 3). Qed.

Lemma meet_addl x y z : (x + y) ∧ z = x ∧ z + y ∧ z.
Proof. apply (@meet_addl _ HP 3). Qed.

Lemma hom3_1 k1 k2 x y : hom k1 x -> hom k2 y -> 3 = (k1 + k2)%nat -> 
   x ∧ y = 'dC[ x ∨ y] .* 1.
Proof. apply (@homn_1 _ HP 3 k1 k2). Qed. 

Lemma splitrr k1 k2 x y z : hom k1 x -> hom 1 y ->  hom k2 z ->
  z ∧ (x ∨ y) = ((-(1))^(3 + k2.+1))%f .* ((z ∨ y) ∧ x - (z ∧ x) ∨ y).
Proof. apply (@splitrr _ HP 3 k1 k2). Qed.

Lemma dual_invoE k v: hom k v ->  v = ((-(1)) ^(k * 3.+1))%f .* '@('@v).
Proof. apply (@dual_invoE _ HP 3). Qed.

Lemma meet_join_distrl k1 k2 x y z : hom k1 x -> hom 1 y ->  hom k2 z ->
  '@y ∧ (x ∨ z) = ((-(1))^k2)%f .* (('@y ∧ x) ∨ z)  +  x ∨ ('@y ∧ z).
Proof. apply (@meet_join_distrl _ HP 3 k1 k2). Qed.

Lemma const1 x : 'C[x .* 1] = x.
Proof.
rewrite const_scal, constk; Krm1.
Qed.


(******************************************************************************)
(*   Definition of the bracket operator                                       *)
(******************************************************************************)

Definition bracket x y z : F := 'dC[x ∨ y ∨ z].

Notation "'E'" := (all Pp 3: vect).
Notation "'[ x , y , z ]" := (bracket x y z).

(******************************************************************************)
(* A tactic to prove homogeneity                                              *)
(******************************************************************************)

Lemma hom3E: hom 3 E.
Proof. apply all_hom; auto. Qed.

Lemma hom3l x y : hom 1 x -> hom 2 y -> hom 3 (x ∨ y).
Proof. change 3 with (1 + 2)%nat; apply join_hom; auto. Qed.

Lemma hom3r x y : hom 2 x -> hom 1 y -> hom 3 (x ∨ y).
Proof. change 3 with (2 + 1)%nat; apply join_hom; auto. Qed.

Lemma hom2 x y : hom 1 x -> hom 1 y -> hom 2 (x ∨ y).
Proof. change 2 with (1 + 1)%nat; apply join_hom; auto. Qed.

Lemma hom1p (x : point) : hom 1 x.
Proof. apply k2g_hom; auto. Qed.

Lemma hom1d x y : hom 2 x -> hom 2 y -> hom 1 (x ∧ y).
Proof.
change 1%nat with (2 + 2 - 3)%nat; apply meet_hom; auto.
Qed.

Lemma hom0l x y : hom 1 x -> hom 2 y -> hom 0 (x ∧ y).
Proof.
change 0%nat with (1 + 2 - 3)%nat; apply meet_hom; auto.
Qed.

Lemma hom0r x y : hom 2 x -> hom 1 y -> hom 0 (x ∧ y).
Proof.
change 0%nat with (2 + 1 - 3)%nat; apply meet_hom; auto.
Qed.

Lemma hom0p x y : hom 0 x -> hom 0 y -> hom 0 (x ∨ y).
Proof.
change 0%nat with (0 + 0)%nat; apply join_hom; auto.
Qed.

Lemma hom01 : hom 0 1.
Proof. apply hom0K; auto. Qed.

Lemma hom0_E x : hom 0 x -> x ∨ E = 0 -> x = 0.
Proof.
intros H; rewrite (hom0E _ HP 3 _ H).
rewrite (joinkl _ HP 3); intros H1.
case (scal_integral _ _ H1); auto.
intros H3; rewrite H3; auto.
intros H2; injection H2; intros HH.
case (one_diff_zero _ HP); auto.
Qed.

Lemma homd k x : hom k x -> hom (3 - k) '@x.
Proof. apply (dual_hom _ HP 3). Qed.

Ltac homt :=
  first [ apply scal_hom; auto; homt | 
          apply add_hom; auto; homt  |
          apply hom3E                 |
          apply hom3l; homt           |
          apply hom3r; homt           |
          apply hom2; homt            |
          apply hom1p                 |
          apply hom1d; homt           |
          apply hom0l; homt           |
          apply hom0r; homt           |
          apply hom0p; homt           |
          apply hom01                 |
          apply homd
   ].

Ltac hom3t :=  
  apply proj_homn_eq; auto; try homt.

Ltac hom0t := 
  apply proj_hom0_eq; auto; try homt. 

(******************************************************************************)
(*   Some properties of the bracket operator                                  *)
(******************************************************************************)


Lemma bracket_defE (x y z : point) :
  x ∨ y ∨ z =  '[x,y,z] .* E.
Proof. apply homn_all; auto; homt. Qed.

Lemma bracket_defl (x y z : point) :
  x ∧ (y ∨ z) = '[x, y, z] .* 1.
Proof. 
rewrite hom3_1  with (k1 := 1%nat) (k2 := 2); try homt; auto.
rewrite <-join_assoc; auto.
Qed.

Lemma bracket_defr (x y z : point) :
  (x ∨ y) ∧ z = '[x, y, z] .* 1.
Proof. 
rewrite hom3_1  with (k1 := 2) (k2 := 1%nat); try homt; auto.
Qed.

Lemma bracket0l (a b: point) : '[a,a,b] = 0%f.
Proof. 
unfold bracket; rewrite join_id, join0l, dconst0; auto.
Qed.

Lemma bracket0m (a b: point) : '[a,b,a] = 0%f.
Proof. 
unfold bracket; rewrite join_swap, join_scall, join_assoc.
rewrite join_id, join0r, scal0r, dconst0; auto.
Qed.

Lemma bracket0r (a b: point) : '[a,b,b] = 0%f.
Proof.
unfold bracket.
rewrite join_assoc, join_id, join0r, dconst0; auto.
Qed.

Lemma bracket_swapl (x y z : point) : '[y,x,z] = (- ('[x,y,z]))%f.
Proof. 
unfold bracket; rewrite join_swap, join_scall.
rewrite dconst_scal; Krm1.
Qed.

Lemma bracket_swapr (x y z : point) : '[x,z,y] = (- ('[x,y,z]))%f.
Proof. 
unfold bracket; rewrite join_assoc, (join_swap z), join_scalr.
rewrite join_assoc, dconst_scal; Krm1.
Qed.

Lemma bracket_norm (a b c: point) : 
  ('[a,c,b] =  (-(1)) * '[a,b,c] /\
  '[b,a,c] = (-(1))%f * '[a,b,c] /\
  '[b,c,a] = '[a,b,c] /\
  '[c,a,b] = '[a,b,c] /\
  '[c,b,a] = (-(1))%f * '[a,b,c])%f.
Proof. 
repeat split.
rewrite bracket_swapr; Krm1.
rewrite bracket_swapl; Krm1.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite bracket_swapl, bracket_swapr, bracket_swapl; Krm1.
Qed.

(* A tactic to normalize one specific bracket *)
Ltac normb a b c :=
 generalize (bracket_norm a b c); 
 intros (Hn1, (Hn2, (Hn3, (Hn4, Hn5))));
 rewrite ?Hn1, ?Hn2, ?Hn3, ?Hn4, ?Hn5;
 clear Hn1 Hn2 Hn3 Hn4 Hn5.

Definition fbracket a b c:= '[a, b, c].

Lemma fbracket_norm (a b c: point) : 
  ('[a,b,c] =  fbracket a b c /\
  '[a,c,b] =  (-(1)) *  (fbracket a b c) /\
  '[b,a,c] = (-(1))%f * (fbracket a b c) /\
  '[b,c,a] = (fbracket a b c) /\
  '[c,a,b] = (fbracket a b c) /\
  '[c,b,a] = (-(1))%f * (fbracket a b c))%f.
Proof.
generalize (bracket_norm a b c).
intros (H1, (H2, (H3, (H4, H5)))); repeat split; auto.
Qed.

(* A tactic to globally normalize brackets *)
Ltac normbs :=
repeat match goal with |- context['[p2v ?a,p2v ?b,p2v ?c]] =>
 generalize (fbracket_norm a b c); 
 intros (Hn1, (Hn2, (Hn3, (Hn4, (Hn5, Hn6)))));
 rewrite ?Hn1, ?Hn2, ?Hn3, ?Hn4, ?Hn5, ?Hn6;
 clear Hn1 Hn2 Hn3 Hn4 Hn5 Hn6
end; unfold fbracket.

(******************************************************************************)
(*   Some distributivity rules                                                *)
(******************************************************************************)

Lemma expand_meetr (x y x1 y1: point) :
(x ∨ y1) ∧ (x1 ∨ y) = '[x,y1,y] .* x1 - '[x,y1,x1] .* y.
Proof.
assert (F1: x ∨ y1 = '@('@(x ∨ y1))).
  generalize (dual_invoE 2 (x ∨ y1)); simpl expK; Krm1.
  rewrite scal1l; intros HH; apply HH; homt.
rewrite F1, (meet_join_distrl 1 1), <-F1, !bracket_defr; try homt.
rewrite join_scall, join1l, join_scalr, join1r, add_com, sub_add; auto.
simpl expK; Krm1.
change 1%nat with (3 - 2)%nat; repeat homt.
Qed.

Lemma meet_swap (x y x1 y1: point) :
  (x ∨ y1) ∧ (x1 ∨ y) =  (-(1))%f .* (x1 ∨ y) ∧ (x ∨ y1).
Proof.
assert (F1: hom 2 (x ∨ y1)) by homt.
assert (F2: hom 2 (x1 ∨ y)) by homt.
apply trans_equal with 
  ((((- (1)) ^ ((3 + 2) * (3 + 2)))%f .* ((x1 ∨ y) ∧ (x ∨ y1)))).
refine (meet_hom_com _ HP _ _ _ _ _ _ _); auto.
change ((3 + 2) * (3 + 2))%nat with (2 * 12 + 1)%nat.
rewrite meet_scall, expKm1_2E; simpl expK; Krm1.
Qed.

Lemma expand_meetl (x y x1 y1: point) :
  (x1 ∨ y) ∧ (x ∨ y1) = '[x,y1,x1] .* y - '[x,y1,y] .* x1.
Proof.
rewrite meet_swap, meet_scall, expand_meetr.
rewrite !sub_add, scal_addr, <-!scal_mul, add_com; Krm1.
Qed.

Lemma split_meetl (x1 x2 x3 x4 x5 x6: point) :
  (x1 ∨ x2) ∧ (x3 ∨ x4) ∧ (x5 ∨ x6) =
     (x1 ∧ (x3 ∨ x4)) ∨ (x2 ∧ (x5 ∨ x6)) +
     (-(1))%f .*  ((x2 ∧ (x3 ∨ x4)) ∨ (x1 ∧ (x5 ∨ x6))).
rewrite expand_meetl.
rewrite sub_add, meet_addl.
rewrite !meet_scall.
pattern (x2 ∧ x5 ∨ x6) at 1; rewrite <- join1l.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite <-join_scall, <-bracket_defl.
pattern (x1 ∧ x5 ∨ x6) at 1; rewrite <- join1l.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite <-join_scall, <-bracket_defl; auto.
Qed.

Lemma split_meetr (x1 x2 x3 x4 x5 x6: point) :
  ((x1 ∨ x2) ∧ (x3 ∨ x4)) ∧ (x5 ∨ x6) =
     ((x1 ∨ x2) ∧ x5) ∨ ((x3 ∨ x4) ∧ x6) +
     (-(1))%f .* ((x3 ∨ x4) ∧ x5) ∨ ((x1 ∨ x2) ∧ x6).
Proof.
rewrite meet_assoc.
rewrite expand_meetr.
rewrite sub_add, meet_addr.
rewrite !meet_scalr.
pattern (x1 ∨ x2 ∧ x5) at 1; rewrite <- join1r.
rewrite <-join_scalr, <-bracket_defr.
pattern (x1 ∨ x2 ∧ x6) at 1; rewrite <- join1l.
rewrite <-join_scall, <-bracket_defr.
rewrite <-join_scall; auto.
Qed.

Lemma meet_swapr (x y x1 y1: point) :
  (x ∨ x1) ∧ (y ∨ y1) = (x1 ∨ x) ∧ (y1 ∨ y).
Proof. 
rewrite join_swap, (join_swap y).
rewrite meet_scall, meet_scalr, <-scal_mul; Krm1.
Qed.

Lemma join_meet3l (a b c d e f: point) :
  (a ∨ b) ∨ ((c ∨ d) ∧ (e ∨ f)) = ((a ∨ b) ∧ (c ∨ d) ∧ (e ∨ f)) ∨ E.
Proof.
assert (H: exists a': point, (c ∨ d) ∧ (e ∨ f) = a').
apply hom1E; auto; homt.
rewrite meet_assoc.
case H; intros a' Ha'; rewrite Ha'.
rewrite bracket_defr, join_scall, join1l, <-bracket_defE; auto.
Qed.

Lemma join_meet3r (a b c d e f: point) :
  ((a ∨ b) ∧ (c ∨ d)) ∨ (e ∨ f) = ((a ∨ b) ∧ (c ∨ d) ∧ (e ∨ f)) ∨ E.
Proof.
assert (H: exists a': point, (a ∨ b) ∧ (c ∨ d) = a').
apply hom1E; auto; homt.
case H; intros a' Ha'; rewrite Ha', bracket_defl, join_scall.
rewrite join1l, <-bracket_defE, join_assoc; auto.
Qed.

Lemma split3l (a b c d : point) :
  (a ∨ b ∨ c) ∧  d = '[b,c,d] .* a - '[a,c,d] .* b + '[a,b,d] .* c.
Proof.
apply trans_equal with
    (((-(1))^(3 + 1.+1))%f .* (((b ∨ c)  ∧ (a ∨ d)) - a ∨ ((b ∨ c) ∧ d))).
rewrite join_assoc.
apply splitll with (k1 := 2%nat); auto; try apply k2g_hom; auto.
change 2 with (1 + 1)%nat; apply join_hom; auto; apply k2g_hom; auto.
rewrite expand_meetl.
change (3 + 2)%nat with (2*2 + 1)%nat.
rewrite expKm1_2E; simpl expK; Krm1.
rewrite bracket_swapr, (bracket_swapr a c d); Krm1.
rewrite bracket_defr, join_scalr, join1r.
rewrite !sub_add, !scal_addr.
rewrite add_com, add_assoc.
apply f_equal2 with (f := Vadd).
rewrite <-scal_mult; Krm1.
rewrite add_com.
apply f_equal2 with (f := Vadd).
rewrite <-!scal_mult; Krm1.
rewrite <-!scal_mult; Krm1.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                         Some plucker relations                            *)
(*                                                                           *)
(*****************************************************************************)
         
Lemma split3b (a b c d e f : point) :
  ('[a,b,c] * '[d,e,f] = 
   '[b,c,d] * '[a,e,f] + (-(1)) * '[a,c,d] * '[b,e,f] + '[a,b,d] * '[c,e,f])%f.
Proof.
rewrite <-const1; apply sym_equal; rewrite <-const1; apply sym_equal.
apply f_equal with (f := const Pp 3).
apply sym_equal; rewrite <-meet_alll; apply sym_equal.
rewrite scal_mult, meet_scalr, <-meet_scall.
rewrite <-bracket_defE, <-bracket_defl, <-meet_assoc.
rewrite split3l, sub_add, !meet_addl, !meet_scall.
rewrite !bracket_defl, <-!scal_mult, !scal_addl; auto.
Qed.

Lemma split3b_v1 (a b c d e f : point) :
  ('[a,b,c] * '[d,e,f] = 
   '[a,d,e] * '[b,c,f] + (-(1)) * '[a,d,f] * '[b,c,e] + '[a,e,f] * '[b,c,d])%f.
Proof.
rewrite multK_com, split3b; auto.
rewrite addK_com, !addK_assoc; auto.
apply f_equal2 with (f := @addK F); auto.
rewrite bracket_swapr, bracket_swapl; Krm1.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite addK_com; auto.
apply f_equal2 with (f := @addK F); auto.
apply f_equal2 with (f := @multK F); auto.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite bracket_swapl, bracket_swapr; Krm1.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite bracket_swapl, bracket_swapr; Krm1.
Qed.

Lemma split3b_v2 (a b c d e f : point) :
  ('[a,b,c] * '[d,e,f] = 
   '[a,b,d] * '[c,e,f] + (-(1)) * '[a,b,e] * '[c,d,f] + '[a,b,f] * '[c,d,e])%f.
Proof.
replace ('[a,b,c]) with ('[c,a,b]).
2: rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite multK_com, split3b; auto.
rewrite !addK_assoc; auto.
apply f_equal2 with (f := @addK F); auto.
rewrite multK_com; auto.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite bracket_swapr, bracket_swapl; Krm1.
apply f_equal2 with (f := @addK F); auto.
rewrite !multK_assoc; auto.
apply f_equal2 with (f := @multK F); auto.
rewrite multK_com; auto.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite bracket_swapr, bracket_swapl; Krm1.
rewrite multK_com; auto.
apply f_equal2 with (f := @multK F); auto.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite bracket_swapr, bracket_swapl; Krm1.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                         Expansions                                        *)
(*                                                                           *)
(*****************************************************************************)

Lemma bracket_expand (x a b c d a1 b1: point) :
 x = (a ∨ b) ∧ (c ∨ d) :> vect ->
 ('[x, a1, b1] =
   (-(1)) * '[a, a1, b1] * '[b, c, d]  + '[b, a1, b1] * '[a, c, d])%f.
Proof.
intros H.
apply sym_equal; rewrite <-const1; apply sym_equal.
rewrite <-bracket_defl, H.
rewrite split_meetl.
rewrite !const_add, !const_scal, !const_join.
rewrite !bracket_defl, !const1.
rewrite addK_com; auto.
rewrite (fun x => multK_com _ x '[b, c, d]); auto.
rewrite (fun x => multK_com _ x '[b, a1, b1]); auto.
rewrite multK_assoc; auto.
Qed.

Lemma bracket_free (x : point) k1 (a: point) k2 (b a1 b1: point) :
 x = k1 .* a + k2 .* b :> vect ->
 '[x, a1, b1] =
   (k1 * '[a, a1, b1] + k2 * '[b, a1, b1] )%f.
Proof.
intros H.
apply sym_equal; rewrite <-const1; apply sym_equal.
rewrite <-bracket_defl, H.
rewrite meet_addl, const_add, !meet_scall, !const_scal.
rewrite !bracket_defl, !const1; auto.
Qed.

(******************************************************************************)
(*    Contraction                                                             *)
(******************************************************************************)

Lemma contraction_v0  (a b c d e: point) :
  ('[a, b, c] * '[a, d, e] + -(1) * '[a, b, e] * '[a, d, c] =
   '[a, b, d] * '[a, c, e])%f.
Proof.
rewrite split3b_v2.
rewrite bracket0m; Krm0.
rewrite !(bracket_swapl a c), (bracket_swapr a c d); ring.
Qed.

Lemma contraction_v1  (a b c d e: point) :
  ('[a, b, c] * '[b, d, e] + -(1) * '[a, b, e] * '[b, d, c] =
   '[a, b, d] * '[b, c, e])%f.
Proof.
rewrite multK_com, split3b_v2; auto.
rewrite bracket0m; Krm0.
rewrite !multK_assoc, (multK_com _ HP '[a, b, e]); auto.
rewrite (bracket_swapr b a d).
rewrite (bracket_swapl b a d).
rewrite (bracket_swapl b e c).
rewrite (bracket_swapr b c e).
rewrite (bracket_swapl a e b).
rewrite (bracket_swapr  a b e).
simpl.
ring.
Qed.

Lemma contraction_v2  (a b c d e: point) :
  ('[a, b, c] * '[d, b, e] + - (1) * '[a, b, e] * '[d, b, c] =
   '[b, a, d] * '[b, c, e])%f.
Proof.
rewrite split3b_v2; auto.
rewrite bracket0r; Krm0.
rewrite (bracket_swapl b a d).
rewrite (bracket_swapl c b e).
rewrite (bracket_swapl d c b).
rewrite (bracket_swapr d b c).
simpl; ring.
Qed.

Lemma contraction_v3  (a b c d e: point) :
  ('[a, b, c] * '[d, a, e] + - (1) * '[a, b, e] * '[d, a, c] =
   '[a, b, d] * '[c, a, e])%f.
Proof.
rewrite split3b_v2.
rewrite bracket0m; Krm0.
rewrite !(bracket_swapl d c a), (bracket_swapr d a c).
ring.
Qed.


(******************************************************************************)
(*   Some standard geometry definitions                                       *)
(******************************************************************************)

Definition collinear x y z := x ∨ y ∨ z = 0.
Definition line (x y : point) := x ∨ y.
Definition intersection (x y : vect) := x ∧ y.
Definition concur (l1 l2 l3 : vect) := l1 ∧ l2 ∧ l3 = 0.
Definition online (x y z : point) := y ∨ z <> 0 /\ x ∨ y ∨ z = 0.
Definition online1 (x : point) k1 (y : point) k2 (z : point) := 
  x = k1 .* y + k2 .* z :> vect.
Definition inter_lines (x a b c d : point) : Prop :=  
  x = (a ∨ b) ∧ (c ∨ d) :> vect.

Lemma online_def x y z :
  online x y z -> exists pk, online1 x (fst pk) y (snd pk) z.
Proof.
intros (H1, H2).
case (decomp_cbl _ HP 3 (y ∨ z) ((y :vect)::(z :vect)::nil) (x : vect)); auto.
case (cbl1_hom1_equiv _ HP 3 (x : vect)); intros _ Hx; apply Hx.
apply k2g_hom; auto.
split; auto.
intros t; simpl; intros [[]|[[]|[]]].
case (cbl1_hom1_equiv _ HP 3 (y : vect)); intros _ Hx; apply Hx.
apply k2g_hom; auto.
case (cbl1_hom1_equiv _ HP 3 (z : vect)); intros _ Hx; apply Hx.
apply k2g_hom; auto.
rewrite join_assoc in H2.
intros H3 _.
case (cbl_mprod _ (fn _ HP 3) _ _ (H3 H2)); simpl.
intros [|k1[|k2[|k3 l]]]; try (intros (HH,_); discriminate).
unfold mprod, fold2; rewrite addE0r, addE_com; auto.
intros (HH1,HH2); exists (k1, k2); auto.
apply fn; auto.
apply fn; auto.
Qed.

Lemma collinear_bracket (x y z : point) :
  collinear x y z <-> '[x,y,z] = 0%f.
Proof.
unfold collinear; rewrite bracket_defE.
split; intros H.
case (scal_integral _ _ H); auto.
intros H1; injection H1; intros H2.
case (one_diff_zero _ HP); auto.
rewrite H, scal0l; auto.
Qed.

Lemma collinear_bracket0 (x y z : point) :
  collinear x y z -> '[x,y,z] = 0%f.
Proof. case (collinear_bracket x y z); auto. Qed.

Lemma bracket0_collinear (x y z : point) :
  '[x,y,z] = 0%f -> collinear x y z.
Proof. case (collinear_bracket x y z); auto. Qed.

(******************************************************************************)
(*   Pappus theorem                                                           *)
(******************************************************************************)
 
Theorem Pappus (a b c a' b' c': point) :
  let AB' := line a b' in
  let A'B := line a' b in
  let p := intersection AB' A'B in
  let BC' := line b c' in
  let B'C := line b' c in
  let q := intersection BC' B'C in
  let CA' := line c a' in
  let C'A := line c' a in
  let r := intersection CA' C'A in
  collinear a b c -> collinear a' b' c' -> collinear p q r.
Proof.
intros AB' A'B p BC' B'C q AC' A'C r H1 H2.
unfold collinear, p, q, r, AB', A'B, BC', B'C, AC', A'C,
  intersection, line.
rewrite !expand_meetr, !sub_add, !join_addr,  !join_addl,
        !join_scall, !join_scalr, !join_scall, !bracket_defE,
        <-!scal_mul, <-!scal_addl, ?bracket0l, ?bracket0m, ?bracket0r.
rewrite <-(scal0l E).
apply f_equal2 with (f := Vscal); auto.
normbs; normb a b c.
ring [(collinear_bracket0 _ _ _ H1) (collinear_bracket0 _ _ _ H2)].
Qed.

Theorem Desargues (a b c a' b' c': point) :
  let AB := line a b in
  let A'B' := line a' b' in
  let p := intersection AB A'B' in
  let AC := line a c in
  let A'C' := line a' c' in
  let q := intersection AC A'C' in
  let BC := line b c in
  let B'C' := line b' c' in
  let r := intersection BC B'C' in
  let AA' := line a a' in
  let BB' := line b b' in
  let CC' := line c c' in
  collinear p q r <-> collinear a b c \/ collinear a' b' c' \/ concur AA' BB' CC'.
Proof.
intros AB A'B' p AC A'C' q BC B'C' r AA' BB' CC'.
unfold p, q, r, AB, A'B', AC, A'C', BC, B'C', AA', BB', CC', concur, collinear,
       intersection, line.
assert (F1:  ((a ∨ b) ∧ (a' ∨ b')) ∨ ((a ∨ c) ∧ (a' ∨ c')) ∨ ((b ∨ c) ∧ (b' ∨ c')) = 
                (-'[a,b,c])%f .* ('[a',b',c'] .* ((a ∨ a') ∧ (b ∨ b') ∧ (c ∨ c'))) ∨ E).
assert (H: exists a1: point, (a ∨ b) ∧ (a' ∨ b') = a1).
apply hom1E; auto; homt.
case H; intros a1 Ha1; rewrite Ha1; clear H.
assert (H: exists a2: point, (a ∨ c) ∧ (a' ∨ c') = a2).
apply hom1E; auto; homt.
case H; intros a2 Ha2; rewrite Ha2; clear H.
assert (H: exists a3: point, (b ∨ c) ∧ (b' ∨ c') = a3).
apply hom1E; auto; homt.
case H; intros a3 Ha3; rewrite Ha3; clear H.
rewrite bracket_defE; rewrite <- (join1l E).
rewrite <-join_scall, <-bracket_defl, <-Ha1.
rewrite split_meetr, <-Ha2, <-Ha3.
replace (a ∨ b ∧ (a ∨ c ∧ (a' ∨ c'))) with ((- '[c', a', a] * '[a,b,c])%f .* 1).
replace (a' ∨ b' ∧ (b ∨ c ∧ (b' ∨ c'))) with ((- '[b,c,b'] * '[a',b',c'])%f .* 1).
replace (a' ∨ b' ∧ (a ∨ c ∧ (a' ∨ c'))) with (('[c,a,a'] * '[a',b',c'])%f .* 1).
replace (a ∨ b ∧ (b ∨ c ∧ (b' ∨ c'))) with (('[b', c', b] * '[a,b,c])%f .* 1).
rewrite !join_scall, !join_scalr, join_addl.
rewrite !join_scall, !join1l.
rewrite <-!scal_mul, <-scal_addl.
rewrite meet_assoc, meet_swap.
rewrite meet_scall.
rewrite expand_meetl, !sub_add.
rewrite meet_scalr, meet_addr, !meet_scalr,
        !bracket_defr, <-!scal_mul, <-scal_addl.
rewrite !join_scall, !join1l, <-!scal_mul.
apply f_equal2 with (f := Vscal); auto.
apply addK_eq_opp; auto; normbs; ring.
rewrite expand_meetl, !sub_add, !meet_addr, 
        !meet_scalr, !bracket_defr, <-!scal_mul, <-scal_addl, bracket0r.
apply f_equal2 with (f := Vscal); auto; ring.
rewrite (join_swap a c), meet_scall, meet_scalr.
rewrite expand_meetr, !sub_add, !meet_addr, !meet_scalr, !bracket_defr, 
        <-!scal_mul, <-!scal_addl, <-!scal_mul, bracket0m.
apply f_equal2 with (f := Vscal); auto; ring.
rewrite expand_meetr, !sub_add, !meet_addr, 
        !meet_scalr, !bracket_defr, <-!scal_mul, <-scal_addl, bracket0r.
apply f_equal2 with (f := Vscal); auto; ring.
rewrite (meet_swapr a a'), expand_meetl, !sub_add, !meet_addr, 
        !meet_scalr, !bracket_defr, <-!scal_mul, <-scal_addl, bracket0m.
apply f_equal2 with (f := Vscal); auto; ring.
rewrite F1.
rewrite !join_scall.
split; intros H.
case (scal_integral _ _ H); auto.
intros H1; left.
assert (H2: ('[a, b, c] = 0)%f).
rewrite  <-(opp_oppK _ HP '[a, b, c]).
simpl; rewrite H1, oppK0; auto.
rewrite <-collinear_bracket in H2; auto.
intros H1; case (scal_integral _ _ H1); auto.
rewrite <-collinear_bracket; auto.
intros H2; right; right; apply hom0_E; auto; homt.
case H; intros H1.
rewrite (collinear_bracket0 _ _ _ H1); Krm0.
case H1; intros H2.
rewrite (collinear_bracket0 _ _ _ H2), scal0l, scal0r; auto.
rewrite H2, join0l, scal0r; auto.
Qed.

End Vect.


Notation "x '∨' y" := (Vjoin _ x y) (at level 40, left associativity).
Notation "x + y" := (Vadd _ x y).
Notation "x - y" := (Vsub _ x y).
Notation "k .* x" := (Vscal _ k x).
Notation "x '∧' y" := (Vmeet _ x y) (at level 45, left associativity).
Notation "'@  x" := (Vdual _ x) (at level 9).
Notation "x ?= y" := (Veq _ x y).
Notation "0" := (Vgenk _ 0%f).
Notation "1" := (Vgenk _ 1%f).
Notation "'dC[ x ]" := (dconst _ _ 3 x).
Notation "'C[ x ]" := (const _ _ 3 x).
Notation "'E'" := (all _ _ 3: vect).
Notation "'[ x , y , z ]" := (bracket _ x y z).
Notation " x 'is_the_intersection_of' [ a , b ] 'and' [ c , d ] " := 
  (inter_lines _ x a b c d) (at level 10, format
                " x  'is_the_intersection_of'  [ a , b ]  'and'  [ c , d ]").
Notation " x 'is_free_on' [ a , b ]" := 
  (online _ x a b) (at level 10, format
             " x  'is_free_on'  [ a , b ]").
Notation " x ':=:' 'xfree' 'on' [ a , b ] ( c , d ) " := 
  (online1 _ x c a d b) (at level 10, format
             " x  ':=:'  'xfree'  'on'  [ a , b ]  ( c , d )").

Notation "'[' a , b , c ']' 'are_collinear' " := (collinear _ a b c) (at level 10).
