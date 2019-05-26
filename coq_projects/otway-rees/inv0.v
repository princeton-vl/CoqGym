(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.

Lemma POinv0 :
 forall st1 st2 : GlobalState, inv0 st1 -> rel st1 st2 -> inv0 st2.

Proof.
simple induction st1; intros a b s l; elim a; elim b; elim s. 
simple induction st2; intros a0 b0 s0 l0; elim a0; elim b0; elim s0.
do 15 intro.
unfold inv0 in |- *; unfold rel in |- *; intros know_c_c0_l rel1_8.

(* rel1 *)
elim rel1_8. intros r1.
elim r1; intros eq_l0 and1; elim and1; intros t1 and2; elim and2;
 intros t2 and3; elim and3; intros i_c1_c2 t3. 
clear rel1_8 r1 and1 and2 and3 t1 t2 t3.
inversion i_c1_c2; elim H4; elim H5; rewrite eq_l0.
split; apply E0; elim know_c_c0_l; intros; assumption.

(* rel2 *)
intro rel2_8; elim rel2_8. intros r2.
elim r2; unfold quad in |- *; intros know_c1_l and1; elim and1;
 intros t1 and2; elim and2; intros t2 and3; elim and3; 
 intros eq_l0 and4; elim and4; intros t3 and5; elim and5; 
 intros t4 eq_c2.
clear rel1_8 rel2_8 r2 and1 and2 and3 and4 and5 t1 t2 t3 t4.
elim eq_l0; elim eq_c2.
split.
apply
 (A2B (B2C (D2B Bid)) c1 l
    (A2B (B2C (D2B d16)) (Pair (B2C (D2B Bid)) c1) l
       (A2B (B2C (D2B d15)) (Pair (B2C (D2B d16)) (Pair (B2C (D2B Bid)) c1))
          l know_c1_l))).
elim know_c_c0_l; intros; assumption.

(* rel3 *)
intros rel3_8; elim rel3_8. intros r3.
elim r3; intros eq_l0 and1; elim and1; intros t1 and2; elim and2;
 intros t2 and3; elim and3; intros t3 and4; elim and4; 
 intros t4 and5; elim and5; intros t5 and6; elim and6; 
 intros t6 and7; elim and7; intros eq_c1 eq_c2.
clear rel1_8 rel2_8 rel3_8 r3 and1 and2 and3 and4 and5 and6 and7 t1 t2 t3 t4
 t5 t6.
elim eq_c1; elim eq_c2; rewrite eq_l0.
split; apply E0; elim know_c_c0_l; intros; assumption.

(* rel4 *)
intros rel4_8; elim rel4_8. intros r4.
elim r4; intros t1 and1; elim and1; intros t2 and2; elim and2;
 intros i_c1_c2 eq_l0.
clear rel1_8 rel2_8 rel3_8 rel4_8 r4 and1 and2 t1 t2.
inversion i_c1_c2; elim H4; elim H5; elim eq_l0; assumption.

(* rel5 *)
intros rel5_8; elim rel5_8. intros r5.
elim r5; intros eq_l0 and1; elim and1; intros t1 and2; elim and2;
 intros i_c1_c2 t2.
clear rel1_8 rel2_8 rel3_8 rel4_8 rel5_8 r5 and1 and2 t1 t2.
inversion i_c1_c2; elim H4; elim H5; rewrite eq_l0.
split; apply E0; elim know_c_c0_l; intros; assumption.

(* rel6 *)
intros rel6_8; elim rel6_8. intros r6.
elim r6; unfold triple in |- *; intros know_c2_l and1; elim and1;
 intros t1 and2; elim and2; intros t2 and3; elim and3; 
 intros eq_l0 and4; elim and4; intros t3 and5; elim and5; 
 intros t4 and6; elim and6; intros t5 eq_c1.
clear rel1_8 rel2_8 rel3_8 rel4_8 rel5_8 rel6_8 r6 and1 and2 and3 and4 and5
 and6 t1 t2 t3 t4 t5.
elim eq_c1; elim eq_l0.
split.
elim know_c_c0_l; intros; assumption.
apply
 (A2A c2 (Encrypt (Pair (B2C (D2B d6)) (B2C (K2B k1))) (KeyX Bid)) l
    (A2B (B2C (D2B d4))
       (Pair c2 (Encrypt (Pair (B2C (D2B d6)) (B2C (K2B k1))) (KeyX Bid))) l
       know_c2_l)).

(* rel7 *)
intros rel7_8; elim rel7_8. intros r7.
elim r7; intros eq_l0 and1; elim and1; intros t1 and2; elim and2;
 intros i_c1_c2 t2.
clear rel1_8 rel2_8 rel3_8 rel4_8 rel5_8 rel6_8 rel7_8 r7 and1 and2 t1 t2.
inversion i_c1_c2; elim H4; elim H5; rewrite eq_l0.
split; apply E0; elim know_c_c0_l; intros; assumption.

(* rel8 *)
intros r8.
elim r8; intros t1 and1; elim and1; intros i_c1_c2 and2; elim and2;
 intros t2 and3; elim and3; intros eq_l0 t3.
clear rel1_8 rel2_8 rel3_8 rel4_8 rel5_8 rel6_8 rel7_8 r8 and1 and2 and3 t1
 t2 t3.
inversion i_c1_c2; elim H4; elim H5; elim eq_l0; assumption.

Qed.