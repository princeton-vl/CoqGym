(* Ugly tacty to resolve sign condition for Z *)

Require Import Reals.
Require Import RPolS.
Require Import PolAux.
Require Import List.


(* Building the tactics *)

Definition Zsign_type := fun (x y:list Z) => Prop.

Definition Zsign_cons : forall x y, (Zsign_type  x y) := fun x y => True.

Ltac Zsign_push term1 term2 := generalize (Zsign_cons term1 term2); intro.

Ltac Zsign_le term :=
  match term with 
    (?X1 * ?X2)%Z =>  Zsign_le X1;
                             match goal with 
                             H1: (Zsign_type ?s1 ?s2) |- _ =>
                                    Zsign_le X2;
                                   match goal with 
                                      H2: (Zsign_type ?s3 ?s4) |- _ => clear H1 H2;
                                              let s5 := eval unfold List.app in (s1++s3) in
                                              let s6 := eval unfold List.app in (s2++s4) in
                                               Zsign_push s5 s6
                                   end
                              end
| _ =>  let H1 := fresh "H" in
    (((assert (H1: (0 <= term)%Z); [auto with zarith; fail | idtac])
      ||
     (assert (H1: (term <= 0)%Z); [auto with zarith; fail | idtac])); clear H1;
         Zsign_push (term::nil) (@nil Z)) || Zsign_push (@nil Z) (term::nil)
end.

Ltac Zsign_lt term :=
  match term with 
    (?X1 * ?X2)%Z =>  Zsign_lt X1;
                             match goal with 
                             H1: (Zsign_type ?s1 ?s2) |- _ =>
                                    Zsign_lt X2;
                                   match goal with 
                                      H2: (Zsign_type ?s3 ?s4) |- _ => clear H1 H2;
                                              let s5 := eval unfold List.app in (s1++s3) in
                                              let s6 := eval unfold List.app in (s2++s4) in
                                               Zsign_push s5 s6
                                   end
                              end
| _ =>  let H1 := fresh "H" in
    (((assert (H1: (0 < term)%Z); [auto with zarith; fail | idtac])
      ||
     (assert (H1: (term < 0)%Z); [auto with zarith; fail | idtac])); clear H1;
         Zsign_push (term::nil) (@nil Z)) || Zsign_push (@nil Z) (term::nil)
end.


Ltac Zsign_top0 :=
  match goal with
  |- (0 <= ?X1)%Z => Zsign_le  X1
| |- (?X1 <= 0)%Z => Zsign_le  X1
| |- (0 < ?X1)%Z => Zsign_lt  X1
| |- (?X1 < 0)%Z => Zsign_le  X1
| |- (0 >= ?X1)%Z => Zsign_le  X1
| |- (?X1 >= 0)%Z => Zsign_le  X1
| |- (0 > ?X1 )%Z => Zsign_lt X1
| |- (?X1 > 0)%Z => Zsign_le  X1
  end.


Ltac Zsign_top :=
  match goal with
| |- (?X1 * _ <= ?X1 * _)%Z => Zsign_le  X1
| |- (?X1 * _ < ?X1 * _)%Z => Zsign_le  X1
| |- (?X1 * _ >= ?X1 * _)%Z => Zsign_le  X1
| |- (?X1 * _ > ?X1 * _)%Z => Zsign_le  X1
  end.


Ltac Zhyp_sign_top0 H:=
  match type of H with
   (0 <= ?X1)%Z => Zsign_lt  X1
|  (?X1 <= 0)%Z => Zsign_lt  X1
|  (0 < ?X1)%Z => Zsign_lt  X1
|  (?X1 < 0)%Z => Zsign_lt X1
|  (0 >= ?X1)%Z => Zsign_lt  X1
|  (?X1 >= 0)%Z => Zsign_lt  X1
|  (0 > ?X1 )%Z => Zsign_lt X1
|  (?X1 > 0)%Z => Zsign_lt  X1
  end.


Ltac Zhyp_sign_top H :=
  match type of H with
|  (?X1 * _ <= ?X1 * _)%Z => Zsign_lt  X1
|  (?X1 * _ < ?X1 * _)%Z => Zsign_lt X1
|  (?X1 * _ >= ?X1 * _)%Z => Zsign_lt  X1
|  (?X1 * _ > ?X1 * _)%Z => Zsign_lt  X1
|  ?X1 => generalize H
  end.

Ltac Zsign_get_term g :=
  match g with
   (0 <= ?X1)%Z =>  X1
|  (?X1 <= 0)%Z => X1
|  (?X1 * _ <= ?X1 * _)%Z =>  X1
|  (0 < ?X1)%Z =>  X1
|  (?X1 < 0)%Z => X1
|  (?X1 * _ < ?X1 * _)%Z =>  X1
|  (0 >= ?X1)%Z => X1
|  (?X1 >= 0)%Z => X1
|  (?X1 * _ >= ?X1 * _)%Z =>  X1
|  (?X1 * _  >= _)%Z => X1
|  (0 > ?X1)%Z => X1
|  (?X1 > 0)%Z => X1
|  (?X1 * _ > ?X1 * _)%Z =>  X1
  end.

Ltac Zsign_get_left g :=
  match g with
|  (_ * ?X1 <=  _)%Z =>  X1
|  (_ * ?X1 <  _)%Z =>  X1
|  (_ * ?X1 >=  _)%Z =>  X1
|  (_ * ?X1 >  _)%Z =>  X1
end.

Ltac Zsign_get_right g :=
  match g with
|  (_ <= _ * ?X1)%Z =>  X1
|  (_ < _ * ?X1)%Z =>  X1
|  (_ >= _ * ?X1)%Z =>  X1
|  (_ > _ * ?X1)%Z =>  X1
end.

Fixpoint mkZprodt (l: list Z)(t:Z) {struct l}: Z :=
match l with nil => t | e::l1 => (e * mkZprodt l1 t)%Z end.

Fixpoint mkZprod (l: list Z) : Z :=
match l with nil => 1%Z  | e::nil => e | e::l1 => (e * mkZprod l1)%Z end.

(* tatic for 0 ? x * y where ? is < > <= >= *)

Ltac zsign_tac_aux0 := 
match goal with
  |- (0 <= ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%Z); auto with zarith; apply Zle_sign_pos_pos)
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; apply Zle_sign_neg_neg); try zsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 <= 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%Z); auto with zarith; apply Zle_sign_pos_neg)
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; apply Zle_sign_neg_pos); try zsign_tac_aux0; clear H1)
| |- (0 < ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; apply Zlt_sign_pos_pos)
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; apply Zlt_sign_neg_neg); try zsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 < 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; apply Zlt_sign_pos_neg)
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; apply Zlt_sign_neg_pos); try zsign_tac_aux0; clear H1)
 | |- (?X1 * ?X2 >= 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 >= X1)%Z); auto with zarith; apply Zge_sign_neg_neg)
      ||
     (assert (H1:  (X1 >= 0)%Z); auto with zarith; apply Zge_sign_pos_pos); try zsign_tac_aux0; clear H1)
| |- (0 >= ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 >= 0)%Z); auto with zarith; apply Zge_sign_pos_neg)
      ||
     (assert (H1: (0 >= X1)%Z); auto with zarith; apply Zge_sign_neg_pos); try zsign_tac_aux0; clear H1)
| |- (0 > ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%Z); auto with zarith; apply Zgt_sign_neg_pos)
      ||
     (assert (H1: (X1 > 0)%Z); auto with zarith; apply Zgt_sign_pos_neg); try zsign_tac_aux0; clear H1)
| |- (?X1 * ?X2 > 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%Z); auto with zarith; apply Zgt_sign_neg_neg)
      ||
     (assert (H1: (X1 > 0)%Z); auto with zarith; apply Zgt_sign_pos_pos); try zsign_tac_aux0; clear H1)
|
 _ => auto with zarith; fail 1 "zsign_tac_aux"
end.

Ltac zsign_tac0 := Zsign_top0;
  match goal with
    H1: (Zsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (mkZprod s2)) in
    let t := Zsign_get_term g in
         replace t with s; [try zsign_tac_aux0 | try ring]; auto with zarith
  end.

(* tatic for hyp 0 ? x * y where ? is < > <= >= *)

Ltac hyp_zsign_tac_aux0 H := 
match  type of H  with
   (0 <= ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zle_sign_pos_pos_rev  _ _ H1 H)
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zle_sign_neg_neg_rev  _ _ H1 H))); 
     clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 <= 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zle_sign_pos_neg_rev  _ _ H1 H))
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; generalize (Zle_sign_neg_pos_rev  _ _ H1 H)); 
      clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (0 < ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zlt_sign_pos_pos_rev _  _ H1 H))
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zlt_sign_neg_neg_rev _ _ H1 H)); 
      clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 < 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zlt_sign_pos_neg_rev _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zlt_sign_neg_pos_rev _ _ H1 H)); 
     clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
 |  (?X1 * ?X2 >= 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 >X1)%Z); auto with zarith; generalize (Zge_sign_neg_neg_rev _ _ H1 H))
      ||
     (assert (H1:  (X1 > 0)%Z); auto with zarith; generalize (Zge_sign_pos_pos _ _ H1 H));
      clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (0 >= ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 > 0)%Z); auto with zarith; generalize (Zge_sign_pos_neg _ _ H1 H))
      ||
     (assert (H1: (0 > X1)%Z); auto with zarith; generalize (Zge_sign_neg_pos _ _ H1 H));
     clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (0 > ?X1 * ?X2)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%Z); auto with zarith; generalize (Zgt_sign_neg_pos _ _ H1 H))
      ||
     (assert (H1: (X1 > 0)%Z); auto with zarith; generalize (Zgt_sign_pos_neg _ _ H1 H));
     clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|  (?X1 * ?X2 > 0)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 > X1)%Z); auto with zarith; generalize (Zgt_sign_neg_neg _ _ H1 H))
      ||
     (assert (H1: (X1 > 0)%Z); auto with zarith; generalize (Zgt_sign_pos_pos _ _ H1 H));
     clear H; intros H; try hyp_zsign_tac_aux0 H; clear H1)
|
 _ => auto with zarith; fail 1 "hyp_zsign_tac_aux0"
end.

Ltac hyp_zsign_tac0 H := Zhyp_sign_top0 H;
  match goal with
    H1: (Zsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (mkZprod s2)) in
    let t := Zsign_get_term g in
         replace t with s in H; [try hyp_zsign_tac_aux0 H | try ring]; auto with zarith
  end.

(* Tactic for goal x1 * x2 ? x1 * x3 where ? is < > <= >= *)

Ltac zsign_tac_aux := 
match goal with
 | |- (?X1 * ?X2 <= ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%Z); auto with zarith; apply Zmult_le_compat_l)
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; apply Zmult_le_neg_compat_l); try zsign_tac_aux; clear H1)
| |- (?X1 * ?X2 < ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%Z); auto with zarith; apply Zmult_lt_compat_l)
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; apply Zmult_lt_neg_compat_l); try zsign_tac_aux; clear H1) 
 | |- (?X1 * ?X2 >= ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 >= 0)%Z); auto with zarith; apply Zmult_ge_compat_l)
      ||
     (assert (H1:  (0 >= X1)%Z); auto with zarith; apply Zmult_ge_neg_compat_l); try zsign_tac_aux; clear H1)
| |- (?X1 * ?X2 > ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 <= X1)%Z); auto with zarith; apply Zmult_lt_compat_l)
      ||
     (assert (H1: (X1 <= 0)%Z); auto with zarith; apply Zmult_lt_neg_compat_l); try zsign_tac_aux; clear H1)
|
 _ => auto with zarith; fail 1 "Zsign_tac_aux"
end.

Ltac zsign_tac := zsign_tac0 || (Zsign_top;
  match goal with
    H1: (Zsign_type ?s1 ?s2) |- ?g => clear H1;
    let s := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (mkZprod s2)) in
    let t := Zsign_get_term g in
    let l := Zsign_get_left g in
    let r := Zsign_get_right g in
    let sl := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (Zmult (mkZprod s2) l)) in
    let sr := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (Zmult (mkZprod s2) r)) in
         replace2_tac (Zmult t l) (Zmult t r) sl sr; [zsign_tac_aux | ring | ring]
  end).


(* Tactic for hyp x1 * x2 ? x1 * x3 where ? is < > <= >= *)

Ltac hyp_zsign_tac_aux H := 
match type of H with
 | (?X1 * ?X2 <= ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zmult_le_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zmult_le_neg_compat_l_rev _ _ _ H1 H)); 
     clear H; intros H; try hyp_zsign_tac_aux H; clear H1)
|  (?X1 * ?X2 < ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zmult_lt_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zmult_lt_neg_compat_l_rev _ _ _ H1 H)); 
    clear H; intros H; try hyp_zsign_tac_aux H; clear H1) 
 |  (?X1 * ?X2 >= ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (X1 > 0)%Z); auto with zarith; generalize (Zmult_ge_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1:  (0 > X1)%Z); auto with zarith; generalize (Zmult_ge_neg_compat_l_rev _ _ _ H1 H)); 
    clear H; intros H; try hyp_zsign_tac_aux H; clear H1)
| (?X1 * ?X2 > ?X1 * ?X3)%Z =>
  let H1 := fresh "H" in
    ((assert (H1: (0 < X1)%Z); auto with zarith; generalize (Zmult_gt_compat_l_rev _ _ _ H1 H))
      ||
     (assert (H1: (X1 < 0)%Z); auto with zarith; generalize (Zmult_gt_neg_compat_l_rev _ _ _ H1 H)); 
     clear H; intros H; try hyp_zsign_tac_aux H; clear H1)
|
 _ => auto with zarith; fail 0 "Zhyp_sign_tac_aux"
end.

Ltac hyp_zsign_tac H := hyp_zsign_tac0  H||( Zhyp_sign_top H;
  match goal with
    H1: (Zsign_type ?s1 ?s2) |- _ => clear H1;
    let s := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (mkZprod s2)) in
    let g := type of H in
    let t := Zsign_get_term g in
    let l := Zsign_get_left g in
    let r := Zsign_get_right g in
    let sl := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (Zmult (mkZprod s2) l)) in
    let sr := eval unfold mkZprod, mkZprodt in 
                  (mkZprodt s1 (Zmult (mkZprod s2) r)) in
         (generalize H; replace2_tac (Zmult t l) (Zmult t r) sl sr; [clear H; intros H; try hyp_zsign_tac_aux H| ring | ring])
  end).

Section Test.

Let test : forall a b c, (0 < a -> a * b < a * c -> b < c)%Z.
intros a b c H H1.
hyp_zsign_tac H1.
Qed.


Let test1 : forall a b c, (a < 0 -> a * b < a * c -> c < b)%Z.
intros a b c H H1.
hyp_zsign_tac H1.
Qed.

Let test2 : forall a b c, (0 < a -> a * b <= a * c -> b <= c)%Z.
intros a b c H H1.
hyp_zsign_tac H1.
Qed.

Let test3 : forall a b c, (a < - 0 -> a * b >= a * c -> c >= b)%Z.
intros a b c H H1.
hyp_zsign_tac H1.
Qed.

End Test.
