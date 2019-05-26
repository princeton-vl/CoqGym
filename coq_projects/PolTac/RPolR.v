Require Import ZArith.
Require Import Reals.
Require Import PolSBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import RPolS.
Require Import RPolF.
Require Import PolRBase.


Definition Rreplace_term_aux :=
  replace Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div.

Ltac
Rreplace_term term from to occ id :=
let rfv := FV RCst Rplus Rmult Rminus Ropp term (@nil R) in
let rfv1 := FV RCst Rplus Rmult Rminus Ropp from rfv in
let rfv2 := FV RCst Rplus Rmult Rminus Ropp to rfv1 in
let fv := Trev rfv2 in
let expr := mkPolexpr Z RCst Rplus Rmult Rminus Ropp term fv in
let expr_from := mkPolexpr Z RCst Rplus Rmult Rminus Ropp from fv in
let expr_to := mkPolexpr Z RCst Rplus Rmult Rminus Ropp to fv in
let re := eval vm_compute in (Rreplace_term_aux expr expr_from expr_to occ) in
let term1 := eval
     unfold Rconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl, Z2R, P2R in (Rconvert_back re fv) in
match id with
     true => term1
  | false =>
     match eqterm term term1 with
       |false => term1
    end
end
.

Ltac rpol_is_compare term :=
match term with
| (_ < _)%R => constr:(true)
| (_ > _)%R => constr:(true)
| (_ <= _)%R => constr:(true)
| (_ >= _)%R => constr:(true)
| (?X = _)%R => match type of X with R => constr:(true) end
| _ => constr:(false)
end.

Ltac rpol_get_term dir term :=
match term with
|  (?op ?X  ?Y)%R =>
     match dir with P.L => X | P.R => Y end
|  (?X = ?Y)%R =>
     match dir with P.L => X | P.R => Y end
| _ => fail 1 "Unknown term in pol_get_term"
end.

Ltac rpol_replace_term term1 term2 dir1 dir2 occ id :=
  let dir2opp := eval compute in (P.pol_dir_opp dir2) in
  let t1 := rpol_get_term dir2 term2 in
  let t2 := match id with true => t1 | false => rpol_get_term dir2opp term2 end in
 match term1 with
   | (?op ?X ?Y) =>
     match dir1 with
       P.L  =>
             Rreplace_term X t1 t2 occ id
       | P.R =>
            Rreplace_term Y t1 t2 occ id
      end
  | (?X = ?Y)%R  =>
     match dir1 with
       P.L  =>
             Rreplace_term X t1 t2 occ id
     | P.R =>
             Rreplace_term Y  t1 t2 occ id
      end
  end.


Ltac rpol_aux_dir term dir :=
  match term with
   (_ < _)%R => dir
  | (_ > _)%R => dir
  | (_ <= _)%R => eval compute in (P.pol_dir_opp dir)
  | (_ >= _)%R  => eval compute in (P.pol_dir_opp dir)
end.

Ltac R_eq_trans_l t:=
   match goal with
     |  |- (?X >= ?Y)%R => apply eq_Rge_trans_l with t
     |  |- (?X > ?Y)%R => apply eq_Rgt_trans_l with t
     |  |- (?X <= ?Y)%R => apply eq_Rle_trans_l with t
     |  |- (?X < ?Y)%R => apply eq_Rlt_trans_l with t
     |  |- ?G  => apply trans_equal with t
    end.

Ltac R_eq_trans_r t:=
   match goal with
     |  |- (?X >= ?Y)%R => apply eq_Rge_trans_r with t
     |  |- (?X > ?Y)%R => apply eq_Rgt_trans_r with t
     |  |- (?X <= ?Y)%R => apply eq_Rle_trans_r with t
     |  |- (?X < ?Y)%R => apply eq_Rlt_trans_r with t
     |  |- ?G  => apply trans_equal_r with t
    end.


(* Do the replacement *)
Ltac Rreplace_tac_full term dir1 dir2 occ :=
match term with
 (?T1 = ?T2)%R =>
  (* We have here a substitution *)
  match goal with
     |-  ?G => let  t := rpol_replace_term G term dir1 dir2 occ false in
              match dir1 with
               P.L => R_eq_trans_l t
              | P.R => R_eq_trans_r t
              end
  end
| _ =>
   match goal with
     |- (?X <= ?Y)%R  =>
            let  t := rpol_replace_term (X <= Y)%R term dir1 dir2 occ false in
               apply Rle_trans with t
     |  |- (?X >= ?Y)%R =>
            let  t := rpol_replace_term (X >= Y)%R term dir1 dir2 occ false in
               apply Rge_trans with t
     | |- (?X < ?Y)%R  =>
           let  t := rpol_replace_term (X < Y)%R term dir1 dir2 occ false in
           match rpol_aux_dir term dir1 with
                P.L =>
                                    (apply Rlt_le_trans with t)
               |P.R =>
                                    (apply Rle_lt_trans with t)
            end
     | |- (?X > ?Y)%R   =>
            let  t := rpol_replace_term (X > Y)%R term dir1 dir2 occ false in
           match rpol_aux_dir term dir1 with
                P.L =>
                                    (apply Rgt_ge_trans with t)
               |P.R =>
                                    (apply Rge_gt_trans with t)
            end
   end
end.


(* Make the term appears *)
Ltac Rreplace_tac_full_id term dir1 dir2 occ :=
  match goal with
     |-  ?G => let t1 := rpol_replace_term G term dir1 dir2 occ true in
                match dir1 with
                  P.L => R_eq_trans_l t1
               | P.R => R_eq_trans_r t1
                end; [ring | idtac]
end.

Ltac rpolrx term dir1 dir2 occ :=
match rpol_is_compare term with
  true => Rreplace_tac_full_id term dir1 dir2 occ; [Rreplace_tac_full term dir1 dir2 occ]
| false =>
     let t := type of term in
     match rpol_is_compare t with  true =>
       Rreplace_tac_full_id t dir1 dir2 occ; [Rreplace_tac_full t dir1 dir2 occ]
     end
end.

Ltac rpolr term :=
  rpolrx term P.L P.L 1%Z ||
  rpolrx term P.R P.L 1%Z ||
  rpolrx term P.L P.R 1%Z ||
  rpolrx term P.R P.R 1%Z.
