Require Import ZArith.
Require Import PolSBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import ZPolS.
Require Import ZPolF.
Require Import PolRBase.

 
Definition Zreplace_term_aux :=
  replace Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div.

Ltac
Zreplace_term term from to occ id :=
let rfv := FV ZCst Zplus Zmult Zminus Z.opp term (@nil Z) in
let rfv1 := FV ZCst Zplus Zmult Zminus Z.opp from rfv in
let rfv2 := FV ZCst Zplus Zmult Zminus Z.opp to rfv1 in
let fv := Trev rfv2 in
let expr := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp term fv in
let expr_from := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp from fv in
let expr_to := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp to fv in
let re := eval vm_compute in (Zreplace_term_aux expr expr_from expr_to occ) in
let term1 := eval
     unfold Zconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl in (Zconvert_back re fv) in
match id with 
     true => term1
  | false =>
     match eqterm term term1 with
       |false => term1
    end
end
.

Ltac zpol_is_compare term :=
match term with
| (_ < _)%Z => constr:(true)
| (_ > _)%Z => constr:(true)
| (_ <= _)%Z => constr:(true)
| (_ >= _)%Z => constr:(true)
| (?X = _)%Z => match type of X with Z => constr:(true) end 
| _ => constr:(false)
end.

Ltac zpol_get_term dir term :=
match term with
|  (?op ?X  ?Y)%Z =>
     match dir with P.L => X | P.R => Y end
|  (?X = ?Y)%Z =>
     match dir with P.L => X | P.R => Y end
| _ => fail 1 "Unknown term in zpolget_term"
end.

Ltac zpol_replace_term term1 term2 dir1 dir2 occ id := 
  let dir2opp := eval vm_compute in (P.pol_dir_opp dir2) in
  let t1 := zpol_get_term dir2 term2 in
  let t2 := match id with true => t1 | false => zpol_get_term dir2opp term2 end in
  match term1 with
   | (?op ?X ?Y) =>
     match dir1 with
         P.L  =>
             Zreplace_term X t1 t2 occ id
       | P.R => 
            Zreplace_term Y t1 t2 occ id
      end
  | (?X = ?Y)%Z  =>
     match dir1 with
       P.L  =>
             Zreplace_term X t1 t2 occ id
     | P.R => 
             Zreplace_term Y  t1 t2 occ id
      end
  end.


Ltac zpol_aux_dir term dir :=
  match term with
   (_ < _)%Z => dir
  | (_ > _)%Z => dir
  | (_ <= _)%Z => eval compute in (P.pol_dir_opp dir) 
  | (_ >= _)%Z  => eval compute in (P.pol_dir_opp dir) 
end.

(* Do the replacement *)
Ltac Zreplace_tac_full term dir1 dir2 occ :=
match term with
 (?T1 = ?T2)%Z =>
  (* We have here a substitution *)
  match goal with
     |-  ?G => let  t := zpol_replace_term G term dir1 dir2 occ false in
              match dir1 with
               P.L =>
                      apply trans_equal with t ||
                      apply eq_Zlt_trans_l with t || apply eq_Zgt_trans_l with t ||
                       apply eq_Zle_trans_l with t || apply eq_Zge_trans_l with t
              | P.R =>
                     apply trans_equal_r with t ||
                       apply eq_Zlt_trans_r with t || apply eq_Zgt_trans_r with t ||
                       apply eq_Zle_trans_r with t || apply eq_Zge_trans_r with t
              end
  end
| _ =>
   match goal with
     |- (?X <= ?Y)%Z  =>
            let  t := zpol_replace_term (X <= Y)%Z term dir1 dir2 occ false in
               apply Z.le_trans with t
     |  |- (?X >= ?Y)%Z =>
            let  t := zpol_replace_term (X >= Y)%Z term dir1 dir2 occ false in
               apply Zge_trans with t
     | |- ?G  =>
            let  t := zpol_replace_term G term dir1 dir2 occ false in
           match zpol_aux_dir term dir1 with
                P.L =>
                                    (apply Z.lt_le_trans with t || apply Zgt_le_trans with t)
               |P.R =>
                                    (apply Z.le_lt_trans with t || apply Zle_gt_trans with t)
            end
   end
end.

(* Make the term appears *)
Ltac Zreplace_tac_full_id term dir1 dir2 occ :=
  match goal with
     |-  ?G => let t1 := zpol_replace_term G term dir1 dir2 occ true in 
                match dir1 with
                  P.L =>
                       apply trans_equal with t1 ||
                       apply eq_Zlt_trans_l with t1 ||
                       apply eq_Zgt_trans_l with t1 ||
                       apply eq_Zle_trans_l with t1 ||
                       apply eq_Zge_trans_l with t1
               | P.R =>
                      apply trans_equal_r with t1 ||
                      apply eq_Zlt_trans_r with t1 ||
                      apply eq_Zgt_trans_r with t1  ||
                      apply eq_Zle_trans_r with t1 ||
                      apply eq_Zge_trans_r with t1
                end; [ring | idtac]
end.

Ltac zpolrx term dir1 dir2 occ :=
match zpol_is_compare term with
  true => Zreplace_tac_full_id term dir1 dir2 occ; 
                [Zreplace_tac_full term dir1 dir2 occ] 
| false => 
     let t := type of term in
     match zpol_is_compare t with true => Zreplace_tac_full_id t dir1 dir2 occ;
                                                                       [Zreplace_tac_full t dir1 dir2 occ]
     end 
end.

Ltac zpolr term :=
  zpolrx term P.L P.L 1%Z ||
  zpolrx term P.R P.L 1%Z ||
  zpolrx term P.L P.R 1%Z ||
  zpolrx term P.R P.R 1%Z.

