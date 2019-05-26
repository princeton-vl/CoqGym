Require Import ZArith.
Require Import NAux.
Require Import PolSBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import NPolS.
Require Import NPolF.
Require Import PolRBase.
 
Definition Nreplace_term_aux :=
  replace Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div.

Ltac
Nreplace_term term from to occ id :=
let rfv := FV NCst Nplus Nmult Nminus Nopp term (@nil N) in
let rfv1 := FV NCst Nplus Nmult Nminus Nopp from rfv in
let rfv2 := FV NCst Nplus Nmult Nminus Nopp to rfv1 in
let fv := Trev rfv2 in
let expr := mkPolexpr Z NCst Nplus Nmult Nminus Nopp term fv in
let expr_from := mkPolexpr Z NCst Nplus Nmult Nminus Nopp from fv in
let expr_to := mkPolexpr Z NCst Nplus Nmult Nminus Nopp to fv in
let re := eval vm_compute in (Nreplace_term_aux expr expr_from expr_to occ) in
let term1 := eval
     unfold Nconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl in (Nconvert_back re fv) in
let term2 := clean_zabs_N term1 in
match id with 
     true => term2
  | false =>
     match eqterm term term1 with
       |false => term2
    end
end
.

Ltac Npol_is_compare term :=
match term with
| (_ < _)%N => constr:(true)
| (_ > _)%N => constr:(true)
| (_ <= _)%N => constr:(true)
| (_ >= _)%N => constr:(true)
| (?X = _)%N => match type of X with N => constr:(true) end
| _ => constr:(false)
end.

Ltac Npol_get_term dir term :=
match term with
|  (?op ?X  ?Y)%N =>
     match dir with P.L => X | P.R => Y end
|  (?X = ?Y)%N =>
     match dir with P.L => X | P.R => Y end
| _ => fail 1 "Unknown term in Npol_get_term"
end.

Ltac Npol_replace_term term1 term2 dir1 dir2 occ id := 
  let dir2opp := eval compute in (P.pol_dir_opp dir2) in
  let t1 := Npol_get_term dir2 term2 in
  let t2 := match id with true => t1 | false =>  Npol_get_term dir2opp term2 end in
 match term1 with
   | (?op ?X ?Y) =>
     match dir1 with
       P.L  =>
             Nreplace_term X t1 t2 occ id
       | P.R => 
            Nreplace_term Y t1 t2 occ id
      end
  | (?X = ?Y)%N  =>
     match dir1 with
       P.L  =>
             Nreplace_term X t1 t2 occ id
     | P.R => 
             Nreplace_term Y  t1 t2 occ id
      end
  end.


Ltac Npol_aux_dir term dir :=
  match term with
   (_ < _)%N => dir
  | (_ > _)%N => dir
  | (_ <= _)%N => eval compute in (P.pol_dir_opp dir) 
  | (_ >= _)%N => eval compute in (P.pol_dir_opp dir) 
end.

(* Do the replacement *)
Ltac Nreplace_tac_full term dir1 dir2 occ :=
match term with
 (?T1 = ?T2)%N =>
  (* We have here a substitution *)
  match goal with
     |-  ?G => let  t := Npol_replace_term G term dir1 dir2 occ false in
              match dir1 with
               P.L =>
                      apply trans_equal with t ||
                      apply Neq_lt_trans_l with t || apply Neq_gt_trans_l with t ||
                       apply Neq_le_trans_l with t || apply Neq_ge_trans_l with t
              | P.R =>
                     apply trans_equal_r with t ||
                       apply Neq_lt_trans_r with t || apply Neq_gt_trans_r with t ||
                       apply Neq_le_trans_r with t || apply Neq_ge_trans_r with t
              end
  end
| _ =>
   match goal with
     |- (?X <= ?Y)%N  =>
            let  t := Npol_replace_term (X <= Y)%N term dir1 dir2 occ false in
               apply N.le_trans with t
     |  |- (?X >= ?Y)%N =>
            let  t := Npol_replace_term (X >= Y)%N term dir1 dir2 occ false in
               apply Nge_trans with t
     | |- ?G  =>
            let  t := Npol_replace_term G term dir1 dir2 occ false in
           match Npol_aux_dir term dir1 with
                P.L =>
                                    (apply N.lt_le_trans with t || apply Ngt_le_trans with t)
               |P.R =>
                                    (apply N.le_lt_trans with t || apply Nle_gt_trans with t)
            end
   end
end.

(* Make the term appears *)
Ltac Nreplace_tac_full_id term dir1 dir2 occ :=
  match goal with
     |-  ?G => let t1 := Npol_replace_term G term dir1 dir2 occ true in 
                match dir1 with
                  P.L =>
                       apply trans_equal with t1 ||
                       apply Neq_lt_trans_l with t1 ||
                       apply Neq_gt_trans_l with t1 ||
                       apply Neq_le_trans_l with t1 ||
                       apply Neq_ge_trans_l with t1
               | P.R =>
                      apply trans_equal_r with t1 ||
                      apply Neq_lt_trans_r with t1 ||
                      apply Neq_gt_trans_r with t1  ||
                      apply Neq_le_trans_r with t1 ||
                      apply Neq_ge_trans_r with t1
                end; [ring | idtac]
end.

Ltac Npolrx term dir1 dir2 occ :=
match Npol_is_compare term with
  true => Nreplace_tac_full_id term dir1 dir2 occ; [Nreplace_tac_full term dir1 dir2 occ] 
| false => 
     let t := type of term in
     match Npol_is_compare t with true => 
        Nreplace_tac_full_id t dir1 dir2 occ; [Nreplace_tac_full t dir1 dir2 occ]
     end 
end.

Ltac Npolr term :=
  Npolrx term P.L P.L 1%Z  ||
  Npolrx term P.R P.L 1%Z ||
  Npolrx term P.L P.R 1%Z ||
  Npolrx term P.R P.R 1%Z.
