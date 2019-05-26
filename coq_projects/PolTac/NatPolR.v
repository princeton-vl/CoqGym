Require Import ZArith.
Require Import PolSBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import NatPolS.
Require Import NatPolF.
Require Import PolRBase.
 
Definition Natreplace_term_aux :=
  replace Z Zplus Zmult Z.opp 0%Z 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div.

Ltac
Natreplace_term term from to occ id :=
let rfv := FV NatCst plus mult minus Natopp term (@nil nat) in
let rfv1 := FV NatCst plus mult minus Natopp from rfv in
let rfv2 := FV NatCst plus mult minus Natopp to rfv1 in
let fv := Trev rfv2 in
let expr := mkPolexpr Z NatCst plus mult minus Natopp term fv in
let expr_from := mkPolexpr Z NatCst plus mult minus Natopp from fv in
let expr_to := mkPolexpr Z NatCst plus mult minus Natopp to fv in
let re := eval vm_compute in (Natreplace_term_aux expr expr_from expr_to occ) in
let term1 := eval
     unfold Natconvert_back, convert_back,  pos_nth,  jump,
         hd,  tl in (Natconvert_back re fv) in
let term2 := clean_zabs term1 in
match id with 
     true => term2
  | false =>
     match eqterm term term1 with
       |false => term2
    end
end
.

Ltac npol_is_compare term :=
match term with
| (_ < _)%nat => constr:(true)
| (_ > _)%nat => constr:(true)
| (_ <= _)%nat => constr:(true)
| (_ >= _)%nat => constr:(true)
| (?X = _)%nat => match type of X with nat => constr:(true) end
| _ => constr:(false)
end.

Ltac npol_get_term dir term :=
match term with
|  (?op ?X  ?Y)%nat =>
     match dir with P.L => X | P.R => Y end
|  (?X = ?Y)%nat =>
     match dir with P.L => X | P.R => Y end
| _ => fail 1 "Unknown term in npol_get_term"
end.

Ltac npol_replace_term term1 term2 dir1 dir2 occ id := 
  let dir2opp := eval compute in (P.pol_dir_opp dir2) in
  let t1 := npol_get_term dir2 term2 in
  let t2 := match id with true => t1 | false => npol_get_term dir2opp term2 end in
  match term1 with
   | (?op ?X ?Y) =>
     match dir1 with
         P.L  =>
             Natreplace_term X t1 t2 occ id
       | P.R => 
            Natreplace_term Y t1 t2 occ id
      end
  | (?X = ?Y)%nat  =>
     match dir1 with
       P.L  =>
             Natreplace_term X t1 t2 occ id
     | P.R => 
             Natreplace_term Y  t1 t2 occ id
      end
  end.


Ltac npol_aux_dir term dir :=
  match term with
   (_ < _)%nat => dir
  | (_ > _)%nat => dir
  | (_ <= _)%nat => eval compute in (P.pol_dir_opp dir) 
  | (_ >= _)%nat => eval compute in (P.pol_dir_opp dir) 
end.

Ltac Nat_eq_trans_l t:= 
   match goal with
     |  |- (?X >= ?Y)%nat => apply eq_ge_trans_l with t 
     |  |- (?X > ?Y)%nat => apply eq_gt_trans_l with t 
     |  |- (?X <= ?Y)%nat => apply eq_le_trans_l with t 
     |  |- (?X < ?Y)%nat => apply eq_lt_trans_l with t 
     |  |- ?G  => apply trans_equal with t 
    end.

Ltac Nat_eq_trans_r t:= 
   match goal with
     |  |- (?X >= ?Y)%nat => apply eq_ge_trans_r with t 
     |  |- (?X > ?Y)%nat => apply eq_gt_trans_r with t 
     |  |- (?X <= ?Y)%nat => apply eq_le_trans_r with t 
     |  |- (?X < ?Y)%nat => apply eq_lt_trans_r with t 
     |  |- ?G  => apply trans_equal_r with t 
    end.

(* Do the replacement *)
Ltac Natreplace_tac_full term dir1 dir2 occ :=
match term with
 (?T1 = ?T2)%nat =>
  (* We have here a substitution *)
  match goal with
     |-  ?G => let  t := npol_replace_term G term dir1 dir2 occ false in
              match dir1 with
               P.L => Nat_eq_trans_l t
              | P.R => Nat_eq_trans_r t
              end
  end
| _ =>
   match goal with
     |  |- (?X >= ?Y)%nat =>
            let  t := npol_replace_term (X >= Y)%nat term dir1 dir2 occ false in
               apply ge_trans with t
     |  |- (?X <= ?Y)%nat =>
            let  t := npol_replace_term (X <= Y)%nat term dir1 dir2 occ false in
               apply le_trans with t
     |  |- (?X > ?Y)%nat  =>
            let  t := npol_replace_term (X > Y)%nat term dir1 dir2 occ false in
           match npol_aux_dir term dir1 with
                P.L =>
                                    (apply gt_le_trans with t)
               |P.R =>
                                    (apply le_gt_trans with t)
            end
     |  |- (?X < ?Y)%nat   =>
            let  t := npol_replace_term (X < Y)%nat term dir1 dir2 occ false in
           match npol_aux_dir term dir1 with
                P.L =>
                                    (apply lt_le_trans with t)
               |P.R =>
                                    (apply le_lt_trans with t)
            end
   end
end.


(* Make the term appears *)
Ltac Natreplace_tac_full_id term dir1 dir2 occ :=
  match goal with
     |-  ?G => let t1 := npol_replace_term G term dir1 dir2 occ true in 
                match dir1 with
                  P.L => Nat_eq_trans_l t1
               | P.R => Nat_eq_trans_r t1
                end; [ring | idtac]
end.

Ltac npolrx term dir1 dir2 occ :=
match npol_is_compare term with
  true => Natreplace_tac_full_id term dir1 dir2 occ; [Natreplace_tac_full term dir1 dir2 occ]
| false => 
     let t := type of term in
     match npol_is_compare t with true => 
Natreplace_tac_full_id t dir1 dir2 occ; [Natreplace_tac_full t dir1 dir2 occ]
     end 
end.

Ltac npolr term :=
  npolrx term P.L P.L 1%Z  ||
  npolrx term P.R P.L 1%Z ||
  npolrx term P.L P.R 1%Z ||
  npolrx term P.R P.R 1%Z.
