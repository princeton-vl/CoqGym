Require Import Reals.
Require Import PolAux.

Ltac RCst0 t :=
  match t with
   | R0 => constr:(Z0)
   | R1 => constr:(Zpos xH)
   | Rplus ?e1 ?e2 =>
       match (RCst0 e1) with
      | ?e3 => match (RCst0 e2) with
              |  ?e4 => constr:(Zplus e3  e4)
              end
      end
   | Rminus ?e1 ?e2 =>
       match (RCst0 e1) with
      | ?e3 => match (RCst0 e2) with
              |  ?e4 => constr:(Zminus e3  e4)
              end
      end
   | Rmult ?e1 ?e2 =>
       match (RCst0 e1) with
      | ?e3 => match (RCst0 e2) with
              |  ?e4 => constr:(Zmult e3  e4)
              end
      end
   | Ropp ?e1 =>
       match (RCst0 e1) with
      | ?e3 => constr:(Z.opp e3)
      end
   | IZR ?e1 =>
       match (ZCst e1) with
       | ?e3 => e3
       end
   | _ => constr:(0%Z)
 end.

Ltac rground_tac := match goal with
|- (?X1 <= ?X2)%R => 
       let r1 := RCst0 X1 in
       let r2 := RCst0 X2 in
       change (Z2R r1 <= Z2R r2)%R; apply Z2R_le; red; apply refl_equal || intros; discriminate
| |- (?X1 < ?X2)%R => 
       let r1 := RCst0 X1 in
       let r2 := RCst0 X2 in
       change (Z2R r1 < Z2R r2)%R; apply Z2R_lt; red; apply refl_equal || intros; discriminate
| |- (?X1 >= ?X2)%R => 
       let r1 := RCst0 X1 in
       let r2 := RCst0 X2 in
       change (Z2R r1 >= Z2R r2)%R; apply Z2R_ge; red; apply refl_equal || intros; discriminate
| |- (?X1 > ?X2)%R => 
       let r1 := RCst0 X1 in
       let r2 := RCst0 X2 in
       change (Z2R r1 > Z2R r2)%R; apply Z2R_gt; red; apply refl_equal || intros; discriminate
end.

Hint Extern 4 (_ <= _)%R => rground_tac: real.
Hint Extern 4 (_ < _)%R => rground_tac: real.
Hint Extern 4 (_ >= _)%R => rground_tac: real.
Hint Extern 4 (_ > _)%R => rground_tac: real.

