Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Proper.

Set Implicit Arguments.
Set Strict Implicit.

Hint Extern 1 (proper (fun x => _)) => apply proper_fun; intros : typeclass_instances.
Hint Extern 1 (equal (fun x => _) _) => apply proper_fun; intros : typeclass_instances.
Hint Extern 1 (equal _ (fun x => _)) => apply proper_fun; intros : typeclass_instances.
Hint Extern 0 (PReflexive _) => eapply equiv_prefl.

Ltac solve_proper :=
  repeat match goal with 
           | |- _ => solve [ eauto ]
           | |- proper (fun x => _) => eapply proper_fun; intros; solve_equal
           | |- _ => eapply proper_app; 
             [ solve [ eauto with typeclass_instances ] 
             | solve [ eauto with typeclass_instances ]
             | solve_proper | solve_proper ]
         end;
  eauto with typeclass_instances
with solve_equal :=
  repeat match goal with
           | |- _ => solve [ eauto ]
           | |- equal ?X ?X => 
             solve [ eapply preflexive with (wf := proper); eauto 100 with typeclass_instances ]
           | |- equal (fun x => _) _ => eapply equal_fun; intros
           | |- equal _ (fun x => _) => eapply equal_fun; intros
           | |- _ => eapply equal_app
         end; eauto with typeclass_instances.

Ltac type_tac :=
  match goal with
    | |- proper _ => solve_proper
    | |- equal _ _ => solve_equal
  end.