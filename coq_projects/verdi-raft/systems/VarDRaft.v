Require Import VerdiRaft.Raft.
Require Import Verdi.VarD.
Require Import String.

Section VarDRaft.
  Variable n : nat.

  Instance raft_params : RaftParams vard_base_params :=
    {
      N := n;
      input_eq_dec := input_eq_dec;
      output_eq_dec := output_eq_dec;
      clientId := string;
      clientId_eq_dec := string_dec
    }.

  Definition vard_raft_base_params := base_params.
  Definition vard_raft_multi_params := multi_params.
  Definition vard_raft_failure_params := failure_params.
End VarDRaft.
