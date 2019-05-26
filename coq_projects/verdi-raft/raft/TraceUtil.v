Require Import VerdiRaft.Raft.

Section TraceUtil.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition has_key (c : clientId) (i : nat) (e : entry) :=
    match e with
      | mkEntry _ c' i' _ _ _ => andb (if clientId_eq_dec c c' then true else false) (beq_nat i i')
    end.

  Definition key_in_output_list (client : clientId) (id : nat) (os : list raft_output) :=
    exists o,
      In (ClientResponse client id o) os.

  Definition is_client_response_with_key (client : clientId) (id : nat) (out : raft_output) : bool :=
    match out with
      | ClientResponse c i _ => andb (if clientId_eq_dec client c then true else false) (beq_nat id i)
      | NotLeader _ _ => false
    end.

  Definition key_in_output_list_dec (client : clientId) (id : nat) (os : list raft_output) :
    {key_in_output_list client id os} + {~ key_in_output_list client id os}.
  Proof using. 
    unfold key_in_output_list.
    destruct (find (is_client_response_with_key client id) os) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      unfold is_client_response_with_key in *. break_match; try discriminate.
      subst. do_bool. break_and. break_if; try discriminate. do_bool. subst. left. eauto.
    - right. intro. break_exists.
      eapply find_none in H; eauto. unfold is_client_response_with_key in *.
      find_apply_lem_hyp Bool.andb_false_elim.
      intuition; try break_if; do_bool; congruence.
  Qed.

  Definition key_in_output_trace (client : clientId) (id : nat)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists os h,
      In (h, inr os) tr /\
      key_in_output_list client id os.

  Definition key_in_output_trace_dec (client : clientId) (id : nat) :
    forall tr : list (name * (raft_input + list raft_output)),
      {key_in_output_trace client id tr} + {~ key_in_output_trace client id tr}.
  Proof using. 
    unfold key_in_output_trace.
    intros.
    destruct (find (fun p => match snd p with
                               | inr l => match find (is_client_response_with_key client id) l with
                                            | Some x => true
                                            | None => false
                                          end
                               | _ => false
                             end) tr) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      repeat break_match; try discriminate.
      find_apply_lem_hyp find_some. break_and.
      unfold is_client_response_with_key, key_in_output_list in *.
      break_match; try discriminate. do_bool. break_and. do_bool. break_if; try discriminate. subst.
      left. exists l, (fst p).
      find_reverse_rewrite. rewrite <- surjective_pairing.
      intuition eauto.
    - right. intro. break_exists. break_and.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. break_match; try discriminate.
      unfold key_in_output_list in *. break_exists.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. find_apply_lem_hyp Bool.andb_false_elim.
      intuition; try break_if; (do_bool; congruence).
  Qed.


  Definition in_output_list (client : clientId) (id : nat) (o : output) (os : list raft_output) :=
    In (ClientResponse client id o) os.

  Definition is_client_response (client : clientId) (id : nat) (o : output) (out : raft_output) : bool :=
    match out with
      | ClientResponse c i o' => andb (andb (if clientId_eq_dec client c then true else false) (beq_nat id i))
                                     (if output_eq_dec o o' then true else false)
      | NotLeader _ _ => false
    end.

  Definition in_output_list_dec (client : clientId) (id : nat) (o : output) (os : list raft_output) :
    {in_output_list client id o os} + {~ in_output_list client id o os}.
  Proof using raft_params. 
    unfold in_output_list.
    destruct (find (is_client_response client id o) os) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      unfold is_client_response in *. break_match; try discriminate.
      subst. do_bool. break_and. break_if; try congruence.
      break_if; try discriminate.
      repeat (do_bool; intuition). subst. intuition.
    - right. intro. break_exists.
      eapply find_none in H; eauto. unfold is_client_response in *.
      find_apply_lem_hyp Bool.andb_false_elim.
      repeat (do_bool; intuition); try break_if; try congruence.
  Qed.

  Definition in_output_trace (client : clientId) (id : nat) (o : output)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists os h,
      In (h, inr os) tr /\
      in_output_list client id o os.
  
  Definition in_input_trace (client : clientId) (id : nat) (i : input)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
      exists h,
        In (h, inl (ClientRequest client id i)) tr.
  
  Definition is_output_with_key (client : clientId) (id : nat)
             (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inr os) => if key_in_output_list_dec client id os then true else false
      | _ => false
    end.

  Definition is_input_with_key (client : clientId) (id: nat)
             (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inl (ClientRequest c i _)) => andb (if clientId_eq_dec client c then true else false) (beq_nat id i)
      | _ => false
    end.
End TraceUtil.
