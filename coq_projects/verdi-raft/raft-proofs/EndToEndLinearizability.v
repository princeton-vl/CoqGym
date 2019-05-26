Require Import VerdiRaft.Raft.
Require Import VerdiRaft.Linearizability.

Require Import VerdiRaft.RaftLinearizableProofs.

Require Import VerdiRaft.OutputCorrectInterface.
Require Import VerdiRaft.OutputCorrectProof.

Require Import VerdiRaft.InputBeforeOutputInterface.
Require Import VerdiRaft.InputBeforeOutputProof.

Require Import VerdiRaft.CausalOrderPreservedInterface.
Require Import VerdiRaft.CausalOrderPreservedProof.

Require Import VerdiRaft.AppliedImpliesInputInterface.
Require Import VerdiRaft.AppliedImpliesInputProof.

Require Import VerdiRaft.OutputImpliesAppliedInterface.
Require Import VerdiRaft.OutputImpliesAppliedProof.

Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.LogMatchingProof.

Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.SortedProof.

Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.TermSanityProof.

Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeaderSublogProof.

Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RaftRefinementProof.

Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.CandidateEntriesProof.

Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesTermProof.

Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectProof.

Require Import VerdiRaft.VotesLeCurrentTermInterface.
Require Import VerdiRaft.VotesLeCurrentTermProof.

Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.VotesCorrectProof.

Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesProof.

Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.OneLeaderPerTermProof.

Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.UniqueIndicesProof.

Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicProof.

Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.StateMachineSafetyProof.

Require Import VerdiRaft.MaxIndexSanityInterface.

Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.LeaderCompletenessProof.

Require Import VerdiRaft.TransitiveCommitInterface.
Require Import VerdiRaft.TransitiveCommitProof.

Require Import VerdiRaft.AllEntriesLeaderLogsInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsProof.

Require Import VerdiRaft.CommitRecordedCommittedInterface.

Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsTermSanityProof.


Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.AllEntriesTermSanityProof.

Require Import VerdiRaft.VotesWithLogTermSanityInterface.
Require Import VerdiRaft.VotesWithLogTermSanityProof.

Require Import VerdiRaft.LeaderLogsPreservedInterface.
Require Import VerdiRaft.LeaderLogsPreservedProof.

Require Import VerdiRaft.PrefixWithinTermInterface.
Require Import VerdiRaft.PrefixWithinTermProof.

Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.EveryEntryWasCreatedProof.

Require Import VerdiRaft.EveryEntryWasCreatedHostLogInterface.
Require Import VerdiRaft.EveryEntryWasCreatedHostLogProof.

Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Require Import VerdiRaft.LeaderLogsVotesWithLogProof.

Require Import VerdiRaft.AllEntriesLogInterface.
Require Import VerdiRaft.AllEntriesLogProof.

Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesVotesWithLogProof.

Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.VotesWithLogSortedProof.

Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingProof.

Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeProof.

Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsProof.

Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersProof.

Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsSortedProof.

Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LeaderLogsContiguousProof.

Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LogsLeaderLogsProof.

Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.OneLeaderLogPerTermProof.

Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderLogsSublogProof.

Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsProof.

Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongProof.

Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.NextIndexSafetyProof.

Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasProof.

Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesProof.

Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Require Import VerdiRaft.AllEntriesCandidateEntriesProof.

Require Import VerdiRaft.AllEntriesLogMatchingInterface.
Require Import VerdiRaft.AllEntriesLogMatchingProof.

Require Import VerdiRaft.AppendEntriesRequestTermSanityInterface.
Require Import VerdiRaft.AppendEntriesRequestTermSanityProof.

Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.AllEntriesLeaderSublogProof.

Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingProof.

Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.LastAppliedLeCommitIndexProof.

Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsTermProof.

Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.StateMachineCorrectProof.

Require Import VerdiRaft.OutputGreatestIdInterface.
Require Import VerdiRaft.OutputGreatestIdProof.

Require Import VerdiRaft.CurrentTermGtZeroInterface.
Require Import VerdiRaft.CurrentTermGtZeroProof.

Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogProof.

Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneProof.

Require Import VerdiRaft.CandidateTermGtLogInterface.
Require Import VerdiRaft.CandidateTermGtLogProof.

Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondProof.

Require Import VerdiRaft.PrevLogLeaderSublogInterface.
Require Import VerdiRaft.PrevLogLeaderSublogProof.

Require Import VerdiRaft.AllEntriesIndicesGt0Interface.
Require Import VerdiRaft.AllEntriesIndicesGt0Proof.

Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Require Import VerdiRaft.PrevLogCandidateEntriesTermProof.

Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Require Import VerdiRaft.MatchIndexAllEntriesProof.

Require Import VerdiRaft.MatchIndexLeaderInterface.
Require Import VerdiRaft.MatchIndexLeaderProof.

Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.MatchIndexSanityProof.

Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.
Require Import VerdiRaft.NoAppendEntriesToLeaderProof.

Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfProof.

Require Import VerdiRaft.NoAppendEntriesRepliesToSelfInterface.
Require Import VerdiRaft.NoAppendEntriesRepliesToSelfProof.

Require Import VerdiRaft.LogAllEntriesInterface.
Require Import VerdiRaft.LogAllEntriesProof.

Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.AppendEntriesReplySublogProof.

Require Import VerdiRaft.LeaderLogsLogPropertiesInterface.
Require Import VerdiRaft.LeaderLogsLogPropertiesProof.

Require Import VerdiRaft.AppendEntriesRequestReplyCorrespondenceInterface.
Require Import VerdiRaft.AppendEntriesRequestReplyCorrespondenceProof.

Require Import VerdiRaft.AppendEntriesLeaderInterface.
Require Import VerdiRaft.AppendEntriesLeaderProof.

Require Import VerdiRaft.RequestVoteMaxIndexMaxTermInterface.
Require Import VerdiRaft.RequestVoteMaxIndexMaxTermProof.

Require Import VerdiRaft.RequestVoteReplyMoreUpToDateInterface.
Require Import VerdiRaft.RequestVoteReplyMoreUpToDateProof.

Require Import VerdiRaft.RequestVoteReplyTermSanityInterface.
Require Import VerdiRaft.RequestVoteReplyTermSanityProof.

Require Import VerdiRaft.RequestVoteTermSanityInterface.
Require Import VerdiRaft.RequestVoteTermSanityProof.

Require Import VerdiRaft.VotedForMoreUpToDateInterface.
Require Import VerdiRaft.VotedForMoreUpToDateProof.

Require Import VerdiRaft.VotedForTermSanityInterface.
Require Import VerdiRaft.VotedForTermSanityProof.

Require Import VerdiRaft.VotesReceivedMoreUpToDateInterface.
Require Import VerdiRaft.VotesReceivedMoreUpToDateProof.

Require Import VerdiRaft.RaftMsgRefinementInterface.
Require Import VerdiRaft.RaftMsgRefinementProof.

Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogCorrectProof.

Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesProof.

Require Import VerdiRaft.InLogInAllEntriesInterface.
Require Import VerdiRaft.InLogInAllEntriesProof.

Require Import VerdiRaft.GhostLogAllEntriesInterface.
Require Import VerdiRaft.GhostLogAllEntriesProof.

Require Import VerdiRaft.GhostLogLogMatchingInterface.
Require Import VerdiRaft.GhostLogLogMatchingProof.


Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Hint Extern 4 (@raft_refinement_interface _ _ _) => apply rri : typeclass_instances.
Hint Extern 4 (@raft_msg_refinement_interface _ _ _) => apply rmri : typeclass_instances.
Hint Extern 4 (@cronies_term_interface _ _ _) => apply cti : typeclass_instances.
Hint Extern 4 (@votes_correct_interface _ _ _) => apply vci : typeclass_instances.
Hint Extern 4 (@votes_le_current_term_interface _ _ _) => apply vlcti : typeclass_instances.
Hint Extern 4 (@cronies_correct_interface _ _ _) => apply cci : typeclass_instances.
Hint Extern 4 (@candidates_vote_for_selves_interface _ _ _) => apply cvfsi : typeclass_instances.
Hint Extern 4 (@candidate_entries_interface _ _ _) => apply cei : typeclass_instances.
Hint Extern 4 (@one_leader_per_term_interface _ _ _) => apply olpti : typeclass_instances.
Hint Extern 4 (@leader_sublog_interface _ _ _) => apply lsi : typeclass_instances.
Hint Extern 4 (@unique_indices_interface _ _ _) => apply uii : typeclass_instances.
Hint Extern 4 (@sorted_interface _ _ _) => apply si : typeclass_instances.
Hint Extern 4 (@term_sanity_interface _ _ _) => apply tsi : typeclass_instances.
Hint Extern 4 (@log_matching_interface _ _ _) => apply lmi : typeclass_instances.
Hint Extern 4 (@applied_entries_monotonic_interface _ _ _) => apply aemi : typeclass_instances.
Hint Extern 4 (@state_machine_safety_interface _ _ _) => apply smsi : typeclass_instances.
Hint Extern 4 (@output_implies_applied_interface _ _ _) => apply oiai : typeclass_instances.
Hint Extern 4 (@applied_implies_input_interface _ _ _) => apply aiii : typeclass_instances.
Hint Extern 4 (@causal_order_preserved_interface _ _ _) => apply copi : typeclass_instances.
Hint Extern 4 (@input_before_output_interface _ _ _) => apply iboi : typeclass_instances.
Hint Extern 4 (@output_correct_interface _ _ _) => apply oci : typeclass_instances.
Hint Extern 4 (@max_index_sanity_interface _ _ _) => apply misi : typeclass_instances.
Hint Extern 4 (@leader_completeness_interface _ _ _) => apply lci : typeclass_instances.
Hint Extern 4 (@transitive_commit_interface _ _ _) => apply tci : typeclass_instances.
Hint Extern 4 (@all_entries_leader_logs_interface _ _ _) => apply aelli : typeclass_instances.
Hint Extern 4 (@commit_recorded_committed_interface _ _ _) => apply crci : typeclass_instances.
Hint Extern 4 (@leaderLogs_term_sanity_interface _ _ _) => apply lltsi : typeclass_instances.
Hint Extern 4 (@allEntries_term_sanity_interface _ _ _) => apply aetsi : typeclass_instances.
Hint Extern 4 (@votesWithLog_term_sanity_interface _ _ _) => apply vwltsi : typeclass_instances.
Hint Extern 4 (@leaderLogs_preserved_interface _ _ _) => apply llpi : typeclass_instances.
Hint Extern 4 (@prefix_within_term_interface _ _ _) => apply pwti : typeclass_instances.
Hint Extern 4 (@every_entry_was_created_interface _ _ _) => apply eewci : typeclass_instances.
Hint Extern 4 (@every_entry_was_created_host_log_interface _ _ _) => apply eewchli : typeclass_instances.
Hint Extern 4 (@leaderLogs_votesWithLog_interface _ _ _) => apply llvwli : typeclass_instances.
Hint Extern 4 (@allEntries_log_interface _ _ _) => apply aeli : typeclass_instances.
Hint Extern 4 (@allEntries_votesWithLog_interface _ _ _) => apply aevwli : typeclass_instances.
Hint Extern 4 (@votesWithLog_sorted_interface _ _ _) => apply vwlsi : typeclass_instances.
Hint Extern 4 (@leaderLogs_entries_match_interface _ _ _) => apply lllmi : typeclass_instances.
Hint Extern 4 (@state_machine_safety'interface _ _ _) => apply sms'i : typeclass_instances.
Hint Extern 4 (@append_entries_leaderLogs_interface _ _ _) => apply aerlli : typeclass_instances.
Hint Extern 4 (@append_entries_came_from_leaders_interface _ _ _) => apply aercfli : typeclass_instances.
Hint Extern 4 (@leaderLogs_sorted_interface _ _ _) => apply llsi : typeclass_instances.
Hint Extern 4 (@leaderLogs_contiguous_interface _ _ _) => apply llci : typeclass_instances.
Hint Extern 4 (@logs_leaderLogs_interface _ _ _) => apply llli : typeclass_instances.
Hint Extern 4 (@one_leaderLog_per_term_interface _ _ _) => apply ollpti : typeclass_instances.
Hint Extern 4 (@leaderLogs_sublog_interface _ _ _) => apply llsli : typeclass_instances.
Hint Extern 4 (@leaders_have_leaderLogs_interface _ _ _) => apply lhlli : typeclass_instances.
Hint Extern 4 (@leaders_have_leaderLogs_strong_interface _ _ _) => apply lhllsi : typeclass_instances.
Hint Extern 4 (@nextIndex_safety_interface _ _ _) => apply nisi : typeclass_instances.
Hint Extern 4 (@refined_log_matching_lemmas_interface _ _ _) => apply rlmli : typeclass_instances.
Hint Extern 4 (@leaderLogs_candidate_entries_interface _ _ _) => apply llcei : typeclass_instances.
Hint Extern 4 (@allEntries_candidate_entries_interface _ _ _) => apply aecei : typeclass_instances.
Hint Extern 4 (@allEntries_log_matching_interface _ _ _) => apply aelmi : typeclass_instances.
Hint Extern 4 (@append_entries_request_term_sanity_interface _ _ _) => apply aertsi : typeclass_instances.
Hint Extern 4 (@allEntries_leader_sublog_interface _ _ _) => apply aelsi : typeclass_instances.
Hint Extern 4 (@lastApplied_commitIndex_match_interface _ _ _) => apply lacimi : typeclass_instances.
Hint Extern 4 (@lastApplied_le_commitIndex_interface _ _ _) => apply lalcii : typeclass_instances.
Hint Extern 4 (@allEntries_leaderLogs_term_interface _ _ _) => apply aellti : typeclass_instances.
Hint Extern 4 (@state_machine_correct_interface _ _ _) => apply smci : typeclass_instances.
Hint Extern 4 (@output_greatest_id_interface _ _ _) => apply ogii : typeclass_instances.
Hint Extern 4 (@current_term_gt_zero_interface _ _ _) => apply ctgzi : typeclass_instances.
Hint Extern 4 (@terms_and_indices_from_one_log_interface _ _ _) => apply taifoli : typeclass_instances.
Hint Extern 4 (@terms_and_indices_from_one_interface _ _ _) => apply taifoi : typeclass_instances.
Hint Extern 4 (@candidate_term_gt_log_interface _ _ _) => apply ctgli : typeclass_instances.
Hint Extern 4 (@votes_votesWithLog_correspond_interface _ _ _) => apply vvci : typeclass_instances.
Hint Extern 4 (@prevLog_leader_sublog_interface _ _ _) => apply pllsi : typeclass_instances.
Hint Extern 4 (@allEntries_indices_gt_0_interface _ _ _) => apply aeigt0 : typeclass_instances.
Hint Extern 4 (@prevLog_candidateEntriesTerm_interface _ _ _) => apply plceti : typeclass_instances.
Hint Extern 4 (@match_index_all_entries_interface _ _ _) => apply miaei : typeclass_instances.
Hint Extern 4 (@match_index_leader_interface _ _ _) => apply mili : typeclass_instances.
Hint Extern 4 (@match_index_sanity_interface _ _ _) => apply matchisi : typeclass_instances.
Hint Extern 4 (@no_append_entries_to_leader_interface _ _ _) => apply noaetli : typeclass_instances.
Hint Extern 4 (@no_append_entries_to_self_interface _ _ _) => apply noaetsi : typeclass_instances.
Hint Extern 4 (@no_append_entries_replies_to_self_interface _ _ _) => apply noaertsi : typeclass_instances.
Hint Extern 4 (@log_all_entries_interface _ _ _) => apply laei : typeclass_instances.
Hint Extern 4 (@append_entries_reply_sublog_interface _ _ _) => apply aersi : typeclass_instances.
Hint Extern 4 (@log_properties_hold_on_leader_logs_interface _ _ _) => apply lpholli : typeclass_instances.
Hint Extern 4 (@log_properties_hold_on_ghost_logs_interface _ _ _) => apply lphogli : typeclass_instances.
Hint Extern 4 (@append_entries_request_reply_correspondence_interface _ _ _) => apply aerrci : typeclass_instances.
Hint Extern 4 (@append_entries_leader_interface _ _ _) => apply appendeli : typeclass_instances.
Hint Extern 4 (@requestVote_maxIndex_maxTerm_interface _ _ _) => apply rvmimti : typeclass_instances.
Hint Extern 4 (@requestVoteReply_moreUpToDate_interface _ _ _) => apply rvrmutdi : typeclass_instances.
Hint Extern 4 (@requestVoteReply_term_sanity_interface _ _ _) => apply rvrtsi : typeclass_instances.
Hint Extern 4 (@requestVote_term_sanity_interface _ _ _) => apply rvtsi : typeclass_instances.
Hint Extern 4 (@votedFor_moreUpToDate_interface _ _ _) => apply vfmutdi : typeclass_instances.
Hint Extern 4 (@votedFor_term_sanity_interface _ _ _) => apply vftsi : typeclass_instances.
Hint Extern 4 (@votesReceived_moreUpToDate_interface _ _ _) => apply vrmutdi : typeclass_instances.
Hint Extern 4 (@ghost_log_correct_interface _ _ _) => apply glci : typeclass_instances.
Hint Extern 4 (@in_log_in_all_entries_interface _ _ _) => apply iliaei : typeclass_instances.
Hint Extern 4 (@ghost_log_allEntries_interface _ _ _) => apply glaei : typeclass_instances.
Hint Extern 4 (@ghost_log_entries_match_interface _ _ _) => apply glemi : typeclass_instances.

Section EndToEndProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star (params := failure_params) step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using. 
    intros.
    eapply (@raft_linearizable' orig_base_params one_node_params raft_params); eauto;
    auto with typeclass_instances.
  Qed.
End EndToEndProof.

