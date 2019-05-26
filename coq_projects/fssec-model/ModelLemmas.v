Require Export ModelProperties. 
Require Export aclstatIsSecure. 
Require Export chmodIsSecure. 
Require Export createIsSecure. 
Require Export mkdirIsSecure. 
Require Export openIsSecure. 
Require Export addUsrGrpToAclIsSecure. 
Require Export chobjscIsSecure. 
Require Export chownIsSecure. 
Require Export chsubscIsSecure. 
Require Export closeIsSecure. 
Require Export delUsrGrpFromAclIsSecure. 
Require Export oscstatIsSecure. 
Require Export owner_closeIsSecure. 
Require Export readIsSecure. 
Require Export readdirIsSecure. 
Require Export rmdirIsSecure. 
Require Export sscstatIsSecure. 
Require Export statIsSecure. 
Require Export unlinkIsSecure. 
Require Export writeIsSecure. 
Require Import InitialState. 
Require Export Le. 
 
 
(*This definition generalizes the notion of secure state. It includes*) 
(*all the security relevant conditions and also the mathematicals    *) 
(*ones (for instance the one that asserts that subjectSC is a partial*) 
(*function).                                                         *) 
 
Definition GeneralSecureState (s : SFSstate) : Prop :=
  SecureState s /\
  StarProperty s /\
  FuncPre1 s /\
  FuncPre2 s /\
  FuncPre3 s /\ FuncPre4 s /\ FuncPre5 s /\ FuncPre6 s /\ FuncPre7 s. 
 
(*********************************************************************) 
(*                       The Model's Lemmas                          *) 
(*********************************************************************) 
 
 
(*The following Lemma shows that the initial state is a secure state.*) 
 
Lemma InitialStateIsSecure : GeneralSecureState InitState. 
unfold GeneralSecureState, SecureState, InitState, DACSecureState,
 MACSecureState, StarProperty, FuncPre1, FuncPre2, FuncPre3, FuncPre4,
 FuncPre5, FuncPre6, FuncPre7 in |- *; simpl in |- *. 
repeat (split; auto). 
intros.
elim (fSSC SysSubjectSC root); auto. 
 
contradiction. 
 
contradiction. 

contradiction.
 
Qed. 

 
(*The main lemma deals with secuences of SFSstates.                  *) 
(*In that lemma we'll use the function nth (defined in PolyList)     *) 
(*which takes a natural (n), a list, and a default element with the  *) 
(*type of the list, and returns the n(th) element of list if there   *) 
(*are enough elements in it, or the default element if not.          *) 
(*For this reason, we need to define a default SFSstate. In fact we  *) 
(*won't use it in the proof, it's just a type requirement.           *) 
 
Parameter defaultState : SFSstate. 
 
 
(*The main Lemma for the model is the following one, wich says that  *) 
(*for any given sequence of states such that the initial state is    *) 
(*secure and for any two consecutives states, s and t, exists an     *) 
(*operation (op) and a user (u) executing it, such that              *) 
(*(TransFunc u s op t) holds, then every state in the secuence is    *) 
(*secure.                                                            *) 
 
Lemma BasicSecurityTheorem :
 forall tr : list SFSstate,
 GeneralSecureState (nth 0 tr defaultState) ->
 (forall n : nat,
  n < length tr ->
  exists op : Operation,
    (exists u : SUBJECT,
       TransFunc u (nth n tr defaultState) op (nth (S n) tr defaultState))) ->
 forall n : nat, n <= length tr -> GeneralSecureState (nth n tr defaultState). 
intros. 
induction  n as [| n Hrecn]. 
auto. 
 
generalize Hrecn. 
cut
 (exists op : Operation,
    (exists u : SUBJECT,
       TransFunc u (nth n tr defaultState) op (nth (S n) tr defaultState))). 
elim (nth n tr defaultState). 
intros. 
elim H2; intros. 
elim H3; intros. 
cut
 (forall u : SUBJECT,
  GeneralSecureState
    (mkSFS groups primaryGrp subjectSC AllGrp RootGrp SecAdmGrp objectSC acl
       secmat files directories) ->
  TransFunc u
    (mkSFS groups primaryGrp subjectSC AllGrp RootGrp SecAdmGrp objectSC acl
       secmat files directories) x (nth (S n) tr defaultState) ->
  GeneralSecureState (nth (S n) tr defaultState)). 
intro GTR; apply (GTR x0). 
apply Hrecn0; auto with *. 
 
auto. 
 
unfold GeneralSecureState in |- *; intros u GSSi TF; decompose [and] GSSi;
 clear GSSi. 
split. 
induction  x as [| | | | | | | | | | | | | | | | | | | ];
 prolog
  [ AclstatPSS AddUsrGrpToAclPSS ChmodPSS ChobjscPSS ChownPSS ChsubscPSS
   ClosePSS CreatePSS DelUsrGrpFromAclPSS MkdirPSS OpenPSS OscstatPSS
   Owner_ClosePSS ReadPSS ReaddirPSS RmdirPSS SscstatPSS StatPSS UnlinkPSS
   WritePSS ] 2. 
 
split. 
induction  x as [| | | | | | | | | | | | | | | | | | | ];
 prolog
  [ AclstatPSP AddUsrGrpToAclPSP ChmodPSP ChobjscPSP ChownPSP ChsubscPSP
   ClosePSP CreatePSP DelUsrGrpFromAclPSP MkdirPSP OpenPSP OscstatPSP
   Owner_ClosePSP ReadPSP ReaddirPSP RmdirPSP SscstatPSP StatPSP UnlinkPSP
   WritePSP ] 2. 
 
split. 
unfold FuncPre1 in |- *; unfold FuncPre1 in H6; decompose [and] H6;
 repeat (split; eauto). 
 
unfold FuncPre2, FuncPre3, FuncPre4, FuncPre5, FuncPre6, FuncPre7 in |- *;
 unfold FuncPre2, FuncPre3, FuncPre4, FuncPre5, FuncPre6, FuncPre7
  in H8, H9, H10, H11, H12, H14; repeat (split; eauto). 
 
auto. 
 
Qed.