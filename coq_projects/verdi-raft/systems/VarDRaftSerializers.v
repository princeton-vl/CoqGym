Require Import Verdi.Verdi.
Require Import Verdi.VarD.

Require Import Cheerios.Cheerios.
Require Import Cheerios.Tree.

Require Import VerdiRaft.Raft.
Require Import VerdiRaft.VarDRaft.

Import DeserializerNotations.

Definition serialize_input (i : VarD.input) :=
  match i with
  | Put k v => serialize x00 +$+ serialize k +$+ serialize v
  | Get k => serialize x01 +$+ serialize k
  | Del k => serialize x02 +$+ serialize k
  | CAS k opt v => serialize x03 +$+ serialize k +$+ serialize opt +$+ serialize v
  | CAD k v => serialize x04 +$+ serialize k +$+ serialize v
  end.

Definition deserialize_input : ByteListReader.t VarD.input :=
  tag <- deserialize;;
  match tag with
  | x00 =>
    k <- deserialize;;
    v <- deserialize;;
    ByteListReader.ret (Put k v)
  | x01 => Get <$> deserialize
  | x02 => Del <$> deserialize
  | x03 =>
    k <- deserialize;;
    opt <- deserialize;;
    v <- deserialize;;
    ByteListReader.ret (CAS k opt v)
  | x04 =>
    k <- deserialize;;
    v <- deserialize;;
    ByteListReader.ret (CAD k v)
  | _ => ByteListReader.error
  end.

Lemma input_serialize_deserialize_id :
  serialize_deserialize_id_spec serialize_input deserialize_input.
Proof.
  intros.
  unfold serialize_input, deserialize_input.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance input_Serializer : Serializer VarD.input :=
  {| serialize := serialize_input;
     deserialize := deserialize_input;
     serialize_deserialize_id := input_serialize_deserialize_id |}.

Section Serializers.
  Variable n : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Definition entry_serialize (e : entry) := 
   serialize (Raft.eAt e) +$+
   serialize (Raft.eClient e) +$+
   serialize (Raft.eId e) +$+
   serialize (Raft.eIndex e) +$+
   serialize (Raft.eTerm e) +$+
   serialize (Raft.eInput e).

  Definition entry_deserialize : ByteListReader.t entry :=
    At <- deserialize;;
    Client <- deserialize;;
    Id <- deserialize;;
    Index <- deserialize;;
    Term <- deserialize;;
    Input <- deserialize;;
    ByteListReader.ret (Raft.mkEntry At Client Id Index Term Input).

  Lemma entry_serialize_deserialize_id :
    serialize_deserialize_id_spec entry_serialize entry_deserialize.
  Proof using.
    intros.
    unfold entry_serialize, entry_deserialize.
    cheerios_crush.
    destruct a;
      reflexivity.
  Qed.

  Instance entry_Serializer : Serializer entry :=
    {| serialize := entry_serialize;
       deserialize := entry_deserialize;
       serialize_deserialize_id := entry_serialize_deserialize_id |}.

  Definition msg_serialize (m : msg) : IOStreamWriter.t :=
    match m with
    | RequestVote t1 n i t2 =>
      serialize x00 +$+
      serialize t1 +$+
      serialize n +$+
      serialize i +$+
      serialize t2
    | RequestVoteReply t b =>
      serialize x01 +$+ serialize t +$+ serialize b
    | AppendEntries t1 n i1 t2 l2 i2 =>
      serialize x02 +$+
      serialize t1 +$+
      serialize n +$+
      serialize i1 +$+
      serialize t2 +$+
      serialize l2 +$+
      serialize i2
    | AppendEntriesReply t l b =>
      serialize x03 +$+ serialize t +$+ serialize l +$+ serialize b
    end.

  Definition RequestVote_deserialize : ByteListReader.t msg :=
    t1 <- deserialize;;
    n <- deserialize;;
    i <- deserialize;;
    t2 <- deserialize;;
    ByteListReader.ret (RequestVote t1 n i t2).

  Definition RequestVoteReply_deserialize : ByteListReader.t msg :=
    t <- deserialize;;
    b <- deserialize;;
    ByteListReader.ret (RequestVoteReply t b).

  Definition AppendEntries_deserialize : ByteListReader.t msg :=
    t1 <- deserialize;;
    n <- deserialize;;
    i1 <- deserialize;;
    t2 <- deserialize;;
    l <- deserialize;;
    i2 <- deserialize;;
    ByteListReader.ret (AppendEntries t1 n i1 t2 l i2).
  
  Definition AppendEntriesReply_deserialize : ByteListReader.t msg :=
    t <- deserialize;;
    l <- deserialize;;
    b <- deserialize;;
    ByteListReader.ret (AppendEntriesReply t l b).
  
  Definition msg_deserialize :=
    tag <- deserialize;;
    match tag with
    | x00 => RequestVote_deserialize
    | x01 => RequestVoteReply_deserialize
    | x02 => AppendEntries_deserialize
    | x03 => AppendEntriesReply_deserialize
    | _ => ByteListReader.error
    end.

  Lemma msg_serialize_deserialize_id :
    serialize_deserialize_id_spec msg_serialize msg_deserialize.
  Proof using.
    intros.
    unfold msg_serialize, msg_deserialize.
    destruct a;
      cheerios_crush;
      simpl;
      (unfold RequestVote_deserialize ||
       unfold RequestVoteReply_deserialize ||
       unfold AppendEntries_deserialize ||
       unfold AppendEntriesReply_deserialize);
      cheerios_crush.
  Qed.

  Global Instance msg_Serializer : Serializer msg :=
    {| serialize := msg_serialize;
       deserialize := msg_deserialize;
       serialize_deserialize_id := msg_serialize_deserialize_id |}.

  Definition serialize_serverType (t : serverType) :=
  match t with
  | Follower => serialize x00
  | Candidate => serialize x01
  | Leader => serialize x02
  end.

  Definition deserialize_serverType : ByteListReader.t serverType :=
  tag <- deserialize;;
  match tag with
  | x00 => ByteListReader.ret Follower
  | x01 => ByteListReader.ret Candidate
  | x02 => ByteListReader.ret Leader
  | _ => ByteListReader.error
  end.

  Lemma serverType_serialize_deserialize_id :
    serialize_deserialize_id_spec serialize_serverType deserialize_serverType.
  Proof using.
    intros.
    unfold serialize_serverType, deserialize_serverType.
    destruct a;
      repeat (cheerios_crush; simpl).
  Qed.

  Instance serverType_Serializer : Serializer serverType :=
    {| serialize := serialize_serverType;
       deserialize := deserialize_serverType;
       serialize_deserialize_id := serverType_serialize_deserialize_id |}.

  Definition serialize_output (o : output) :=
  match o with
  | Response key vo1 vo2 =>
    serialize key +$+ serialize vo1 +$+ serialize vo2
  end.

  Definition deserialize_output : ByteListReader.t output :=
  key <- deserialize;;
  vo1 <- deserialize;;
  vo2 <- deserialize;;
  ByteListReader.ret (Response key vo1 vo2).

  Lemma output_serialize_deserialize_id :
    serialize_deserialize_id_spec serialize_output deserialize_output.
  Proof using.
    intros.
    unfold serialize_output, deserialize_output.
    destruct a;
      repeat (cheerios_crush; simpl).
  Qed.

  Global Instance output_Serializer : Serializer output :=
    {| serialize := serialize_output;
       deserialize := deserialize_output;
       serialize_deserialize_id := output_serialize_deserialize_id |}.

  Definition serialize_raft_data (d : raft_data) :=
  serialize (currentTerm d) +$+
  serialize (votedFor d) +$+
  serialize (leaderId d) +$+
  serialize (log d) +$+
  serialize (commitIndex d) +$+
  serialize (lastApplied d) +$+
  serialize (stateMachine d) +$+
  serialize (nextIndex d) +$+
  serialize (matchIndex d) +$+
  serialize (shouldSend d) +$+
  serialize (votesReceived d) +$+
  serialize (type d) +$+
  serialize (clientCache d) +$+
  serialize (electoralVictories d).

  Definition deserialize_raft_data : ByteListReader.t raft_data :=
  cT <- deserialize;;
  lI <- deserialize;;
  l <- deserialize;;
  vF <- deserialize;;
  cI <- deserialize;;
  lA <- deserialize;;
  sM <- deserialize;;
  nI <- deserialize;;
  mI <- deserialize;;
  sS <- deserialize;;
  vR <- deserialize;;
  t <- deserialize;;
  cC <- deserialize;;
  eV <- deserialize;;
  ByteListReader.ret (mkRaft_data cT lI l vF cI lA sM nI mI sS vR t cC eV).

  Lemma raft_data_serialize_deserialize_id :
    serialize_deserialize_id_spec serialize_raft_data deserialize_raft_data.
  Proof using.
    intros.
    unfold serialize_raft_data, deserialize_raft_data.
    cheerios_crush.
    destruct a.
    reflexivity.
  Qed.

  Global Instance raft_data_Serializer : Serializer raft_data :=
    {| serialize := serialize_raft_data;
       deserialize := deserialize_raft_data;
       serialize_deserialize_id := raft_data_serialize_deserialize_id |}.

  Definition serialize_raft_input (ri : raft_input) :=
  match ri with
  | Timeout => serialize x00
  | ClientRequest n1 n2 i =>
    serialize x01 +$+ serialize n1 +$+ serialize n2 +$+ serialize i
  end.

  Definition deserialize_raft_input : ByteListReader.t raft_input :=
  tag <- deserialize;;
  match tag with
  | x00 => ByteListReader.ret Timeout
  | x01 =>
    n1 <- deserialize;;
    n2 <- deserialize;;
    i <- deserialize;;
    ByteListReader.ret (ClientRequest n1 n2 i)
  | _ => ByteListReader.error
  end.

  Lemma raft_input_serialize_deserialize_id :
    serialize_deserialize_id_spec serialize_raft_input deserialize_raft_input.
  Proof using.
    intros.
    unfold serialize_raft_input, deserialize_raft_input.
    destruct a;
      repeat (cheerios_crush; simpl).
    rewrite nat_serialize_deserialize_id.
    repeat (cheerios_crush; simpl).
    unfold serialize_input, deserialize_input.
    destruct i; repeat (cheerios_crush; simpl).
  Qed.

  Global Instance raft_input_Serializer : Serializer raft_input :=
    {| serialize := serialize_raft_input;
       deserialize := deserialize_raft_input;
       serialize_deserialize_id := raft_input_serialize_deserialize_id |}.
End Serializers.
