Require Export DACandMAC. 
 
Section Chsubsc. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition chsubsc_SC (v : SUBJECT) (sc : SecClass) :
  set (SUBJECT * SecClass) :=
  match fSSC (subjectSC s) v with
  | None => subjectSC s
  | Some y =>
      set_add SSCeq_dec (v, sc) (set_remove SSCeq_dec (v, y) (subjectSC s))
  end. 
 
 
Let t (u : SUBJECT) (sc : SecClass) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (chsubsc_SC u sc) 
    (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
    (acl s) (secmat s) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                           chsubsc                                 *) 
(*********************************************************************) 
 
(*This operation changes the security class of a given subject. The  *) 
(*only users allowed to execute this operations are the Security     *) 
(*Administrators (secadm), in other words those belonging to         *) 
(*SecAdmGrp group.                                                   *) 
 
Inductive chsubsc (secadm u : SUBJECT) (sc : SecClass) : SFSstate -> Prop :=
    chsubscOK :
      set_In secadm (groups s (SecAdmGrp s)) ->
      (forall rw : ReadersWriters,
       ~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)) ->
      chsubsc secadm u sc (t u sc). 
 
End Chsubsc. 
 
Hint Unfold chsubsc_SC.