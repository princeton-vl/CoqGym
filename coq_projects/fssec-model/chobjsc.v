Require Export DACandMAC. 
 
Section Chobjsc. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition chobjsc_SC (o : OBJECT) (sc : SecClass) :
  set (OBJECT * SecClass) :=
  match fOSC (objectSC s) o with
  | None => objectSC s
  | Some y =>
      set_add OSCeq_dec (o, sc) (set_remove OSCeq_dec (o, y) (objectSC s))
  end. 
 
 
Let t (o : OBJECT) (sc : SecClass) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (chobjsc_SC o sc) (acl s) 
    (secmat s) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                           chobjsc                                 *) 
(*********************************************************************) 
 
(*This operation changes the security class of a given object. The   *) 
(*only users allowed to execute this operations are the Security     *) 
(*Administrators (secadm), in other words those belonging to         *) 
(*SecAdmGrp group.                                                   *) 
 
Inductive chobjsc (secadm : SUBJECT) (o : OBJECT) (sc : SecClass) :
SFSstate -> Prop :=
    chsobjscOK :
      set_In secadm (groups s (SecAdmGrp s)) ->
      ~ set_In o (domsecmat (secmat s)) -> chobjsc secadm o sc (t o sc). 
 
End Chobjsc. 
 
Hint Unfold chobjsc_SC. 