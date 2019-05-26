Require Export aclstat. 
Require Export chmod. 
Require Export create. 
Require Export mkdir. 
Require Export open. 
Require Export addUsrGrpToAcl. 
Require Export chobjsc. 
Require Export chown. 
Require Export chsubsc. 
Require Export close. 
Require Export delUsrGrpFromAcl. 
Require Export oscstat. 
Require Export owner_close. 
Require Export read. 
Require Export readdir. 
Require Export rmdir. 
Require Export sscstat. 
Require Export stat. 
Require Export unlink. 
Require Export write. 
 
Section TransitionFunction. 
 
(*********************************************************************) 
(*                   The Transition Relation                         *) 
(*********************************************************************) 
 
(*This is the transition relation of the abstract machine that models*) 
(*the security of the filesystem. It takes a subject, an state, an   *) 
(*operation and another state and asserts in what cases the          *) 
(*transition is possible. The possible transitions are, simply, those*) 
(*defined in each operation, i.e. if an operation can occur, then a  *) 
(*transition can take place. In other words, write, read, chmod, etc.*) 
(*are all possible transitions.                                      *) 
 
Inductive TransFunc : SUBJECT -> SFSstate -> Operation -> SFSstate -> Prop :=
  | DoAclstat :
      forall (u : SUBJECT) (o : OBJECT) (out : Exc AccessCtrlListData)
        (s : SFSstate), aclstat s u o s out -> TransFunc u s Aclstat s
  | DoChmod :
      forall (u : SUBJECT) (o : OBJECT) (perms : PERMS) (s t : SFSstate),
      chmod s u o perms t -> TransFunc u s Chmod t
  | DoCreate :
      forall (u : SUBJECT) (p : OBJNAME) (perms : PERMS) (s t : SFSstate),
      create s u p perms t -> TransFunc u s Create t
  | DoMkdir :
      forall (u : SUBJECT) (p : OBJNAME) (perms : PERMS) (s t : SFSstate),
      mkdir s u p perms t -> TransFunc u s Mkdir t
  | DoOpen :
      forall (u : SUBJECT) (o : OBJECT) (m : MODE) (s t : SFSstate),
      open s u o m t -> TransFunc u s Open t
  | DoAddUsrGrpToAcl :
      forall (u : SUBJECT) (o : OBJECT) (ru wu pu : SUBJECT)
        (rg wg pg : GRPNAME) (s t : SFSstate),
      addUsrGrpToAcl s u o ru wu pu rg wg pg t ->
      TransFunc u s AddUsrGrpToAcl t
  | DoChobjsc :
      forall (secadm : SUBJECT) (o : OBJECT) (sc : SecClass) (s t : SFSstate),
      chobjsc s secadm o sc t -> TransFunc secadm s Chobjsc t
  | DoChown :
      forall (u : SUBJECT) (o : OBJECT) (p : SUBJECT) 
        (g : GRPNAME) (s t : SFSstate),
      chown s u o p g t -> TransFunc u s Chown t
  | DoChsubsc :
      forall (secadm u : SUBJECT) (sc : SecClass) (s t : SFSstate),
      chsubsc s secadm u sc t -> TransFunc secadm s Chsubsc t
  | DoClose :
      forall (u : SUBJECT) (o : OBJECT) (s t : SFSstate),
      close s u o t -> TransFunc u s Close t
  | DoDelUsrGrpFromAcl :
      forall (u : SUBJECT) (o : OBJECT) (ru wu pu : SUBJECT)
        (rg wg pg : GRPNAME) (s t : SFSstate),
      delUsrGrpFromAcl s u o ru wu pu rg wg pg t ->
      TransFunc u s DelUsrGrpFromAcl t
  | DoOscstat :
      forall (u : SUBJECT) (o : OBJECT) (out : Exc SecClass) (s : SFSstate),
      oscstat s u o s out -> TransFunc u s Oscstat s
  | DoOwner_Close :
      forall (owner u : SUBJECT) (o : OBJECT) (s t : SFSstate),
      owner_close s owner u o t -> TransFunc owner s Owner_Close t
  | DoRead :
      forall (u : SUBJECT) (o : OBJECT) (n : nat) (out : Exc FILECONT)
        (s : SFSstate), read s u o n s out -> TransFunc u s Read s
  | DoReaddir :
      forall (u : SUBJECT) (o : OBJECT) (n : nat) (out : Exc DIRCONT)
        (s : SFSstate), readdir s u o n s out -> TransFunc u s Readdir s
  | DoRmdir :
      forall (u : SUBJECT) (o : OBJECT) (s t : SFSstate),
      rmdir s u o t -> TransFunc u s Rmdir t
  | DoSscstat :
      forall (u user : SUBJECT) (out : Exc SecClass) (s : SFSstate),
      sscstat s u user s out -> TransFunc u s Sscstat s
  | DoStat :
      forall (u : SUBJECT) (o : OBJECT) (out : Exc stat_struct)
        (s : SFSstate), stat s u o s out -> TransFunc u s Stat s
  | DoUnlink :
      forall (u : SUBJECT) (o : OBJECT) (s t : SFSstate),
      unlink s u o t -> TransFunc u s Unlink t
  | DoWrite :
      forall (u : SUBJECT) (o : OBJECT) (n : nat) (buf : FILECONT)
        (s t : SFSstate), write s u o n buf t -> TransFunc u s Write t. 
 
End TransitionFunction. 