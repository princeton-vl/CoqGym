Require Export DACandMAC. 
 
Section DelUsrGrpFromAcl. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
(*ru stands for reader user                                          *) 
(*wu stands for writer user                                          *) 
(*pu stands for proprietary user                                     *) 
(*rg stands for reader group                                         *) 
(*wg stands for writer group                                         *) 
(*pg stands for proprietary group                                    *) 
 
Let NEWOWNER (owner pu : SUBJECT) : SUBJECT :=
  match SUBeq_dec owner pu with
  | left _ => root
  | right _ => owner
  end. 
 
Let NEW_UO (owner pu : SUBJECT) (us : set SUBJECT) : 
  set SUBJECT :=
  match SUBeq_dec owner pu with
  | left _ => set_add SUBeq_dec root (set_remove SUBeq_dec pu us)
  | right _ => set_remove SUBeq_dec pu us
  end. 
 
Let NEW (o : OBJECT) (ru wu pu : SUBJECT) (rg wg pg : GRPNAME) :
  Exc AccessCtrlListData :=
  match facl (acl s) o with
  | None => None (A:=AccessCtrlListData)
  | Some y =>
      Some
        (acldata (NEWOWNER (owner y) pu) (group y)
           (set_remove SUBeq_dec ru (UsersReaders y))
           (set_remove GRPeq_dec rg (GroupReaders y))
           (set_remove SUBeq_dec wu (UsersWriters y))
           (set_remove GRPeq_dec wg (GroupWriters y))
           (NEW_UO (owner y) pu (UsersOwners y))
           (set_remove GRPeq_dec pg (GroupOwners y)))
  end. 
 
 
Definition delUsrGrpFromAcl_acl (o : OBJECT) (ru wu pu : SUBJECT)
  (rg wg pg : GRPNAME) : set (OBJECT * AccessCtrlListData) :=
  match facl (acl s) o, NEW o ru wu pu rg wg pg with
  | None, _ => acl s
  | _, None => acl s
  | Some y, Some z =>
      set_add ACLeq_dec (o, z) (set_remove ACLeq_dec (o, y) (acl s))
  end. 
 
 
Let t (o : OBJECT) (ru wu pu : SUBJECT) (rg wg pg : GRPNAME) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s)
    (delUsrGrpFromAcl_acl o ru wu pu rg wg pg) (secmat s) 
    (files s) (directories s). 
 
 
(*********************************************************************) 
(*                      delUsrGrpFromAcl                             *) 
(*********************************************************************) 
 
(*This operation possibly removes a reader, a writer, an owner, a    *) 
(*group of readers, a group of writers and a group of owners from the*) 
(*ACL of a given object. RootGrp group can't be removed from any ACL.*) 
 
Inductive delUsrGrpFromAcl (u : SUBJECT) (o : OBJECT) 
(ru wu pu : SUBJECT) (rg wg pg : GRPNAME) : SFSstate -> Prop :=
    delUsrGrpFromAclOK :
      ExecuterIsOwner s u o ->
      ~ set_In o (domsecmat (secmat s)) ->
      pg <> RootGrp s ->
      delUsrGrpFromAcl u o ru wu pu rg wg pg (t o ru wu pu rg wg pg). 
          
Hint Unfold delUsrGrpFromAcl_acl t. 
 
End DelUsrGrpFromAcl.