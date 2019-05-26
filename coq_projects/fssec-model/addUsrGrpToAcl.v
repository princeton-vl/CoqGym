Require Export DACandMAC. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section AddUsrGrpToAcl. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
(*ru stands for reader user                                          *) 
(*wu stands for writer user                                          *) 
(*pu stands for proprietary user                                     *) 
(*rg stands for reader group                                         *) 
(*wu stands for writer group                                         *) 
(*pu stands for proprietary group                                    *) 
 
Let NEW (o : OBJECT) (ru wu pu : SUBJECT) (rg wg pg : GRPNAME) :
  Exc AccessCtrlListData :=
  match facl (acl s) o with
  | None => None (A:=AccessCtrlListData)
  | Some y =>
      Some
        (acldata (owner y) (group y) (set_add SUBeq_dec ru (UsersReaders y))
           (set_add GRPeq_dec rg (GroupReaders y))
           (set_add SUBeq_dec wu (UsersWriters y))
           (set_add GRPeq_dec wg (GroupWriters y))
           (set_add SUBeq_dec pu (UsersOwners y))
           (set_add GRPeq_dec pg (GroupOwners y)))
  end. 
 
 
Definition addUsrGrpToAcl_acl (o : OBJECT) (ru wu pu : SUBJECT)
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
    (addUsrGrpToAcl_acl o ru wu pu rg wg pg) (secmat s) 
    (files s) (directories s). 
 
 
(*********************************************************************) 
(*                       addUsrGrpToAcl                              *) 
(*********************************************************************) 
 
(*This operation possibly adds a new reader, a new writer, a new     *) 
(*owner, a new group of readers, a new group of writers and a new    *) 
(*group of owners to the ACL of a given object.                      *) 
 
Inductive addUsrGrpToAcl (u : SUBJECT) (o : OBJECT) 
(ru wu pu : SUBJECT) (rg wg pg : GRPNAME) : SFSstate -> Prop :=
    addUsrGrpToAclOK :
      ExecuterIsOwner s u o ->
      ~ set_In o (domsecmat (secmat s)) ->
      addUsrGrpToAcl u o ru wu pu rg wg pg (t o ru wu pu rg wg pg). 
 
Hint Unfold addUsrGrpToAcl_acl t. 
 
End AddUsrGrpToAcl. 