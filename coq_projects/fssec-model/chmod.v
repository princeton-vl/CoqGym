Require Export DACandMAC. 
Require Export setACLdata. 
 
Section Chmod. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************)
 
Let ChangeGAR (o : OBJECT) (oct : RIGHTS) : Exc (set GRPNAME) :=
  match facl (acl s) o with
  | None => None (A:=set GRPNAME)
  | Some y =>
      Some
        (ChangeGroupR (AllGrp s) oct
           (ChangeGroupR (group y) oct (GroupReaders y)))
  end. 
 
Let ChangeGAW (o : OBJECT) (oct : RIGHTS) : Exc (set GRPNAME) :=
  match facl (acl s) o with
  | None => None (A:=set GRPNAME)
  | Some y =>
      Some
        (ChangeGroupW (AllGrp s) oct
           (ChangeGroupW (group y) oct (GroupWriters y)))
  end. 
 
Let NEW (u : SUBJECT) (o : OBJECT) (perms : PERMS) :
  Exc AccessCtrlListData :=
  match
    facl (acl s) o, ChangeGAR o (groupp perms), ChangeGAW o (groupp perms)
  with
  | None, _, _ => None (A:=AccessCtrlListData)
  | _, None, _ => None (A:=AccessCtrlListData)
  | _, _, None => None (A:=AccessCtrlListData)
  | Some y, Some gar, Some gaw =>
      Some
        (acldata (owner y) (group y)
           (ChangeUserR u (UsersReaders y) (ownerp perms)) gar
           (ChangeUserW u (UsersWriters y) (ownerp perms)) gaw
           (UsersOwners y) (GroupOwners y))
  end. 
 
 
Definition chmod_acl (u : SUBJECT) (o : OBJECT) (perms : PERMS) :
  set (OBJECT * AccessCtrlListData) :=
  match facl (acl s) o, NEW u o perms with
  | None, _ => acl s
  | _, None => acl s
  | Some y, Some z =>
      set_add ACLeq_dec (o, z) (set_remove ACLeq_dec (o, y) (acl s))
  end. 
 
 
Let t (u : SUBJECT) (o : OBJECT) (perms : PERMS) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (chmod_acl u o perms) 
    (secmat s) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                            chmod                                  *) 
(*********************************************************************) 
 
(*This operation changes the mode (permissions) of a given object.   *) 
(*Only the (UNIX) owner can do this.                                 *) 
 
Inductive chmod (u : SUBJECT) (o : OBJECT) (perms : PERMS) :
SFSstate -> Prop :=
    ChmodOK :
      ExecuterIsOwner s u o ->
      ~ set_In o (domsecmat (secmat s)) -> chmod u o perms (t u o perms). 
 
 
Hint Resolve ChangeGAR ChangeGAW chmod_acl t. 

End Chmod.