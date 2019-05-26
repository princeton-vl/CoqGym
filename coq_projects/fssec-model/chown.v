Require Export DACandMAC. 
 
Section Chown. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Let NEW_GRP (old new : GRPNAME) (gs : set GRPNAME) : 
  set GRPNAME :=
  match set_In_dec GRPeq_dec old gs with
  | left _ => set_add GRPeq_dec new (set_remove GRPeq_dec old gs)
  | right _ => gs
  end. 
 
Let NEW_UO (old new : SUBJECT) (us : set SUBJECT) : 
  set SUBJECT := set_add SUBeq_dec new (set_remove SUBeq_dec old us). 
 
Let NEW (o : OBJECT) (p : SUBJECT) (g : GRPNAME) : 
  Exc AccessCtrlListData :=
  match facl (acl s) o with
  | None => None (A:=AccessCtrlListData)
  | Some y =>
      Some
        (acldata p g (UsersReaders y) (NEW_GRP (group y) g (GroupReaders y))
           (UsersWriters y) (NEW_GRP (group y) g (GroupWriters y))
           (NEW_UO (owner y) p (UsersOwners y)) (GroupOwners y))
  end. 
 
 
Definition chown_acl (o : OBJECT) (p : SUBJECT) (g : GRPNAME) :
  set (OBJECT * AccessCtrlListData) :=
  match facl (acl s) o, NEW o p g with
  | None, _ => acl s
  | _, None => acl s
  | Some y, Some z =>
      set_add ACLeq_dec (o, z) (set_remove ACLeq_dec (o, y) (acl s))
  end. 
 
 
Let t (o : OBJECT) (p : SUBJECT) (g : GRPNAME) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (chown_acl o p g) 
    (secmat s) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                            chown                                  *) 
(*********************************************************************) 
 
(*This operation changes the UNIX owner and group of a given object. *)

Inductive chown (u : SUBJECT) (o : OBJECT) (p : SUBJECT) 
(g : GRPNAME) : SFSstate -> Prop :=
    ChownOK :
      ExecuterIsOwner s u o ->
      ~ set_In o (domsecmat (secmat s)) -> chown u o p g (t o p g). 
 
Hint Unfold chown_acl t. 
 
End Chown.