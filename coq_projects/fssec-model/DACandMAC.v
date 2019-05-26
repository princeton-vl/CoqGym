Require Export SFSstate. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
(*********************************************************************) 
(*                Preconditions for DAC and MAC                      *) 
(*********************************************************************) 
 
Section Preconditions. 
 
Variable s : SFSstate. 
 
(*This predicate asserts that for a subject to read an object, the   *) 
(*former must belong to the set of readers of the last. Also, this   *) 
(*condition holds if the subject belongs to a group wich in turn     *) 
(*belongs to the object's readers.                                   *) 
 
Definition PreDACRead (u : SUBJECT) (o : OBJECT) : Prop :=
  match facl (acl s) o with
  | Some y =>
      set_In u (UsersReaders y) \/
      (exists g : GRPNAME, set_In u (groups s g) /\ set_In g (GroupReaders y))
  | None => False
  end. 
 
 
(*This predicate asserts that for a subject to write to an object,   *) 
(*the former must belong to the set of writers of the last. Also,    *) 
(*this condition holds if the subject belongs to a group wich in turn*) 
(*belongs to the object's writers.                                   *) 
 
Definition PreDACWrite (u : SUBJECT) (o : OBJECT) : Prop :=
  match facl (acl s) o with
  | Some y =>
      set_In u (UsersWriters y) \/
      (exists g : GRPNAME, set_In u (groups s g) /\ set_In g (GroupWriters y))
  | None => False
  end. 
 
 
(*This predicate asserts that for a subject to read or write an      *) 
(*object, the object's security class must be dominated by the       *) 
(*subject's security class.                                          *) 
 
Definition PreMAC (u : SUBJECT) (o : OBJECT) : Prop :=
  match fOSC (objectSC s) o, fSSC (subjectSC s) u with
  | None, _ => False
  | _, None => False
  | Some a, Some b => le_sc a b
  end. 
 
 
(*This predicate asserts that if a user is an active writer of any   *) 
(*object b, then the security class of b must dominates the security *) 
(*class of o. This predicate is used to preserve the *-property*) 
 
Definition PreStarPropRead (u : SUBJECT) (o : OBJECT) : Prop :=
  forall b : OBJECT,
  match fsecmat (secmat s) b, fOSC (objectSC s) o, fOSC (objectSC s) b with
  | None, _, _ => False
  | _, None, _ => False
  | _, _, None => False
  | Some x, Some y, Some z => set_In u (ActWriters x) -> le_sc y z
  end. 
 

(*This predicate asserts that if a user is an active reader of any   *)
(*object b, then the security class of b must be dominated by the    *)
(*security class of o. This predicate is used to preserve the        *)
(**-property.                                                        *)

Definition PreStarPropWrite (u : SUBJECT) (o : OBJECT) : Prop :=
  forall b : OBJECT,
  match fsecmat (secmat s) b, fOSC (objectSC s) o, fOSC (objectSC s) b with
  | None, _, _ => False
  | _, None, _ => False
  | _, _, None => False
  | Some x, Some y, Some z => set_In u (ActReaders x) -> le_sc z y
  end. 
 
 
(*This predicate determines if a given user is one of the owners or  *) 
(*belong to one of the owner groups of a given object.               *) 
 
Inductive IsUNIXOwner (u : SUBJECT) : AccessCtrlListData -> Prop :=
    IUO :
      forall a : AccessCtrlListData,
      IsUNIXOwner u
        (acldata u (group a) (UsersReaders a) (GroupReaders a)
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a)). 
                              
    
Inductive ExecuterIsOwner (u : SUBJECT) (o : OBJECT) : Prop :=
  | UNIXOwner :
      forall y : AccessCtrlListData,
      facl (acl s) o = Some y -> IsUNIXOwner u y -> ExecuterIsOwner u o
  | ACLOwner :
      forall y : AccessCtrlListData,
      facl (acl s) o = Some y ->
      set_In u (UsersOwners y) -> ExecuterIsOwner u o
  | ACLGrp :
      forall y : AccessCtrlListData,
      facl (acl s) o = Some y ->
      (exists g : GRPNAME, set_In u (groups s g) /\ set_In g (GroupOwners y)) ->
      ExecuterIsOwner u o. 
 
 
Definition InFileSystem (o : OBJECT) : Prop :=
  set_In o
    (set_union OBJeq_dec (DOM OBJeq_dec (files s))
       (DOM OBJeq_dec (directories s))). 
 
End Preconditions. 
 
Hint Resolve IUO UNIXOwner ACLOwner ACLGrp. 
 
Hint Unfold PreDACRead PreDACWrite PreMAC PreStarPropRead PreStarPropWrite
  InFileSystem. 
 