Require Export TransFunc. 
 
Section ModelProperties. 
 
(*This is the defintion of a secure state from the DAC security      *) 
(*policy point of view.                                              *) 
 
Definition DACSecureState (s : SFSstate) : Prop :=
  forall (u : SUBJECT) (o : OBJECT),
  match fsecmat (secmat s) o with
  | None => True
  | Some y =>
      (set_In u (ActReaders y) -> PreDACRead s u o) /\
      (set_In u (ActWriters y) -> PreDACWrite s u o)
  end. 
 
 
(*This is the defintion of a secure state from the MAC security      *) 
(*policy point of view. It says that an state is MAC secure if for   *) 
(*each subject accesing an object, the security class of the former  *) 
(*is dominates the security class of the object.                     *) 
 
Definition MACSecureState (s : SFSstate) : Prop :=
  forall (u : SUBJECT) (o : OBJECT),
  match fsecmat (secmat s) o, fOSC (objectSC s) o, fSSC (subjectSC s) u with
  | None, _, _ => True
  | _, None, _ => True
  | _, _, None => True
  | Some x, Some y, Some z =>
      set_In u (ActReaders x) \/ set_In u (ActWriters x) -> le_sc y z
  end. 
       
 
(*An state is secure if it's both DAC and MAC secure.                *) 
 
Definition SecureState (s : SFSstate) : Prop :=
  DACSecureState s /\ MACSecureState s. 
 
 
(*This is the definition of the *-property adapted from the          *) 
(*Bell-LaPadula's model. It says that whenever a subject is accesing *) 
(*an object for reading and, possibly, another object for writing,   *) 
(*then the security class of any object that is being open for       *) 
(*reading must be dominated by the security class of any             *) 
(*of those objects that are already open for writing.                *) 
 
Definition StarProperty (s : SFSstate) : Prop :=
  forall (u : SUBJECT) (o1 o2 : OBJECT),
  match
    fsecmat (secmat s) o1, fsecmat (secmat s) o2, fOSC (objectSC s) o2,
    fOSC (objectSC s) o1
  with
  | None, _, _, _ => True
  | _, None, _, _ => True
  | _, _, None, _ => True
  | _, _, _, None => True
  | Some w, Some x, Some y, Some z =>
      set_In u (ActWriters w) -> set_In u (ActReaders x) -> le_sc y z
  end. 
 
 
(*We also want operations that deal securely with control            *) 
(*attributes, i.e. the owners of an ACL, the security class          *) 
(*associated with subjects and objects, etc.                         *) 
(*Informally, the policy says that the owner of an object or a       *) 
(*member of RootGrp are the only allowed to change the DAC           *) 
(*control attributes associated with the object; that the members    *) 
(*of SecAdmGrp are the ones that can change the MAC control          *) 
(*attributes associated with subjects and objects; and that RootGrp  *) 
(*must always be owner of all objects.                               *) 
 
Inductive AclChanged : AccessCtrlListData -> AccessCtrlListData -> Prop :=
  | UR :
      forall (a : AccessCtrlListData) (b c : set SUBJECT),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) b (GroupReaders a) 
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
        (acldata (owner a) (group a) c (GroupReaders a) 
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
  | GR :
      forall (a : AccessCtrlListData) (b c : set GRPNAME),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) (UsersReaders a) b 
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
        (acldata (owner a) (group a) (UsersReaders a) c 
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
  | UW :
      forall (a : AccessCtrlListData) (b c : set SUBJECT),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) b (GroupWriters a) (UsersOwners a)
           (GroupOwners a))
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) c (GroupWriters a) (UsersOwners a)
           (GroupOwners a))
  | GW :
      forall (a : AccessCtrlListData) (b c : set GRPNAME),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) b (UsersOwners a)
           (GroupOwners a))
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) c (UsersOwners a)
           (GroupOwners a))
  | UO :
      forall (a : AccessCtrlListData) (b c : set SUBJECT),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) (GroupWriters a) b
           (GroupOwners a))
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) (GroupWriters a) c
           (GroupOwners a))
  | GO :
      forall (a : AccessCtrlListData) (b c : set GRPNAME),
      b <> c ->
      AclChanged
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) (GroupWriters a) 
           (UsersOwners a) b)
        (acldata (owner a) (group a) (UsersReaders a) 
           (GroupReaders a) (UsersWriters a) (GroupWriters a) 
           (UsersOwners a) c). 
 
 
Inductive UNIXAttrChanged :
AccessCtrlListData -> AccessCtrlListData -> Prop :=
  | Owner :
      forall (a : AccessCtrlListData) (b c : SUBJECT),
      b <> c ->
      UNIXAttrChanged
        (acldata b (group a) (UsersReaders a) (GroupReaders a)
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
        (acldata c (group a) (UsersReaders a) (GroupReaders a)
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
  | Group :
      forall (a : AccessCtrlListData) (b c : GRPNAME),
      b <> c ->
      UNIXAttrChanged
        (acldata (owner a) b (UsersReaders a) (GroupReaders a)
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a))
        (acldata (owner a) c (UsersReaders a) (GroupReaders a)
           (UsersWriters a) (GroupWriters a) (UsersOwners a) 
           (GroupOwners a)). 
 
Inductive DACCtrlAttrHaveChanged (s t : SFSstate) (o : OBJECT) : Prop :=
  | ACL :
      forall y z : AccessCtrlListData,
      facl (acl s) o = Some y ->
      facl (acl t) o = Some z ->
      AclChanged y z -> DACCtrlAttrHaveChanged s t o
  | UNIX :
      forall y z : AccessCtrlListData,
      facl (acl s) o = Some y ->
      facl (acl t) o = Some z ->
      UNIXAttrChanged y z -> DACCtrlAttrHaveChanged s t o. 
 
 
Inductive SecClassChanged : SecClass -> SecClass -> Prop :=
  | Level :
      forall (a : SecClass) (b c : set CATEGORY),
      b <> c -> SecClassChanged (sclass (level a) b) (sclass (level a) c)
  | Categ :
      forall (a : SecClass) (b c : SECLEV),
      b <> c -> SecClassChanged (sclass b (categs a)) (sclass c (categs a)). 
 
Inductive MACObjCtrlAttrHaveChanged (s t : SFSstate) (o : OBJECT) : Prop :=
    SCo :
      forall x y : SecClass,
      fOSC (objectSC s) o = Some x ->
      fOSC (objectSC t) o = Some y ->
      SecClassChanged x y -> MACObjCtrlAttrHaveChanged s t o. 
 
Inductive MACSubCtrlAttrHaveChanged (s t : SFSstate) (u : SUBJECT) : Prop :=
    SCu :
      forall x y : SecClass,
      fSSC (subjectSC s) u = Some x ->
      fSSC (subjectSC t) u = Some y ->
      SecClassChanged x y -> MACSubCtrlAttrHaveChanged s t u. 
 
 
Definition ControlProperty (u : SUBJECT) (s t : SFSstate) : Prop :=
  (forall o : OBJECT,
   (DACCtrlAttrHaveChanged s t o -> ExecuterIsOwner s u o) /\
   (MACObjCtrlAttrHaveChanged s t o -> set_In u (groups s (SecAdmGrp s)))) /\
  (forall u0 : SUBJECT,
   MACSubCtrlAttrHaveChanged s t u0 -> set_In u (groups s (SecAdmGrp s))). 
 
 
Definition PreservesControlProp (s : SFSstate) (op : Operation)
  (t : SFSstate) : Prop :=
  forall u : SUBJECT, TransFunc u s op t -> ControlProperty u s t. 
 
 
(*Well-formedness system invariants.                                     *) 
Axiom
  WFSI1 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    (forall o : OBJECT,
     set_In o (DOM OBJeq_dec (files s)) -> ObjType o = File) ->
    TransFunc u s op t ->
    forall o : OBJECT, set_In o (DOM OBJeq_dec (files t)) -> ObjType o = File. 
 
Axiom
  WFSI2 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    (forall o : OBJECT,
     set_In o (DOM OBJeq_dec (directories s)) -> ObjType o = Directory) ->
    TransFunc u s op t ->
    forall o : OBJECT,
    set_In o (DOM OBJeq_dec (directories t)) -> ObjType o = Directory. 
 
Axiom
  WFSI3 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    DOM OBJeq_dec (acl s) =
    set_union OBJeq_dec (DOM OBJeq_dec (files s))
      (DOM OBJeq_dec (directories s)) ->
    TransFunc u s op t ->
    DOM OBJeq_dec (acl t) =
    set_union OBJeq_dec (DOM OBJeq_dec (files t))
      (DOM OBJeq_dec (directories t)). 
 
Definition FuncPre1 (s : SFSstate) : Prop :=
  (forall o : OBJECT,
   set_In o (DOM OBJeq_dec (directories s)) -> ObjType o = Directory) /\
  (forall o : OBJECT, set_In o (DOM OBJeq_dec (files s)) -> ObjType o = File) /\
  DOM OBJeq_dec (acl s) =
  set_union OBJeq_dec (DOM OBJeq_dec (files s))
    (DOM OBJeq_dec (directories s)). 
 
 
Axiom
  WFSI4 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    DOM OBJeq_dec (acl s) = DOM OBJeq_dec (objectSC s) ->
    TransFunc u s op t -> DOM OBJeq_dec (acl t) = DOM OBJeq_dec (objectSC t). 
 
 
Definition FuncPre2 (s : SFSstate) : Prop :=
  DOM OBJeq_dec (acl s) = DOM OBJeq_dec (objectSC s). 
 
 
Axiom
  WFSI5 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    Included (DOM OBJeq_dec (secmat s)) (DOM OBJeq_dec (acl s)) ->
    TransFunc u s op t ->
    Included (DOM OBJeq_dec (secmat t)) (DOM OBJeq_dec (acl t)). 
 
 
Definition FuncPre3 (s : SFSstate) : Prop :=
  Included (DOM OBJeq_dec (secmat s)) (DOM OBJeq_dec (acl s)). 
 
 
Axiom
  WFSI6 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    IsPARTFUNC OBJeq_dec (acl s) ->
    TransFunc u s op t -> IsPARTFUNC OBJeq_dec (acl t). 
 
 
Definition FuncPre4 (s : SFSstate) : Prop := IsPARTFUNC OBJeq_dec (acl s). 
 
 
Axiom
  WFSI7 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    IsPARTFUNC OBJeq_dec (secmat s) ->
    TransFunc u s op t -> IsPARTFUNC OBJeq_dec (secmat t). 
 
 
Definition FuncPre5 (s : SFSstate) : Prop := IsPARTFUNC OBJeq_dec (secmat s). 
 
 
Axiom
  WFSI8 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    IsPARTFUNC OBJeq_dec (objectSC s) ->
    TransFunc u s op t -> IsPARTFUNC OBJeq_dec (objectSC t). 
 
 
Definition FuncPre6 (s : SFSstate) : Prop :=
  IsPARTFUNC OBJeq_dec (objectSC s). 
 
 
Axiom
  WFSI9 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (u : SUBJECT),
    IsPARTFUNC SUBeq_dec (subjectSC s) ->
    TransFunc u s op t -> IsPARTFUNC SUBeq_dec (subjectSC t). 
 
 
Definition FuncPre7 (s : SFSstate) : Prop :=
  IsPARTFUNC SUBeq_dec (subjectSC s). 
 
End ModelProperties. 
 
 
Hint Unfold SecureState DACSecureState MACSecureState ControlProperty
  PreservesControlProp. 
 
Hint Resolve UR GR UW GW UO GO Owner Group Level Categ. 
Hint Resolve WFSI1 WFSI2 WFSI3 WFSI4 WFSI5 WFSI6 WFSI7 WFSI8 WFSI9.