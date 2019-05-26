Require Export ListFunctions. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
(*Definition of security class, and its standard partial order.      *) 

(*
SECLEV: security levels
CATEGORY: categories, departments or need-to-know
*)

Definition SECLEV := nat. 
Parameter CATEGORY : Set. 

(*SecClass: security class or access class*)

Record SecClass : Set := sclass {level : SECLEV; categs : set CATEGORY}. 
 
Definition eq_sc (a b : SecClass) : Prop :=
  level a = level b /\ categs a = categs b. 
 
Definition le_sc (a b : SecClass) : Prop :=
  level a <= level b /\ Included (categs a) (categs b). 
 
Hint Unfold eq_sc le_sc. 
 
 
(*********************************************************************) 
(*                  Security Policy Subjects                         *) 
(*********************************************************************) 
 
(*This are global parameters introducing the basic sets of the model.*) 

(*
SUBJECT: all the subjects of the system
GRPNAME: all the group names of the system
root: UNIX superuser
secofr: security officer, in charge of MAC attributes
*)
 
Parameter SUBJECT GRPNAME : Set. 
Parameter root secofr : SUBJECT. 
 
 
(*These axioms are needed by functions of ListSet.                   *) 
 
Axiom SUBeq_dec : forall x y : SUBJECT, {x = y} + {x <> y}. 
Axiom GRPeq_dec : forall x y : GRPNAME, {x = y} + {x <> y}. 
 
Hint Resolve SUBeq_dec GRPeq_dec. 
 
 
(*********************************************************************) 
(*                         The Filesystem                            *) 
(*********************************************************************) 
 
(*
OBJNAME: all the possible absolute path names for files and directories
BYTE: elements that can be stored in a file
*) 

Parameter OBJNAME BYTE : Set. 
 
 
(*These axioms are needed by functions of ListSet.                   *) 
Axiom OBJNAMEeq_dec : forall x y : OBJNAME, {x = y} + {x <> y}. 
Axiom BYTEeq_dec : forall x y : BYTE, {x = y} + {x <> y}. 
 
Hint Resolve OBJNAMEeq_dec BYTEeq_dec. 
 
 
(*OBJTYPE: used to distinguish between files and directories*)

Inductive OBJTYPE : Set :=
  | File : OBJTYPE
  | Directory : OBJTYPE. 
 
Lemma OBJTYPEeq_dec : forall x y : OBJTYPE, {x = y} + {x <> y}. 
intros. 
elim x; elim y. 
left; auto. 
 
right; intro; discriminate H. 
 
right; intro; discriminate H. 
 
left; auto. 
 
Qed. 
 
Hint Resolve OBJTYPEeq_dec. 
 
 
(*FILECONT: all the possible contents of files*)

Definition FILECONT := list BYTE. 
 
Lemma FILECONTeq_dec : forall x y : FILECONT, {x = y} + {x <> y}. 
unfold FILECONT in |- *; intros; apply Listeq_dec. 
auto. 
 
Qed. 
 
Hint Resolve FILECONTeq_dec. 
 
 
(*DIRCONT: all the possible contents of directories*)

Definition DIRCONT := list OBJNAME. 

Lemma DIRCONTeq_dec : forall x y : DIRCONT, {x = y} + {x <> y}. 
unfold DIRCONT in |- *; intros; apply Listeq_dec. 
auto. 
 
Qed. 
 
Hint Resolve DIRCONTeq_dec. 
 

Definition OBJECT := (OBJNAME * OBJTYPE)%type. 
 
Lemma OBJeq_dec : forall x y : OBJECT, {x = y} + {x <> y}. 
unfold OBJECT in |- *. 
intros. 
apply Prodeq_dec; auto. 
Qed. 
 
(*MyDir(o): parent directory of object o*)

Parameter MyDir : OBJNAME -> OBJECT. 
 
Definition ObjName (o : OBJECT) : OBJNAME := fst o. 
 
Definition ObjType (o : OBJECT) : OBJTYPE := snd o. 
 
 
(*********************************************************************) 
(*                  Security Policy Objects                          *) 
(*********************************************************************) 
 
(*
(allowedTo a b):
 if a pattern-matches (PM) true, then read access is allowed; otherwise it isn'
 if b PM true, then write access is allowed; otherwise it isn't
*)
 
Record RIGHTS : Set := allowedTo {read_right : bool; write_right : bool}. 


(*
(rwx o g a):
 if o PM (allowedTo x y) then the owner has or has't read and/or write access;
 if g PM (allowedTo x y) then group g has or has't read and/or write access;
 if a PM (allowedTo x y) then all the system subjects has or has't read and/or write access
*)
 
Record PERMS : Set := rwx {ownerp : RIGHTS; groupp : RIGHTS; otherp : RIGHTS}. 
 
(*Designated below*)
Record AccessCtrlListData : Set := acldata
  {owner : SUBJECT;
   group : GRPNAME;
   UsersReaders : set SUBJECT;
   GroupReaders : set GRPNAME;
   UsersWriters : set SUBJECT;
   GroupWriters : set GRPNAME;
   UsersOwners : set SUBJECT;
   GroupOwners : set GRPNAME}. 
 
 
(*Designated below*)
Record ReadersWriters : Set := mkRW
  {ActReaders : set SUBJECT; ActWriters : set SUBJECT}. 
 
Axiom RWeq_dec : forall x1 x2 : ReadersWriters, {x1 = x2} + {x1 <> x2}. 
 
 
(*********************************************************************) 
(*                     Secured FileSystem                            *) 
(*********************************************************************) 
 
(*This record represents the state of the filesystem from the security point of view. Designations for each field:

(groups g): all the subjects which belong to group g

(primaryGrp s): the (UNIX) primary group of subject s

(set_In (u,sc) (subjectSC s)): iff sc is the security class of u in state s

AllGrp: group containing all the system subjects

SecAdmGrp: group of the security administrators in charge of MAC attributes

RootGrp: group of all subjects with the same access of subject root

(set_In (o,sc) (objectSC s)): iff sc is the security class of o in state s

(set_In (o,(acldata o g ur gr uw gw uo go)) (acl s)):
  iff (acldata o g ur gr uw gw uo go) is the ACL of o in state s, in that case:
   o is the UNIX owner of o,
   g is the UNIX group of o,
   ur is a set of subjects with read access to o,
   gr is a set of groups with read access to o,
   uw is a set of subjects with write access to o,
   gw is a set of groups with write access to o,
   uo is a set of subjects which are owners of o,
   go is a set of groups wich are owners of o.

(set_In (o, (mkRW ar aw)) (secmat s): 
 iff (mkRW ar aw) are the subjects accessing object o in state s, in that case:
  ar: subjects reading from o
  aw: subjects writing into o

(set_In (f,fc) (files s)): iff file name f with file content fc is stored in the file system in state s

(set_In (f,dc) (directories s)): iff directory name d with directory content dc is stored in the filesystem in state s.
*)

Record SFSstate : Set := mkSFS
  {groups : GRPNAME -> set SUBJECT;
   primaryGrp : SUBJECT -> GRPNAME;
   subjectSC : set (SUBJECT * SecClass);
   AllGrp : GRPNAME;
   RootGrp : GRPNAME;
   SecAdmGrp : GRPNAME;
   objectSC : set (OBJECT * SecClass);
   acl : set (OBJECT * AccessCtrlListData);
   secmat : set (OBJECT * ReadersWriters);
   files : set (OBJECT * FILECONT);
   directories : set (OBJECT * DIRCONT)}. 
 
 
(*Axioms needed for decidability                                     *) 
Axiom SSCeq_dec : forall x1 x2 : SUBJECT * SecClass, {x1 = x2} + {x1 <> x2}. 
Axiom OSCeq_dec : forall x1 x2 : OBJECT * SecClass, {x1 = x2} + {x1 <> x2}. 
Axiom
  ACLeq_dec :
    forall x1 x2 : OBJECT * AccessCtrlListData, {x1 = x2} + {x1 <> x2}. 
Axiom
  SECMATeq_dec :
    forall x1 x2 : OBJECT * ReadersWriters, {x1 = x2} + {x1 <> x2}. 
Axiom OBJFeq_dec : forall x1 x2 : OBJECT * FILECONT, {x1 = x2} + {x1 <> x2}. 
Axiom OBJDeq_dec : forall x1 x2 : OBJECT * DIRCONT, {x1 = x2} + {x1 <> x2}. 
 
Hint Resolve SSCeq_dec OSCeq_dec ACLeq_dec SECMATeq_dec RWeq_dec. 
 
 

(*In this section we implement finite partial functions (FPF) with type set defined at module ListSet.v.

A FPF is a set of pairs. Given that both (x,y1) and (x,y2) with y1 != y2 may belong to a set of pairs, not every set of pairs is a FPF. For this reason, the specifier should use function IsPARTFUNC to test whether a given set of pairs is a FPF or not. All the other functions (DOM, RAN and PARTFUNC) assume that this test has been performed, otherwise their results are usless.

If f is a FPF and (x,y) belongs to f, then
 -f applied to x yields y,
 -x belongs to the domain of f
 -y belongs to the range of f.
*)
 
Section PartialFunctions.

Variable X Y : Set. 
 
Hypothesis Xeq_dec : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}. 
Hypothesis Yeq_dec : forall x1 x2 : Y, {x1 = x2} + {x1 <> x2}. 
Hypothesis XYeq_dec : forall x1 x2 : X * Y, {x1 = x2} + {x1 <> x2}. 

(*Domain of a FPF*)
Fixpoint DOM (f : set (X * Y)) : set X :=
  match f with
  | nil => nil (A:=X)
  | (x, y) :: g => set_add Xeq_dec x (DOM g)
  end. 

(*Range of a FPF*)
Fixpoint RAN (f : set (X * Y)) : set Y :=
  match f with
  | nil => nil (A:=Y)
  | (x, y) :: g => set_add Yeq_dec y (RAN g)
  end. 

(*Application of a FPF*)
Fixpoint PARTFUNC (f : set (X * Y)) : X -> Exc Y :=
  fun x : X =>
  match f with
  | nil => None (A:=Y)
  | (x1, y) :: g =>
      match Xeq_dec x x1 with
      | left _ => Some y
      | right _ => PARTFUNC g x
      end
  end. 
 
(*Test to decide whether a set of pairs is a FPF or not*)
Fixpoint IsPARTFUNC (f : set (X * Y)) : Prop :=
  match f with
  | nil => True
  | a :: l =>
      match set_In_dec Xeq_dec (fst a) (DOM l) with
      | left _ => False
      | right _ => IsPARTFUNC l
      end
  end. 
 
(*Some usefull lemmas about our implementation of FPF*)

Lemma AddEq :
 forall (a b : X) (y : Y) (f : set (X * Y)),
 a <> b -> PARTFUNC f a = PARTFUNC (set_add XYeq_dec (b, y) f) a. 
intros. 
induction  f as [| a0 f Hrecf]. 
simpl in |- *. 
elim (Xeq_dec a b). 
intros. 
cut False. 
intro. 
elim H0. 
 
unfold not in H; apply H. 
auto. 
 
auto. 
 
simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F. 
elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
intros. 
auto. 
 
Qed. 
 
 
Lemma AddEq1 :
 forall (x : X) (y : Y) (f : set (X * Y)),
 ~ set_In x (DOM f) -> value y = PARTFUNC (set_add XYeq_dec (x, y) f) x. 
simple induction f. 
simpl in |- *. 
elim (Xeq_dec x x); auto. 
intro; absurd (x = x); auto. 
 
simpl in |- *. 
intros until l. 
elim a. 
intros until b. 
elim (XYeq_dec (x, y) (a0, b)). 
simpl in |- *. 
elim (Xeq_dec x a0). 
intros. 
injection a2; intros. 
rewrite H1; auto. 
 
intros. 
injection a1; intros; absurd (x = a0); auto. 
 
simpl in |- *. 
elim (Xeq_dec x a0). 
intros. 
rewrite a1 in H0. 
cut False. 
tauto. 
 
apply H0. 
apply set_add_intro2; auto. 
 
intros. 
apply H. 
intro; apply H0; apply set_add_intro1; auto. 
 
Qed. 
 
 
Lemma RemEq :
 forall (a b : X) (y : Y) (f : set (X * Y)),
 a <> b -> PARTFUNC f a = PARTFUNC (set_remove XYeq_dec (b, y) f) a. 
intros. 
induction  f as [| a0 f Hrecf].
auto.

simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F. 
elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
intros. 
auto. 
 
Qed. 
 
 
Lemma AddRemEq :
 forall (a b : X) (y z : Y) (f : set (X * Y)),
 a <> b ->
 PARTFUNC f a =
 PARTFUNC (set_add XYeq_dec (b, z) (set_remove XYeq_dec (b, y) f)) a. 
intros. 
induction  f as [| a0 f Hrecf]. 
simpl in |- *. 
elim (Xeq_dec a b). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F; elim F. 
 
unfold not in H; apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (XYeq_dec (b, z) (a1, b0)). 
intros. 
cut False. 
intro F; elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
auto. 
 
intros. 
simpl in |- *. 
elim (XYeq_dec (b, z) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
intros. 
apply RemEq. 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma NotInDOMIsUndef :
 forall (o : X) (f : set (X * Y)), ~ set_In o (DOM f) -> PARTFUNC f o = None. 
intros. 
induction  f as [| a f Hrecf]. 
simpl in |- *. 
auto. 
 
generalize H. 
simpl in |- *. 
elim a. 
intro; intro. 
elim (Xeq_dec o a0). 
intro. 
rewrite a1. 
intro. 
cut False. 
intro F; elim F. 
 
unfold not in H0. 
apply H0. 
apply set_add_intro2. 
auto. 
 
intros. 
apply Hrecf. 
unfold not in H0; unfold not in |- *. 
intro; apply H0. 
apply set_add_intro1. 
auto. 
 
Qed. 
 
Hint Resolve NotInDOMIsUndef.    
 
Lemma InDOMIsNotUndef :
 forall (o : X) (f : set (X * Y)), set_In o (DOM f) -> PARTFUNC f o <> None. 
simple induction f. 
auto. 
 
simpl in |- *. 
intro. 
elim a. 
intro. 
elim (Xeq_dec o a0). 
intros; intro H3; discriminate H3. 
 
intros; apply H. 
 
eauto. 
 
Qed. 
 
 
Lemma InDOMWhenAdd :
 forall (x : X) (y : Y) (f : set (X * Y)),
 set_In x (DOM (set_add XYeq_dec (x, y) f)). 
intros; induction  f as [| a f Hrecf]. 
simpl in |- *. 
left; auto. 
 
simpl in |- *. 
elim (XYeq_dec (x, y) a). 
simpl in |- *. 
elim a. 
intros. 
injection a1; intros. 
apply set_add_intro2; auto. 
 
simpl in |- *. 
elim a. 
intros. 
apply set_add_intro1; auto. 
 
Qed. 
 
 
Lemma DOMFuncRel :
 forall (a : X * Y) (f : set (X * Y)),
 ~ set_In (fst a) (DOM f) -> f = set_remove XYeq_dec a f. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intro; elim a0. 
intros until b; elim (XYeq_dec a (a1, b)). 
elim a. 
intros. 
injection a3; intros. 
simpl in H0; rewrite H2 in H0. 
cut False. 
tauto. 
 
apply H0; apply set_add_intro2; auto. 
 
elim a. 
simpl in |- *. 
intros. 
cut (l = set_remove XYeq_dec (a2, b0) l). 
intro. 
rewrite <- H1; auto. 
 
apply H. 
intro; apply H0; apply set_add_intro; auto. 
 
Qed. 
 
Hint Resolve DOMFuncRel. 
 
 
Lemma DOMFuncRel2 :
 forall (z : X * Y) (f : set (X * Y)), set_In z f -> set_In (fst z) (DOM f). 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intro; elim a. 
elim z. 
simpl in |- *. 
intros. 
elim H0; intro. 
injection H1; intros. 
apply set_add_intro; auto. 
 
cut (set_In a0 (DOM l)). 
intro; apply set_add_intro1; auto. 
 
auto. 
 
Qed. 
 
Hint Resolve DOMFuncRel2. 
 
 
Lemma DOMFuncRel3 :
 forall (x : X) (y : Y) (f : set (X * Y)),
 IsPARTFUNC f ->
 set_In (x, y) f -> ~ set_In x (DOM (set_remove XYeq_dec (x, y) f)). 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l; elim (set_In_dec Xeq_dec (fst a) (DOM l));
 elim (XYeq_dec (x, y) a). 
tauto. 
 
tauto. 
 
intros; cut (l = set_remove XYeq_dec (x, y) l). 
intro H2; rewrite <- H2; replace x with (fst a); auto. 
rewrite <- a0; auto. 
 
rewrite a0; auto. 
 
simpl in |- *. 
elim a. 
simpl in |- *. 
intros. 
elim H1; intro. 
absurd ((a0, b) = (x, y)); auto. 
 
elim (Xeq_dec x a0); intro. 
rewrite <- a1 in b1. 
intro; apply b1; replace x with (fst (x, y)); auto. 
 
cut (~ set_In x (DOM (set_remove XYeq_dec (x, y) l))). 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma DOMFuncRel4 :
 forall (x : X) (f : set (X * Y)),
 match PARTFUNC f x with
 | Some a => set_In (x, a) f
 | None => ~ set_In x (DOM f)
 end. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l; elim a. 
intros until b; elim (Xeq_dec x a0). 
elim (PARTFUNC l x). 
intros y2 H; left; rewrite H; auto. 
 
intros H H1; left; rewrite H; auto. 
 
elim (PARTFUNC l x). 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma UndefWhenRem :
 forall (x : X) (y : Y) (f : set (X * Y)),
 IsPARTFUNC f ->
 set_In (x, y) f -> PARTFUNC (set_remove XYeq_dec (x, y) f) x = None. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l. 
elim (set_In_dec Xeq_dec (fst a) (DOM l)); elim (XYeq_dec (x, y) a). 
tauto. 
 
tauto. 
 
intros. 
replace (set_remove XYeq_dec (x, y) l) with l. 
rewrite <- a0 in b. 
simpl in b. 
auto. 
 
rewrite <- a0 in b. 
auto. 
 
simpl in |- *. 
elim a. 
intros. 
elim H1; intro. 
cut False. 
tauto. 
 
apply b0; symmetry  in |- *; auto. 
 
elim (Xeq_dec x a0). 
intro. 
simpl in b1. 
rewrite <- a1 in b1. 
absurd (set_In x (DOM l)). 
auto. 
 
replace x with (fst (x, y)); auto. 
 
auto. 
 
Qed. 
 
End PartialFunctions. 
 
Hint Resolve AddEq RemEq AddRemEq NotInDOMIsUndef InDOMIsNotUndef
  InDOMWhenAdd UndefWhenRem AddEq1 DOMFuncRel3. 
 
 
 
(*Shorthands for domains and partial functions defined for each of the state's*) 
(*components.                                                        *) 
Definition domf (f : set (OBJECT * FILECONT)) := DOM OBJeq_dec f. 
 
Definition ffiles (f : set (OBJECT * FILECONT)) : OBJECT -> Exc FILECONT :=
  PARTFUNC OBJeq_dec f. 
 
Definition domd (f : set (OBJECT * DIRCONT)) := DOM OBJeq_dec f. 
 
Definition fdirs (f : set (OBJECT * DIRCONT)) : OBJECT -> Exc DIRCONT :=
  PARTFUNC OBJeq_dec f. 
 
Definition domacl (f : set (OBJECT * AccessCtrlListData)) := DOM OBJeq_dec f. 
 
Definition facl (f : set (OBJECT * AccessCtrlListData)) :
  OBJECT -> Exc AccessCtrlListData := PARTFUNC OBJeq_dec f. 
 
Definition domsecmat (f : set (OBJECT * ReadersWriters)) := DOM OBJeq_dec f. 
 
Definition ransecmat (f : set (OBJECT * ReadersWriters)) := RAN RWeq_dec f. 
 
Definition fsecmat (f : set (OBJECT * ReadersWriters)) :
  OBJECT -> Exc ReadersWriters := PARTFUNC OBJeq_dec f. 
 
Definition domOSC (f : set (OBJECT * SecClass)) := DOM OBJeq_dec f. 
 
Definition fOSC (f : set (OBJECT * SecClass)) : OBJECT -> Exc SecClass :=
  PARTFUNC OBJeq_dec f. 
 
Definition domSSC (f : set (SUBJECT * SecClass)) := DOM SUBeq_dec f. 
 
Definition fSSC (f : set (SUBJECT * SecClass)) : SUBJECT -> Exc SecClass :=
  PARTFUNC SUBeq_dec f. 
                 
 
(*Filesystem update functions.                                       *) 
Parameter create_files : SUBJECT -> OBJNAME -> set (OBJECT * FILECONT). 
Parameter create_directories : SUBJECT -> OBJNAME -> set (OBJECT * DIRCONT). 
Parameter mkdir_directories : SUBJECT -> OBJNAME -> set (OBJECT * DIRCONT). 
Parameter rmdir_directories : OBJECT -> set (OBJECT * DIRCONT). 
Parameter unlink_files : OBJECT -> set (OBJECT * FILECONT). 
Parameter unlink_directories : OBJECT -> set (OBJECT * DIRCONT). 
Parameter write_files : OBJECT -> nat -> FILECONT -> set (OBJECT * FILECONT). 
 
 
(*
READ: pure read access
WRITE: pure write access
*)
 
Inductive MODE : Set :=
  | READ : MODE
  | WRITE : MODE. 
 
 
(*The names of the system operations.                                *) 
 
Inductive Operation : Set :=
  | Aclstat : Operation
  | AddUsrGrpToAcl : Operation
  | Chmod : Operation
  | Chobjsc : Operation
  | Chown : Operation
  | Chsubsc : Operation
  | Close : Operation
  | Create : Operation
  | DelUsrGrpFromAcl : Operation
  | Mkdir : Operation
  | Open : Operation
  | Oscstat : Operation
  | Owner_Close : Operation
  | Read : Operation
  | Readdir : Operation
  | Rmdir : Operation
  | Sscstat : Operation
  | Stat : Operation
  | Unlink : Operation
  | Write : Operation.