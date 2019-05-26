Require Export DACandMAC. 
Require Export setACLdata. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section Mkdir. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition NEWDIR (p : OBJNAME) : OBJECT := (p, Directory). 
 
 
Definition mkdir_oSC (u : SUBJECT) (p : OBJNAME) : 
  set (OBJECT * SecClass) :=
  match fSSC (subjectSC s) u, fsecmat (secmat s) (MyDir p) with
  | None, _ => objectSC s
  | _, None => objectSC s
  | Some y, Some z => set_add OSCeq_dec (NEWDIR p, y) (objectSC s)
  end. 
 
 
Let ChangeGAR (u : SUBJECT) (oct : RIGHTS) : set GRPNAME :=
  ChangeGroupR (AllGrp s) oct
    (ChangeGroupR (primaryGrp s u) oct (empty_set GRPNAME)). 
 
Let ChangeGAW (u : SUBJECT) (oct : RIGHTS) : set GRPNAME :=
  ChangeGroupW (AllGrp s) oct
    (ChangeGroupW (primaryGrp s u) oct (empty_set GRPNAME)). 
 
Let NEW (u : SUBJECT) (p : OBJNAME) (perms : PERMS) : AccessCtrlListData :=
  acldata u (primaryGrp s u)
    (ChangeUserR u (empty_set SUBJECT) (ownerp perms))
    (ChangeGAR u (groupp perms))
    (ChangeUserW u (empty_set SUBJECT) (ownerp perms))
    (ChangeGAW u (groupp perms)) (set_add SUBeq_dec u (empty_set SUBJECT))
    (ChangeGroupO (RootGrp s) (empty_set GRPNAME)). 
 
Definition mkdir_acl (u : SUBJECT) (p : OBJNAME) (perms : PERMS) :
  set (OBJECT * AccessCtrlListData) :=
  match fSSC (subjectSC s) u, fsecmat (secmat s) (MyDir p) with
  | None, _ => acl s
  | _, None => acl s
  | Some y, Some z => set_add ACLeq_dec (NEWDIR p, NEW u p perms) (acl s)
  end. 
 
Let t (u : SUBJECT) (p : OBJNAME) (perms : PERMS) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (mkdir_oSC u p) (mkdir_acl u p perms)
    (secmat s) (files s) (mkdir_directories u p). 
 
 
(*********************************************************************) 
(*                            mkdir                                  *) 
(*********************************************************************) 
 
(*This operation creates a new, empty directory given by an absolute *) 
(*path. The directory is created with the mode indicated by perms.   *) 
 
Inductive mkdir (u : SUBJECT) (p : OBJNAME) (perms : PERMS) :
SFSstate -> Prop :=
    MkdirOK :
      ~ set_In (p, File) (domf (files s)) ->
      ~ set_In (p, Directory) (domd (directories s)) ->
      set_In (MyDir p) (domd (directories s)) ->
      match fsecmat (secmat s) (MyDir p) with
      | None => False
      | Some y => set_In u (ActWriters y)
      end -> mkdir u p perms (t u p perms). 
 
End Mkdir. 
 
Hint Unfold mkdir_oSC mkdir_acl. 