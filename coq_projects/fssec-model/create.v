Require Export DACandMAC. 
Require Export setACLdata. 
 
Section Create. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition NEWFILE (p : OBJNAME) : OBJECT := (p, File). 
 
 
Definition create_oSC (u : SUBJECT) (p : OBJNAME) :
  set (OBJECT * SecClass) :=
  match fSSC (subjectSC s) u, fsecmat (secmat s) (MyDir p) with
  | None, _ => objectSC s
  | _, None => objectSC s
  | Some y, Some z => set_add OSCeq_dec (NEWFILE p, y) (objectSC s)
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
 
 
Definition create_acl (u : SUBJECT) (p : OBJNAME) (perms : PERMS) :
  set (OBJECT * AccessCtrlListData) :=
  match fSSC (subjectSC s) u, fsecmat (secmat s) (MyDir p) with
  | None, _ => acl s
  | _, None => acl s
  | Some y, Some z => set_add ACLeq_dec (NEWFILE p, NEW u p perms) (acl s)
  end. 
 
 
Let t (u : SUBJECT) (p : OBJNAME) (perms : PERMS) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (create_oSC u p) (create_acl u p perms)
    (secmat s) (create_files u p) (create_directories u p). 
 
 
(*********************************************************************) 
(*                            create                                 *) 
(*********************************************************************) 
 
(*This operation creates a new, empty file given by an absolute path.*) 
(*The file is created with the mode indicated by perms.              *) 
 
Inductive create (u : SUBJECT) (p : OBJNAME) (perms : PERMS) :
SFSstate -> Prop :=
    CreateOK :
      ~ set_In (p, File) (domf (files s)) ->
      ~ set_In (p, Directory) (domd (directories s)) ->
      set_In (MyDir p) (domd (directories s)) ->
      match fsecmat (secmat s) (MyDir p) with
      | None => False
      | Some y => set_In u (ActWriters y)
      end -> create u p perms (t u p perms). 
 
End Create. 
 
Hint Unfold create_oSC create_acl.