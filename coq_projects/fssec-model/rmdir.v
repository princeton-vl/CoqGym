Require Export DACandMAC. 
 
Section Rmdir. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition rmdir_oSC (o : OBJECT) : set (OBJECT * SecClass) :=
  match fOSC (objectSC s) o with
  | None => objectSC s
  | Some y => set_remove OSCeq_dec (o, y) (objectSC s)
  end. 
 
 
Definition rmdir_acl (o : OBJECT) : set (OBJECT * AccessCtrlListData) :=
  match facl (acl s) o with
  | None => acl s
  | Some y => set_remove ACLeq_dec (o, y) (acl s)
  end. 
 
 
Let t (o : OBJECT) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (rmdir_oSC o) (rmdir_acl o) 
    (secmat s) (files s) (rmdir_directories o). 
 
 
(*********************************************************************) 
(*                            rmdir                                  *) 
(*********************************************************************) 
 
(*This operation removes a given directory from the filesystem.      *) 
 
Inductive rmdir (u : SUBJECT) (o : OBJECT) : SFSstate -> Prop :=
    RmdirOK :
      ObjType o = Directory ->
      set_In (MyDir (ObjName o)) (domd (directories s)) ->
      match fsecmat (secmat s) (MyDir (ObjName o)) with
      | None => False
      | Some y => set_In u (ActWriters y)
      end -> ~ set_In o (domsecmat (secmat s)) -> rmdir u o (t o). 
 
End Rmdir. 
 
Hint Unfold rmdir_oSC rmdir_acl. 