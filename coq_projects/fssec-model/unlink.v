Require Export DACandMAC. 
 
Section Unlink. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition unlink_oSC (o : OBJECT) : set (OBJECT * SecClass) :=
  match fOSC (objectSC s) o with
  | None => objectSC s
  | Some y => set_remove OSCeq_dec (o, y) (objectSC s)
  end. 
 
 
Definition unlink_acl (o : OBJECT) : set (OBJECT * AccessCtrlListData) :=
  match facl (acl s) o with
  | None => acl s
  | Some y => set_remove ACLeq_dec (o, y) (acl s)
  end. 
 
 
Let t (o : OBJECT) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (unlink_oSC o) (unlink_acl o) 
    (secmat s) (unlink_files o) (unlink_directories o). 
 
 
(*********************************************************************) 
(*                           unlink                                  *) 
(*********************************************************************) 
 
(*This operation removes a given file form the filesystem.           *) 
 
Inductive unlink (u : SUBJECT) (o : OBJECT) : SFSstate -> Prop :=
    UnlinkOK :
      ObjType o = File ->
      set_In (MyDir (ObjName o)) (domd (directories s)) ->
      match fsecmat (secmat s) (MyDir (fst o)) with
      | None => False
      | Some y => set_In u (ActWriters y)
      end -> ~ set_In o (domsecmat (secmat s)) -> unlink u o (t o).              
 
End Unlink. 
 
Hint Unfold unlink_oSC unlink_acl. 