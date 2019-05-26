Require Export DACandMAC. 
 
Set Strict Implicit.
Unset Implicit Arguments. 
 
Section Write. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Let t (o : OBJECT) (n : nat) (buf : FILECONT) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (acl s) 
    (secmat s) (write_files o n buf) (directories s). 
 
(*********************************************************************) 
(*                            write                                  *) 
(*********************************************************************) 
 
(*This operation writes the first n BYTEs of buf to the file         *) 
(*represented by object o.                                           *) 
 
Inductive write (u : SUBJECT) (o : OBJECT) (n : nat) 
(buf : FILECONT) : SFSstate -> Prop :=
    WriteOK :
      ObjType o = File ->
      match fsecmat (secmat s) o with
      | None => False
      | Some y => set_In u (ActWriters y)
      end -> write u o n buf (t o n buf). 
 
End Write. 