Require Export DACandMAC. 
Require Export open. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section Read. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                             read                                  *) 
(*********************************************************************) 
 
(*This operation outputs the first n BYTEs stored in a given file.   *)  
 
Inductive read (u : SUBJECT) (o : OBJECT) (n : nat) :
SFSstate -> Exc FILECONT -> Prop :=
    ReadOK :
      ObjType o = File ->
      match fsecmat (secmat s) o with
      | None => False
      | Some y => set_In u (ActReaders y)
      end ->
      read u o n s
        match fsecmat (secmat s) o, ffiles (files s) o with
        | None, _ => None (A:=FILECONT)
        | _, None => None (A:=FILECONT)
        | Some y, Some z => Some (take n z)
        end. 
 
End Read.