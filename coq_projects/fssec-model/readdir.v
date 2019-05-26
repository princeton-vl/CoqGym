Require Export DACandMAC. 
 
Section Readdir. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                          readdir                                  *) 
(*********************************************************************) 
 
(*This operation outputs the first n objects stored in a given       *) 
(*directory.                                                         *) 
 
Inductive readdir (u : SUBJECT) (o : OBJECT) (n : nat) :
SFSstate -> Exc DIRCONT -> Prop :=
    ReaddirOK :
      ObjType o = Directory ->
      match fsecmat (secmat s) o with
      | None => False
      | Some y => set_In u (ActReaders y)
      end ->
      readdir u o n s
        match fsecmat (secmat s) o, fdirs (directories s) o with
        | None, _ => None (A:=DIRCONT)
        | _, None => None (A:=DIRCONT)
        | Some y, Some z => Some (take n z)
        end. 
 
End Readdir.