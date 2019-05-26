Require Import DACandMAC. 
 
Section Close. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition NEWRW (u : SUBJECT) (o : OBJECT) (y : ReadersWriters) :
  ReadersWriters :=
  mkRW (set_remove SUBeq_dec u (ActReaders y))
    (set_remove SUBeq_dec u (ActWriters y)). 
 
 
Let NEWSET (u : SUBJECT) (o : OBJECT) (y : ReadersWriters) :
  set (OBJECT * ReadersWriters) :=
  match
    set_remove SUBeq_dec u (ActReaders y),
    set_remove SUBeq_dec u (ActWriters y)
  with
  | nil, nil => set_remove SECMATeq_dec (o, y) (secmat s)
  | _, _ =>
      set_add SECMATeq_dec (o, NEWRW u o y)
        (set_remove SECMATeq_dec (o, y) (secmat s))
  end. 
 
(*close_sm is assuming the precondition of close (i.e, that u is an  *) 
(*active reader or an active writer of o); with this assumption,     *) 
(*(ActReaders z)=(ActWriters z)=nil, means that the only active      *) 
(*reader and writer of o was u, and so, if he is closing the file, it*) 
(*should be erased from memory.                                      *) 
 
Definition close_sm (u : SUBJECT) (o : OBJECT) :
  set (OBJECT * ReadersWriters) :=
  match fsecmat (secmat s) o with
  | None => secmat s
  | Some y => NEWSET u o y
  end. 
 
 
Let t (u : SUBJECT) (o : OBJECT) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (acl s) 
    (close_sm u o) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                            Close                                  *) 
(*********************************************************************) 
 
(*This operation closes an open object. Acctually the user           *) 
(*requesting the operation is removed from the set of active readers *) 
(*or writers associated with the object.                             *) 
 
Inductive close (u : SUBJECT) (o : OBJECT) : SFSstate -> Prop :=
    CloseOK :
      match fsecmat (secmat s) o with
      | None => False
      | Some y =>
          set_In u (set_union SUBeq_dec (ActReaders y) (ActWriters y))
      end -> close u o (t u o). 
 
Hint Unfold close_sm t. 
 
End Close.