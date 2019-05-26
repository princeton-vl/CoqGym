Require Import DACandMAC. 
 
Section Owner_Close. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition NEWRWOC (u : SUBJECT) (o : OBJECT) (y : ReadersWriters) :
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
      set_add SECMATeq_dec (o, NEWRWOC u o y)
        (set_remove SECMATeq_dec (o, y) (secmat s))
  end. 
 
 
Definition ownerclose_sm (u : SUBJECT) (o : OBJECT) :
  set (OBJECT * ReadersWriters) :=
  match fsecmat (secmat s) o with
  | None => secmat s
  | Some y => NEWSET u o y
  end. 
 
 
Let t (u : SUBJECT) (o : OBJECT) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (acl s) 
    (ownerclose_sm u o) (files s) (directories s). 
 
 
(*********************************************************************) 
(*                        Owner_Close                                *) 
(*********************************************************************) 
 
(*This operation closes an open object. Acctually user u is removed  *) 
(*from the set of active readers or writers associated with the      *) 
(*object.                                                            *)
 
Inductive owner_close (owner u : SUBJECT) (o : OBJECT) : SFSstate -> Prop :=
    Owner_CloseOK :
      match fsecmat (secmat s) o with
      | None => False
      | Some y =>
          set_In u (set_union SUBeq_dec (ActReaders y) (ActWriters y))
      end -> ExecuterIsOwner s owner o -> owner_close owner u o (t u o). 
 
End Owner_Close. 
 
Hint Unfold ownerclose_sm. 