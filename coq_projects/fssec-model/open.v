Require Export DACandMAC. 
 
Section Open. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Definition open_sm (u : SUBJECT) (o : OBJECT) (m : MODE) :
  set (OBJECT * ReadersWriters) :=
  match fsecmat (secmat s) o with
  | None =>
      match m with
      | READ =>
          set_add SECMATeq_dec
            (o,
            mkRW (set_add SUBeq_dec u (empty_set SUBJECT))
              (empty_set SUBJECT)) (secmat s)
      | WRITE =>
          set_add SECMATeq_dec
            (o,
            mkRW (empty_set SUBJECT)
              (set_add SUBeq_dec u (empty_set SUBJECT))) 
            (secmat s)
      end
  | Some y =>
      match m with
      | READ =>
          set_add SECMATeq_dec
            (o, mkRW (set_add SUBeq_dec u (ActReaders y)) (ActWriters y))
            (set_remove SECMATeq_dec (o, y) (secmat s))
      | WRITE =>
          set_add SECMATeq_dec
            (o, mkRW (ActReaders y) (set_add SUBeq_dec u (ActWriters y)))
            (set_remove SECMATeq_dec (o, y) (secmat s))
      end
  end. 
 
Let t (u : SUBJECT) (o : OBJECT) (m : MODE) : SFSstate :=
  mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
    (RootGrp s) (SecAdmGrp s) (objectSC s) (acl s) 
    (open_sm u o m) (files s) (directories s). 
 
(*********************************************************************) 
(*                            Open                                   *) 
(*********************************************************************) 
 
(*This operation opens a given object. This means to add the invoking*) 
(*user to the set of active readers or writers associated with the   *) 
(*object by secmat.                                                  *) 
 
Inductive open (u : SUBJECT) (o : OBJECT) : MODE -> SFSstate -> Prop :=
  | OpenRead :
      InFileSystem s o ->
      PreDACRead s u o ->
      PreMAC s u o -> PreStarPropRead s u o -> open u o READ (t u o READ)
  | OpenWrite :
      InFileSystem s o ->
      PreDACWrite s u o ->
      PreMAC s u o -> PreStarPropWrite s u o -> open u o WRITE (t u o WRITE). 
 
Hint Unfold open_sm t. 
 
End Open.