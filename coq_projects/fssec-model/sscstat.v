Require Export SFSstate. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section Sscstat. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                           sscstat                                 *) 
(*********************************************************************) 
 
(*This operation outputs the security class of a given subject. The  *) 
(*security class of the invoking user should be less or equal than   *) 
(*that of the requested user.                                        *) 
 
Inductive sscstat (u user : SUBJECT) : SFSstate -> Exc SecClass -> Prop :=
    SscstatOK :
      match fSSC (subjectSC s) user, fSSC (subjectSC s) u with
      | None, _ => True
      | _, None => True
      | Some y, Some z => le_sc y z
      end -> sscstat u user s (fSSC (subjectSC s) user). 
 
End Sscstat.