Require Export SFSstate. 
 
Section setACLdata. 
 
Variable s : SFSstate. 
 
(*This operator adds or removes a reader from a set of subjects      *)
(*on the rights the user has.                                        *)
 
Definition ChangeUserR (u : SUBJECT) (x : set SUBJECT) 
  (oct : RIGHTS) : set SUBJECT :=
  match oct with
  | allowedTo false false => set_remove SUBeq_dec u x
  | allowedTo false true => set_remove SUBeq_dec u x
  | allowedTo true false => set_add SUBeq_dec u x
  | allowedTo true true => set_add SUBeq_dec u x
  end. 

(*This operator adds or removes a writer from a set of subjects      *)
(*on the rights the user has.                                        *)  

Definition ChangeUserW (u : SUBJECT) (x : set SUBJECT) 
  (oct : RIGHTS) : set SUBJECT :=
  match oct with
  | allowedTo false false => set_remove SUBeq_dec u x
  | allowedTo false true => set_add SUBeq_dec u x
  | allowedTo true false => set_remove SUBeq_dec u x
  | allowedTo true true => set_add SUBeq_dec u x
  end. 
 
(*The next two operators do the same than the previous two but for   *)
(*a group of users                                                   *) 
 
Definition ChangeGroupR (g : GRPNAME) (oct : RIGHTS) 
  (x : set GRPNAME) : set GRPNAME :=
  match oct with
  | allowedTo false false => set_remove GRPeq_dec g x
  | allowedTo false true => set_remove GRPeq_dec g x
  | allowedTo true false => set_add GRPeq_dec g x
  | allowedTo true true => set_add GRPeq_dec g x
  end. 
 
Definition ChangeGroupW (g : GRPNAME) (oct : RIGHTS) 
  (x : set GRPNAME) : set GRPNAME :=
  match oct with
  | allowedTo false false => set_remove GRPeq_dec g x
  | allowedTo false true => set_add GRPeq_dec g x
  | allowedTo true false => set_remove GRPeq_dec g x
  | allowedTo true true => set_add GRPeq_dec g x
  end. 
 
Definition ChangeGroupO (g : GRPNAME) (x : set GRPNAME) : 
  set GRPNAME := set_add GRPeq_dec g x. 

End setACLdata.