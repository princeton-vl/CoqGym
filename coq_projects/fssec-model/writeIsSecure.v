Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section writeIsSecure. 
 
Lemma WritePSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Write t -> SecureState t. 
StartPSS. 
inversion H. 
auto. 
 
Qed. 
 
 
Lemma WritePSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Write t -> StarProperty t. 
StartPSP. 
inversion H. 
auto. 
 
Qed. 
 
 
Lemma WritePCP : forall s t : SFSstate, PreservesControlProp s Write t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro;
 absurd
  (DACCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (secmat s) (write_files o n buf) (directories s)) o0); 
 auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (secmat s) (write_files o n buf) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (secmat s) (write_files o n buf) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End writeIsSecure. 
 
Hint Resolve WritePSS WritePSP WritePCP. 