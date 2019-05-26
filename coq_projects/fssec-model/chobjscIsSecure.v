Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section chobjscIsSecure. 
 
Lemma ChobjscPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre6 s -> SecureState s -> TransFunc u s Chobjsc t -> SecureState t. 
intros s t Sub FP6 SS TF; inversion TF. 
inversion H. 
unfold SecureState in |- *. 
BreakSS. 
split. 
auto. 
 
unfold MACSecureState in |- *; simpl in |- *; intros. 
elim (OBJeq_dec o o0). 
intro. 
rewrite <- a. 
cut (fsecmat (secmat s) o = None). 
intro. 
rewrite H6. 
elim (fOSC (objectSC s) o); elim (fOSC (chobjsc_SC s o sc) o);
 elim (fSSC (subjectSC s) u); contradiction || auto. 
 
unfold fsecmat in |- *; auto. 
 
intro. 
replace (fOSC (chobjsc_SC s o sc) o0) with (fOSC (objectSC s) o0). 
unfold MACSecureState in MAC; apply MAC. 
 
auto. 
 
Qed. 
 
 
Lemma ChobjscPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre6 s -> StarProperty s -> TransFunc u s Chobjsc t -> StarProperty t. 
intros s t Sub FP6 SP TF; inversion TF. 
inversion H. 
unfold StarProperty in |- *; simpl in |- *; intros. 
elim (OBJeq_dec o o1); elim (OBJeq_dec o o2); intros EQ2 EQ1. 
rewrite <- EQ1; rewrite <- EQ2. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
elim (fOSC (objectSC s) o); elim (fOSC (chobjsc_SC s o sc) o);
 contradiction || auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
auto. 
rewrite <- EQ1. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
replace (fOSC (chobjsc_SC s o sc) o2) with (fOSC (objectSC s) o2). 
elim (fsecmat (secmat s) o2); elim (fOSC (chobjsc_SC s o sc) o);
 elim (fOSC (objectSC s) o); elim (fOSC (objectSC s) o2); 
 intros; contradiction || auto. 
 
auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
rewrite <- EQ2. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
replace (fOSC (chobjsc_SC s o sc) o1) with (fOSC (objectSC s) o1). 
elim (fsecmat (secmat s) o1); elim (fOSC (chobjsc_SC s o sc) o);
 elim (fOSC (objectSC s) o); elim (fOSC (objectSC s) o1); 
 intros; contradiction || auto. 
 
auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
replace (fOSC (chobjsc_SC s o sc) o2) with (fOSC (objectSC s) o2). 
replace (fOSC (chobjsc_SC s o sc) o1) with (fOSC (objectSC s) o1). 
unfold StarProperty in SP; apply SP. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma ChobjscPCP : forall s t : SFSstate, PreservesControlProp s Chobjsc t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro. 
absurd
 (DACCtrlAttrHaveChanged s
    (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
       (AllGrp s) (RootGrp s) (SecAdmGrp s) (chobjsc_SC s o sc) 
       (acl s) (secmat s) (files s) (directories s)) o0); 
 auto. 
 
auto. 
 
intros. 
absurd
 (MACSubCtrlAttrHaveChanged s
    (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
       (AllGrp s) (RootGrp s) (SecAdmGrp s) (chobjsc_SC s o sc) 
       (acl s) (secmat s) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End chobjscIsSecure. 
 
Hint Resolve ChobjscPSS ChobjscPSP ChobjscPCP.