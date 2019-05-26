Require Import ModelProperties.
Require Import AuxiliaryLemmas.

Section rmdirIsSecure. 
 
Lemma RmdirPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Rmdir t -> SecureState t. 
StartPSS. 
inversion H. 
unfold SecureState in |- *; BreakSS; split. 
unfold DACSecureState in |- *; simpl in |- *; intros. 
elim (OBJeq_dec o o0); intros. 
rewrite <- a. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
trivial. 
 
symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
unfold PreDACRead, PreDACWrite in |- *; simpl in |- *. 
replace (facl (rmdir_acl s o) o0) with (facl (acl s) o0). 
unfold DACSecureState, PreDACRead, PreDACWrite in DAC; apply DAC. 
 
auto. 
 
unfold MACSecureState in |- *; simpl in |- *. 
intros. 
elim (OBJeq_dec o o0). 
intro; rewrite <- a. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
elim (fOSC (rmdir_oSC s o) o); elim (fSSC (subjectSC s) u0); trivial. 
 
symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
intro EQ. 
replace (fOSC (rmdir_oSC s o) o0) with (fOSC (objectSC s) o0). 
unfold MACSecureState in MAC; apply MAC. 
 
auto. 
 
Qed. 
 
 
Lemma RmdirPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Rmdir t -> StarProperty t. 
StartPSP. 
inversion H. 
unfold StarProperty in |- *; simpl in |- *; intros. 
elim (OBJeq_dec o o1); elim (OBJeq_dec o o2); intros EQ2 EQ1. 
replace (fsecmat (secmat s) o1) with (None (A:=ReadersWriters)). 
elim (fOSC (objectSC s) o2); elim (fOSC (objectSC s) o1);
 elim (fOSC (rmdir_oSC s o) o2); elim (fOSC (rmdir_oSC s o) o1);
 elim (fsecmat (secmat s) o2); trivial. 
 
rewrite <- EQ1; symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
replace (fsecmat (secmat s) o1) with (None (A:=ReadersWriters)). 
elim (fsecmat (secmat s) o2); elim (fOSC (objectSC s) o2);
 elim (fOSC (objectSC s) o1); elim (fOSC (rmdir_oSC s o) o2);
 elim (fOSC (rmdir_oSC s o) o1); trivial. 
 
rewrite <- EQ1; symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
replace (fsecmat (secmat s) o2) with (None (A:=ReadersWriters)). 
elim (fsecmat (secmat s) o1); elim (fOSC (objectSC s) o2);
 elim (fOSC (objectSC s) o1); elim (fOSC (rmdir_oSC s o) o2);
 elim (fOSC (rmdir_oSC s o) o1); trivial. 
 
rewrite <- EQ2; symmetry  in |- *; unfold fsecmat in |- *; auto. 
 
replace (fOSC (rmdir_oSC s o) o2) with (fOSC (objectSC s) o2). 
replace (fOSC (rmdir_oSC s o) o1) with (fOSC (objectSC s) o1). 
unfold StarProperty in SP; apply SP. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma RmdirPCP :
 forall s t : SFSstate,
 FuncPre4 s -> FuncPre6 s -> PreservesControlProp s Rmdir t. 
intros s t FP4 FP6; unfold PreservesControlProp in |- *; intros Sub TF;
 inversion TF; unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro. 
inversion H8. 
elim (OBJeq_dec o o0); simpl in H10; intro y0. 
cut False. 
tauto. 
 
rewrite y0 in H10. 
eauto. 
 
cut (y = z). 
intro; rewrite H12 in H11; cut False; [ tauto | inversion H11; auto ]. 
 
cut (facl (acl s) o0 = facl (rmdir_acl s o) o0);
 [ rewrite H9; rewrite H10; intro; injection H12; auto | auto ]. 
 
elim (OBJeq_dec o o0); simpl in H10; intro y0. 
cut False. 
tauto. 
 
rewrite y0 in H10. 
eauto. 
 
cut (y = z). 
intro; rewrite H12 in H11; cut False; [ tauto | inversion H11; auto ]. 
 
cut (facl (acl s) o0 = facl (rmdir_acl s o) o0);
 [ rewrite H10; rewrite H9; intro; injection H12; auto | auto ]. 
 
intro. 
inversion H8. 
elim (OBJeq_dec o o0); simpl in H10; intros y0. 
cut False. 
tauto. 
 
rewrite y0 in H10. 
eauto. 
 
cut (x = y). 
intro; rewrite H12 in H11; cut False; [ tauto | inversion H11; auto ]. 
 
cut (fOSC (objectSC s) o0 = fOSC (rmdir_oSC s o) o0);
 [ rewrite H10; rewrite H9; intro; injection H12; auto | auto ]. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (rmdir_oSC s o) 
        (rmdir_acl s o) (secmat s) (files s) (rmdir_directories o)) u0); 
 auto. 
 
Qed. 
 
 
End rmdirIsSecure. 
 
Hint Resolve RmdirPSS RmdirPSP RmdirPCP. 
 