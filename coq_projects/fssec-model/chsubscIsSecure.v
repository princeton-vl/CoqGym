Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section chsubscIsSecure. 
 
Lemma ChsubscPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre7 s -> SecureState s -> TransFunc u s Chsubsc t -> SecureState t. 
intros s t Sub FP7 SS TF; inversion TF. 
inversion H. 
unfold SecureState in |- *. 
BreakSS. 
split. 
auto. 
 
unfold MACSecureState in |- *; simpl in |- *. 
intros; elim (SUBeq_dec u u0); intro y0. 
rewrite <- y0. 
elim (fsecmat (secmat s) o); elim (fSSC (chsubsc_SC s u sc) u);
 elim (fOSC (objectSC s) o); (intros; contradiction || auto). 
absurd (set_In u (ActReaders a1) \/ set_In u (ActWriters a1)); auto. 
 
replace (fSSC (chsubsc_SC s u sc) u0) with (fSSC (subjectSC s) u0). 
unfold MACSecureState in MAC; apply MAC; auto. 
 
auto. 
 
Qed. 
 
 
Lemma ChsubscPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Chsubsc t -> StarProperty t. 
StartPSP. 
inversion H. 
auto. 
 
Qed. 
 
 
Lemma ChsubscPCP : forall s t : SFSstate, PreservesControlProp s Chsubsc t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro;
 absurd
  (DACCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (chsubsc_SC s u sc) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (secmat s) (files s) (directories s)) o); 
 auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (chsubsc_SC s u sc) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (secmat s) (files s) (directories s)) o); 
 auto. 
 
auto. 
 
Qed. 
 
 
End chsubscIsSecure. 
 
Hint Resolve ChsubscPSS ChsubscPSP ChsubscPCP. 
 