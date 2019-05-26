Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section closeIsSecure. 
 
Lemma ClosePSS :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre5 s -> SecureState s -> TransFunc u s Close t -> SecureState t. 
intros s t Sub FP5 SS TF; inversion TF. 
inversion H. 
unfold SecureState in |- *. 
BreakSS. 
split. 
unfold DACSecureState in |- *; intros; simpl in |- *. 
elim (OBJeq_dec o o0); intro y0. 
rewrite <- y0. 
elim (SUBeq_dec Sub u0); intro y1. 
rewrite <- y1. 
cut
 match fsecmat (close_sm s Sub o) o with
 | None => True
 | Some y => ~ set_In Sub (ActReaders y) /\ ~ set_In Sub (ActWriters y)
 end. 
elim (fsecmat (close_sm s Sub o) o). 
intros; split; intro; tauto. 
 
auto. 
 
apply Close_smCorr; auto. 
 
cut
 match fsecmat (close_sm s Sub o) o, fsecmat (secmat s) o with
 | _, None => False
 | None, Some z => True
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
cut
 match fsecmat (secmat s) o with
 | None => True
 | Some y =>
     (set_In u0 (ActReaders y) -> PreDACRead s u0 o) /\
     (set_In u0 (ActWriters y) -> PreDACWrite s u0 o)
 end. 
unfold close_sm at 3 4, PreDACRead, PreDACWrite in |- *; simpl in |- *;
 elim (fsecmat (secmat s) o); elim (fsecmat (close_sm s Sub o) o). 
intros. 
elim H6; elim H5; intros. 
split; intro. 
apply H7; apply H9; auto. 
 
apply H8; apply H10; auto. 
 
auto. 
 
tauto. 
 
auto. 
 
unfold DACSecureState in DAC; apply DAC. 
 
apply Close_smCorr2; auto. 
 
replace (fsecmat (close_sm s Sub o) o0) with (fsecmat (secmat s) o0). 
unfold close_sm, PreDACRead, PreDACWrite in |- *; simpl in |- *;
 unfold DACSecureState, PreDACRead, PreDACWrite in DAC; 
 apply DAC. 
 
auto. 
 
unfold MACSecureState in |- *; intros; simpl in |- *. 
elim (OBJeq_dec o o0); intro y0. 
rewrite <- y0. 
cut
 match fsecmat (close_sm s Sub o) o, fsecmat (secmat s) o with
 | _, None => False
 | None, Some z => True
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
cut
 match fsecmat (secmat s) o, fOSC (objectSC s) o, fSSC (subjectSC s) u0 with
 | None, _, _ => True
 | _, None, _ => True
 | _, _, None => True
 | Some x, Some y, Some z =>
     set_In u0 (ActReaders x) \/ set_In u0 (ActWriters x) -> le_sc y z
 end. 
elim (fsecmat (secmat s) o); elim (fsecmat (close_sm s Sub o) o);
 elim (fOSC (objectSC s) o); elim (fSSC (subjectSC s) u0);
 contradiction || trivial. 
tauto. 
 
unfold MACSecureState in MAC; apply MAC. 
 
apply Close_smCorr2; auto. 
 
replace (fsecmat (close_sm s Sub o) o0) with (fsecmat (secmat s) o0). 
unfold MACSecureState in MAC; apply MAC. 
 
auto. 
 
Qed. 
 
 
Lemma ClosePSP :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre5 s -> StarProperty s -> TransFunc u s Close t -> StarProperty t. 
intros s t Sub FP5 SP TF; inversion TF. 
inversion H. 
unfold StarProperty in |- *; simpl in |- *; intros. 
cut
 match
   fsecmat (secmat s) o1, fsecmat (secmat s) o2, fOSC (objectSC s) o2,
   fOSC (objectSC s) o1
 with
 | None, _, _, _ => True
 | _, None, _, _ => True
 | _, _, None, _ => True
 | _, _, _, None => True
 | Some w, Some x, Some y, Some z =>
     set_In u0 (ActWriters w) -> set_In u0 (ActReaders x) -> le_sc y z
 end. 
cut
 match fsecmat (close_sm s Sub o) o, fsecmat (secmat s) o with
 | _, None => False
 | None, Some z => True
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
elim (OBJeq_dec o o1); elim (OBJeq_dec o o2); intros EQ2 EQ1. 
rewrite <- EQ1; rewrite <- EQ2. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (close_sm s Sub o) o); intros; auto. 
 
replace (fsecmat (close_sm s Sub o) o2) with (fsecmat (secmat s) o2). 
rewrite <- EQ1. 
elim (fsecmat (secmat s) o2); elim (fOSC (objectSC s) o);
 elim (fOSC (objectSC s) o2); elim (fsecmat (secmat s) o);
 elim (fsecmat (close_sm s Sub o) o); intros; contradiction || auto. 
tauto. 
 
auto. 
 
replace (fsecmat (close_sm s Sub o) o1) with (fsecmat (secmat s) o1). 
rewrite <- EQ2. 
elim (fsecmat (secmat s) o1); elim (fOSC (objectSC s) o);
 elim (fOSC (objectSC s) o1); elim (fsecmat (secmat s) o);
 elim (fsecmat (close_sm s Sub o) o); intros; contradiction || auto. 
tauto. 
 
auto. 
 
replace (fsecmat (close_sm s Sub o) o2) with (fsecmat (secmat s) o2). 
replace (fsecmat (close_sm s Sub o) o1) with (fsecmat (secmat s) o1). 
auto. 
 
auto. 
 
auto. 
 
apply Close_smCorr2; auto. 
 
unfold StarProperty in SP; apply SP. 
 
Qed. 
 
 
Lemma ClosePCP : forall s t : SFSstate, PreservesControlProp s Close t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intros;
 absurd
  (DACCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (close_sm s Sub o) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (close_sm s Sub o) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (close_sm s Sub o) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End closeIsSecure. 
 
Hint Resolve ClosePSS ClosePSP ClosePCP. 
 