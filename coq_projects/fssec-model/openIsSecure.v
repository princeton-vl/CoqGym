Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section openIsSecure. 
 
Lemma OpenPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre5 s -> SecureState s -> TransFunc u s Open t -> SecureState t. 
intros s t Sub FP5 SS TF; inversion TF. 
inversion H. 
unfold SecureState, DACSecureState, MACSecureState in |- *; simpl in |- *;
 BreakSS. 
split; intros. 
elim (OBJeq_dec o o0); intro EQo. 
rewrite <- EQo. 
elim (SUBeq_dec Sub u0); intro EQu. 
rewrite <- EQu. 
unfold open_sm at 1, PreDACRead, PreDACWrite in |- *; simpl in |- *. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
cut
 match fsecmat (secmat s) o with
 | None => True
 | Some y => set_In Sub (ActWriters y) -> PreDACWrite s Sub o
 end. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))). 
simpl in |- *. 
split; intros. 
auto. 
 
unfold PreDACWrite in H9; apply H9; auto. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec (o, mkRW (Sub :: nil) (empty_set SUBJECT))
        (secmat s)) o) with (Some (mkRW (Sub :: nil) (empty_set SUBJECT))). 
simpl in |- *. 
split; (intro H12; elim H12). 
auto. 
 
tauto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
apply ReadWriteImpWrite; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
cut
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | None, _ => False
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
unfold PreDACRead, PreDACWrite in |- *; simpl in |- *;
 elim (fsecmat (secmat s) o); elim (fsecmat (open_sm s Sub o READ) o). 
tauto. 
 
auto. 
 
split; intros. 
elim H10; intros. 
absurd (Sub = u0); auto. 
rewrite H12 in H11. 
simpl in H11. 
tauto. 
 
elim H10; intros H12 H13; rewrite H13 in H11; simpl in H13; contradiction. 
 
auto. 
 
apply DAC. 
 
apply Open_smCorr21; auto. 
 
replace (fsecmat (open_sm s Sub o READ) o0) with (fsecmat (secmat s) o0). 
unfold PreDACRead, PreDACWrite in |- *; simpl in |- *;
 unfold DACSecureState, PreDACRead, PreDACWrite in DAC; 
 apply DAC. 
 
auto. 
 
unfold MACSecureState in |- *; intros; simpl in |- *. 
elim (OBJeq_dec o o0); intro EQo. 
rewrite <- EQo. 
elim (SUBeq_dec Sub u0); intro EQu. 
rewrite <- EQu. 
unfold open_sm in |- *; simpl in |- *. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
cut
 match fOSC (objectSC s) o with
 | Some t =>
     match fSSC (subjectSC s) Sub with
     | Some b => le_sc t b
     | None => False
     end
 | None =>
     match fSSC (subjectSC s) Sub with
     | Some _ => False
     | None => False
     end
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fSSC (subjectSC s) Sub); contradiction || auto. 
intros until a1;
 elim
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (set_add SUBeq_dec Sub (ActReaders a1)) (ActWriters a1))
        (set_remove SECMATeq_dec (o, a1) (secmat s))) o); 
 auto. 
 
intros until a0;
 elim
  (fsecmat
     (set_add SECMATeq_dec (o, mkRW (Sub :: nil) (empty_set SUBJECT))
        (secmat s)) o); auto. 
 
unfold PreMAC in H5.
cut
 (match fSSC (subjectSC s) Sub with
  | Some _ => False
  | None => False
  end = False).
intro; rewrite H9.
assumption.
case (fSSC (subjectSC s) Sub); reflexivity.

 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
cut
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
cut
 match fOSC (objectSC s) o with
 | Some t =>
     match fSSC (subjectSC s) Sub with
     | Some b => le_sc t b
     | None => False
     end
 | None =>
     match fSSC (subjectSC s) Sub with
     | Some _ => False
     | None => False
     end
 end. 
cut
 match fsecmat (secmat s) o, fOSC (objectSC s) o, fSSC (subjectSC s) u0 with
 | None, _, _ => True
 | _, None, _ => True
 | _, _, None => True
 | Some x, Some y, Some z =>
     set_In u0 (ActReaders x) \/ set_In u0 (ActWriters x) -> le_sc y z
 end. 
elim (fSSC (subjectSC s) u0); elim (fsecmat (open_sm s Sub o READ) o);
 elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fSSC (subjectSC s) Sub); contradiction || auto. 
tauto. 
 
intros. 
elim H11; intros H13 H14; rewrite H13 in H12; rewrite H14 in H12;
 simpl in H12; tauto. 
 
unfold MACSecureState in MAC; apply MAC; auto. 
 
replace
 match fSSC (subjectSC s) Sub with
 | Some _ => False
 | None => False
 end with False.
auto. 
case (fSSC (subjectSC s) Sub); reflexivity.
 
apply Open_smCorr21; auto. 
 
replace (fsecmat (open_sm s Sub o READ) o0) with (fsecmat (secmat s) o0). 
unfold MACSecureState in MAC; apply MAC; auto. 
 
auto. 
 
(*********************************************************************) 
(*                         End READ                                  *) 
(*                                                                   *) 
(*                                                                   *) 
(*                                                                   *) 
(*                       Begin WRITE                                 *) 
(*********************************************************************) 
 
unfold SecureState, DACSecureState, MACSecureState in |- *; simpl in |- *;
 BreakSS. 
split; intros. 
elim (OBJeq_dec o o0); intro EQo. 
rewrite <- EQo. 
elim (SUBeq_dec Sub u0); intro EQu. 
rewrite <- EQu. 
unfold open_sm at 1, PreDACRead, PreDACWrite in |- *; simpl in |- *. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
cut
 match fsecmat (secmat s) o with
 | None => True
 | Some y => set_In Sub (ActReaders y) -> PreDACRead s Sub o
 end. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))). 
simpl in |- *. 
split; intros. 
unfold PreDACRead in H9; apply H9; auto. 
 
auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec (o, mkRW (empty_set SUBJECT) (Sub :: nil))
        (secmat s)) o) with (Some (mkRW (empty_set SUBJECT) (Sub :: nil))). 
simpl in |- *. 
split; (intro H11; elim H11). 
auto. 
 
contradiction. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
apply ReadWriteImpRead; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
cut
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
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
unfold PreDACRead, PreDACWrite in |- *; simpl in |- *;
 elim (fsecmat (secmat s) o); elim (fsecmat (open_sm s Sub o WRITE) o). 
tauto. 
 
contradiction. 
 
split; intros. 
elim H10; intros. 
absurd (Sub = u0); auto. 
rewrite H13 in H11. 
simpl in H11. 
tauto. 
 
elim H10; intros H12 H13; rewrite H12 in H11; simpl in H11; tauto. 
 
auto. 
 
apply DAC. 
 
apply Open_smCorr22; auto. 
 
replace (fsecmat (open_sm s Sub o WRITE) o0) with (fsecmat (secmat s) o0). 
unfold PreDACRead, PreDACWrite in |- *; simpl in |- *;
 unfold DACSecureState, PreDACRead, PreDACWrite in DAC; 
 apply DAC. 
 
auto. 
 
unfold MACSecureState in |- *; intros; simpl in |- *. 
elim (OBJeq_dec o o0); intro EQo. 
rewrite <- EQo. 
elim (SUBeq_dec Sub u0); intro EQu. 
rewrite <- EQu. 
unfold open_sm in |- *; simpl in |- *. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
cut
 match fOSC (objectSC s) o with
 | Some t =>
     match fSSC (subjectSC s) Sub with
     | Some b => le_sc t b
     | None => False
     end
 | None =>
     match fSSC (subjectSC s) Sub with
     | Some _ => False
     | None => False
     end
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fSSC (subjectSC s) Sub); contradiction || auto. 
intros until a1;
 elim
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (ActReaders a1) (set_add SUBeq_dec Sub (ActWriters a1)))
        (set_remove SECMATeq_dec (o, a1) (secmat s))) o); 
 auto. 
 
intros until a0;
 elim
  (fsecmat
     (set_add SECMATeq_dec (o, mkRW (empty_set SUBJECT) (Sub :: nil))
        (secmat s)) o); auto. 
 
replace
 match fSSC (subjectSC s) Sub with
 | Some _ => False
 | None => False
 end with False.
auto. 
case (fSSC (subjectSC s) Sub); reflexivity.
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
cut
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
cut
 match fOSC (objectSC s) o with
 | Some t =>
     match fSSC (subjectSC s) Sub with
     | Some b => le_sc t b
     | None => False
     end
 | None =>
     match fSSC (subjectSC s) Sub with
     | Some _ => False
     | None => False
     end
 end. 
cut
 match fsecmat (secmat s) o, fOSC (objectSC s) o, fSSC (subjectSC s) u0 with
 | None, _, _ => True
 | _, None, _ => True
 | _, _, None => True
 | Some x, Some y, Some z =>
     set_In u0 (ActReaders x) \/ set_In u0 (ActWriters x) -> le_sc y z
 end. 
elim (fSSC (subjectSC s) u0); elim (fsecmat (open_sm s Sub o WRITE) o);
 elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fSSC (subjectSC s) Sub); contradiction || auto. 
tauto. 
 
intros. 
elim H11; intros H13 H14; rewrite H13 in H12; rewrite H14 in H12;
 simpl in H12; tauto. 
 
unfold MACSecureState in MAC; apply MAC; auto. 

replace
 match fSSC (subjectSC s) Sub with
 | Some _ => False
 | None => False
 end with False.
auto. 
case (fSSC (subjectSC s) Sub); reflexivity.

 
apply Open_smCorr22; auto. 
 
replace (fsecmat (open_sm s Sub o WRITE) o0) with (fsecmat (secmat s) o0). 
unfold MACSecureState in MAC; apply MAC; auto. 
 
auto. 
 
Qed. 
 
 
 
(*********************************************************************) 
(*                                                                   *) 
(*                                                                   *) 
(*                              OpenPSP                              *) 
(*                                                                   *) 
(*                                                                   *) 
(*********************************************************************) 
 
 
 
Lemma OpenPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre5 s -> StarProperty s -> TransFunc u s Open t -> StarProperty t. 
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
elim (OBJeq_dec o o1); elim (OBJeq_dec o o2); intros EQ2 EQ1. 
rewrite <- EQ1; rewrite <- EQ2. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (open_sm s Sub o READ) o); auto. 
 
rewrite <- EQ1. 
replace (fsecmat (open_sm s Sub o READ) o2) with (fsecmat (secmat s) o2). 
cut
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | None, _ => False
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | Some x, Some y => set_In u0 (ActWriters x) -> set_In u0 (ActWriters y)
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o2); elim (fsecmat (open_sm s Sub o READ) o);
 elim (fOSC (objectSC s) o2); auto. 
intros. 
elim H9; intros H16 H17; rewrite H17 in H11; simpl in H11; contradiction. 
 
apply Open_smCorr31; auto. 
 
auto. 
 
rewrite <- EQ2. 
replace (fsecmat (open_sm s Sub o READ) o1) with (fsecmat (secmat s) o1). 
elim (SUBeq_dec Sub u0); intro EQu. 
cut
 match fsecmat (secmat s) o1, fOSC (objectSC s) o, fOSC (objectSC s) o1 with
 | None, _, _ => False
 | _, None, _ => False
 | _, _, None => False
 | Some x, Some y, Some z => set_In Sub (ActWriters x) -> le_sc y z
 end. 
rewrite <- EQu. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o1); elim (fsecmat (open_sm s Sub o READ) o);
 elim (fOSC (objectSC s) o1); auto. 
 
unfold PreStarPropRead in H6; apply H6. 
 
cut
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o1); elim (fsecmat (open_sm s Sub o READ) o);
 elim (fOSC (objectSC s) o1); auto. 
tauto. 
 
intros. 
elim H9; intros H16 H17; rewrite H16 in H12; simpl in H12; elim H12; intro;
 contradiction. 
 
apply Open_smCorr21; auto. 
 
auto. 
 
replace (fsecmat (open_sm s Sub o READ) o1) with (fsecmat (secmat s) o1). 
replace (fsecmat (open_sm s Sub o READ) o2) with (fsecmat (secmat s) o2). 
auto. 
 
auto. 
 
auto. 
 
unfold StarProperty in SP; apply SP; auto. 
 
 
(*********************************************************************) 
(*                         End READ                                  *) 
(*                                                                   *) 
(*                                                                   *) 
(*                                                                   *) 
(*                       Begin WRITE                                 *) 
(*********************************************************************) 
 
 
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
elim (OBJeq_dec o o1); elim (OBJeq_dec o o2); intros EQ2 EQ1. 
rewrite <- EQ1; rewrite <- EQ2. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (open_sm s Sub o WRITE) o); auto. 
 
rewrite <- EQ1. 
replace (fsecmat (open_sm s Sub o WRITE) o2) with (fsecmat (secmat s) o2). 
elim (SUBeq_dec Sub u0); intro EQu. 
cut
 match fsecmat (secmat s) o2, fOSC (objectSC s) o, fOSC (objectSC s) o2 with
 | None, _, _ => False
 | _, None, _ => False
 | _, _, None => False
 | Some x, Some y, Some z => set_In Sub (ActReaders x) -> le_sc z y
 end. 
rewrite <- EQu. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o2); elim (fsecmat (open_sm s Sub o WRITE) o);
 elim (fOSC (objectSC s) o2); auto. 
 
unfold PreStarPropWrite in H6; apply H6. 
 
cut
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o2); elim (fsecmat (open_sm s Sub o WRITE) o);
 elim (fOSC (objectSC s) o2); auto. 
tauto. 
 
intros. 
elim H9; intros H15 H16. 
rewrite H15 in H11; simpl in H11; elim H11; intro; try contradiction. 
 
apply Open_smCorr22; auto. 
 
auto. 
 
rewrite <- EQ2. 
replace (fsecmat (open_sm s Sub o WRITE) o1) with (fsecmat (secmat s) o1). 
elim (SUBeq_dec Sub u0); intro EQu. 
cut
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z => set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)
 end. 
rewrite <- EQu. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o1); elim (fsecmat (open_sm s Sub o WRITE) o);
 elim (fOSC (objectSC s) o1); auto. 
intros. 
elim H9; intros H14 H15; rewrite H15 in H12; simpl in H12; contradiction. 
 
apply Open_smCorr32; auto. 
 
cut
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
elim (fsecmat (secmat s) o); elim (fOSC (objectSC s) o);
 elim (fsecmat (secmat s) o1); elim (fsecmat (open_sm s Sub o WRITE) o);
 elim (fOSC (objectSC s) o1); auto. 
tauto. 
 
intros. 
elim H9; intros H14 H15; rewrite H15 in H12; simpl in H12; contradiction. 
 
apply Open_smCorr22; auto. 
 
auto. 
 
replace (fsecmat (open_sm s Sub o WRITE) o1) with (fsecmat (secmat s) o1). 
replace (fsecmat (open_sm s Sub o WRITE) o2) with (fsecmat (secmat s) o2). 
auto. 
 
auto. 
 
auto. 
 
unfold StarProperty in SP; apply SP; auto. 
 
Qed. 
 
 
Lemma OpenPCP : forall s t : SFSstate, PreservesControlProp s Open t. 
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
        (acl s) (open_sm s Sub o READ) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (open_sm s Sub o READ) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (open_sm s Sub o READ) (files s) (directories s)) u0); 
 auto. 
 
split. 
intros. 
split. 
intros;
 absurd
  (DACCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (open_sm s Sub o WRITE) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (open_sm s Sub o WRITE) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (acl s) (open_sm s Sub o WRITE) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End openIsSecure. 
 
Hint Resolve OpenPSS OpenPSP OpenPCP. 
 