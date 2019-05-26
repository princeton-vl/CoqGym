Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section oscstatIsSecure. 
 
Lemma OscstatPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Oscstat t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma OscstatPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Oscstat t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma OscstatPCP : forall s t : SFSstate, PreservesControlProp s Oscstat t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
split. 
intros. 
split. 
intro. 
absurd (DACCtrlAttrHaveChanged t t o0); auto. 
 
intro; absurd (MACObjCtrlAttrHaveChanged t t o0); auto. 
 
intros; absurd (MACSubCtrlAttrHaveChanged t t u0); auto. 
 
Qed. 
 
 
End oscstatIsSecure. 
 
Hint Resolve OscstatPSS OscstatPSP OscstatPCP. 
 