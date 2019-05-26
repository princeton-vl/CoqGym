Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section statIsSecure. 
 
Lemma StatPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Stat t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma StatPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Stat t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma StatPCP : forall s t : SFSstate, PreservesControlProp s Stat t. 
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
 
 
End statIsSecure. 
 
Hint Resolve StatPSS StatPSP StatPCP. 