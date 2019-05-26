Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section sscstatIsSecure. 
 
Lemma SscstatPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Sscstat t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma SscstatPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Sscstat t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma SscstatPCP : forall s t : SFSstate, PreservesControlProp s Sscstat t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
split. 
intros. 
split. 
intro. 
absurd (DACCtrlAttrHaveChanged t t o); auto. 
 
intro; absurd (MACObjCtrlAttrHaveChanged t t o); auto. 
 
intros; absurd (MACSubCtrlAttrHaveChanged t t u0); auto. 
 
Qed. 
 
 
End sscstatIsSecure. 
 
Hint Resolve SscstatPSS SscstatPSP SscstatPCP. 