Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.

(* --------------------------------------------------------------------------- *)
(* Infinite subsequences *)

Section sec_subseq.

Variable T: Type.

(* suff s s'  means  s is a suffix of s' *)
Inductive suff (s : infseq T) : infseq T -> Prop :=
  | sp_eq : suff s s
  | sp_next : forall x s0, suff s s0 -> suff s (Cons x s0).

(* simple but not the most useful -- useless indeed *)
CoInductive subseq : infseq T -> infseq T -> Prop :=
  | Subseq : forall s s0 s1,
             suff s1 s0 -> subseq s (tl s1) -> subseq (Cons (hd s1) s) s0.

CoInductive subseqs' : infseq (infseq T) -> infseq T -> Prop :=
  | Subseqs' : forall si s0 s1,
             suff s1 s0 -> subseqs' si (tl s1) -> subseqs' (Cons s1 si) s0. 

CoInductive subseqs : infseq (infseq T) -> infseq T -> Prop :=
  | Subseqs : forall si s,
             suff (hd si) s -> subseqs (tl si) (tl (hd si)) -> subseqs si s. 

Lemma subseqs_subseqs' : forall si s, subseqs si s -> subseqs' si s.
Proof using.
cofix subsub. 
intros si s su. case su; clear su si s.
intros (s1, si) s0. simpl. intros su sb. constructor.
- assumption.
- apply subsub. assumption.
Qed.

Lemma subseqs'_subseqs : forall si s, subseqs' si s -> subseqs si s.
cofix subsub.
intros si s su. case su; clear su si s.
intros si s0 s1 su sb. constructor; simpl.
- assumption. 
- apply subsub. assumption. 
Qed.

(* Relating inf subseq to infinitely often *)

(* In the next lemma, always1 is bit overkill, but is just what is needed below *)
Lemma subseqs_eventually : 
  forall P si s, subseqs si s -> always1 P si -> eventually P s.
Proof using.
intros P si s su. destruct su as [si s sf _].
induction sf as [ | x s0 _ Hrec]; intro a. 
- constructor 1. case a; simpl. intros; assumption.
- constructor 2. apply Hrec. apply a.
Qed.

Lemma subseqs_tl : forall si s, subseqs si (tl s) -> subseqs si s. 
Proof using.
intros si (x, s) su. simpl in su.
case su. clear su si s; intros si s sf su.
constructor.
- constructor 2. exact sf.
- exact su.
Qed.

Theorem subseq_inf_often :
  forall P si s, subseqs si s -> always1 P si -> inf_often P s.
Proof using.
intros P. red. cofix sio.
intros si s su a.
constructor.
- apply subseqs_eventually with si; assumption.
- genclear a. case su. 
  clear su si s; intros (s0, si) s sf su a; simpl in * |- * . 
  apply (sio si); clear sio.
  * induction sf; simpl.
    trivial. 
    apply subseqs_tl. assumption (* induction hyp *). 
  * change (always1 P (tl (Cons s0 si))). case a; simpl; trivial. 
Qed.

(* Conversely : TODO *)

Inductive ex_suff (P: infseq T -> Prop) (s' : infseq T) : Prop :=
  Esp : forall s, suff s s' -> P s -> ex_suff P s'.

Theorem eventually_suff :
   forall P s', eventually P s' -> ex_suff P s'.
Proof using.
intros P s ev. induction ev.   
- exists s; [ constructor | assumption]. 
- destruct IHev. exists s0. 
  * constructor; assumption.
  * assumption.
Qed.

(* Extensional version *)

Inductive suff_exteq (s : infseq T) : infseq T -> Prop :=
  | sb_eq : forall s', exteq s s' -> suff_exteq s s'
  | sb_next : forall x s', suff_exteq s s' -> suff_exteq s (Cons x s').

Inductive suffb (x : T) (s : infseq T) : infseq T -> Prop :=
  | sp_eqb : forall s', exteq (Cons x s) s' -> suffb x s s'
  | sp_nextb : forall y s', suffb x s s' -> suffb x s (Cons y s').

CoInductive subseqb : infseq T -> infseq T -> Prop :=
  | Subseqb : forall x s s', suffb x s s' -> subseqb s s' -> subseqb (Cons x s) s'.

Inductive mem (x : T) : infseq T -> Prop :=
  | mem0 : forall s, mem x (Cons x s)
  | mem_next : forall y s, mem x s -> mem x (Cons y s).

Lemma subseqb_included : forall x s, mem x s -> forall s', subseqb s s' -> mem x s'.
Proof using.
induction 1 as [| y s M IHmem].
- inversion_clear 1 as [a b c ssp _]. induction ssp as [s' ssp | ].
  inversion_clear ssp. constructor.
  constructor. assumption.
- inversion_clear 1. apply IHmem; assumption.
Qed.

End sec_subseq. 
