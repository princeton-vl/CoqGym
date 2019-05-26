From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Actions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Framing with respect to the world *)

Module Injection.
Section Injection.

Variable W : world.

Structure injects (U V : world) (K : hooks) := Inject {
  (* The "delta world" *)
  E : world;
                                       
  _ : hook_complete U /\ hook_complete E;

  (* Additional hooks are included with an empty world *)
  _ : V = U \+ E \+ (Unit, K);

  (* Additional hooks are well-formed with respect to the world *)
  _ : hooks_consistent (getc (U \+ E)) K;
  
  (* These all should be easy to prove given a standard world disentanglement *)
  _ : forall s, Coh V s <-> exists s1 s2,
        [/\ s = s1 \+ s2, Coh U s1 & Coh E s2];

  (* Framing wrt. worlds and hooks *)
  _ : forall s1 s2 s this,
      s1 \+ s \In Coh V -> network_step U this s1 s2 ->
      network_step V this (s1 \+ s) (s2 \+ s);

  _ : forall s1 s2 s1' s2' this,
      s1 \In Coh U -> s2 \In Coh U ->
      network_step V this (s1 \+ s1') (s2 \+ s2') ->
      (network_step U this s1 s2   /\ s1' = s2') \/
      (network_step E this s1' s2' /\ s1 = s2); }.

End Injection.

Module Exports.
Section Exports.

Definition inj_ext := E.
Definition injects := injects. 
Definition Inject := Inject.

Lemma cohK (U V : world) (K : hooks) (w : injects U V K) :
  V = U \+ inj_ext w \+ (Unit, K).
Proof. by case: w=>E/=. Qed.

Lemma cohE (U V : world) (K : hooks) (w : injects U V K) s :
  Coh V s <-> exists s1 s2,
      [/\ s = s1 \+ s2, Coh U s1 & Coh (inj_ext w) s2].
Proof. by case: w=>W ??? cohE sL sR; apply: cohE. Qed.

Lemma sem_extend (U V : world) (K : hooks) (w : injects U V K) s1 s2 s this: 
      s1 \+ s \In Coh V -> s2 \+ s \In Coh V ->
      network_step U this s1 s2 -> network_step V this (s1 \+ s) (s2 \+ s).
Proof.
by case: w=>W _ _ _ cohE sL sR C G; apply: sL=>//.
Qed.

Lemma sem_split (U V : world) (K : hooks) (w : injects U V K) s1 s1' s2 s2' this: 
      s1 \In Coh U -> s2 \In Coh U ->
      network_step V this (s1 \+ s1') (s2 \+ s2') ->
      (network_step U this s1 s2   /\ s1' = s2') \/
      (network_step (inj_ext w) this s1' s2' /\ s1 = s2).
Proof. by case: w=>W ??? cohE sl sR; apply: sR. Qed.

Definition extends (U V : world) (K : hooks) (w : injects U V K) s s1 := 
  exists s2, [/\ s = s1 \+ s2, s1 \In Coh U & s \In Coh V].

Notation dom_filt W := (fun k => k \in dom W).

(* TODO: prove something about hooks K being irrelevant for coherence *)

(* TODO: remove all irrelevant hooks *)

Definition projectS (W : world) (s : state) :=
  um_filter (dom_filt (getc W)) s.

Lemma projectS_cohL W1 W2 s :
  s \In Coh (W1 \+ W2) -> hook_complete W1 -> projectS W1 s \In Coh W1.
Proof.
case=>V1 V2 G1 D H G2; split=>//; first by move/validL: V1.
- by rewrite valid_umfilt.
- move=>z; case B: (z \in dom (getc W1)).
  + by rewrite dom_umfilt !inE B/= -D/=domUn !inE B/=; case/andP:V1=>->.
  by rewrite dom_umfilt !inE B.
move=>l; move: (H l)=>{H}H.
case B: (l \in dom (getc W1)); last first.
- rewrite /getProtocol /getStatelet; move: (B).
  case: dom_find=>//-> _.
  suff X: ~~(l \in dom (projectS W1 s)) by case: dom_find X=>//-> _. 
  by rewrite /projectS dom_umfilt inE/= B.
have E1: find l s = find l (projectS W1 s).
- by rewrite /projectS/= find_umfilt B.
have E2: getProtocol (W1 \+ W2) l = getProtocol W1 l.
  - rewrite /getProtocol findUnL//?B//.
    by rewrite /valid/= in V1; case/andP: V1.
by rewrite -E2 /getStatelet -E1 in H *.  
Qed.

Lemma projectS_cohR W1 W2 s :
  s \In Coh (W1 \+ W2) -> hook_complete W2 -> projectS W2 s \In Coh W2.
Proof. by rewrite joinC; apply: projectS_cohL. Qed.

Lemma projectSE W1 W2 s :
  s \In Coh (W1 \+ W2) ->
  s = projectS W1 s \+ projectS W2 s.
Proof.
case=>Vw Vs G D H; rewrite /projectS.
have X: {in dom s, dom_filt (getc W2) =1 predD (dom_filt (getc W2)) (dom_filt (getc W1))}.
- move=>z _/=; case I : (z \in dom (W1.1 \+ W2.1)).
  + move: I; rewrite domUn !inE/==>/andP[V']/orP[]Z; rewrite Z/=.
    - by case: validUn V'=>//_ _/(_ z Z)/=G' _;apply/negbTE. 
    rewrite joinC in V'; case: validUn V'=>//_ _/(_ z Z)G' _.
    by rewrite andbC.
  move: I; rewrite domUn inE/==>/negbT; rewrite negb_and negb_or/=.
  have X: valid (W1 \+ W2) by [].
  by case/andP: X=>->/=_/andP[]->.
rewrite (eq_in_umfilt X) -umfilt_predU/=; clear X.
suff X: {in dom s, predU (dom_filt (getc W1)) (dom_filt (getc W2)) =1 predT}.
- by rewrite (eq_in_umfilt X) umfilt_predT. 
by move=>z; rewrite/= -D domUn inE=>/andP[].
Qed.

Lemma coh_split W1 W2 s :
  s \In Coh (W1 \+ W2) ->
  hook_complete W1 -> hook_complete W2 ->
  exists s1 s2 : state,
    [/\ s1 \In Coh W1, s2 \In Coh W2 & s = s1 \+ s2].
Proof.
move=>C G1 G2; move/projectSE: (C)->.
exists (projectS W1 s), (projectS W2 s).
split=>//; [by apply: projectS_cohL C G1| by apply: projectS_cohR C G2].
Qed.

Lemma injExtL' (W1 W2 : world) K (pf : injects W1 (W1 \+ W2) K) :
  valid (W1 \+ W2) -> inj_ext pf \+ (Unit, K) = W2.
Proof.
move=>H; case: pf=>W2' _ E/=_ _ _ _.
rewrite -joinA in E.
case/andP: H=>H1 H2.
rewrite /PCM.join/= in H1 H2 E *.
case: W2 H1 H2 E=>/=c2 h2 H1 H2 [E1 E2].
by rewrite (joinxK H1 E1) (joinxK H2 E2).
Qed.

Lemma injExtR' W1 W2 K (pf : injects W2 (W1 \+ W2) K) :
  valid (W1 \+ W2) -> inj_ext pf \+ (Unit, K) = W1.
Proof.
move=>H; case: pf=>W2' _ E/= _ _ _ _.
rewrite -(joinC W2) in E H.
case/andP: H=>H1 H2; rewrite -joinA in E.
rewrite /PCM.join/= in H1 H2 E *.
case: W1 H1 H2 E=>/=c1 h1 H1 H2 [E1 E2].
by rewrite (joinxK H1 E1) (joinxK H2 E2).
Qed.

Lemma injExtL W1 W2 (pf : injects W1 (W1 \+ W2) Unit) :
  valid (W1 \+ W2) -> inj_ext pf = W2.
Proof. by move/(injExtL' pf); rewrite unitR. Qed.

Lemma injExtR W1 W2 (pf : injects W2 (W1 \+ W2) Unit) :
  valid (W1 \+ W2) -> inj_ext pf  = W1.
Proof. by move/(injExtR' pf); rewrite unitR. Qed.

End Exports.
End Exports.

End Injection.

Export Injection.Exports.

Module InjectExtra.

Lemma cohUnKR U W s s':
  s \+ s' \In Coh (U \+ W) -> s \In Coh U ->
  hook_complete W -> s' \In Coh W.
Proof.
move=>H C G2; move: (cohH C) => G1.
suff X: s' = projectS W (s \+ s').
- by rewrite X; apply: (projectS_cohR H).
suff X: s = projectS U (s \+ s').
- move: (cohS H)=>V; move/projectSE: (H)=>E.
  rewrite E in V.
  rewrite {1}X in E.
  by rewrite (joinxK V (sym_eq E)).
rewrite /projectS.
suff X: {in dom (s \+ s'), dom U.1 =i dom s}.
- by rewrite (eq_in_umfilt X) umfilt_dom ?(cohS H)//.
by move=>z _; move: (cohD C z); rewrite /in_mem.
Qed.

Lemma cohUnKL U W s s':
  s \+ s' \In Coh (U \+ W) -> s' \In Coh W ->
  hook_complete U -> s \In Coh U .
Proof.
by move=>H C G1; rewrite [U \+ W]joinC [s\+_]joinC in H; apply: (cohUnKR H).
Qed.

Lemma getPUn (U W : world) l :
  valid (U \+ W) -> l \in dom U.1 ->
  getProtocol U l = getProtocol (U \+ W) l.
Proof.
move=>V; rewrite /getProtocol=>D.
case/andP: (V)=>V1 V2.
by rewrite findUnL ?V1// D.
Qed.

Lemma getSUn s1 s2 l :
  valid (s1 \+ s2) -> l \in dom s1 ->
  getStatelet s1 l = getStatelet (s1 \+ s2) l.
Proof.
move=>V; rewrite /getStatelet=>D.
by rewrite findUnL ?V// D.
Qed.

Lemma hook_completeL (U : world) K :
  valid (U \+ (Unit, K)) ->
  hook_complete (U \+ (Unit, K)) -> hook_complete U.
Proof.
case: U=>c h=> V H z lc ls st D.
move: (H z lc ls st); rewrite domUn inE/= D/=.
case/andP: V=>_->/==>/(_ is_true_true)=>/andP[].
by rewrite !unitR=>->->.
Qed.

Lemma get_protocol_hooks (U: world) K l:
  valid U -> getProtocol (U \+ (Unit, K)) l = getProtocol U l.
Proof.
move=>V; rewrite /getProtocol.
by rewrite findUnR ?dom0 ?inE//; rewrite unitR; case/andP: V.
Qed.

Lemma coh_hooks (U : world) K s :
  s \In (Coh (U \+ (Unit, K))) -> s \In (Coh U).
Proof.
case=>V Vs Hk D L.
split=>//; first by move/validL: V.
- by apply: hook_completeL V Hk.
- move=>z; rewrite -D domUn !inE/= unitR dom0 orbC/=.
  by move/validL:V=>/andP[]->_.
by move=>l; move: (L l); rewrite (get_protocol_hooks K l (validL V)).
Qed.

Lemma inj_hooks_complete (U W : world) K:
  valid (U \+ W \+ (Unit, K)) ->
  hook_complete U -> hook_complete W ->
  hooks_consistent (U \+ W).1 K ->
  hook_complete (U \+ W \+ (Unit, K)).
Proof.
move=>V G1 G2 G.
move=>z lc ls st; rewrite domUn !inE/= !unitR.
move/andP: (V)=>[_]->/=; case/orP; last by move/G.
rewrite !domUn !inE; case/validL/andP:V=>->->/=.
case/orP; first by case/G1/andP=>->->.
by case/G2/andP=>->->; rewrite -!(orbC true).
Qed.

Lemma inject_step U W K this s1 s2 s1' s2' :
  valid (U \+ W) ->
  s1 \In Coh U -> s2 \In Coh U ->
  hook_complete U -> hook_complete W ->
  network_step (U \+ W \+ (Unit, K)) this (s1 \+ s1') (s2 \+ s2') ->
  network_step U this s1 s2 /\ s1' = s2' \/
  network_step W this s1' s2' /\ s1 = s2.
Proof.
move=>V C1 C2 Hu Hw S; move/step_coh: (S)=>[C1' C2'].
move: (cohW C1')=>V1.
move: (coh_hooks C1')(coh_hooks C2')=>{C1'}C1'{C2'}C2'.
move: (cohUnKR C1' C1 Hw) (cohUnKR C2' C2 Hw)=>D1 D2.
case: S; first 2 last.

(* Receive Step *)
move=>l rt R i from H1.
rewrite domUn inE=>/andP[Vs]/=/orP; case=>D C msg H2 [H3 H4]/=;
[rewrite updUnL D|rewrite updUnR D]=>G;[left|right].
- have X: s1' = s2'.
  + move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1'). 
    move/cohUnKR/(_ D1)/(_ Hu)=>C1''.
    move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
    by rewrite (joinxK (cohS C2') G).
  split=>//; subst s2'; rewrite -![_ \+ s1'](joinC s1') in G C2'.
  rewrite -[upd _ _ _ \+ s1'](joinC s1') in G; rewrite (joinC U) in C2'.
  move: (joinxK (cohS C2') G)=>{G}G. 
  have E: getProtocol U l = getProtocol (U \+ W) l.
    by rewrite (getPUn V)// (cohD C1).
  have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
    by rewrite (getSUn (cohS C1')). 
  rewrite /get_rt /InMem/= in R. 
  move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
  move: (getProtocol (U \+ W \+ (Unit, K)) l)
        (get_protocol_hooks K l V) E rt R H2=>_-><-rt R H2 coh_s H1 G H3 H4.
  apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)). 
  split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s';
  by rewrite -(pf_irr coh_s coh_s').

(* Second part or receive-step *)
move: U W V {V1} Hw Hu s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 rt H1 H2 Vs D C R H3 H4 G.
move=>W U V Hw Hu s1' s2' s1 s2 D1 D2.
rewrite !(joinC W) -!(joinC s1) -!(joinC s2)=> C1' C2' C1 C2.
move=>rt H1 H2 Vs D C R H3 H4 G.
have X: s1' = s2'.
- move: (C2'); rewrite (joinC U) G. 
  move/cohUnKR/(_ D1)/(_ Hw)=>C1''; rewrite (joinC s1') in G.
  move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
  by rewrite (joinxK (cohS C2') G).
split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
rewrite joinC in V.
have E: getProtocol U l = getProtocol (U \+ W) l.
  by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
  by rewrite (getSUn (cohS C1')). 
rewrite /get_rt /InMem/= in R. 
move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
move: (getProtocol (U \+ W \+ (Unit, K)) l)
      (get_protocol_hooks K l V) E rt R H2=>_-><-rt R H2 coh_s H1 G H3 H4.
apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)). 
split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s';
by rewrite -(pf_irr coh_s coh_s').

(* Idle Step *)
- case=>_ E; move: (coh_prec (cohS C1') C1 C2 E)=>Z; subst s2.
  rewrite (joinC U) (joinC s1) in C1'; rewrite !(joinC s1) in E.
  move: (coh_prec (cohS C1') D1 D2 E)=>Z; subst s2'.
  by left; split=>//; apply: Idle.

(* Send Step *)
- move=>l st H1 to msg h H2.
  rewrite domUn inE=>/andP[Vs]/orP; case=> D _ S Hk H3;
  [rewrite updUnL D|rewrite updUnR D]=>G;[left|right];
  [| move: U W V1 Hu Hw V s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 st Hk H1 H2 Vs D S H3 G;
    move=> W U V1 Hw Hu V s1' s2' s1 s2 D1 D2 C1' C2' C1 C2 st Hk H1 H2 Vs D S H3 G;
     rewrite (joinC W) in V C1' C2' st H1 S H3 G H2 Hk;
     rewrite -?(joinC s1) -?(joinC s2) in C1' C2' S G H3 Vs].
  + have X: s1' = s2'.
    - move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1'). 
      move/cohUnKR/(_ D1)/(_ Hu)=>C1''.
      move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
      by rewrite (joinxK (cohS C2') G).
    split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
    rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
    rewrite (joinC s1') in G.
    have E: getProtocol U l = getProtocol (U \+ W) l.
      by rewrite (getPUn V)// (cohD C1).
    have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
      by rewrite (getSUn Vs). 
    rewrite /get_st /InMem in H1.
    move: (getStatelet (s1 \+ s1') l) (E') H2 S H3 G=>_<- H2 S H3 G.
    move: (getProtocol (U \+ W \+ (Unit, K)) l)
     (get_protocol_hooks K l V) E st H1 S H2 H3 G Hk=>_-><- st H1 S H2 H3 G Hk.
    apply: (SendMsg H1 H2 D C1 _ H3 G).

    (* Now proving the obligation about all_hooks_fire *)
    move=>z lc hk F A1 A2.
    apply sym_eq in F.
    move: (Hk z lc hk).
    rewrite -F -joinA !domUn !inE !Vs A1 A2 findUnL ?E' ?(find_some F)/=;
      last by case/andP:V1; rewrite-joinA =>_->.
    move/(_ erefl is_true_true is_true_true).
    by rewrite {1 3}/getStatelet findUnL// A1.

  have X: s1' = s2'.
  - move: (C2'); rewrite (joinC U) G. 
    move/cohUnKR/(_ D1)/(_ Hu)=>C1''; rewrite (joinC s1') in G.
    move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
    by rewrite (joinxK (cohS C2') G).
  split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
  rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
  rewrite (joinC s1') in G.
  have E: getProtocol U l = getProtocol (U \+ W) l.
    by rewrite (getPUn V)// (cohD C1).
  have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
    by rewrite (getSUn Vs). 
  rewrite /get_st /InMem in H1; rewrite (joinC s1') in H2.
    move: (getStatelet (s1 \+ s1') l) (E') H2 S H3 G=>_<- H2 S H3 G.
    move: (getProtocol (U \+ W \+ (Unit, K)) l)
     (get_protocol_hooks K l V) E st H1 S H2 H3 G Hk=>_-><- st H1 S H2 H3 G Hk.
    apply: (SendMsg H1 H2 D C1 _ H3 G).

    (* Now proving the obligation about all_hooks_fire *)
    move=>z lc hk F A1 A2.
    apply sym_eq in F.
    move: (Hk z lc hk).
    rewrite -F -joinA !domUn !inE A1 A2 findUnL ?E' ?(find_some F)/=;
      last by rewrite joinA (joinC U.2); case/andP:V1=>_->.
    rewrite !(joinC s1') !Vs/= -!(orbC true).
    move/(_ erefl is_true_true is_true_true).
    by rewrite {1 3}/getStatelet findUnL// A1.
Qed.

(* The following two definitions are central for framing with respect
to the hooks. In essence. we can add more hooks via the frame rule, if
none of the protocols in the "core" world (i.e., the world, to which
we attach the frame with more hooks) are going to become constrained
by the newly added hooks.

In other words, the new hooks only constrain the world "to be
attached" but not our "core" world. *)

Definition not_hooked_by (K : hooks) l :=
  forall z lc l' st, (z, lc, (l', st)) \in dom K -> l != l'.

Definition world_not_hooked (W: world) K :=
  forall l, l \in dom W.1 -> not_hooked_by K l.

Lemma hooks_frame (U W : world) (K : hooks) l st s s' n msg to :
  hook_complete U -> hook_complete W ->
  hooks_consistent (U \+ W).1 K ->
  l \in dom s -> s \In Coh U -> s \+ s' \In Coh (U \+ W \+ (Unit, K)) ->
  not_hooked_by K l ->        
  all_hooks_fire (geth U) l st s n msg to ->
  all_hooks_fire (geth (U \+ W \+ (Unit, K))) l st (s \+ s') n msg to.
Proof.
move=>G1 G2 G D' C1 C' N A z lc hk F D1 D2; move: F.
case/andP: (cohW C')=>/=V1 V2.
move: (cohUnKR (coh_hooks C') C1 G2) => C2.
rewrite findUnL ?V2//=; case: ifP=>D3; last first.
- move => F; apply sym_eq in F; move: F.
  by move/find_some/N/negP; rewrite eqxx. 
rewrite findUnR ?(validL V2)//; case: ifP=>[D|_].
+ case/G2/andP: D=>_ D; rewrite (cohD C2) in D.
  by case: validUn (cohS C')=>//_ _/(_ _ D'); rewrite D.
move => F.
apply sym_eq in F.
have D'': lc \in dom s by case/andP:(G1 _ _ _ _ (find_some F)); rewrite (cohD C1).
have E: getStatelet s l = getStatelet (s \+ s') l
  by rewrite (getSUn (cohS C'))// -?(cohD C1').
have E': getStatelet s lc = getStatelet (s \+ s') lc.
  by rewrite (getSUn (cohS C'))// -?(cohD C1').
move: (getStatelet (s \+ s') l) (getStatelet (s \+ s') lc) E E'.
by move=>y1 y2 Z1 Z2; subst y1 y2; apply sym_eq in F; apply: (A z).
Qed.

(********************************************************************)
(*                      Framing result                              *)
(********************************************************************)

Lemma inject_frame U W K this s1 s2 s:
  s1 \+ s \In Coh (U \+ W \+ (Unit, K)) ->
  network_step U this s1 s2 ->
  hook_complete U -> hook_complete W ->
  hooks_consistent (U \+ W).1 K ->
  (* State something about hook direction *)
  world_not_hooked U K ->
  network_step (U \+ W \+ (Unit, K)) this (s1 \+ s) (s2 \+ s).
Proof.
move=>C1 S Ku Kw Hk N; move/step_coh: (S)=>[C1' C2'].
case: S; first by move=>[_ <-]; apply: Idle. 

(* Send-transition *)
- move=>l st H1 to msg h H2 H3 _ S A H4 G.
  have E: getProtocol U l = getProtocol (U \+ W \+ (Unit, K)) l.
  have Y: getProtocol U l = getProtocol (U \+ W) l.
    + by rewrite (getPUn (validL (cohW C1)))// (cohD C1').
    rewrite Y; rewrite (getPUn (cohW C1))// domUn inE (cohD C1') H3/=.
    by case/andP: (validL (cohW C1))=>->.
  have E': getStatelet s1 l = getStatelet (s1 \+ s) l.
    by rewrite (getSUn (cohS C1))// -?(cohD C1').
  have X: l \in dom (s1 \+ s) by rewrite domUn inE H3 (cohS C1).
  move: (getProtocol U) (E) H2=>_ -> H2.
  rewrite /get_st /InMem/= in H1.
  rewrite E' in H2 G S H4; clear E'.
  move: (getProtocol U l) E st H1 S H4 G H2 A=>_->st H1 S H4 G H2 A.
  apply: (SendMsg H1 H2 X C1 _ H4 (s2 := s2 \+ s)); last first.
  - by rewrite updUnL H3; congr (_ \+ _).
  by apply: hooks_frame=>//; apply: N; rewrite -(cohD C1') in H3.
 
    
(* Receive-transition *)
move=> l rt H1 msg from H2 H3 C tms G [G1 G2/= G3].
have E: getProtocol U l = getProtocol (U \+ W \+ (Unit, K)) l.
  have Y: getProtocol U l = getProtocol (U \+ W) l.
  - by rewrite (getPUn (validL (cohW C1)))// (cohD C1').
  rewrite Y; rewrite (getPUn (cohW C1))// domUn inE (cohD C1') H3/=.
  by case/andP: (validL (cohW C1))=>->.
have E': getStatelet s1 l = getStatelet (s1 \+ s) l.
  by rewrite (getSUn (cohS C1))// -?(cohD C1').
have X: l \in dom (s1 \+ s) by rewrite domUn inE (cohS C1) H3.
rewrite /get_rt /InMem /= in H1.
move: (getProtocol U l) (getStatelet s1 l) E E' C H2
      (coh_s l C) rt G3 G G2 H1 G1=>z1 z2 Z1 Z2.
subst z1 z2=>C pf C' G3 G G2 H1 H2 G1.
apply: (ReceiveMsg H2 X G2 (i := msg) (from := from) (s2 := s2 \+ s)).
split=>//=; first by rewrite (pf_irr (coh_s l C1) C').
rewrite updUnL H3; congr (_ \+ _); move: (NetworkSem.coh_s l C1)=>pf'. 
by rewrite (pf_irr pf' C').
Qed.


Lemma injectL (U W : world) K :
  valid (U \+ W \+ (Unit, K)) ->
  hook_complete U -> hook_complete W ->
  hooks_consistent (getc (U \+ W)) K ->
  world_not_hooked U K ->
  injects U (U \+ W \+ (Unit, K)) K.
Proof.
move=>H G1 G2 G N.
exists W=>//[s|s1 s2 s this|s1 s2 s1' s2' this]; [split | |].
- move/coh_hooks=>C; exists (projectS U s), (projectS W s).
  split; [by apply projectSE|by apply: (projectS_cohL C)|
          by apply: (projectS_cohR C)].
- case=>s1[s2][Z]C1 C2; subst s.
  have W1 : valid (s1 \+ s2).
  + case: validUn; rewrite ?(cohS C1) ?(cohS C2)//.
    move=>l; rewrite -(cohD C1)-(cohD C2).
    case/validL/andP: H=>H _;
    by case: validUn H=>//_ _/(_ l) G' _/G'; move/negbTE=>->.
  split=>//[||l].
  + by apply: inj_hooks_complete.
  + move=>l; rewrite !domUn !inE !unitR dom0 orbC/=.
    rewrite W1/= -(cohD C1)-(cohD C2) domUn !inE//=.
    by move/validL/andP:H=>[->]_.
  + rewrite (get_protocol_hooks K l (validL H)).
    rewrite /getProtocol/getStatelet !findUnL//; last by case/validL/andP:H.
    by rewrite (cohD C1); case B: (l \in dom s1)=>//; apply: coh_coh.
- by move=>C1 C2; apply: inject_frame. 
by move=>C1 C2; apply: (inject_step (validL H)).
Qed.


Lemma injectR (U W : world) K :
  valid (W \+ U \+ (Unit, K)) ->
  hook_complete U -> hook_complete W ->
  hooks_consistent (getc (U \+ W)) K ->
  world_not_hooked U K ->
  injects U (W \+ U \+ (Unit, K)) K.
Proof. by rewrite (joinC W); apply: injectL. Qed.

Lemma locProjL (W1 W2 : world) l s1 s2:
  (s1 \+ s2) \In Coh (W1 \+ W2) -> l \in dom W1.1 ->
  s1 \In Coh W1 -> getStatelet (s1 \+ s2) l = getStatelet s1 l.
Proof.
move=>C D C1; rewrite (cohD C1) in D.
by rewrite (getSUn (cohS C) D).
Qed.

Lemma locProjR (W1 W2 : world) l s1 s2:
  (s1 \+ s2) \In Coh (W1 \+ W2) -> l \in dom W2.1 ->
  s2 \In Coh W2 -> getStatelet (s1 \+ s2) l = getStatelet s2 l.
Proof. by rewrite !(joinC W1) !(joinC s1); apply: locProjL. Qed.

End InjectExtra.

Export InjectExtra.
