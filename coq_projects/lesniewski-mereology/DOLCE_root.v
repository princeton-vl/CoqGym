Module Type DOLCE_root.

Require Export Coq.Classes.RelationClasses.
(* The DOLCE core ontology subsumption is hardcoded with coercions
  All concepts are names -> compatibility with mereology *)

Class N : Type.
Class PT.
Class PD.
Class ED.
Class AB.
Class Q.
Class RE.
Class TR.
Class PR.
Class S.
Class TI.
Class TP.
Class NPED.
Class NPOB.
Class SOB.
Class MOB.
Class ASO.
Class NASO.
Class SAG.
Class SC.
Class TQ.
Class PQ.
Class AQ.
Class STV.
Class PRO.
Class PED.
Class POB.
Class NAPO.
Class APO.

Parameter D1  : PT -> N. Coercion D1 : PT >-> N.
Parameter D2  : PD -> PT. Coercion D2 : PD >-> PT.
Parameter D3  : ED -> PT. Coercion D3 : ED >-> PT.
Parameter D4  : AB -> PT. Coercion D4 : AB >-> PT.
Parameter D5  : Q -> PT. Coercion D5 : Q >-> PT.
Parameter D6  : RE -> AB. Coercion D6 : RE >-> AB.
Parameter D7  : TR -> RE. Coercion D7 : TR >-> RE.
Parameter D8  : PR -> RE. Coercion D8 : PR >-> RE.
Parameter D9  : S -> PR. Coercion D9 : S >-> PR.
Parameter D10 : TI -> TR. Coercion D10 : TI >-> TR.
Parameter D11 : TP -> TR. Coercion D11 : TP >-> TR.
Parameter D12 : NPED -> ED. Coercion D12 : NPED >-> ED.
Parameter D13 : NPOB -> NPED. Coercion D13 : NPOB >-> NPED.
Parameter D14 : SOB -> NPOB. Coercion D14 : SOB >-> NPOB.
Parameter D15 : MOB -> NPOB. Coercion D15 : MOB >-> NPOB.
Parameter D16 : ASO -> SOB. Coercion D16 : ASO >-> SOB.
Parameter D17 : NASO -> SOB. Coercion D17 : NASO >-> SOB.
Parameter D18 : SAG -> ASO. Coercion D18 : SAG >-> ASO.
Parameter D19 : SC -> ASO. Coercion D19 : SC >-> ASO.
Parameter D20 : TQ -> Q. Coercion D20 : TQ >-> Q.
Parameter D21 : PQ -> Q. Coercion D21 : PQ >-> Q.
Parameter D22 : AQ -> Q. Coercion D22 : AQ >-> Q.
Parameter D23 : STV -> PD. Coercion D23 : STV >-> PD.
Parameter D24 : PRO -> STV. Coercion D24 : PRO >-> STV.
Parameter D25 : PED -> ED. Coercion D25 : PED >-> ED.
Parameter D26 : POB -> PED. Coercion D26 : POB >-> PED.
Parameter D27 : NAPO -> POB. Coercion D27 : NAPO >-> POB.
Parameter D28 : APO -> POB. Coercion D28 : APO >-> POB.

End DOLCE_root. 

