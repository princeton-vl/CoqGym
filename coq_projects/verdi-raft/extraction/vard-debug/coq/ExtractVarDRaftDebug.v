Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import VerdiRaft.VarDRaft.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFinInt.

Extraction "extraction/vard-debug/ml/VarDRaftDebug.ml" seq vard_raft_base_params vard_raft_multi_params vard_raft_failure_params.
