Class SL_Parameter: Type := {
  EM: bool;
  IC: bool;
  WEM: bool;
  SCE: bool;
  ESE: bool;
  ED: bool
}.

Class SA_Parameter: Type := {
  ID: bool;
  NB: bool;
  BJ: bool;
  INCR: bool;
  ISS: bool;
  IJS: bool
}.

Inductive Parameter_coincide (SLP: SL_Parameter) (SAP: SA_Parameter) : Prop :=
  Build_Parameter_coincide:
    EM = ID ->
    IC = NB ->
    WEM = BJ ->
    SCE = INCR ->
    ESE = ISS ->
    ED = IJS ->
    Parameter_coincide SLP SAP.
