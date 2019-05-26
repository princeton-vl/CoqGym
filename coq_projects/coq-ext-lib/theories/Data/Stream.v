
Set Implicit Arguments.
Set Strict Implicit.

Section stream.
  Variable T : Type.

  CoInductive stream : Type :=
  | snil : stream
  | scons : T -> stream -> stream.

End stream.

Arguments snil {T}.
Arguments scons {T} _ _.
