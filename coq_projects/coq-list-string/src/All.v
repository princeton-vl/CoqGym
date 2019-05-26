Require Case.
Require Comparison.
Require Conversion.
Require Etc.
Require LString.
Require Trim.

Module LString.
  Include ListString.Case.
  Include ListString.Comparison.
  Include ListString.Conversion.
  Include ListString.Etc.
  Include ListString.LString.
  Include ListString.Trim.

  Module Char.
    Require Char.
    Include ListString.Char.
  End Char.
End LString.