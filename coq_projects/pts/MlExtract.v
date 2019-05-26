Require Extraction.

  Extract Inductive bool => "bool" [ "true" "false" ].
  Extract Inductive sumbool => "bool" [ "true" "false" ].
  Extract Inductive sumor => "option" [ "Some" "None" ].
  Extract Inductive option => "option" [ "Some" "None" ].
