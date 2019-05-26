(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load "hTerm".
Notation pOO := (pO A n) (only parsing).
Notation canonical1 := (canonical A0 eqA ltM) (only parsing).
Notation ltP1 := (ltP (A:=A) (n:=n) ltM) (only parsing).
Notation poly1 := (poly A0 eqA ltM) (only parsing).

Hint Resolve (ltPO (A:=A) (n:=n) ltM).
Hint Resolve (ltP_hd (A:=A) (n:=n) (ltM:=ltM)).
Hint Resolve (ltP_tl (A:=A) (n:=n) (ltM:=ltM)).
Hint Resolve (canonical0 A A0 eqA n ltM).
Hint Resolve (canonical_cons A A0 eqA n ltM).

