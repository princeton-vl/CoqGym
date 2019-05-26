Require Export bbv.HexNotation.
Require Import bbv.WordScope.

Notation "'Ox' a" := (NToWord _ (hex a)) (at level 50).

Notation "sz ''h' a" := (NToWord sz (hex a)) (at level 50).

Goal 8'h"a" = WO~0~0~0~0~1~0~1~0.
Proof. reflexivity. Qed.

Goal Ox"41" = WO~1~0~0~0~0~0~1.
Proof. reflexivity. Qed.

Notation "sz ''b' a" := (natToWord sz (bin a)) (at level 50).

Notation "''b' a" := (natToWord _ (bin a)) (at level 50).

Goal 'b"00001010" = WO~0~0~0~0~1~0~1~0.
Proof. reflexivity. Qed.

Goal 'b"1000001" = WO~1~0~0~0~0~0~1.
Proof. reflexivity. Qed.


