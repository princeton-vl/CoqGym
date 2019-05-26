Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import CUnit.All.
Require Conversion.

Import ListNotations.
Local Open Scope char.
Local Open Scope N.

Definition s := Conversion.s.

Module Case.
  Require Import Case.

  Definition test_capitalize :
    List.map capitalize [s ""; s "A"; s "aAgZ,3%"] = [s ""; s "A"; s "AAgZ,3%"] :=
    eq_refl.

  Definition test_down_case :
    List.map down_case [s ""; s "aAgZ,3%"] = [s ""; s "aagz,3%"] :=
    eq_refl.

  Definition test_up_case :
    List.map up_case [s ""; s "aAgZ,3%"] = [s ""; s "AAGZ,3%"] :=
    eq_refl.
End Case.

Module Char.
  Require Import Char.

  Definition test_of_N :
    List.map of_N [0; 1; 5; 9; 10; 12; 23] =
      ["0"; "1"; "5"; "9"; "A"; "C" ; "N"] :=
    eq_refl.

  Definition test_to_N :
    List.map to_N ["0"; "1"; "5"; "9"; "A"; "C" ; "N"; "."] =
      [Some 0; Some 1; Some 5; Some 9; Some 10; Some 12; Some 23; None] :=
    eq_refl.

  Definition test_is_ascii :
    List.map is_ascii ["A"; "?"; """"; "010"; "127"; "128"; "255"] =
      [true; true; true; true; true; false; false] :=
      eq_refl.

  Definition test_is_white_space :
    List.map is_white_space [" "; "010"; "r"; ","] =
      [true; true; false; false] :=
      eq_refl.

  Definition test_down_case :
    List.map down_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["a"; "a"; "g"; "z"; ","; """"; "128"; "255"] :=
      eq_refl.

  Definition test_up_case :
    List.map up_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["A"; "A"; "G"; "Z"; ","; """"; "128"; "255"] :=
      eq_refl.
End Char.

Module Comparison.
  (* TODO *)
End Comparison.

Module Conversion.
  Require Import Conversion.

  Definition test_to_string :
    List.map to_string [
      [];
      ["h"; "e"; "l"; "l"; "o"]] = [
      "";
      "hello"] % string :=
    eq_refl.

  Definition test_of_string :
    List.map of_string [
      "";
      "hello"] % string = [
      [];
      ["h"; "e"; "l"; "l"; "o"]] :=
    eq_refl.

  Definition test_of_N :
    List.map_quad of_N [
      (10, 0%nat, None, 0);
      (10, 0%nat, None, 10);

      (2, 10%nat, None, 0);
      (2, 10%nat, None, 1);
      (2, 10%nat, None, 2);
      (2, 10%nat, None, 3);
      (2, 10%nat, None, 12);
      (2, 10%nat, None, 23);

      (8, 10%nat, None, 0);
      (8, 10%nat, None, 1);
      (8, 10%nat, None, 2);
      (8, 10%nat, None, 3);
      (8, 10%nat, None, 12);
      (8, 10%nat, None, 23);

      (10, 10%nat, None, 0);
      (10, 10%nat, None, 1);
      (10, 10%nat, None, 2);
      (10, 10%nat, None, 3);
      (10, 10%nat, None, 12);
      (10, 10%nat, None, 23);

      (16, 10%nat, None, 0);
      (16, 10%nat, None, 1);
      (16, 10%nat, None, 2);
      (16, 10%nat, None, 3);
      (16, 10%nat, None, 12);
      (16, 10%nat, None, 23);

      (2, 3%nat, None, 0);
      (2, 3%nat, None, 1);
      (2, 3%nat, None, 2);
      (2, 3%nat, None, 3);
      (2, 3%nat, None, 12);
      (2, 3%nat, None, 23);

      (10, 0%nat, Some "*", 0);
      (10, 0%nat, Some "*", 10);

      (2, 5%nat, Some "*", 0);
      (2, 5%nat, Some "*", 1);
      (2, 5%nat, Some "*", 2);
      (2, 5%nat, Some "*", 3);
      (2, 5%nat, Some "*", 12);
      (2, 5%nat, Some "*", 23);

      (8, 5%nat, Some "*", 0);
      (8, 5%nat, Some "*", 1);
      (8, 5%nat, Some "*", 2);
      (8, 5%nat, Some "*", 3);
      (8, 5%nat, Some "*", 12);
      (8, 5%nat, Some "*", 23);

      (10, 5%nat, Some "*", 0);
      (10, 5%nat, Some "*", 1);
      (10, 5%nat, Some "*", 2);
      (10, 5%nat, Some "*", 3);
      (10, 5%nat, Some "*", 12);
      (10, 5%nat, Some "*", 23);

      (16, 5%nat, Some "*", 0);
      (16, 5%nat, Some "*", 1);
      (16, 5%nat, Some "*", 2);
      (16, 5%nat, Some "*", 3);
      (16, 5%nat, Some "*", 12);
      (16, 5%nat, Some "*", 23);

      (2, 3%nat, Some "0", 0);
      (2, 3%nat, Some "0", 1);
      (2, 3%nat, Some "0", 2);
      (2, 3%nat, Some "0", 3);
      (2, 3%nat, Some "0", 12);
      (2, 3%nat, Some "0", 23)] = [
      s "";
      s "";

      s "0";
      s "1";
      s "10";
      s "11";
      s "1100";
      s "10111";

      s "0";
      s "1";
      s "2";
      s "3";
      s "14";
      s "27";

      s "0";
      s "1";
      s "2";
      s "3";
      s "12";
      s "23";

      s "0";
      s "1";
      s "2";
      s "3";
      s "C";
      s "17";

      s "0";
      s "1";
      s "10";
      s "11";
      s "100";
      s "111";

      s "";
      s "";

      s "****0";
      s "****1";
      s "***10";
      s "***11";
      s "*1100";
      s "10111";

      s "****0";
      s "****1";
      s "****2";
      s "****3";
      s "***14";
      s "***27";

      s "****0";
      s "****1";
      s "****2";
      s "****3";
      s "***12";
      s "***23";

      s "****0";
      s "****1";
      s "****2";
      s "****3";
      s "****C";
      s "***17";

      s "000";
      s "001";
      s "010";
      s "011";
      s "100";
      s "111"] :=
    eq_refl.

  Definition test_of_Z :
    List.map_triple of_Z [
      (2, 10%nat, 0%Z);
      (2, 10%nat, 1%Z);
      (2, 10%nat, 2%Z);
      (2, 10%nat, (-3)%Z);
      (2, 10%nat, (-12)%Z);
      (2, 10%nat, 23%Z);

      (8, 10%nat, 0%Z);
      (8, 10%nat, 1%Z);
      (8, 10%nat, 2%Z);
      (8, 10%nat, (-3)%Z);
      (8, 10%nat, (-12)%Z);
      (8, 10%nat, 23%Z);

      (10, 10%nat, 0%Z);
      (10, 10%nat, 1%Z);
      (10, 10%nat, 2%Z);
      (10, 10%nat, (-3)%Z);
      (10, 10%nat, (-12)%Z);
      (10, 10%nat, 23%Z);

      (16, 10%nat, 0%Z);
      (16, 10%nat, 1%Z);
      (16, 10%nat, 2%Z);
      (16, 10%nat, (-3)%Z);
      (16, 10%nat, (-12)%Z);
      (16, 10%nat, 23%Z);

      (2, 3%nat, 0%Z);
      (2, 3%nat, 1%Z);
      (2, 3%nat, 2%Z);
      (2, 3%nat, (-3)%Z);
      (2, 3%nat, (-12)%Z);
      (2, 3%nat, 23%Z)] = [
      s "0";
      s "1";
      s "10";
      s "-11";
      s "-1100";
      s "10111";

      s "0";
      s "1";
      s "2";
      s "-3";
      s "-14";
      s "27";

      s "0";
      s "1";
      s "2";
      s "-3";
      s "-12";
      s "23";

      s "0";
      s "1";
      s "2";
      s "-3";
      s "-C";
      s "17";

      s "0";
      s "1";
      s "10";
      s "-11";
      s "-100";
      s "111"] :=
    eq_refl.

  Definition test_to_N :
    List.map_pair to_N [
      (2, s "0");
      (2, s "1");
      (2, s "10");
      (2, s "11");
      (2, s "1100");
      (2, s "10111");

      (8, s "0");
      (8, s "1");
      (8, s "2");
      (8, s "3");
      (8, s "14");
      (8, s "27");

      (10, s "0");
      (10, s "1");
      (10, s "2");
      (10, s "3");
      (10, s "12");
      (10, s "23");

      (16, s "0");
      (16, s "1");
      (16, s "2");
      (16, s "3");
      (16, s "C");
      (16, s "17");

      (2, s "2");
      (8, s "8");
      (10, s "A");
      (16, s "G");
      (10, s "G")] = [
      Some 0; Some 1; Some 2; Some 3; Some 12; Some 23;
      Some 0; Some 1; Some 2; Some 3; Some 12; Some 23;
      Some 0; Some 1; Some 2; Some 3; Some 12; Some 23;
      Some 0; Some 1; Some 2; Some 3; Some 12; Some 23;
      None; None; None; None; None] :=
    eq_refl.
End Conversion.

Module Etc.
  Require Import Etc.

  Definition test_is_ascii :
    List.map is_ascii [s ""; s "ahah"; "128" :: s "ahah"] = [true; true; false] :=
    eq_refl.

  Definition test_is_empty :
    List.map is_empty [s ""; s "aAgZ"] = [true; false] :=
    eq_refl.

  Definition test_repeat :
    List.map_pair repeat [(s "", 0); (s "", 2); (s "ab", 0); (s "ab", 2)] % nat =
      [s ""; s ""; s ""; s "abab"] :=
      eq_refl.

  Definition test_center :
    List.map_pair center [(s "", 4); (s "a", 4); (s "ab", 4); (s "abcd", 4);
      (s "abcde", 4); (s "ab", 0)] % nat = [
      s "    "; s " a  "; s " ab "; s "abcd"; s "abcde"; s "ab"] :=
    eq_refl.

  Definition test_join :
    List.map_pair join [
      (s "", []);
      (s ", ", []);
      (s "", [s "hello"; s "world"]);
      (s ", ", [s "hello"; s "world"])] = [
      s "";
      s "";
      s "helloworld";
      s "hello, world"] :=
    eq_refl.

  Definition test_split :
    List.map_pair split [
      (s "", " ");
      (s "go stop go", " ");
      (s "go stop go ", " ");
      (s "go stop go  ", " ");
      (s "grr", " ")] = [
      [s ""];
      [s "go"; s "stop"; s "go"];
      [s "go"; s "stop"; s "go"; s ""];
      [s "go"; s "stop"; s "go"; s ""; s ""];
      [s "grr"]] :=
    eq_refl.

  Definition test_split_limit :
    List.map_triple split_limit [
      (s "", " ", 2);
      (s "go stop go", " ", 0);
      (s "go stop go ", " ", 3);
      (s "go stop go  ", " ", 1);
      (s "grr", " ", 4)] % nat = [
      [s ""];
      [];
      [s "go"; s "stop"; s "go "];
      [s "go stop go  "];
      [s "grr"]] :=
    eq_refl.

  Definition test_escape_html :
    List.map escape_html [
      s "";
      s "hello";
      s "&";
      s "'""&<>"] = [
      s "";
      s "hello";
      s "&amp;";
      s "&apos;&quot;&amp;&lt;&gt;"] :=
    eq_refl.
End Etc.

Module Trim.
  Require Import Trim.

  Definition test_chomp :
    List.map chomp [s ""; s "aa"; s "aa "; s "aa" ++ ["010"];
      s "aa" ++ ["010"; "013"]; s "aa" ++ ["013"; "010"]] =
      [s ""; s "aa"; s "aa "; s "aa"; s "aa" ++ ["010"]; s "aa"] :=
    eq_refl.

  Definition test_trim_head :
    List.map trim_head [s ""; s "aa"; s "a "; s " aa"; s "  a"; "011" :: s "aa"] =
      [s ""; s "aa"; s "a "; s "aa"; s "a"; s "aa"] :=
    eq_refl.

  Definition test_trim_tail :
    List.map trim_tail [s ""; s "aa"; s "a "; s " aa"; s "a  "; "011" :: s "aa"] =
      [s ""; s "aa"; s "a"; s " aa"; s "a"; "011" :: s "aa"] :=
    eq_refl.

  Definition test_trim :
    List.map trim [s ""; s "aa"; s "a "; s " aa"; s "a  "; "011" :: s "aa"] =
      [s ""; s "aa"; s "a"; s "aa"; s "a"; s "aa"] :=
    eq_refl.
End Trim.