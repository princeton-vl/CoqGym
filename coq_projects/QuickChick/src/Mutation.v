From Coq Require Extraction.
From Coq Require Import String.

From SimpleIO Require Import SimpleIO.

(* Simple mutation testing framework for Coq.

   A Gallina expression [a] with a mutant [b] can be written
   as follows:

       a mutant! b        (* anonymous mutant *)
       a mutant: "bug" b  (* explicitly named "bug" *)

   In an interactive session, those expressions both reduce to
   [a] (mutations are ignored).

   Multiple mutants [b1, ..., bn] for the same expression can be
   specified, either anonymous or explicitly named
   ([mutant!] and [mutant: name] are left-associative):

       a mutant! b1 mutant! ... mutant! bn
       a mutant: "firstbug" b1 mutant! b2

   In extracted OCaml code however, those mutations can be
   selected via the environment variable [QC_MUTANT]. *)

(* - If [QC_MUTANT] is empty, the program executes normally,
     without mutations.
   - If [QC_MUTANT=DISCOVERY], the program executes normally,
     but also writes identifiers for reachable mutants into
     a file [./qc-mutants].
   - If [QC_MUTANT=(mutantid)] where [(mutantid)] is one of those
     identifiers, the program executes using that mutation.

   A typical usage is to run the program once with [DISCOVERY]:

       $ QC_MUTANT=DISCOVERY ./MyTestProgram

   Then we can test each mutant using [xargs]:

       $ cat qc-mutants|xargs -I {} -n 1 env QC_MUTANT={} ./MyTestProgram

   Mutants can also be enumerated statically by looking for the
   [__POS__] token in the extracted OCaml source code.

   The script [quickchick-expectfailure] (under [scripts/]) can be used to
   ensure a QuickChick test fails.

       $ cat qc-mutants|xargs -I {} -n 1 env quickchick-expectfailure ./MyTestProgram {}

 *)

(* Sections

   Mutants can be grouped under a common section declared as a
   [Local Instance] of the [section] type class.

       Local Instance this_section : section := "ThisSection"%string.

   Then mutants where that instance is visible will be named as
   [ThisSection:mutant_name] (instead of [:mutant_name] by default).
 *)

(* Gotchas:
   - Definitions should not be simplified using [Eval], since that
     simplifies the mutants away.
   - Mutants should not be nested: in [a mutant! (b mutant! c)],
     [c] will not be discoverable.

   Other issues:
   - [quickChickTool], being text-based, can do a richer set of
     mutations more conveniently:
     + Changing the type of an expression
     + Operations that can't be easily described at the granularity
       of expressions, for example, modifying branches of [match]
       or changing an infix symbol.
 *)

(** * Implementation. *)

Module Magic.

Definition section_name : Type := ocaml_string.
Definition mutation_id : Type := ocaml_string.

Parameter loc : Type.
Parameter HERE : loc.
Parameter serialize_loc : section_name -> loc -> mutation_id.
Parameter serialize_name_ :
  section_name -> ocaml_string -> mutation_id.

Definition serialize_name : section_name -> string -> mutation_id :=
  fun section name => serialize_name_ section (to_ostring name).

Extract Constant loc => "string * int * int * int".

Extract Inlined Constant HERE => "__POS__".

Extract Constant serialize_loc => "fun section (locf,locl,locc,_) ->
     Printf.sprintf ""%s:%s:%d:%d"" section locf locl locc".

Extract Constant serialize_name_ => "fun section name ->
     Printf.sprintf ""%s:%s"" section name".

(* Magically extracted. *)
Definition mutation : mutation_id -> bool := fun _ => false.

Definition mutate : forall a,
    (unit -> a) -> (unit -> a) -> mutation_id -> a :=
  fun _ f g l => if mutation l then g tt else f tt.

(* [Sys.getenv_opt] also exists but only since OCaml 4.05.  *)
Extract Constant mutation =>
  "match try Some (Sys.getenv ""QC_MUTANT"") with Not_found -> None with
   | None -> fun _ -> false
   | Some ""DISCOVERY"" ->
     let mutant_log = open_out ""qc-out/qc-mutants"" in
     let mutants = Hashtbl.create 10 in
     fun mid ->
        begin try ignore (Hashtbl.find mutants mid) with
        | Not_found ->
            Hashtbl.add mutants mid ();
            output_string mutant_log mid;
            output_char mutant_log '\n';
            flush mutant_log
        end; false
   | Some this_mutant ->
     (* print_string this_mutant; *) (* Debugging *)
     fun mid -> mid = this_mutant".

End Magic.

Module Mutant.
Export String.

(* Section *)
Class section : Type := current_section_ : string.

Definition current_section `{section} : ocaml_string :=
  to_ostring current_section_.

Instance default_section : section | 9 := ""%string.

End Mutant.

Notation MAGIC_LOC :=
  (Magic.serialize_loc Mutant.current_section Magic.HERE).

Notation MAGIC_NAME name :=
  (Magic.serialize_name Mutant.current_section name).

Notation "a 'mutant!' b" :=
  (Magic.mutate _ (fun _ => a) (fun _ => b) MAGIC_LOC)
(at level 98, left associativity).

Notation "a 'mutant:' name b" :=
  (Magic.mutate _ (fun _ => a) (fun _ => b) (MAGIC_NAME name))
(at level 98, name at level 0, left associativity).
