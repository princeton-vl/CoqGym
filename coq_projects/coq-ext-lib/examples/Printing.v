Require Import Coq.Strings.String.
Require Import ExtLib.Structures.MonadWriter.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Programming.Show.

Definition PrinterMonad : Type -> Type :=
  writerT (@show_mon _ ShowScheme_string_compose) ident.

Definition print {T : Type} {ST : Show T} (val : T) : PrinterMonad unit :=
  @MonadWriter.tell _ (@show_mon _ ShowScheme_string_compose) _ _
                    (@show _ ST val _ show_inj (@show_mon _ ShowScheme_string_compose)).

Definition printString (str : string) : PrinterMonad unit :=
  @MonadWriter.tell _ (@show_mon _ ShowScheme_string_compose) _ _
                    (@show_exact str _ show_inj (@show_mon _ ShowScheme_string_compose)).

Definition runPrinter {T : Type} (c : PrinterMonad T) : T * string :=
  let '(ppair val str) := unIdent (runWriterT c) in
  (val, str ""%string).


Eval compute in
    runPrinter (Monad.bind (print 1) (fun _ => print 2)).

Eval compute in
    runPrinter (Monad.bind (print "hello "%string) (fun _ => print 2)).
Eval compute in
    runPrinter (Monad.bind (printString "hello "%string) (fun _ => print 2)).