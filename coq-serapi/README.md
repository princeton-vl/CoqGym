## The Coq Se(xp)rialized Protocol

[![Build Status](https://travis-ci.org/ejgallego/coq-serapi.svg?branch=v8.8)](https://travis-ci.org/ejgallego/coq-serapi) [![Gitter](https://badges.gitter.im/coq-serapi/Lobby.svg)](https://gitter.im/coq-serapi/Lobby)

```
$ opam install coq-serapi
$ sertop --help
```

SerAPI is a library for machine-to-machine interaction with the [Coq proof assistant](https://github.com/coq/coq),
with particular emphasis on IDE support and code analysis
tools. SerAPI provides automatic serialization of
[Ocaml](https://github.com/ocaml/ocaml) datatypes from/to
S-expressions.

SerAPI is a proof-of-concept and should be considered
alpha-quality. However, it is fully functional and supports, among
other things, asynchronous proof checking, full-document parsing, and
serialization of Coq's core datatypes. SerAPI can also be run as
[WebWorker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
thread, providing a self-contained Coq system inside the
browser. Typical load times in Google Chrome are less than a second.

The main design philosophy of SerAPI is to **make clients life easy**,
trying to provide a convenient, robust interface that hides away most
of the scary details involved in interacting with Coq.

Feedback from Coq users and developers is very welcome and _intrinsic_
to the project. We are open to implementing new features and exploring
new use cases, let us know what you think via the [mailing
list](https://x80.org/cgi-bin/mailman/listinfo/jscoq), the [issue
tracker](https://github.com/ejgallego/coq-serapi/issues), or our
[Gitter chat](https://gitter.im/coq-serapi/Lobby) channel. See also
[SerAPI's FAQ](FAQ.md).

### Roadmap:

SerAPI 0.6.x is based on Coq 8.9. These days, most work related to
SerAPI is directly happening over Coq's upstream itself. The main
objective is to improve the proof-document model; building a rich
query language will be next.

### Quick Overview and Documentation:

SerAPI can be installed as the OPAM package `coq-serapi`. See [build instructions](notes/build.md)
for manual installation. The experimental [in-browser version](https://x80.org/rhino-hawk)
is also online.

The principal entry point in SerAPI is the `sertop` REPL, a basic
toplevel that reads and executes commands (S-Expressions) from stdin
to stdout in both machine or human-friendly format. See `sertop --help`
for an overview of the main options. `Ctrl-C` will interrupt a busy
Coq process in the same way `coqtop` does.

We recommend `rlwrap` or the [emacs mode](sertop.el) for direct
interaction.

## Protocol Description

**API WARNING:** _The protocol is experimental and may change often_.

The canonical documentation for the protocol is the [interface
file](serapi/serapi_protocol.mli) itself; the data types exposed there
are serialized in an automatic way so any change in that file will
imply a change in the actual protocol.

### Coq Objects:

An important part of the SerAPI protocol is the
[`CoqObject`](serapi/serapi_protocol.mli#L22) data type, a _union
type_ that encapsulates most core Coq objects.

### Commands:

Interaction with `sertop` is done using _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are three categories of [commands](serapi/serapi_protocol.mli#L147):

- **Document manipulation:** `Add`, `Cancel`, `Exec`, ...: these commands instruct Coq to perform some action on the current document.
  Every command will produce zero or more different _tagged_ [answers](serapi/serapi_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  SerAPI document commands are an evolution of the OCaml STM API, [here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works. We are working on a more detailed specification, for now you can get some more details in the issue tracker.

- **Queries:** `(Query ((opt value) ...) kind)`:

  Queries stream Coq objects of type `kind`. This can range from options, goals and hypotheses, tactics, etc... The first argument is a list of options: `preds` is a list of conjunctive filters, `limit` specifies how many values the query may return. `pp` controls the output format: `PpSer` for full serialization, or `PpStr` for "pretty printing". For instance:
   ```lisp
   (tag (Query ((preds (Prefix "Debug")) (limit 10) (pp PpSexp)) Option))
   ```
   will stream all Coq options that start with "Debug", limiting to the first 10 and printing the full internal Coq datatype:
   ```lisp
   (CoqOption (Default Goal Selector)
      ((opt_sync true) (opt_depr false) (opt_name "default goal selector")
      (opt_value (StringValue 1))))
   ...
   ```
  Options can be omitted, as in: `(tag (Query ((limit 10)) Option))`, and
  currently supported queries can be seen [here](serapi/serapi_protocol.mli#L118)

- **Printing:** `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers. Its intended use is for printing (maybe IDE manipulated) objects returned by `Query`.

### Quick demo (not always up to date)

```lisp
$ rlwrap sertop --printer=human
(Add () "Lemma addn0 n : n + 0 = n. Proof. now induction n. Qed.")
  > (Answer 0 Ack)
  > (Answer 0 (Added 2 ((fname "") (line_nb 1) (bol_pos 0) (line_nb_last 1) (bol_pos_last 0) (bp 0) (ep 26))
  >            NewTip))
  > ...
  > (Answer 0 (Added 5 ... NewTip))
  > (Answer 0 Completed)

(Exec 5)
  > (Answer 1 Ack)
  > (Feedback ((id 5) (route 0) (contents (ProcessingIn master))))
  > ...
  > (Feedback ((id 5) (route 0) (contents Processed)))
  > (Answer 1 Completed)

(Query ((sid 3)) Goals)
  > (Answer 2 Ack)
  > (Answer 2
  >  (ObjList ((CoqGoal ((fg_goals (((name 5) (ty (App (Ind ...))))
                         (bg_goals ()) (shelved_goals ()) (given_up_goals ()))))))
  > (Answer 2 Completed)

(Query ((sid 3) (pp ((pp_format PpStr)))) Goals)
  > (Answer 3 Ack)
  > (Answer 3 (ObjList ((CoqString
  >   "\
  >    \n  n : nat\
  >    \n============================\
  >    \nn + 0 = n"))))
  > (Answer 3 Completed)

(Query ((sid 4)) Ast)
  > (Answer 4 Ack)
  > (Answer 4 (ObjList ((CoqAst ((((fname "") (line_nb 1) (bol_pos 0) (line_nb_last 1)
  >                                (bol_pos_last 0) (bp 34) (ep 50)))
  > ...
  >            ((Tacexp
  >              (TacAtom
  >                (TacInductionDestruct true false
  > ...
  > (Answer 4 Completed)

(pp_ex (Print () (CoqConstr (App (Rel 0) ((Rel 0))))))
  > (Answer pp_ex Ack)
  > (Answer pp_ex(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))

(Query () (Vernac "Print nat. "))
  > (Answer 6 Ack)
  > (Feedback ((id 5) (route 0) (contents
  >    (Message Notice ()
  >    ((Pp_box (Pp_hovbox 0) ...)
  > (Answer 6 (ObjList ()))
  > (Answer 6 Completed)

(Query () (Definition nat))
  > (Answer 7 Ack)
  > (Answer 7 (ObjList ((CoqMInd (Mutind ....)))))
  > (Answer 7 Completed)
```

### Technical Report

There is a brief technical report with some details at
https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.

## Clients using SerAPI

- [jsCoq](https://github.com/ejgallego/jscoq) allows you run Coq in
  your browser. JsCoq is the predecessor of SerAPI and will be shortly
  fully based on it.
- [elcoq](https://github.com/cpitclaudel/elcoq), an emacs technology
  demo based on SerAPI by [Clément Pit--Claudel](https://github.com/cpitclaudel). `elcoq` is not fully
  functional but illustrates some cool features of SerAPI.
- [peacoq](https://github.com/Ptival/PeaCoq), a Coq IDE for the
  browser has an experimental branch that uses SerAPI.

## Developer information

### Technical details

Coq SerAPI has three main components:

- `serapi`: an extended version of the current IDE protocol,
- `serlib` a library providing automatic de/serialization of most Coq data structures using `ppx_conv_sexp`. This should be eventually incorporated into Coq itself. Support for `ppx_deriving_yojson` is work in progress,
- `sertop`, `sertop_js`, toplevels offering implementation of the protocol.

Building your own toplevels using `serlib` and `serapi` is encouraged.

### Advanced use cases

With a bit more development effort, you can also:

- use SerAPI as an Ocaml library. The low-level serialization library
  [`serlib/`](/serlib) and the higher-level SerAPI protocol in
  [`serapi/serapi_protocol.mli`](/serapi/serapi_protocol.mli) can be
  linked standalone,

- use SerAPI's web worker [JavaScript Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
  from your web/node application. In this model, you communicate with SerAPI using
  the typical `onmessage/postMessage` worker API. Ready-to-use builds
  may be found at
  [here](https://github.com/ejgallego/jscoq-builds/tree/serapi), we
  provide an example REPL at: https://x80.org/rhino-hawk

- we would also like to provide a [Jupyter/IPython kernel](https://github.com/ejgallego/coq-serapi/issues/17).

### Developer/Users Mailing List ###

SerApi development is main discussed in GitHub and in the Gitter
channel. You can lso use the jsCoq mailing list, subscribe at:
https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available at the Gmane group:
`gmane.science.mathematics.logic.coq.jscoq`. You can post to the list
using nntp.
