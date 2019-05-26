# Notes on a Coq Protocol for IDEs

These are some notes on the JsCoq Coq Protocol, which IOVH should work
for other IDEs too.

## State of the art:

### Emacs/ProofGeneral

The current interface used by Emacs/ProofGeneral (and possibly other
tools) is a `string -> string` based interface with a bit of extra
information.

This approach is fragile, PG is fully coupled to the printer and
parser, and must do it own printing/parsing of Coq's output.

This design choice also has the the effect to require a new Vernacular
command everytime an IDE needs some functionality, see for instance
coq/coq#64.

A few examples of how the Vernacular situation is are:

```ocaml
type showable =
  | ShowGoal of goal_reference
  | ShowGoalImplicitly of int option
  | ShowProof
  | ShowNode
  | ShowScript
  | ShowExistentials
  | ShowUniverses
  | ShowTree
  | ShowProofNames
  | ShowIntros of bool
  | ShowMatch of lident
  | ShowThesis
```

```ocaml
type printable =
  | PrintTables
  | PrintFullContext
  | PrintSectionContext of reference
  | PrintInspect of int
  | PrintGrammar of string
  | PrintLoadPath of DirPath.t option
  | PrintModules
  | PrintModule of reference
  | PrintModuleType of reference
  | PrintNamespace of DirPath.t
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName of reference or_by_notation
  | PrintGraph
  | PrintClasses
  | PrintTypeClasses
  | PrintInstances of reference or_by_notation
  | PrintLtac of reference
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintCanonicalConversions
  | PrintUniverses of bool * string option
  | PrintHint of reference or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintRewriteHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of reference or_by_notation*int option
  | PrintImplicit of reference or_by_notation
  | PrintAssumptions of bool * bool * reference or_by_notation
  | PrintStrategy of reference or_by_notation option
```

Not much more can be said.

### CoqIDE

CoqIDE has done a significant effort to provide a more structured API
to IDEs. The main entry points for the api are documented at (`interface.ml`)[ide/interface.ml].

Unfolding the types the current API resutls:

```ocaml
type handler = {
  add     : (string * edit_id) * (state_id * verbose)
         -> state_id * ((unit, state_id) union * string);

  edit_at : state_id
         -> (unit, state_id * (state_id * state_id)) union;

  query   : string * state_id
         -> string;

  goals   : unit
         -> goals option;

  evars   : unit
         -> evar list option;

  hints   : unit
         -> (hint list * hint) option;

  status  : bool
         -> status;

  search  : search_flags
         -> string coq_object list;

  get_options : unit
             -> (option_name * option_state) list;

  set_options : (option_name * option_value) list
             -> unit

  mkcases     : string
             -> string list list;

  about       : unit
             -> coq_info;

  stop_worker : string ->
                unit;

  print_ast   : string
             -> Xml_datatype.xml;

  annotate    : string
             -> Xml_datatype.xml;

  handle_exn  : Exninfo.iexn
             -> state_id * location * string;

  init        : string option
             -> state_id;

  quit        : unit
             -> unit;

  (* Retrocompatibility stuff *)
  interp      : (raw * verbose) * string
             -> state_id * (string,string) Util.union;
}
```

This is looking much better! Some comments about the API:

- Serialization of data structures is intertwined in the API. Two
  level serialization happens, first from Coq objects to strings, then
  to XML. This results in duplication.
- Synchronous/asynchronous calling convention is hidden in a different
  layer.
- It doesn't reflect what feedback a call may produce.
- It may be difficult to extend in a compatible way.
- It doesn't support streaming of results.
- It doesn't support per-command options.

Also, how error handling happens is not very clear in general.

## Main design principles for SerAPI:

We want to propose an evolution of the above API suited for use in
(jsCoq)[https://github.com/ejgallego/jscoq/]. The main design mottu
are:

- Separate API from RPC.
- Separate data serialization from API.
- Favor extensibility.
- Remove duplication.
- Be fully asynchronous, support streaming.

This last point is likely the most debatable one; however in principle
any Coq operation can be quite expensive so we think it is a good
approach to have the IDEs assume a full asynchronous operation.

## Identifying the main use cases:

Aside from these foundational principles, we may ask us the somewhat
important question, _what do IDEs need?_

Broadly speaking, IDEs perform 3 kind of operations:

1. Updating the Coq document; this includes adding/editing the document.
2. Searching/querying for objects, "select objects of kind X using criterion Y".
3. Printing/parsing objects.
4. Listening to feedback from the theorem prover.

Other auxiliary operations are needed like option setting, path handling, etc...

## Identifying the communication modes.

For tasks 1 and 3, it seems some synchronicity is needed.
Thus, some form of RPC is needed.

For 2 and 4, IDEs can react in an asynchronous way.
Thus, some form of streaming is needed.

## A First Try:

Let's define two layers:

### Coq Objects:

This includes goals, evars, tactics, constr, etc... We use tags to ensure extensibility.
Object can be generally queried, parsed, and printed. Some examples are:

- tactics
- options
- definitions [== search]
- loadpaths

Plugins can add things here!

```ocaml
type _ coq_object =
 | Constr : constr -> constr coq_object
 | Tactic : tactic -> tactic coq_object
 | Hint   : tactic -> tactic coq_object
 etc...
```

### The STM: Control

STM manipulation primitives are:

+ add
+ edit
+ commit
+ worker_ctrl/ctrl (quit, init)

And we have a set of specific answers:

+ exn?

### Queries: Search

- Allow `Query` to return a diff.
- Allow `Query` to return objects in different forms: uid refs, printed, raw
- Allow `Query` to filter objects.

The filter library should be strongly typed.

```ocaml
type _ query =
  | U : int  -> int    query
  | B : int  -> string query
  | C : unit -> unit   query
```

### Printing/Parsing: Display

+ printer: `object -> string`
+ parser:  `string -> object`


