## What is SerAPI?

Is a library plus a set of "toplevels" aimed to improve the
communication of third party tools with Coq.

## How mature is SerAPI?

SerAPI has _extremely experimental_ status, and there are no protocol
stability guarantees. In fact, the protocol is expected to evolve.

## Which Coq versions does SerAPI support?

At the moment, Coq 8.8 is the current supported version for the
current protocol. Older versions (8.6/8.7) should work however the
protocol will differ. SerAPI is thus only suitable for developers
willing to use up-to-date Coq versions. This will change in the future
once the project stabilizes.

## How can I install SerAPI?

The supported way is to use the OPAM package manager. The
`.travis.yml` file contains up to date install instructions if you
want to build SerAPI manually.

## SerAPI hangs with inputs larger than 4096 characters:

This is due to a historical limitation of the UNIX/Linux TTY API. See
[#38](https://github.com/ejgallego/coq-serapi/issues/38). If you
communicate with SerAPI using a **pipe** this shouldn't be a problem.
Alternatively, you can use the `ReadFile` experimental command.

## Can SerAPI produce `.vo` files?

Not yet, but support for this is planned.

## Can SerAPI evaluate a document incrementally?

Yes, by using Coq's capabilities to that effect. Just issue the proper
`(Cancel ...)` `(Add ... ...)` sequence to simulate an update. This is
limited now to prefix-only incremental evaluation. It will be improved
in the future.

## Does SerAPI support asynchronous proof processing?

Yes, it does. Note however that asynchronous proof processing is still
in experimental status upstream. In particular, there are some issues
on Windows, and `EditAt` may be inconvenient to use. We recommend not
using `EditAt` and instead using the less powerful `Cancel` for now.

## Does SerAPI support Coq's command line flags:

We support only a limited set of `coqtop` command line flags, in
particular `-R` and `-Q` for setting library paths. Unfortunately, due
to our command line parsing library, the format is slightly
different. See `sertop --help` for a comprehensive list of flags.

SerAPI aims to be "command line flag free", with all the options for
each document passed in the document creation call, so this will be
the preferred method.

## What does SerAPI expose?

SerAPI exposes all core Coq datatypes. Tactics, AST, kernel terms and
types are all serialized. SerAPI also provide an API to manipulate and
query "Coq documents".

## How many ASTs does Coq have?

That's a very interesting question! The right answer is: _countably many_!

Logician jokes aside, the truth is that Coq features an _extensible_
AST. While this gives great power to plugins, it means that consumers
of the AST need to design their tools to support an _open_ AST.

Coq's core parsing AST is called `vernac_expr`. This type represents
the so-called "Coq vernaculars". Plugins can extend the "vernacular",
so you should be prepared to handle arbitrary content under the
`VernacExtend` constructor. Such arbitrary content is called in Coq
terminology "generic arguments".

### Interpretation and Terms

After parsing, a term will undergo two elaboration phases before it
will reach "kernel" form. The top-level parsing type for terms is
`constr_expr`, which is then _internalized_ to a `glob_constr`. This
process will perform:

- Name resolution. Example `λ x : nat. x` is resolved to `λ (x: Init.nat), Var 1`
  [using debruijn for bound variables].
- Notation interpretation. For example, `a + b` is desugared to `Nat.add a b`.
- Implicit argument resolution. For example `fst a` is desugared to
  `@fst _ _ a` [note the holes].
- Some desugaring of pattern-matching problems also takes place.

The next step is type inference (called pretyping in Coq, as "typing"
is used for the kernel-level type checking), which will turn a term
in `glob_constr` form into a full-typed `Constr.t` value. `Constr.t`
are the core terms manipulated by Coq's kernel and tactics.

When a _generic argument_ is added to Coq's AST, we must also provide
the corresponding _internalization_ and _pretyping_ functions. To that
purpose, generic arguments have associated 3-levels, `raw`, `glb`, and
`top` which correspond to parsing-level, internalized-level, and
kernel-level.

Thus, a generic argument of type `foo`, may carry 3 different OCaml
types depending on the level the type is. This is used for example to
define the AST of _LTAC_ tactics, where the expression `pose s := foo`
with `foo` initially a `constr_expr` will undergo interpretation and
inference up to a term with a fully elaborated `foo` term.
