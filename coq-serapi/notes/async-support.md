Notes on async support:

## Current flags for async STM support are:

- `async_proofs [= APoff]`: Enable first level (CoqIDE-like) async support.

```ocaml
type async_proofs = APoff | APonLazy | APon
```
  This flag seems to activate the STM async mode. TODO: What does `APonLazy` do?

- `async_proofs_full [= false]`: Enable second level (Coqoon-like) async support.
  Seems unstable for now.

- `async_proofs_never_reopen_branch [= false]`: Disables "branch" editing.

- `async_proofs_worker_id [= "master"]`: Maintains the identity of the
  particular worker. This is a flag given that the identity is set via
  a command line flag.

- Error resilience ( coq/coq#173 ):

```ocaml
let async_proofs_tac_error_resilience = ref (`Only [ "par" ; "curly" ])
let async_proofs_cmd_error_resilience = ref true
```

- Resource control flags:

```ocaml
let async_proofs_n_workers = ref 1
let async_proofs_n_tacworkers = ref 2
```

- More flags:

```ocaml
let async_proofs_delegation_threshold = ref 0.03

type cache = Force
let async_proofs_cache = ref None

let async_proofs_private_flags = ref None

let async_proofs_flags_for_workers = ref []

type priority = Low | High
let async_proofs_worker_priority = ref Low

type tac_error_filter = [ `None | `Only of string list | `All ]
```

## Flags logic:

On `Stm.init ()`, flags are checked to determine what mode to put the
STM on. Queues will be created and workers setup.

```ocaml
let async_proofs_is_worker () = !async_proofs_worker_id <> "master"
let async_proofs_is_master () = !async_proofs_mode = APon && !async_proofs_worker_id = "master"
```
