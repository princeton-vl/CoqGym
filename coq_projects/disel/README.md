# Disel - Distributed Separation Logic

Implementation and case studies of Disel, a separation-style logic for
compositional verification of distributed systems.

This code accompanies the paper entitled **Programming and Proving
with Distributed Protocols** by Ilya Sergey, James R. Wilcox and
Zachary Tatlock, in the POPL 2018 proceedings.

## Building the Project

### Requirements

* [Coq 8.7 or later](https://coq.inria.fr)
* [Mathematical Components 1.6.2 or later](http://math-comp.github.io/math-comp/) (`ssreflect` suffices)
* [FCSL PCM library 1.0.0 or later](https://github.com/imdea-software/fcsl-pcm)
* [OCaml 4.05.0 or later](https://ocaml.org) (to compile and run the extracted applications)

### Building Manually

If Coq is not installed such that its binaries like `coqc` and
`coq_makefile` are in the `PATH`, then the `COQBIN` environment variable
must be set to point to the directory containing such binaries.  For
example:
```
export COQBIN=/home/user/coq/bin/
```

To build the whole project, including examples, simply run `make`
in the root directory of the repository. For a faster build, use
several parallel make jobs, e.g., `make -j 4`.

### Installation via OPAM

The latest release of the framework components of the project may be installed into Coq's
`user-contrib` directory via [OPAM](https://opam.ocaml.org/doc/Install.html)
for easy use in other developments; this will automatically install all
requirements.

Make sure OPAM is installed and use the following commands:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-disel
```

As an alternative, a VM for a previous version has been provided for
your convenience and is described below.

## Project Structure

* `Core` -- Disel implementation, metatheory and inference rules;

* `Examples` -- Case studies implemented in Disel

	- `Calculator` -- the calculator system;

	- `Greeter` -- a toy "Hello World"-like protocol, where
         participants can only exchange greetings with each other;

	- `TwoPhaseCommit` -- Two Phase Commit protocol implementation;

	- `Query` -- querying protocol and its composition with Two Phase
      Commit via hooks;

* `shims` -- DiSeL runtime system

## VM Instructions

Please download
[the virtual machine](http://homes.cs.washington.edu/~jrw12/popl18-disel-artifact.ova),
import it into VirtualBox, and boot the machine. This VM image has been tested with
VirtualBox versions 5.1.24 and 5.1.28 with Oracle VM VirtualBox Extension Pack. Versions
4.X are known not to work with this image.

If prompted for login information, both the username and password are
"popl" (without quotes).

For your convenience, all necessary software, including Coq 8.6 and
ssreflect have been installed, and a checkout of Disel is present in
`~/disel`. Additionally, emacs and Proof General are installed so that
you can browse the sources.

We recommend checking the proofs using the provided Makefile and
running the two extracted applications. Additionally, you might be interested
to compare the definitions and theorems from some parts of the paper to their
formalizations in Coq.

Checking the proofs can be accomplished by opening a terminal and running

    cd ~/disel
    make clean; make -j 4

You may see lots of warnings about notations and "nothing to inject";
these are expected.  Success is indicated by the build terminating
without printing "error".

Extracting and running the example applications is described below.

## Code corresponding to the paper

The following describes how [the paper](http://homes.cs.washington.edu/~jrw12/disel.pdf)
corresponds to the code:

* The Calculator (Section 2)
    - The directory `Examples/Calculator` contains the relevant files.
    - The protocol is defined in `CalculatorProtocol.v`,
      including the state space, coherence predicate, and four transitions
      described in Figure 2. Note that the coherence predicate is stronger than 
      the one given in the paper: it incorporates Inv_1 from Section 2.3. This is
      discussed further below.
    - The program that implements blocking receive of server requests from
      Section 2.2 is defined in `CalculatorServerLib.v`, 
      as `blocking_receive_req`.
    - The simple server from Section 2.3, as well as the batching and memoizing
      servers from Figure 3 are implemented in 
      `SimpleCalculatorServers.v`. They are all implemented in
      terms of the higher-order `server_loop` function. The invariant Inv1 from 
      Section 2.3 is incorporated into the protocol itself, as part of the coherence
      predicate. 
    - The simple client from Section 2.4 is implemented in 
      `CalculatorClientLib.v`. The invariant Inv2 is proved as
      a separate inductive invariant using the WithInv rule in 
      `CalculatorInvariant.v`. It is used to prove the clients
      satisfy their specifications.
    - The delegating server is in `DelegatingCalculatorServer.v`.
      It again uses the invariant Inv2.
    - A runnable example using extraction to OCaml is given in 
      `SimpleCalculatorApp.v`. It consists of one client and two
      servers, one of which delegates to the other. Instructions for how to run
      the example are given below under "Extracting and Running Disel Programs".
* The Logic and its Soundness (Section 3)
    - The definitions from Figure 6 in Section 3.1 are given in `Core/State.v`
      `Core/Protocols.v`, and `Core/Worlds.v`.
    - The primitives of Disel language is defined in `Core/Actions.v`
      (defines send/receive wrappers as in Definitions 3.2 and 3.3).
	- `Core/Process.v`, `Core/Always.v` and `Core/HoareTriples.v`
      define traces, modal predicates (`always` is the formalization
      of post-safety from Definition 3.6). Definition 3.7 from the
      paper corresponds to `has_spec` from `Core/HoareTriples.v`. The
      Theorem 3.8 follows from the soundness of the shallow embedding
      into Coq: any well-typed program has a specification ascribed to it.
    - Inference rules are represented by lemmas named `*_rule` in
      `Core/InferenceRules.v`. For example, `bind_rule` is an
      implementation of `Bind` from Figure 8. 
* Two-Phase Commit and Querying (Section 4)
    - The relevant directory is `Examples/TwoPhaseCommit`.
    - The protocol as described in Section 4.1 is implemented in `TwoPhaseProtocol.v`.
    - The implementations of the coordinator (described in 4.2) and the participant
      are in `TwoPhaseCoordinator.v` and `TwoPhaseParticipant.v`.
    - The strengthened invariant from 4.3 is stated in `TwoPhaseInductiveInv.v` and
      proved to be preserved by all transitions in `TwoPhaseInductiveProof.v`.
    - A runnable example is in `SimpleTPCApp.v`. Instructions for how to run it
      are given below under "Extracting and Running Disel Programs".
    - The querying protocol from Section 4.4 is implemented in the directory
      `Examples/Querying`.

## Exploring further

We encourage you to explore Disel further by extending one of the
examples or trying your own. For example, you could build an application
that uses the calculator to evaluate arithmetic expressions and prove
its correctness. As a more involved example, you could define a new
protocol for leader election in a ring and prove that at most one node
becomes leader. To get started, we recommend following the Calculator example
and modifying it as necessary.

## Extracting and Running Disel Programs

As described in Section 5.1, Disel programs can be extracted to OCaml and run.
You can build the two examples as follows.

- From `~/disel`, run `make CalculatorMain.d.byte` to build the calculator
  application. The extracted code will be placed in `extraction/calculator`.
  (Note that all the proofs will be checked as well.) Then run
  `~/disel/scripts/calculator.sh` to execute the system in three processes
  locally. The system will make several requests to a delegating
  calculator to add up some numbers. (See the definition of `client_input` in
  `Examples/Calculator/SimpleCalculatorApp.v`.) A log of messages from the
  client perspective is printed to the console. Logs of the servers are
  available in the files `server1.log` (the delegating server) and
  `server3.log` (the server that actually computes).

  Each log contains a debugging info about the state of each node and the
  messages it sends and receives. For example, the first message sent by the
  client is logged as

```
sending msg in protocol 1 with tag = 0, contents = [1; 2] to 1
```

  Tag 0 indicates a request in the Calculator protocol. Contents `1; 2`
  indicate the arguments to the function being calculated (in this case,
  addition). The message is sent to node 1, which is the delegating server.

  The client then receives a response logged as

```
got msg in protocol 1 with tag = 1, contents = [3; 1; 2] from 1
```

  Tag 1 indicates a response. The contents mean that the answer to
  `1 + 2` is `3`.

  Several more rounds of messages are exchanged. The final line summarizes
  the entire execution.

```
client got result list [([1; 2], 3); ([3; 4], 7); ([5; 6], 11); ([7; 8], 15); ([9; 10], 19)]
```

- Run `make TPCMain.d.byte` from the root folder to build the
  Two-Phase Commit application. Then run `./scripts/tpc.sh` to
  execute the system in four processes on the local machine.
  The system will achieve consensus on several values. (See
  the definition of `data_seq` in `Examples/TwoPhaseCommit/SimpleTPCApp.v`.)
  Each participant votes on whether to commit the value or abort it.
  (See the definitions of `choice_seq1`, `choice_seq2`, and `choice_seq3`.)
  A log of messages from the coordinator's point of view is printed to the
  console. Participant logs are available in `participant1.log`,
  `participant2.log`, and `participant3.log`.

  The protocol executes a sequence of four rounds, since there are four
  elements in `data_seq`. Each round consists of two phases. The first messages
  sent by the coordinator are prepare messages which request votes about
  the first data item. They are logged as

```
sending msg in protocol 0 with tag = 0, contents = [0; 1; 2] to 1
sending msg in protocol 0 with tag = 0, contents = [0; 1; 2] to 2
sending msg in protocol 0 with tag = 0, contents = [0; 1; 2] to 3
```

  Tag 0 indicates a prepare message. The contents indicate the index of the 
  current request (0, since this is the first data item) and the actual data
  to commit (in this case, `[1; 2]`, as specified in `data_seq`). A separate
  prepare message is sent to each participant.

  The participants respond with votes, which are logged as follows

```
got msg in protocol 0 with tag = 1, contents = [0] from 1
got msg in protocol 0 with tag = 1, contents = [0] from 3
got msg in protocol 0 with tag = 1, contents = [0] from 2
```

  Tag 1 indicates a Yes vote. The messages are ordered nondeterministically
  based on the operating system's and network's scheduling decisions.

  Since all participants voted yes, the coordinator proceeds to commit the
  data by sending Commit messages (tag 3) to all participants.

```
sending msg in protocol 0 with tag = 3, contents = [0] to 1
sending msg in protocol 0 with tag = 3, contents = [0] to 2
sending msg in protocol 0 with tag = 3, contents = [0] to 3
```

  Participants acknowledge the commit with AckCommit messages (tag 5)

```
got msg in protocol 0 with tag = 5, contents = [0] from 3
got msg in protocol 0 with tag = 5, contents = [0] from 1
got msg in protocol 0 with tag = 5, contents = [0] from 2
```

  This completes the first round. The remaining three rounds execute
  similarly, based on the decisions from the choice sequences. When any
  participant votes no (tag 2), the coordinator instead aborts the
  transaction by sending Abort messages (tag 4). In that case, participants
  respond with AckAbort messages (tag 6). Once all four rounds are over,
  all nodes exit.

## Proof Size Statistics

Section 5.2 and Table 1 describe the size of our development. Those
were obtained by using the `coqwc` tool on manually dissected files, 
according to our vision of what should count as a program, spec, or a proof. 
These numbers might slightly differ from reported in the paper due to
the evolution of the project since the submission.
