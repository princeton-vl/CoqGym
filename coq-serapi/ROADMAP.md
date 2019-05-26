### Full document parsing.

- Full asynchronous `Add/Cancel` protocol.
  => Add a cache so users can efficiently send full documents.

### Better Locate

- Implement Locate -> "file name where the object is defined".
- Improve locate [EJGA: how?]
- Help with complex codepaths:
  Load Path parsing and completion code is probably one of the most complex part of company-coq

### Completion / Naming

- Improve the handling of names and environments, see

  `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of
  `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

   Maybe we could add some options `Short`, `Full`, `Best` ? ...
   Or we could even serialize the naming structure and let the ide decide if we export the current open namespace.

### Benchmarking

- add bench option to queries commands
  basically (bench (any list of serapi commands))
  will return BenchData

- Define timing info? Maybe this is best handled at the STM level.

### Misc

- Redo Query API, make Query language a GADT.

- Support regexps in queries.

- Would be easy to get a list of vernacs? Things like `Print`, `Typeclasses eauto`, etc.
  => ppx to enumerate datatypes. Write the help command with this and also Clément suggestions about Vernac enumeration.

- enable an open CoqObject tag for plugin use (see coq/coq#209 ) ?

- Checkstyle support.


