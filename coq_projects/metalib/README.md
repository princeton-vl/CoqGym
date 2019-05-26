COMPILATION, INSTALLATION, AND DOCUMENTATION:

  This library requires Coq 8.6, available via [opam](https://opam.ocaml.org/)
  or from the Coq website [https://coq.inria.fr/download].

  To compile the library, cd to the [Metalib](Metalib/) directory:

    `make`          generate Coq makefile, compile Coq files
	  `make html`     generate Coq documentation
	  `make install`  install library on your system (locally)

  Note that both step 1 and 3 are needed in order to be able to run/compile
  the examples and the tutorial. In particular, step 3 only install the
  library in your local Coq setup, and does not require special privileges.

  The main documentation for this library is available as a collection of HTML
  files.

TUTORIAL:

  The metatheory library comes with a tutorial in directory [Stlc](Stlc/).
  Make sure that you've compiled the library first. These tutorial files
  contains an introduction to mechanizing programming language definitions
  with binding in Coq and how to reason about them.

  An additional example of the library is available in the
  [Fsub](Fsub/) directory.

  Those new to Coq should start with Software Foundations, which is an
  introduction to using Coq. The tutorial assumes some familarity with
  this resource.
  (https://softwarefoundations.cis.upenn.edu/current/index.html)
