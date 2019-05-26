(** * Postscript *)

(** Congratulations: We've made it to the end! *)

(* ################################################################# *)
(** * Looking Back *)

(** We've covered quite a bit of ground so far.  Here's a quick review...  

   - _Functional programming_:
          - "declarative" programming style (recursion over persistent
            data structures, rather than looping over mutable arrays
            or pointer structures)
          - higher-order functions
          - polymorphism *)

(**
     - _Logic_, the mathematical basis for software engineering:

               logic                        calculus
        --------------------   ~   ----------------------------
        software engineering       mechanical/civil engineering


          - inductively defined sets and relations
          - inductive proofs
          - proof objects *)

(**
     - _Coq_, an industrial-strength proof assistant
          - functional core language
          - core tactics
          - automation
*)

(* ################################################################# *)
(** * Looking Forward *)

(** If what you've seen so far has whetted your interest, you have two
    choices for further reading in the _Software Foundations_ series:

           - _Programming Language Foundations_ (volume 2, by a
             similar set of authors to this book) covers material that
             might be found in a graduate course on the theory of
             programming languages, including Hoare logic, operational
             semantics, and type systems.

           - _Verified Functional Algorithms_ (volume 3, by Andrew
             Appel) builds on the themes of functional programming and
             program verification in Coq, addressing a range of topics
             that might be found in a standard data structures course,
             with an eye to formal verification. *)

(* ################################################################# *)
(** * Other sources *)

(** Here are some other good places to learn more...

       - This book includes some optional chapters covering topics
         that you may find useful.  Take a look at the table of contents and the chapter dependency diagram to find
         them.

       - If you're interested in real-world applications of formal
         verification to critical software, see the Postscript chapter
         of _Programming Language Foundations_.

       - Here are some great books on functional programming
            - Learn You a Haskell for Great Good, by Miran Lipovaca
              [Lipovaca 2011].
            - Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart [O'Sullivan 2008]
            - ...and many other excellent books on Haskell, OCaml,
              Scheme, Racket, Scala, F sharp, etc., etc.

       - And some deeper resources for Coq:
           - Verified Functional Algorithms, by Andrew Appel
             [Chlipala 2013].
           - Certified Programming with Dependent Types, by Adam
             Chlipala [Chlipala 2013].
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran [Bertot 2004].
*)

(* $Date: 2017-05-23 13:45:44 -0400 (Tue, 23 May 2017) $ *)
