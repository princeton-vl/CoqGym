# A library of formalised undecidable problems in Coq

This library contains undecidable problems and formalised reductions between them.
Feel free to contribute or start using the problems!

## Existing undecidable problems

- Post correspondence problem (`PCP` in [`Problems/PCP.v`](Problems/PCP.v))
- Halting problem for Turing machines (`Halt` in [`Problems/TM.v`](Problems/TM.v))
- Halting problem for Minsky machines (`MM_HALTING` in [`Problems/MM.v`](Problems/MM.v))
- Halting problem for Binary Stack Machines (`BSM_HALTING` in [`Problems/BSM.v`](Problems/BSM.v))
- Halting problem for the call-by-value lambda-calculus (`eva` in [`Problems/L.v`](Problems/L.v))
- String rewriting (`SR` in [`Problems/SR.v`](Problems/SR.v))
- Entailment in Elementary Intuitionistic Linear Logic (`EILL_PROVABILITY` in [`Problems/ILL.v`](Problems/ILL.v))
- Entailment in Intuitionistic Linear Logic (`ILL_PROVABILITY` in [`Problems/ILL.v`](Problems/ILL.v))
- Provability in Minimal (Intuitionistic, Classical) First-Order Logic (`prv` in [`Problems/FOL.v`](Problems/FOL.v))
- Validity in Minimal (Intuitionistic, Classical) First-Order Logic (`valid` in [`Problems/FOL.v`](Problems/FOL.v), `kvalid` in [`Problems/FOL.v`](Problems/FOL.v))
- Satisfiability in Intuitionistic (Classical) First-Order Logic (`satis` in [`Problems/FOL.v`](Problems/FOL.v), `ksatis` in [`Problems/FOL.v`](Problems/FOL.v))
- Halting problem for FRACTRAN programs (`FRACTRAN_REG_HALTING` in [`Problems/FRACTRAN.v`](Problems/FRACTRAN.v))
- Satisfiability for elementary diophantine constraints (`DIO_ELEM_SAT` 
  in [`Problems/DIOPHANTINE.v`](Problems/DIOPHANTINE.v))
- [Hilbert's 10th problem](https://uds-psl.github.io/H10), i.e. solvability of a single diophantine equation (`H10` in 
  in [`Problems/DIOPHANTINE.v`](Problems/DIOPHANTINE.v))

## How to build

- the subprojects are currently in subdirectories, roughly corresponding to papers or theses covering them
- `make all` builds all subprojects by calling `make all` of the corresponding subproject's makefile
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files and `.html` files
<!---
- the `gh-pages` branch contains a snapshot of the `html` files and this `README` file and is accessible under `uds-psl.github.io/coq-library-undecidability`
-->

## Published work and technical reports

- Hilbert's Tenth Problem in Coq. Dominique Larchey-Wendling and Yannick Forster. Technical report. Subdirectory `H10`. https://uds-psl.github.io/H10
- Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. Subdirectory `ILL`. http://uds-psl.github.io/ill-undecidability/
- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP '19. Subdirectory `FOL`. https://www.ps.uni-saarland.de/extras/fol-undec
- Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic. Yannick Forster and Dominique Larchey-Wendling. LOLA 2018. Subdirectory `ILL`. https://www.ps.uni-saarland.de/~forster/downloads/LOLA-2018-coq-library-undecidability.pdf 
- Verification of PCP-Related Computational Reductions in Coq. Yannick Forster, Edith Heiter, and Gert Smolka. ITP 2018. Subdirectory `PCP`. https://ps.uni-saarland.de/extras/PCP 
- Call-by-Value Lambda Calculus as a Model of Computation in Coq. Yannick Forster and Gert Smolka. Journal of Automated Reasoning (2018) Subdirectory `L`. https://www.ps.uni-saarland.de/extras/L-computability/

## How to contribute

- Fork the project.
- Create a new subdirectory for your project and add your files.
- Add a license for your project.
- Edit the "Existing undecidable problems" and the "Contributors" section in this file
- File a pull request.

## Contributors

- Yannick Forster
- Edith Heiter
- Dominik Kirst 
- Dominique Larchey-Wendling
- Gert Smolka

