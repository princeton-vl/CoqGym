This repository must be built with Coq 8.6.

It requires MathComp (v1.6), and the 8.6 branch of
[metalib](https://github.com/plclub/metalib) to
install.  The former comes from opam, the latter from Github.  For full
installation instructions, see LIBRARIES.md.

To build the Coq, run `make coq`.

This work checks with Coq's native theory -- it includes no Axioms or other
extensions.

Note: sigs.v contains the definition of several Coq module types that allow us
to break the development into multiple pieces. These signatures use the
keyword "Axiom" to specify the expected results of the modules.  All of these
"Axioms" are proved in the development.

    Modules and Sigs:
     ext_wf     : ext_wf_sig
     ext_weak   : ext_weak_sig
     ext_subst  : ext_subst_sig
     ext_invert : ext_invert_sig
     fc_wf      : fc_wf_sig
     fc_weak    : fc_weak_sig
     fc_subst   : fc_subst_sig
     fc_unique  : fc_unique_sig

Libraries (not language specific)
* dep_prog.v     - support for dependently-typed programming in Coq
* fset_facts.v   - lemmas about finite sets
* imports.v      - external libraries (such as ssreflect) and global settings
* tactics.v      - (our own) general purpose tactics & solvers
* utils.v        - auxiliary definitions

Syntactic definitions
* ett.ott        - source definitions in OTT
* ett_ott.v      - Coq definitions from OTT  [generated]
* ett_inf.v      - Coq definitions & lemmas from lngen [generated]
* ett_inf_tc.v   - ett_inf plus typeclasses [not used]
* ett_inf_cs.v   - ett_inf plus canonical structures
* ett_ind.v      - induction scheme, gather_atoms
                   more syntactic infrastructure results



Example concrete signature

* fix_typing.v   - defines toplevel signature to include fixed point operator
* toplevel.v     - properties about the toplevel signatures

Properties about type-agnostic functions and relations:

* beta.v         - lc / subst for beta reduction relation
* ett_par.v      - facts about parallel reduction
* erase_syntax.v - interaction between erasure & syntactic functions
* ett_value.v    - Value/CoercedValue/Path/DataTy


Metatheory of Implicit Language
* ext_wf.v       - well-formedness of judgements, i.e. local closure, ctx wff
                   done, but could use more automation
* ext_context_fv.v - free variables contained in the context
* ext_weak.v     - weakening lemma
* ext_subst.v    - substitution lemma
* ext_invert.v   - inversion lemmas, regularity   G |- a : A => G |- A : *
* ext_red.v      - preservation lemma (reduction_in_one)
* ext_red_one.v  - facts about Values & reduction_in_one
* ext_consist.v  - consistency via confluence & reduction


Metatheory of Explicit Language
* fc_wf.v           - well-formedness of judgements, i.e. local closure, ctx wff
* fc_weak.v         - weakening lemma
* fc_subst.v        - substitution lemma & smart constructors
* fc_head_reduction - weakening/substitution properties of head_reduction relation
* fc_unique.v       - uniqueness of typing
* fc_preservation.v - preservation theorem
* fc_invert.v       - regularity lemmas

Decidability of type checking
* fc_get.v          - function to get the type of a well typed term
* fc_dec_aux.v      - decidability of various relations
                      (tm equality, binds, RhoCheck, beta)
* fc_dec_fuel.v     - recursive structure of typechecking function
* fc_dec_fun.v      - type checking function(s) (including correctness)
* fc_dec.v          - decidability of typing


Connection between languages
* erase.v           - connection between implicit and explicit languages
                      uses canonical structures

Results that depend on annotation/erasure
* fc_consist.v      - progress lemma for fc
* congruence.v      - substitutivity
