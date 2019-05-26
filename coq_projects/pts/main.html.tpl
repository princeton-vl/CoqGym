<html>
<TITLE> Type-checking PTS (sources)</TITLE>

<H2> Type-checking PTS (sources)</H2>

<HR>

Since the development is parametric, the parameters are defined in the
main file, which glues together all the others, using Load.

<UL>
<LI><A HREF="Main.html">Main file</A>
</UL>

Theory of PTS with abstract subtyping:
<UL>
<LI><A HREF="Termes.html">Definition of terms and substitution</A>
<LI><A HREF="Env.html">Environments</A>
<LI><A HREF="Subtyping_rule.html">Abstract subtyping rule</A>
<LI><A HREF="PTS_spec.html">Abstract PTS structure</A>
<LI><A HREF="Metatheory.html">Metatheory of PTS</A>
<LI><A HREF="Errors.html">Error messages</A>
<LI><A HREF="Infer.html">Type-checking algorithms</A>
</UL>

First example of subtyping: when the subtyping relation is the
reflexive-symmetric-transitive closure of a reduction rule:

<UL>
<LI><A HREF="Rules.html">Reduction operators</A>
<LI><A HREF="Normal.html">Normal forms and head normal forms</A>
<LI><A HREF="Conv.html">Conversion algorithm</A>
<LI><A HREF="Soundness.html">Subject Reduction property w.r.t the
  reduction operators</A>
</UL>

Second example: the subtyping relation is cumulativity, parameterized
by the inclusion between sorts and a reduction rule:
<UL>
<LI><A HREF="CTS_spec.html">Cumulative PTS structure</A>
<LI><A HREF="Cumul.html">Definition of cumulativity</A>
<LI><A HREF="CumulDec.html">Decidability of cumulativity</A>
<LI><A HREF="CumulInfer.html">Type-checking cumulative PTS</A>
</UL>

Examples of reduction rules: beta and delta

<UL>
<LI><A HREF="Lambda_Rules.html">Definition of beta and delta reductions</A>
<LI><A HREF="LambdaSound.html">Subject Reduction for beta and delta</A>
<LI><A HREF="Confluence.html">Definition of confluence and the
  Tait-Martin-Lof proof</A>
<LI><A HREF="BD.html">Confluence of beta-delta-reduction</A>
<LI><A HREF="Beta.html">Confluence of beta-reduction alone</A>
</UL>

<HR>

Examples of sort inclusion:

<UL>
<LI><A HREF="GenericSort.html">Type of sorts for both V5.10 and V6.2</A>,
<LI><A HREF="SortECC.html">Sorts of Coq V5.10</A>,
<LI><A HREF="SortV6.html">Sorts of Coq V6.2</A>,
<LI><A HREF="ECC.html">Type-checker for Coq V5.10</A>
<LI><A HREF="CoqV6.html">Type-checker for Coq V6.2</A>,
    <A HREF="ExtractV6.html">extraction command</A>
<LI><A HREF="CoqV6Beta.html">Type-checker for Coq V6.2 (no delta)</A>
</UL>

<HR>

Building a standalone proof-checker:

<UL>
<LI><A HREF="kernel.ml">Extracted program</A>
<LI><A HREF="checker.ml">Interface code</A>(hand-written)
</UL>

You can try and run the proof-checker (<A HREF="eccd">bytecode file</A>):

<UL>
<TT>
$ ocamlrun eccd<p>
</TT>
</UL>

<HR>

Library files:
<UL>
<LI><A HREF="MyList.html">Lists</A>
<LI><A HREF="MyRelations.html">Relations</A>
<LI><A HREF="General.html">Misc.</A>
</UL>

<HR>
Coq files compiled on: COMPILDATE<br>
<HR>
COQBANNER
<HR>
</html>
