(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**

Note: since this file is generated automatically, theorems occur in order of dependency
 of their containing files rather than theorem number.%\newpage%

%\newcommand{\intoc}[1]{\addtocontents{toc}{\protect\contentsline{subsection}{\numberline{}{#1}}{{\hfill\thepage}}} {#1}}
\newcommand{\tocdef}[1]{\addtocontents{toc}{\protect\contentsline{subsection}{\numberline{}{definition: #1}}{{\hfill\thepage}}}}
The table on the next page sums up the most important auxiliary definitions. Throughout, the following is assumed (where applicable):
\begin{verbatim}
    A,D : Setoid;
  B,X,Y : (part_set A);
      C : (part_set B);
      a : A;
      H': X='Y in A
    n,k : nat
      i : (fin n)
      v : (seq n A)
      w : (seq k A)
      H : n=k
\end{verbatim}
This development is based on the book {\bf Linear Algebra}, 2nd edition, by Friedberg,
Insel and Spence, (c)1989, 1979 by Prentice Hall, Inc. ISBN 0-13-536855-3. 
Theorem numbers refer to this book. The file 
Linear\_Algebra\_by\_Friedberg\_Insel\_Spence.v explains in more detail. 

\renewcommand{\leadsto}{\quad\Longrightarrow\quad}
\newcommand{\dr}[3]{~\ \protect{#2} &\pageref{#1}&$#3$ \\}
\begin{tabular}{lcr}
Definition & see page & intended meaning \\
  \hline
\dr{equalsyntax}{='\ \em[in\ A]}{}
\dr{moresyntax}{+',\ rX,\ mX,\ zero,\ one,\ min}{}
\dr{fin}{fin}{(fin\ n) = \{0,\ldots,n-1\}=\Sigma i:nat.i<n}
\dr{seq}{seq}{v:(seq\ n\ A)\leadsto \vec v=(v_0,\ldots,v_{n-1})}
\dr{conseq}{conseq (;;)}{a;;v = (a,v_0,\ldots,v_{n-1})}
\dr{Seqtl}{Seqtl}{(Seqtl\ (v_0,\ldots,v_{n-1})) = (v_1,\ldots,v_{n-1})}
\dr{head}{head}{(head\ v) = v_0}
\dr{hdtl}{hdtl}{(hdtl\ v) = v_0;;(v_1,\ldots,v_{n-1})}
\dr{concat}{concat (++)}{v++w = (v_0,\ldots,v_{n-1},w_0,\ldots,w_{k-1})}
\dr{omit}{omit, etc.}{(omit\ v\ i) = (v_0,\ldots,v_{i-1},v_{i+1},\ldots,v_{n-1})}
\dr{modifyseq}{modify\_seq}{}
\multicolumn{3}{r}{$(modify\_seq\ v\ i\ a) = (v_0,\ldots,v_{i-1},a,v_{i+1},\ldots,v_{n-1})$} \\
\dr{emptyseq}{empty\_seq}{(empty\_seq\ A) = ( )\in A^0}
\dr{constmap}{const\_map, const\_seq}{(const\_map\ A\ (d::D))=\lambda a:A.d}
& & $(const\_seq\ n\ a)=(a,\ldots,a)\in A^n$ \\
\dr{castfin}{cast\_fin, cast\_seq}{(cast\_fin\ i\ H):(fin\ k)}
& & $(cast\_seq\ v\ H):(seq\ k\ A)$ \\
\dr{seqequal}{seq\_equal}{\rm (enable\ writing\ v=w\ even\ if\ n\not\equiv k)}
  \hline
\dr{injectsubsets}{inject\_subsets}{(inject\_subsets\ C):(part\_set\ A)}
\dr{injectsubsetsify}{inject\_subsetsify}{c:C\leadsto}
\multicolumn{3}{r}{$(inject\_subsetsify\ c):(inject\_subsets\ C)$} \\
\dr{uninjectsubsetsify}{uninject\_subsets}{c:(inject\_subsets\ C)\leadsto}
& & $(uninject\_subsetsify\ c):C$ \\
\dr{mapbetweenequalsubsets}{map\_between\_equal\_subsets}{x:X\leadsto}
& & $(map\_between\_equal\_subsets\ H'\ x):Y$ \\
\dr{Maptoequalsubsets}{Map\_to\_equal\_subsets}{v:(Map\ D\ X)\leadsto}
\multicolumn{3}{r}{$(Map\_to\_equal\_subsets\ H\ v):(Map\ D\ Y)$} \\
\dr{castmaptosubset}{cast\_map\_to\_subset}{f:(Map\ D\ A); H'':(\forall i.v_i:B)\leadsto}
\multicolumn{3}{r}{$(cast\_map\_to\_subset\ H''\ f):(Map\ D\ B)$} \\
\dr{Mapembed}{Map\_embed}{f:(Map\ D\ B)\leadsto}
& & $(Map\_embed\ f):(Map\ D\ A)$ \\
  \hline
\dr{Map2}{Map2, etc.}{A\to B\to C{\rm \ for\ setoids}}
\dr{distinct}{distinct}{{\rm tells\ if\ }v_0,\ldots,v_{n-1}{\rm\ are\ all\ distinct}}
\dr{sum}{sum}{(sum\ v)=\sum_i v_i}
\dr{pointwise}{pointwise}{}
\multicolumn{3}{r}{$(pointwise\ \star\ v\ w) = (v_0\ \star\ w_0, \ldots, v_{n-1}\ \star w_{n-1})$} \\
\dr{multbyscalars}{mult\_by\_scalars}{\cong(pointwise\ mX\ a\ v)}
\dr{seqset}{seq\_set}{(seq\_set\ v)=\{v_0,\ldots,v_{n-1}\}::(part\_set\ A)}
\dr{seqsetseq}{seq\_set\_seq}{(seq\_set\_set\ v):(seq\ n\ (seq\_set\ v))}
\dr{isfiniteset}{is\_finite\_{\em[sub]}set}{}
\dr{hasnelements}{has\_n\_elements}{}
\dr{hasatleastnelements}{has\_at\_$\{least|most\}$\_n\_elements}{}
\end{tabular}%
*)
