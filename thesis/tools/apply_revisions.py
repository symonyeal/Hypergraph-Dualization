"""Apply the corrections of thesis/CLAIMS.md to the revised edition's chapters.

Usage (from the repository root): python thesis/tools/apply_revisions.py

Each edit is an exact span that must occur exactly once in the 2024 chapter; the script stops
on the first span that does not. It always reads thesis/2024/chapters and overwrites
thesis/revised/chapters, so it can be re-run.
"""
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "thesis" / "2024" / "chapters"
DST = ROOT / "thesis" / "revised" / "chapters"

EDITS = {
"ch1-introduction.tex": [
(r"""\begin{proposition}
Let $H=(V,E(H))$ be a hypergraph""", r"""\begin{proposition}[\leanref{tr_minimal}]
Let $H=(V,E(H))$ be a hypergraph"""),
(r"""\begin{definition}
The \emph{clique hypergraph} of a graph""", r"""\begin{definition}\label{def:clique}
The \emph{clique hypergraph} of a graph"""),
],
"ch2-background.tex": [
(r"\begin{lemma}\label{lem:partition}", r"\begin{lemma}[\leanref{eq_tr_iff_partition}]\label{lem:partition}"),
(r"""\begin{corollary}
Let $G$ and $H$ be two Sperner hypergraphs on the same vertex set $V$. Then $H=\Tr(G)$ if and only if $G=\Tr(H)$.""",
 r"""\begin{corollary}[\leanref{eq_tr_comm}]
Let $G$ and $H$ be two Sperner hypergraphs on the same vertex set $V$. Then $H=\Tr(G)$ if and only if $G=\Tr(H)$."""),
(r"""\begin{corollary}
Let $H$ be a Sperner hypergraph. Then $\Tr(\Tr(H))=H$.
\end{corollary}""",
 r"""\begin{corollary}[\leanref{tr_tr_of_sperner}]
Let $H$ be a Sperner hypergraph. Then $\Tr(\Tr(H))=H$. For an arbitrary hypergraph, $\Tr(\Tr(H))=min(H)$ \leanref{tr_tr}.
\end{corollary}"""),
(r"\cite{FK96-missing}", r"\cite{FK96}"),
(r"\begin{proposition}\label{prop:intersect}", r"\begin{proposition}[\leanref{edges_meet}]\label{prop:intersect}"),
(r"\begin{proposition}\label{prop:support}", r"\begin{proposition}[\leanref{support_eq}]\label{prop:support}"),
(r"\begin{proposition}\label{prop:size}", r"\begin{proposition}[\leanref{card_le_card_tr}]\label{prop:size}"),
(r"\begin{proposition}\label{prop:sum}", r"\begin{proposition}[\leanref{kraft_sum}]\label{prop:sum}"),
(r"""\begin{corollary}\label{cor:shortest}
Let $G$ and $H$ be mutually transversal hypergraphs, where $n=|G|+|H|$, and let $s=\min\{|e_l|:e_l\in E(G)\cup E(H)\}$ represent the length of the shortest hyperedge. Then:
\[
s\geq\log n,\quad\text{since }n\cdot 2^{-s}=(|G|+|H|)\cdot 2^{-s}\geq 1.
\]
\end{corollary}
\noindent\textit{\cite{FK96}}""",
 r"""\begin{corollary}[\leanref{two_pow_shortest_le}]\label{cor:shortest}
Let $G$ and $H$ be mutually transversal hypergraphs, where $n=|G|+|H|$, and let $s=\min\{|e_l|:e_l\in E(G)\cup E(H)\}$ represent the length of the shortest hyperedge. Then:
\[
s\leq\log_2 n,\quad\text{since }1\leq\sum_{e\in E(G)}2^{-|e|}+\sum_{e\in E(H)}2^{-|e|}\leq n\cdot 2^{-s}.
\]
\end{corollary}
\noindent\textit{\cite{FK96}.} The 2024 edition printed $s\geq\log n$. The inequality is reversed: for $G=H=K_3$, $s=2<\log_2 6$ \leanref{k3_refutes_printed_cor_2_3_1}."""),
(r"\begin{lemma}\label{lem:frequency}", r"\begin{lemma}[\leanref{exists_frequent_vertex}]\label{lem:frequency}"),
],
"ch3-symmetry.tex": [
(r"""\begin{claim}
The vertex sets of the subhypergraphs of $H$ under the automorphism group $\mathcal{G}=\Aut(H)$ are precisely the orbits of the action of $\mathcal{G}$ on $V$. \cite{Lec}
\end{claim}""",
 r"""\begin{claim}[\leanref{invariant_eq_union_orbits}, \leanref{orbit_minimal}]
The vertex sets of the subhypergraphs of $H$ invariant under the automorphism group $\mathcal{G}=\Aut(H)$ are precisely the unions of orbits of the action of $\mathcal{G}$ on $V$, and the orbits are exactly the minimal nonempty ones. \cite{Lec}
\end{claim}

The 2024 edition stated that the invariant vertex sets are precisely the orbits. A union of two orbits is invariant and is not an orbit: for $St_2$ the whole vertex set is invariant, while $v_1$ is fixed by every automorphism \leanref{claim_3_1_6_counterexample}."""),
(r"""Therefore, each orbit under $\mathcal{G}$ corresponds to a subhypergraph of $H$, and any subhypergraph is a union of orbits. Thus, the vertex sets of the subhypergraphs of $H$ are precisely the orbits of the action of $\mathcal{G}$ on $V$.""",
 r"""Therefore, each orbit under $\mathcal{G}$ corresponds to a subhypergraph of $H$, and any invariant vertex set is a union of orbits. A nonempty invariant set contained in an orbit $O(v_i)$ contains some $\sigma(v_i)$, hence all of $O(v_i)$, so the orbits are the minimal nonempty invariant sets."""),
(r"""P_{n_3}:\{\{v_2,v_1\}\},\{\{v_3,v_1\},\{v_4,v_1\},\{v_3,v_4\}\},\{\{v_1,v_3\},\{v_1,v_4\},\{v_4,v_3,v_2\}\},\\[4pt]
\overline{P_{n_3}}:\{\{v_3,v_2\},\{v_4,v_3\},\{v_1\}\},\{\{v_1,v_2\},\{v_1,v_3,v_4\}\},\\[4pt]
P_4:\{\{v_1,v_3\},\{v_2,v_3\},\{v_2,v_4\},\{v_1,v_2\}\},\{\{v_1,v_2\},\{v_2,v_3\},\{v_3,v_4\}\}.""",
 r"""P_{n_3}:\{\{v_1,v_2\},\{v_1,v_3\},\{v_1,v_4\},\{v_3,v_4\}\},\{\{v_1,v_3\},\{v_1,v_4\},\{v_2,v_3,v_4\}\},\\[4pt]
\overline{P_{n_3}}:\{\{v_1\},\{v_2,v_3\},\{v_2,v_4\}\},\{\{v_1,v_2\},\{v_1,v_3,v_4\}\},\\[4pt]
P_4:\{\{v_1,v_2\},\{v_2,v_3\},\{v_3,v_4\}\},\{\{v_1,v_3\},\{v_2,v_3\},\{v_2,v_4\}\}."""),
(r"""\end{gather*}

The group $S_2$ represents""", r"""\end{gather*}
The transversals are verified in Lean (\leanref{pn3_tr}, \leanref{pn3bar_tr}, \leanref{p4_tr}). The 2024 edition printed $P_{n_3}$ as three families, $\overline{P_{n_3}}$ with the labels of $v_2$ and $v_3$ exchanged, and the $P_4$ pair with an extra edge; none of those printed pairs is a transversal pair (\leanref{pn3bar_printed_not_tr}, \leanref{p4_printed_not_tr}).

The group $S_2$ represents"""),
(r"with a maximum depth of 3.", r"with at most three levels, i.e.\ height 2 \leanref{max_tree_four}."),
(r"""Since $S_1\times S_2\cong S_2$""", r"""Since $S_1\times S_2\cong S_2$"""),
(r"""In general $\Aut(D_{m,1})\cong S_m\times S_{n-m}$ (for $m<n$).""",
 r"""In general $\Aut(D_{m,1})\cong S_m\times S_{n-m}$ (for $m<n$) \leanref{young_aut_singletons}."""),
(r"""In $\overline{Pn_3}$, the frequencies of $v_1,v_2,v_3$, and $v_4$ are $1$, $\frac{2}{3}$, $\frac{1}{2}$, and $\frac{1}{2}$, respectively.""",
 r"""In $\overline{Pn_3}$, the frequencies of $v_1,v_2,v_3$, and $v_4$ are $1$, $\frac{2}{3}$, $\frac{1}{2}$, and $\frac{1}{2}$, respectively \leanref{pn3bar_freq}."""),
(r"""Lastly, in $Pn_3$, $v_1,v_4$, and $v_3$ are frequent (as defined by \FKA{} preconditions) with frequency $\frac{2}{3}$, while""",
 r"""Lastly, in $Pn_3$, $v_1$ is the most frequent vertex, with frequency $\frac{3}{4}$, and $v_4$ and $v_3$ are frequent with frequency $\frac{2}{3}$ \leanref{pn3_freq}, while"""),
(r"""K_3^{\cdot}:\{\{v_2\},\{v_1,v_3\},\{v_2,v_4\},\{v_3,v_4\}\},\{\{v_1,v_2,v_3,v_4\}\}.""",
 r"""K_3^{\cdot}:\{\{v_2\},\{v_1,v_3\},\{v_1,v_4\},\{v_3,v_4\}\},\{\{v_1,v_2,v_3\},\{v_1,v_2,v_4\},\{v_2,v_3,v_4\}\}."""),
(r"""also have $S_3$ as their automorphism group.""",
 r"""also have $S_3$ as their automorphism group (\leanref{table_aut}; transversals \leanref{st3_tr}, \leanref{hw3_tr}, \leanref{k3dot_tr}). The 2024 edition printed $K_3^{\cdot}$ with the edge $\{v_2,v_4\}$, which is not Sperner, and with transversal $\{\{v_1,v_2,v_3,v_4\}\}$ \leanref{k3dot_printed_not_sperner}."""),
(r"""K_4^-:\{\{v_3,v_4\},\{v_1,v_4\},\{v_1,v_3\},\{v_2,v_4\},\{v_2,v_3\}\},\{\{v_1,v_2,v_3,v_4\},\{v_1,v_2,v_4\},\{v_1,v_3,v_4\}\},""",
 r"""K_4^-:\{\{v_3,v_4\},\{v_1,v_4\},\{v_1,v_3\},\{v_2,v_4\},\{v_2,v_3\}\},\{\{v_1,v_2,v_3\},\{v_1,v_2,v_4\},\{v_3,v_4\}\},"""),
(r"""K_2^{\cdot\cdot}:\{\{v_1,v_2\},\{v_3,v_4\}\},\{\{v_1,v_2\},\{v_3,v_4\}\}.""",
 r"""K_2^{\cdot\cdot}:\{\{v_1\},\{v_2\},\{v_3,v_4\}\},\{\{v_1,v_2,v_3\},\{v_1,v_2,v_4\}\}."""),
(r"""i.e., we can either permute $(v_1,v_2)$ or $(v_3,v_4)$ or both.""",
 r"""i.e., we can either permute $(v_1,v_2)$ or $(v_3,v_4)$ or both (\leanref{k4minus_tr}, \leanref{k2dd_tr}). The 2024 edition printed the transversal of $K_4^-$ as $\{\{v_1,v_2,v_3,v_4\},\{v_1,v_2,v_4\},\{v_1,v_3,v_4\}\}$ and $K_2^{\cdot\cdot}$ as the self-paired $\{\{v_1,v_2\},\{v_3,v_4\}\}$; neither is a transversal pair (\leanref{k4minus_printed_not_tr}, \leanref{k2dd_printed_not_tr})."""),
(r"""Interestingly, in this case, choosing the vertex with the highest frequency is not optimal in terms of tree size.""",
 r"""Interestingly, in this case, choosing the vertex with the highest frequency is not optimal in terms of tree size \leanref{k2dd_mfv_not_optimal}."""),
(r"""The cycle graph $C_4:\{\{v_1,v_3\},\{v_2,v_3\},\{v_2,v_4\},\{v_1,v_2\}\},\{\{v_1,v_2\},\{v_2,v_3\},\{v_3,v_4\}\}$""",
 r"""The cycle graph $C_4:\{\{v_1,v_2\},\{v_2,v_3\},\{v_3,v_4\},\{v_1,v_4\}\},\{\{v_1,v_3\},\{v_2,v_4\}\}$ \leanref{c4_tr}"""),
(r"""K_4:\{\{v_1,v_2\},\{v_2,v_3\},\{v_2,v_4\},\{v_1,v_3\},\{v_3,v_4\},\{v_1,v_4\}\},\{\{v_1,v_2,v_3,v_4\},\{v_1,v_2,v_4,v_3\},\{v_1,v_3,v_2,v_4\}\}.""",
 r"""K_4:\{\{v_1,v_2\},\{v_2,v_3\},\{v_2,v_4\},\{v_1,v_3\},\{v_3,v_4\},\{v_1,v_4\}\},\{\{v_1,v_2,v_3\},\{v_1,v_2,v_4\},\{v_1,v_3,v_4\},\{v_2,v_3,v_4\}\}."""),
(r"""Altogether, up to 4 vertices, there are 13 pairs of distinct hypergraphs, for a total of 30 equivalence classes i.e. distinct hypergraphs under permutation (see Table 3.1). There are in total 168 distinct hypergraphs on 4 vertices (see Table 3.2),""",
 r"""Altogether, on 4 vertices there are 30 equivalence classes, i.e.\ distinct hypergraphs under permutation (see Table 3.1) \leanref{classes_four}: 4 self-transversal classes and 13 pairs of classes $\{G,\Tr(G)\}$ with $G\not\cong\Tr(G)$ \leanref{self_dual_classes_four}. There are in total 168 distinct hypergraphs on 4 vertices (see Table 3.2) \leanref{sperner_four_card},"""),
(r"""\caption{Hypergraphs grouped by their automorphism groups.}""",
 r"""\caption{Hypergraphs grouped by their automorphism groups (\leanref{table_aut}, \leanref{table_orbits}).}"""),
(r"""\begin{lemma}\label{lem:aut-tr}
Suppose $\Aut(H)=\mathcal{G}$ for a hypergraph $H$ and its transversal hypergraph is denoted $\Tr(H)$. Then $\Aut(\Tr(H))\cong\mathcal{G}$.
\end{lemma}""",
 r"""\begin{lemma}[\leanref{aut_tr_of_sperner}]\label{lem:aut-tr}
Suppose $\Aut(H)=\mathcal{G}$ for a Sperner hypergraph $H$ and its transversal hypergraph is denoted $\Tr(H)$. Then $\Aut(\Tr(H))=\mathcal{G}$. For an arbitrary hypergraph, $\Aut(\Tr(H))=\Aut(min(H))$ \leanref{aut_tr_eq_aut_minimal}.
\end{lemma}

The Sperner hypergraph is needed: for $H=\{\{v_1\},\{v_1,v_2\}\}$ on three vertices, $(v_2\,v_3)$ is an automorphism of $\Tr(H)=\{\{v_1\}\}$ but not of $H$ \leanref{lemma_3_3_1_needs_sperner}."""),
(r"""A similar argument applies if $\phi\in\mathcal{G}'$ but $\phi\notin\mathcal{G}$. Hence, $\mathcal{G}=\mathcal{G}'$.""",
 r"""If $\phi\in\mathcal{G}'$, the same argument applied to $\Tr(H)$ gives $\phi\in\Aut(\Tr(\Tr(H)))$, and $\Tr(\Tr(H))=H$ because $H$ is Sperner (Corollary 2.1.3). Hence, $\mathcal{G}=\mathcal{G}'$."""),
(r"""\begin{lemma}\label{lem:break}
In \FKA, the recursive decomposition on the most frequent vertex $v_i$ eliminates all symmetries associated with $v_i$ in the hypergraphs $H$ and $\Tr(H)$ by ensuring that any automorphism generators including $v_i$ are removed. As a result, all nontrivial automorphism generators that include $v_i$ are removed.
\end{lemma}""",
 r"""\begin{lemma}[\leanref{aut_child_moves_split_to_isolated}, \leanref{stab_mem_aut_del}, \leanref{stab_mem_aut_con}]\label{lem:break}
Let \FKA{} split a pair on the vertex $v_i$. In both subproblems, before and after Sperner reduction, $v_i$ lies in no hyperedge, so an automorphism of a subproblem can move $v_i$ only to a vertex that also lies in no hyperedge of that subproblem. Every automorphism of the parent that fixes $v_i$ is an automorphism of both subproblems.
\end{lemma}

The 2024 edition stated this lemma informally, as the elimination of all automorphism generators containing $v_i$. The statement above is what holds; its proof replaces the one below, which is kept as printed for the record."""),
(r"""\begin{lemma}\label{lem:independent}
Let $H$ and $\Tr(H)$ be transversal hypergraphs with vertex set $V$.""",
 r"""The 2024 edition followed with a lemma asserting that symmetries independent of $v_i$ survive the split. It is false:

\begin{example}[\leanref{lemma_3_3_3_false}]
Let $G=\{\{v_1,v_3\},\{v_2,v_4\}\}$. Then $(v_1\,v_2)(v_3\,v_4)\in\Aut(G)$, and \FKA{} splits on $v_1$. The transposition $(v_3\,v_4)$ belongs to a different cycle of this automorphism than $v_1$, yet it is an automorphism of neither subproblem, before or after Sperner reduction.
\end{example}

For the record, the printed lemma read:

\begin{lemma}[false; see the example above]\label{lem:independent}
Let $H$ and $\Tr(H)$ be transversal hypergraphs with vertex set $V$."""),
(r"""\begin{corollary}\label{cor:aut-min}
Let $min(H)$ be the Sperner reduced hypergraph of $H$ (\ref{def:sperner-reduction}). Then $\Aut(H)\cong\Aut(min(H))$.
\end{corollary}""",
 r"""\begin{corollary}[\leanref{aut_le_aut_minimal}]\label{cor:aut-min}
Let $min(H)$ be the Sperner reduced hypergraph of $H$. Then $\Aut(H)\le\Aut(min(H))$.
\end{corollary}

The 2024 edition claimed $\Aut(H)\cong\Aut(min(H))$. For $H=\{\{v_1\},\{v_1,v_2\}\}$ on three vertices, $|\Aut(H)|=1$ and $|\Aut(min(H))|=2$ \leanref{cor_3_3_4_not_iso}. The first paragraph of the proof below is correct; the second is not, because a superset of an edge need not be an edge."""),
(r"\ref{def:clique-missing}", r"\ref{def:clique}"),
(r"""Consider the automorphism $\alpha\in\Aut(G(H))$ defined as:
\[
\alpha(v_1)=v_3,\quad\alpha(v_2)=v_2,\quad\alpha(v_3)=v_1,\quad\alpha(v_4)=v_4.
\]

This permutation preserves adjacency in $G(H)$ but maps the hyperedges of $H$ as:
\[
\alpha(e_1)=\{v_3,v_2,v_1\},\quad\alpha(e_2)=\{v_2,v_4\},\quad\alpha(e_3)=\{v_1,v_4\}.
\]""",
 r"""Consider the automorphism $\alpha\in\Aut(G(H))$ defined as:
\[
\alpha(v_1)=v_4,\quad\alpha(v_2)=v_2,\quad\alpha(v_3)=v_3,\quad\alpha(v_4)=v_1.
\]

This permutation preserves adjacency in $G(H)$ but maps the hyperedges of $H$ as:
\[
\alpha(e_1)=\{v_4,v_2,v_3\},\quad\alpha(e_2)=\{v_2,v_1\},\quad\alpha(e_3)=\{v_3,v_1\}.
\]
The 2024 edition used $\alpha=(v_1\,v_3)$, which is not an automorphism of $G(H)$: it sends the edge $\{v_3,v_4\}$ to the non-edge $\{v_1,v_4\}$ \leanref{ex34_corrected}."""),
(r"""\begin{observation}
The \FKA{} recursive decomposition method induces a minor map between the primal graph of input hypergraphs and their induced subhypergraphs.
\end{observation}""",
 r"""\begin{observation}[\leanref{primal_children_le}]
Let \FKA{} split the pair $(C,D)$ on $v$. The primal graph of each subproblem, after Sperner reduction, is a subgraph of $G(C)-v$ or of $G(D)-v$. It is therefore a minor of the parent's primal graph, obtained by deleting $v$ and edges only.
\end{observation}"""),
],
"ch4-hard-classes.tex": [
(r"""|E_0|=1,\quad|E_i|=\begin{cases}2\times|E_{i-1}|&\text{if }i\text{ is odd,}\\|E_{i-1}|^2&\text{if }i\text{ is even,}\end{cases}\qquad|E_i|=2^{2^{(i/2)-1}}\text{ for even }i.""",
 r"""|E_0|=1,\quad|E_i|=\begin{cases}|E_{i-1}|^2&\text{if }i\text{ is odd,}\\2\times|E_{i-1}|&\text{if }i\text{ is even,}\end{cases}\qquad|E_i|=2^{2^{i/2}-1}\text{ for even }i."""),
(r"""|E_0'|=1,\quad|E_i'|=\begin{cases}|E_{i-1}'|^2&\text{if }i\text{ is odd,}\\2\times|E_{i-1}'|&\text{if }i\text{ is even,}\end{cases}\qquad|E_i'|=2^{(i/2)-1}\text{ for even }i.
\]""",
 r"""|E_0'|=1,\quad|E_i'|=\begin{cases}2\times|E_{i-1}'|&\text{if }i\text{ is odd,}\\|E_{i-1}'|^2&\text{if }i\text{ is even,}\end{cases}\qquad|E_i'|=2^{2^{i/2+1}-2}\text{ for even }i.
\]
These are \leanref{card_alt_succ}, \leanref{card_coalt_succ} and \leanref{alt_counts}. The 2024 edition printed the two cases of each recurrence exchanged \leanref{printed_recurrence_fails} and the closed forms $2^{2^{(i/2)-1}}$ and $2^{(i/2)-1}$, which fail at $i=4$."""),
(r"""$|E(f_1)|=2,|E(f_2)|=2^2,\dots,|E(f_{k+1})|=2\cdot|E(f_k)|^2$. This leads to, $|(f_k)|=2^{2^k-1}$ for $k=1,2,\dots$.""",
 r"""$|E(f_1)|=2,|E(f_2)|=2^3,\dots,|E(f_{k+1})|=2\cdot|E(f_k)|^2$. This leads to, $|(f_k)|=2^{2^k-1}$ for $k=1,2,\dots$ \leanref{alt_counts}."""),
(r"""we get that $\epsilon_k=2^{-k}$.""", r"""we get that $\epsilon_k=2^{-k}$ \leanref{alt_shape}."""),
(r"""|E(g_{k+1})|=(2\cdot|E(f_k)|)^2""", r"""|E(g_{k+1})|=(2\cdot|E(g_k)|)^2"""),
(r"""we get $\epsilon(S_i)=2^{-i}$.""", r"""we get $\epsilon(S_i)=2^{-i}$ \leanref{alt_shape}."""),
(r"""Cographs and chordal graphs belong to the class of distance-hereditary graphs.""",
 r"""Cographs belong to the class of distance-hereditary graphs. (The 2024 edition included chordal graphs; the gem, a path $v_1v_2v_3v_4$ with a fifth vertex adjacent to all four, is chordal and not distance-hereditary: \leanref{gem_chordal_four}, \leanref{gem_chordal_five}, \leanref{gem_not_distance_hereditary}.)"""),
(r"""\begin{observation}
The alternating tree presented in \cite{Her04} (\ref{sec:alternating}) is a cotree representation of the $\GK$-faamily.
\end{observation}""",
 r"""\begin{observation}[\leanref{primalAdj_alt}]
The alternating tree presented in \cite{Her04} (\ref{sec:alternating}) is a cotree representation of the $\GK$-family and of the $\TK$-family: for every $i$, two vertices are adjacent in the primal graph of $\Gamma_i$ (resp.\ $\Gamma_i'$) exactly when they are adjacent in the cograph of the alternating tree.
\end{observation}"""),
(r"""\begin{lemma}\label{lem:twins-permute}
Let $G=(V,E)$ be a distance-hereditary graph, $H$ its conformal clique hypergraph, and $\Tr(H)$ its transversal hypergraph. If $u,v\in V$ are twin vertices in $G$, then $u$ and $v$ permute in both $H$ and $\Tr(H)$. \cite{Tim13}
\end{lemma}

\begin{proof}""",
 r"""\begin{lemma}[\leanref{twins_mem_aut_cliques}]\label{lem:twins-permute}
Let $G=(V,E)$ be a graph, $H$ its clique hypergraph, and $\Tr(H)$ its transversal hypergraph. If $u,v\in V$ are twin vertices in $G$, then $u$ and $v$ permute in both $H$ and $\Tr(H)$. \cite{Tim13}
\end{lemma}

\begin{proof}
The transposition $(u\,v)$ is an automorphism of $G$: it fixes every vertex other than $u,v$, and twins have the same neighbours outside $\{u,v\}$ \leanref{swap_isAut_of_twins}. A graph automorphism maps maximal cliques to maximal cliques, so $(u\,v)\in\Aut(H)$, and $\Aut(H)\le\Aut(\Tr(H))$ \leanref{aut_le_aut_tr}. No hypothesis on $G$ is needed.
\end{proof}

The 2024 edition assumed $G$ distance-hereditary and $H$ conformal, and its proof, kept below for the record, is incorrect: a stable set containing $u$ need not contain its false twin $v$.

\begin{proof}[Proof printed in 2024]"""),
(r"""\begin{lemma}\label{lem:twins-map}""", r"""\begin{lemma}[\leanref{twins_map}]\label{lem:twins-map}"""),
(r"""and wreath product (\cite{wreath-missing}) with a symmetric group. \cite{Cam22}""",
 r"""and wreath product with a symmetric group. \cite{Cam22}"""),
],
"ch5-experiments.tex": [
(r"\cite{missing-2, Tak08}", r"\cite{Tak08}"),
(r"\cite{Uno24}, \cite{missing-3} defined", r"\cite{Uno24}, defined"),
(r"""G=\{\{v_1,v_5,v_6\},\{v_4,v_5,v_6\},\{v_1,v_2\},\{v_2,v_3,v_4\}\},\\[4pt]
H=\{\{v_2,v_4,v_6\},\{v_2,v_5\},\{v_1,v_4\},\{v_1,v_3,v_5\}\}""",
 r"""G=\{\{v_1,v_5,v_6\},\{v_4,v_5\},\{v_1,v_2\},\{v_2,v_3,v_4\}\},\\[4pt]
H=\{\{v_2,v_4,v_6\},\{v_2,v_5\},\{v_1,v_4\},\{v_1,v_3,v_5\}\}"""),
(r"""H=\{\{v_3,v_4,v_6\},\{v_2,v_3,v_5\},\{v_8,v_1,v_2\},\{v_8,v_3,v_5\},\{v_4,v_5,v_7\},\{v_2,v_4,v_7\},\{v_1,v_5,v_7\},\\[4pt]
\{v_1,v_2,v_7\},\{v_3,v_5,v_7\},\{v_1,v_3,v_7\},\{v_8,v_1,v_6\},\{v_8,v_4,v_6\},\{v_3,v_5,v_6\},\\[4pt]
\{v_8,v_2,v_4\},\{v_8,v_1,v_5\},\{v_2,v_3,v_4\},\{v_4,v_6,v_7\},\{v_1,v_3,v_6\},\{v_8,v_4,v_5\}\}
\end{gather*}
\end{itemize}""",
 r"""H=\{\{v_1,v_2,v_3\},\{v_2,v_3,v_4\},\{v_2,v_3,v_5\},\{v_1,v_3,v_6\},\{v_3,v_4,v_6\},\{v_3,v_5,v_6\},\{v_1,v_2,v_7\},\\[4pt]
\{v_2,v_4,v_7\},\{v_1,v_5,v_7\},\{v_3,v_5,v_7\},\{v_4,v_5,v_7\},\{v_1,v_6,v_7\},\{v_4,v_6,v_7\},\{v_1,v_2,v_8\},\\[4pt]
\{v_2,v_4,v_8\},\{v_1,v_5,v_8\},\{v_3,v_5,v_8\},\{v_4,v_5,v_8\},\{v_1,v_6,v_8\},\{v_4,v_6,v_8\}\}
\end{gather*}
\end{itemize}

Each pair is a transversal pair (\leanref{sixA_dual}, \dots, \leanref{eightVer_dual}). The 2024 edition printed the 6-A edge $\{v_4,v_5\}$ as $\{v_4,v_5,v_6\}$ and the 8-Ver transversal with 19 edges; as printed, neither is a transversal pair (\leanref{sixA_printed_not_dual}, \leanref{eightVer_printed_not_dual})."""),
(r"""The hypergraph has $7k$ edges and the transversal has $\frac{(k-2)^2}{4}+k/2+1$ edges.""",
 r"""The $k$ disjoint copies have $7k$ edges and their transversal has $7^k$ edges (\leanref{kFano_card}, \leanref{tr_kFano_card}); the 2024 edition printed $\frac{(k-2)^2}{4}+k/2+1$, which already fails at $k=2$, where the count is $49$ \leanref{two_fano_tr_card}."""),
(r"""\begin{observation}\label{obs:false-twins}
In the \FKA{} decomposition of certain read-once hypergraphs, when the most frequent vertex is deleted, its false twin vertices are filtered out by the Sperner condition in the contraction subhypergraph.
\end{observation}""",
 r"""\begin{observation}[\leanref{falseTwin_filtered}, \leanref{f2g2_false_twin_filtered}]\label{obs:false-twins}
In the \FKA{} decomposition of certain read-once hypergraphs, when the most frequent vertex is deleted, its false twin vertices are filtered out by the Sperner condition in the contraction subhypergraph. In general: if $u\ne x$ and every edge through $u$ is a pair $\{u,w\}$ with $\{x,w\}$ also an edge, then $u$ lies in no edge of $min(G/x)$.
\end{observation}"""),
(r"""\begin{observation}\label{obs:fano-tight}
For hypergraphs with $n=3$ and $n=7$ vertices, the lower bound on the vertex frequency $\epsilon$ for \FKA{} is tight, with $\epsilon(3)=\frac{2}{3}$ and $\epsilon(7)=\frac{3}{7}$, where $\epsilon(n)$ is the lower bound for hypergraphs on $n$ vertices. So, the lower bound is tight for $n=3,7$.
\end{observation}""",
 r"""\begin{observation}[\leanref{eps_three}, \leanref{eps_four}, \leanref{fano_eps}]\label{obs:fano-tight}
Let $\epsilon(n)$ be the least frequency of a most frequent vertex over transversal pairs on $n$ vertices with both hypergraphs nonempty and without the empty edge. Then $\epsilon(3)=\frac{2}{3}$, attained only by $K_3$, and $\epsilon(4)=\frac{1}{2}$. The Fano plane has $\epsilon=\frac{3}{7}$, so $\epsilon(7)\le\frac{3}{7}$.
\end{observation}

The 2024 edition also claimed $\epsilon(7)=\frac{3}{7}$. Whether any transversal pair on seven vertices has $\epsilon<\frac{3}{7}$ is not established; it is left open."""),
(r"""No larger projective plane hypergraph has been shown to be self-transversal, further highlighting their distinctiveness in this context.""",
 r"""No larger projective plane hypergraph has been shown to be self-transversal, further highlighting their distinctiveness in this context. The projective plane of order 3 is not: six of its points meet every line and contain none \leanref{pg23_not_self_dual}."""),
],
}


def main() -> None:
    for name, edits in EDITS.items():
        text = (SRC / name).read_text(encoding="utf-8")
        for old, new in edits:
            n = text.count(old)
            if n != 1:
                sys.exit(f"{name}: span occurs {n} times: {old[:80]!r}")
            text = text.replace(old, new)
        (DST / name).write_text(text, encoding="utf-8")
        print(f"{name}: {len(edits)} edits")
    for name in ("appendix.tex",):
        shutil.copy(SRC / name, DST / name)


if __name__ == "__main__":
    main()
