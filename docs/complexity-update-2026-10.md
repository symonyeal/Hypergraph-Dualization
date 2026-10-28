# Complexity update, 28 October 2026

The new SAT results directly challenge the hypothesis supporting Proposition 4.6.
They do not settle the project's unconditional growth conjectures or establish a
faster dualization algorithm. This assessment uses revision `c1e49a1`, compared
with GitHub main after fetching on 28 October 2026.

## Sources and verification scope

[OpenAI's manuscript](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf),
dated 17 October and revised 25 October, states a deterministic algorithm for
exactly counting satisfying assignments of fixed-width CNF formulas in polynomial
space. Theorem 1.1 bounds its time by
`(n+m)^{O_k(1)} 2^{O_k(n log log n / sqrt(log n))}`; at fixed clause density the
exponent improves to `O_{k,D}(n / sqrt(log n))`. Here `n` counts variables, `m`
counts clauses and `k` bounds clause width.

[Anthropic's manuscript](https://github.com/anthropics/formal-math/blob/main/eth/paper.pdf),
dated 26 October, states a deterministic counting algorithm with time
`2^{O(min{k² n log log n / sqrt(log n), k m / sqrt(log m)})}`. Both results would
refute ETH, and their fixed-width guarantees also contradict SETH.

Both publishers provide Lean formalizations. The main theorem statements and
introductory scope of both manuscripts were read; the complete proofs were not
audited. Anthropic's [statement file](https://github.com/anthropics/formal-math/blob/main/eth/MainResults.lean)
explicitly defines the machine, input encoding, count and time bound; its
[README](https://github.com/anthropics/formal-math/blob/main/eth/README.md) documents
axiom and comparator checks. These external builds were not run here.
[OpenAI's announcement](https://openai.com/index/building-scientific-understanding-with-academic-communities/)
describes an independent examination led by Impagliazzo, Paturi and Williams.
The status used below is therefore a published claim with accompanying formal
artifacts, not an independently reproduced theorem in this project.

## Consequences for the existing results

| Project statement | Consequence if the SAT claims hold |
| --- | --- |
| Proposition 4.6: ETH implies no polynomial bound on `δ` over all dual pairs | The implication remains conditional, but its premise is false; it supplies no obstruction to a polynomial bound |
| Kobayashi–Kurita–Wasa reduction underlying that proposition | The reduction remains a mathematical construction; its ETH-based hardness conclusion loses its premise |
| Exponential FK-A trees on GK/TK, matching tree/DAG separation, `ro12` counterexample | No change: these are unconditional statements about specified algorithms or instances |
| Conjectures 4.19 and 4.30: unbounded `δ/N` and `δ_iso/N` under the degree-sum rule | Remain open; neither SAT algorithm counts FK-A states |
| C3: monotone small-DNF/small-CNF functions requiring large FBDDs | Remains open in this assessment; SAT runtime does not imply a bound on FBDD representation size |

The [Kobayashi–Kurita–Wasa paper](https://arxiv.org/abs/2610.11473) reduces 3-SAT
to non-duality, constructing an instance of size
`2^{O(n^{2/3}(log n)^{1/3})}`. This direction transfers a fast duality algorithm
to SAT. A faster SAT algorithm cannot be substituted into that reduction to obtain
a faster duality algorithm.

A further relevant preprint is [Mary, 20 October](https://arxiv.org/abs/2610.28012),
on bounded-dimension transversal enumeration and maximum minimal hitting sets.
Its abstract gives ETH- and SETH-based lower bounds. These face the same premise
problem; they are not replacement unconditional barriers. Only its abstract was
read, and AI involvement is not asserted here.

## What an algorithmic transfer would require

The following is a standard encoding argument, not a new theorem from either
manuscript. First check `L ⊆ Tr(H)` explicitly. Then a missing transversal exists
exactly when the formula

`F(x) = (AND_{E in H} OR_{v in E} x_v) AND (AND_{T in L} OR_{v in T} NOT x_v)`

is satisfiable. A satisfying assignment is a hitting set containing no listed
transversal. Minimizing it preserves that property and gives a missing minimal
transversal; conversely a missing minimal transversal contains no other minimal
transversal. This proves the stated equivalence under the inclusion check.

Its width is the largest edge on either side, not just the rank of `H`. Thus a
bounded-rank input alone does not provide fixed-width CNF. A conversion to 3-CNF
can introduce a number of variables proportional to the total incidence size.
A subexponential bound in that expanded size need not improve on FK-B's existing
quasipolynomial input-size bound. No such improvement has been established here.

The new algebraic and tensor-contraction methods could motivate algorithms beyond
variable splitting. A useful transfer must specify a representation, include its
construction and arithmetic costs, and beat the existing bound in the same input
parameter. A faster evaluation algorithm alone does not compress the FK-A DAG.

## Relation to the earlier manuscript survey

Ryser covering counterexamples and threshold/influence results are already recorded
in [the existing survey](openai-math-connections.md). The current catalogue entries
were checked against that note. Those connections do not provide a degree-sum
growth recurrence, a shape-collision bound or an irregular D3 template. No new
solution to those questions was identified in this bounded literature check.

The immediate research priority is to follow the independent ETH examination and
audit the exact hypotheses behind Proposition 4.6. The constructive GK questions
remain worthwhile without ETH: an explicit lower bound for a specified split rule
is independent of the existence of a faster algorithm using another method.
