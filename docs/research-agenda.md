# Research agenda

The result register and open-item list are in
[`research-2026-10.md`](research-2026-10.md), §§4 and 7. These are the next tests for
the principal open questions. Counts below use modified FK-A unless stated otherwise.

## Q1. Degree-sum growth on the alternating trees

Conjectures 4.19 and 4.30 ask whether `δ/N` and `δ_iso/N` are unbounded on GK.
At `f₄`, `N = 49,152`, `δ = 67,247,387` and `δ_iso = 827,175` (computed).
The identity `N_{k+1} = (4/3)N_k²` makes a uniform squaring inequality a sufficient
route to growth, provided its constant and starting ratio meet the strict threshold
in Proposition 4.37. That inequality remains unproved.

The unrestricted block embedding fails at `f₃` (Observation 4.31); equal odd-size
supports never occur jointly in the measured cases (Observation 4.39); even matching
endpoint degree profiles do not ensure joint shape reach (Observation 4.48).
Embedded blocks also continue after the standalone singleton-edge stop, so the
relaxation in Lemma 4.36 must suppress that stop.

The remaining candidate is Conjecture 4.40: a constant share of standalone support
pairs occurs jointly. A useful advance must constrain the weight histories the
surrounding blocks can realize, or provide a counterexample to that claim.
The existing labelled-support tables do not establish a bound on shape collisions.
Enumerating `f₅` is impractical: the proposed law would give at least `1.1×10¹⁵` states.

## Q2. A frequency guarantee with few subproblems

The guarded rule satisfies FK96's frequency guarantee (Proposition 4.18), but reaches
124,876 states on GK `f₅`, against 512 for leftmost (computed). Its least eligible
choice already uses zero degree-sum fallbacks; eligibility forces 92,776 departures
from leftmost (Observation 4.32).

Test alternative eligible choices or component decomposition. The target is a rule
with the guarantee and polynomial `δ` on GK and TK. Proving FK96's existing tree
bound for the guarded rule in Lean is a separate task.

## Q3. FK-A's worst-case tree exponent

Theorems 4.24–4.25 give `τ ≥ N^{Ω(log N)}` on GK and TK under every valid rule.
FK96 gives `N^{O(log² N)}` under the frequency guarantee (cited).
A rule attaining `N^{O(log N)}` on all monotone dual pairs would close this gap.
Start with read-once inputs, or find a family on which every eligible rule exceeds
that scale. The finite ratios in `results/iso-memo.md` are evidence, not an
asymptotic upper bound.

## Q4. Symmetry in the thesis

Audit 4.33 distinguishes local automorphism groups, inherited input symmetries and
isomorphisms between reached nodes. Local group-order changes alone predict neither
`δ/δ_Aut` nor `δ/δ_iso`. The shallow-depth bound of Theorem 4.22 and the cache
correctness theorem 4.28 have separate hypotheses and conclusions.
