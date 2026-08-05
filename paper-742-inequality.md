# Every diameter-2-critical graph on n vertices has at most ⌊n²/4⌋ edges

**Author:** Claude Code

This proof was found, written, and formalized by a multi-agent AI research
campaign (Claude, Anthropic), with the Lean formalization serving as the
campaign's machine-checked record; the verification of the formal statement is
deliberately independent of that provenance.

**Acknowledgments:** [to be filled before posting]

---

## Abstract

A graph is *diameter-2-critical* (D2C) if it has diameter 2 and the deletion
of any edge increases the diameter. We prove that every D2C graph on `n`
vertices has at most `⌊n²/4⌋` edges, for every `n`. This is Erdős Problem
#742 as posed, and it settles it; the bound was previously known only for
`n` beyond a tower-type threshold, by a theorem of Füredi (1992).

The engine is a new inequality about **arbitrary** graphs — a hereditary
strengthening of Füredi's Lemma 2.1 by a criticality term. For every graph
`F` on `n` vertices,

>     e(F) + disj(F) + X(F)  ≤  ⌊n²/2⌋,

where `disj` counts vertex pairs with disjoint neighbourhoods and `X` counts
edges carrying a criticality certificate (a *witness*). The proof is by
induction, deleting two adjacent vertices at a time. The induction step
reduces to a global counting inequality `Σ(F) ≥ 0` over the witnessed edges
of graphs with no codegree-0 edge, which we prove by an explicit injection
carrying a global charge transfer; its final obstruction is dissolved by a
two-line lemma.

Every argument is elementary and self-contained. **No step of the proof
closes by exhaustion**, and the paper depends on no external theorem: the
machine computations reported in Appendix A are a check on the proof, not an
input to it.

We do **not** prove the *equality* clause — that `K_{⌈n/2⌉,⌊n/2⌋}` is the
unique extremal graph. That clause is a strengthening due to the Murty–Simon
literature, it is not part of Erdős #742, and §1.5 states carefully what is
and is not known about it.

---

## 0. Scope: what this paper proves, and what it does not

The literature attaches two distinct claims to the name "Murty–Simon":

> **(MS-ineq)** every D2C graph on `n` vertices has at most `⌊n²/4⌋` edges;
>
> **(MS-eq)** equality holds precisely for `K_{⌈n/2⌉,⌊n/2⌋}`.

**Erdős Problem #742 as posed is (MS-ineq) only** — its statement is the
question whether `G` has at most `n²/4` edges. This paper proves (MS-ineq),
for all `n`, unconditionally.

| | status in this paper |
|---|---|
| **(MS-ineq)** | **proved for all `n`, unconditionally** (Corollary B) |
| **(MS-eq)** | **not addressed.** See §1.5 for what the literature does and does not establish |

Because the two clauses are routinely quoted under one name, we avoid the
phrase "the Murty–Simon conjecture" for either clause separately, and use the
labels above throughout.

**Status vocabulary.** For every statement in this paper the honest claim is
*"no gap found after N independent passes"*, never *"gap-free"*. A machine
search that terminates without a counterexample is reported as *"no
counterexample found"*, never as evidence that a statement is true. The
inequality itself has, in addition, been formalised in Lean 4 and checked by
the Lean kernel; §6 states precisely what that does and does not certify.

---

## 1. Introduction

### 1.1 The problem and its history

All graphs are finite and simple. A graph `G` of diameter 2 is
**diameter-2-critical** (D2C) if `diam(G − e) > 2` for every edge `e`.

The extremal question for this class is attributed to Murty and Simon (see
Caccetta–Häggkvist [CH79]); Füredi [Fü92, p. 81] reports, crediting a private
communication of Erdős, that it goes back to Ore in the 1960s. An incorrect
proof was published in 1984 ([Fü92, p. 82]). The balanced complete bipartite
graph `K_{⌈n/2⌉,⌊n/2⌋}` is D2C and has `⌊n²/4⌋` edges, so the bound
(MS-ineq), if true, is attained.

Prior partial results. **These attributions carry different weights, and the
weights are recorded in Appendix B; the reader should consult it before
citing any of them onward.**

- **Füredi [Fü92]** proved both clauses — the bound *and* the equality
  characterisation — for all `n > n₀`, where `n₀` is explicit but of tower
  type: a tower of 2s of height about `10¹⁴`. The proof routes through the
  Ruzsa–Szemerédi (6,3)-theorem / removal lemma. Consequently the problem has
  standardly been described as *decidable but open*: a finite check remained,
  far beyond computational reach. The route is intrinsically stuck — no
  improvement of the generic (6,3) bound can bring `n₀` into feasible range,
  a Behrend-type lower bound blocking it below about `10⁵⁴`.
- **Fan [F87]** proved the **bound** `e ≤ ⌊n²/4⌋` for `n ≤ 24` and for
  `n = 26`, and for all `n ≥ 25` the estimate
  `e < n²/4 + (n² − 16.2n + 56)/320 < 0.2532n²`. Fan proves the
  **inequality only**, and says so explicitly [F87, p. 240]: *"in both
  cases (`n ⩽ 24` and `n = 26`) we only prove affirmatively the first part
  of the conjecture."* We are not aware of any bound valid for all `n`
  stronger than Fan's prior to the present work.
- **Plesník [P75]** proved a bound of order `(3/8)n²`; **Caccetta and
  Häggkvist [CH79]** improved it to `e ≤ 0.27n²`. *(Secondary attributions;
  not checked by us at first hand — Appendix B.)*
- The bound was established for several structured classes: graphs with a
  dominating edge, complements of claw-free graphs [HHY11], and graphs of
  large maximum degree; the total-domination reformulation of Hanson–Wang
  [HW03] underlies several of these. *(Secondary attributions. ⚠ In
  particular, the published Haynes–Henning–van der Merwe–Yeo proofs for the
  dominating-edge class are for graphs of **even order**, and we have not
  located a manuscript completing the odd case. See Appendix B.)*
- **Kirchweger and Szeider [KS21]** enumerated all D2C graphs up to `n = 13`
  by SAT-modulo-symmetries and verified the bound computationally to
  `n ≤ 19`.
- A **local** certificate route is provably impossible: **Loh and Ma [LM16]**
  constructed D2C graphs with `Σ_v d_v² ≥ (10/9 − o(1))nm`, refuting the
  edge-degree inequality that would have given `n²/4` directly. The failure
  of local certificates is specific to diameter 2, where the extremal graph
  is dense. Our §5.3 records the same phenomenon from the inside: every
  per-edge and every fixed-selection-rule form of our main counting
  inequality is false.

This paper proves (MS-ineq) for all `n`.

### 1.2 Statement of results

For a graph `F` on `n` vertices with open neighbourhoods `N(·)`, let

- **`e(F)`** := the number of edges;
- **`disj(F)`** := the number of unordered vertex pairs `{u,v}` — adjacent or
  not — with `N(u) ∩ N(v) = ∅`;
- a **witness at `u` for an edge `{u,v}`** := a vertex `y ≠ u` with
  `uy ∉ E` and `N(u) ∩ N(y) = {v}`;
- **`X(F)`** := the number of edges `{u,v}` with
  `codeg(u,v) := |N(u) ∩ N(v)| ≥ 1` possessing a witness at `u` or at `v`;
- **`Φ(F)`** := `e(F) + disj(F) + X(F)`.

> ### Theorem A
> For every graph `F` on `n` vertices, `Φ(F) ≤ ⌊n²/2⌋`.

Theorem A is a statement about **arbitrary** graphs; no criticality, no
diameter hypothesis, no connectedness.

Füredi's Lemma 2.1 [Fü92, p. 83] is the inequality
`e(F) + disj(F) ≤ ⌊n²/2⌋` for every graph. (Verbatim: *"Lemma 2.1.
|E(F)| + |E(disj F)| ≤ ⌊n²/2⌋"*, with `disj F` defined on p. 82 as the set of
pairs with disjoint neighbourhoods, adjacent or not — matching our `disj(F)`
exactly.) **Theorem A is its hereditary strengthening by the criticality term
`X(F)`**: the witness relation is exactly the literature's criticality
certificate — an edge `uv` is critical for a pair `{x,y}` iff the only
`≤2`-path from `x` to `y` uses `uv`; cf. [DFH19, Definition 5] — abstracted
from D2C graphs to all graphs.

Theorem A also contains **Mantel's theorem** [M07]: if `F` is triangle-free
then every edge has codegree 0, so every edge is counted by `disj` as well as
by `e`, giving `2e(F) ≤ Φ(F) ≤ ⌊n²/2⌋` and hence `e(F) ≤ ⌊n²/4⌋`. Mantel's
theorem is *not* used anywhere in this paper; it is a consequence.

> ### Corollary B — Erdős Problem #742
> Every diameter-2-critical graph on `n` vertices has at most `⌊n²/4⌋` edges.

Corollary B follows because `Φ = 2e` on D2C graphs (Proposition 3.2: in a D2C
graph every edge either has codegree 0 — then it is counted by `disj` — or
carries a witness — then it is counted by `X`). The bound is attained by
`K_{⌈n/2⌉,⌊n/2⌋}` for every `n ≥ 3`.

The engine of Theorem A is a new **global** counting inequality. For an edge
`{u,v}` of `F`, §2 defines nonnegative integers `R_c(u,v)`, `B(u,v)`,
`K_B(u,v)` — counts of certain non-edges and edges near `{u,v}` — and sets
`Slack_c := R_c − B`. Write `E0(F)` for the set of edges of codegree 0 and
`Ew(F)` for the set of witnessed edges of codegree `≥ 1`.

> ### Theorem Σ
> Let `F` be a finite simple graph with `E0(F) = ∅`. Then
>
>     Σ(F)  :=  Σ_{{u,v} ∈ Ew(F)} [ Slack_c(u,v) − K_B(u,v) ]  ≥  0.
>
> Connectedness is not assumed; `Ew(F) = ∅` makes `Σ` an empty sum.

### 1.3 Overview of the proof

Theorem A is proved by strong induction on `n`, **deleting two adjacent
vertices at a time**. Writing `A(F)` for the set of non-adjacent pairs with a
common neighbour, an elementary count (Proposition 3.1) gives
`Φ(F) = C(n,2) + D(F)` with

>     D(F) := |E0(F)| + |Ew(F)| − |A(F)|,

so that Theorem A becomes the statement `D(F) ≤ ⌊n/2⌋`. Since
`⌊n/2⌋ − ⌊(n−2)/2⌋ = 1`, the induction closes as soon as every graph on
`n ≥ 2` vertices in a suitable residual class has an **edge** `{u,v}` whose
deletion increment `D_inc(u,v) := D(F) − D(F − {u,v})` is at most 1, where
`F − {u,v}` deletes **both** vertices. The trichotomy is:

1. **`F` has an `E0` edge.** Every `E0` edge has `D_inc ≤ 1`,
   unconditionally (Theorem 3.9, by an injection).
2. **`F` has no `E0` edge and no `Ew` edge.** Then `D(F) = −|A(F)| ≤ 0`
   directly; no deletion is needed.
3. **`F` has no `E0` edge but some `Ew` edge.** This is the hard case, and
   the reason Theorem Σ exists. A per-edge sufficiency inequality
   (Corollary 3.8, from deletion bookkeeping refined by two rebate terms)
   shows that **any** `Ew` edge with `Slack_c ≥ K_B` has `D_inc ≤ 1`.
   Theorem Σ says that the sum of `Slack_c − K_B` over all `Ew` edges is
   nonnegative; by pigeonhole **some** `Ew` edge has `Slack_c ≥ K_B`.

Only the **sign of a sum** is used in case 3 — no structure, and in
particular no explicit selection rule. This evasion is essential rather than
stylistic: small examples kill every natural fixed selection rule (§5.3), and
per-edge deficits are real and unbounded (§5.2).

Theorem Σ itself (§4) is proved by re-indexing `Σ` as `#R − #B − #K` for
three explicit families of combinatorial *units*, and constructing an
injection `φ` from B-units and K-units into R-units. **The injection is not
local**: a charge created at one edge is, in a designated exceptional branch
(the *transfer* branch), paid at a **different** vertex's stock of R-units.
The case analysis is organised by a single invariant — transfer targets have
codegree `≥ 2` in their first two coordinates, all other targets have
codegree exactly 1 — and its final obstruction, a two-witness configuration
whose private capacity could conceivably be exhausted, is dissolved by a
two-line lemma (Lemma A, §4.6): for every witnessed edge `{p,v}` and every
common neighbour `z` of `p` and `v`, the witnessed neighbourhoods of `p` and
`v` cannot both be contained in `N[z]`.

The hypothesis `E0(F) = ∅` is used exactly three times, all three being
instances of one upgrade ("a witnessed edge of codegree `≥ 1` lies in `Ew`");
each use is necessary, with an explicit counterexample when it is dropped
(§4.8).

### 1.4 Tightness

`Σ(F) = 0` holds for every friendship graph (windmill) `F_k` — there all
three unit families are empty — and, more interestingly, for a growing family
of *full-capacity* graphs on which `φ` is a perfect bijection (2 instances at
`n = 6`, 555 at `n = 9`); §5.1 dissects both mechanisms. Theorem A is tight
for perfect matchings and for balanced complete bipartite graphs; Corollary B
is tight for `K_{⌈n/2⌉,⌊n/2⌋}`.

### 1.5 What this paper does not prove

**We do not prove (MS-eq)**, the uniqueness of `K_{⌈n/2⌉,⌊n/2⌋}` among
extremal graphs, and we make no claim about it. We also make no claim that
the literature closes it. Specifically, and stated because the opposite is
easy to assume:

- Füredi [Fü92] proves (MS-eq) for `n > n₀` only, with the same tower-type
  `n₀` as the bound.
- **Feeding an all-`n` bound into Füredi's stability analysis does not
  discharge it.** Füredi states his own interface at [Fü92, p. 87]: *"The
  huge values of `n₀` and `m` were needed to satisfy the inequalities
  `ε ≤ 0.005` and (4.2). In the proof we use only these two constraints."*
  Condition (4.2) is a **sparsification** — the existence of an edge subset
  of size `O(n²)` with a small constant whose deletion makes every critical
  pair have disjoint neighbourhoods. The present paper supplies **no**
  sparsification and no removal-lemma machinery of any kind; nothing in
  §§2–5 produces the object (4.2) asks for. So the two results do not
  compose in that direction.
- The one small-order result that might have supplied (MS-eq) does not:
  [F87] proves the **inequality** only, at every order it covers, by Fan's
  own statement (quoted in §1.1 and Appendix B). We have **not** audited the
  remaining small-order and structured-class results in the literature for
  the same distinction. See Appendix B.

The honest summary is therefore: **after the present paper, (MS-ineq) is
settled for all `n`, and (MS-eq) remains open below Füredi's threshold** —
and, since [F87] supplies the equality clause at no order, the range
`n ≤ 24` and `n = 26` is not an exception to that.

---

## 2. Definitions

`F` is a finite simple graph, `V = V(F)`, with open neighbourhoods `N(·)`,
`N[x] := N(x) ∪ {x}`, and `codeg(u,v) := |N(u) ∩ N(v)|`.

- **Witness.** For an **edge** `{x,z} ∈ E(F)`, a *witness at `x`* is a vertex
  `y` with `y ≠ x`, `xy ∉ E`, and `N(x) ∩ N(y) = {z}`. Write
  `Wit_x(z) := {witnesses at x for {x,z}}` and
  `Wit(e) := Wit_a(b) ∪ Wit_b(a)` for `e = {a,b}`.
- **`E0(F)`** := the edges of codegree 0. **`Ew(F)`** := the edges of
  codegree `≥ 1` with `Wit(e) ≠ ∅`. **`A(F)`** := the **non**-edges `{x,s}`
  with `codeg(x,s) ≥ 1`.
- `e(F)`, `disj(F)`, `X(F)`, `Φ(F)` as in §1.2; note `X(F) = |Ew(F)|`
  identically.
- **Per-pair quantities**, for an edge `{u,v}` of `F`. Partition
  `V ∖ {u,v}` into four categories:
  **(a)** `N(u)∖N[v]`, **(b)** `N(v)∖N[u]`, **(d)** `W_uv := N(u)∩N(v)`,
  **(c)** the rest (adjacent to neither `u` nor `v`).
  - `R_c(u,v) := #{(x,w) : x ∈ {u,v}, w ∈ category (c), {x,w} ∈ A(F)}`.
  - `B(u,v) := #{edges {w,z} ∈ Ew(F) with w,z ∉ {u,v} and
    Wit({w,z}) ⊆ {u,v}}` — "remote edges every witness of which lies in the
    pair".
  - For `w0 ∈ W_uv` and `x ∈ {u,v}` with `{x,w0} ∈ Ew(F)`: the edge
    `{x,w0}` is **`K_A`** if it has a witness at `w0`, and **`K_B`** if it
    has a witness at `x` and none at `w0`. `K_A(u,v)`, `K_B(u,v)` denote the
    two counts. **`K(u,v)`** is the *independent* count
    `K(u,v) := Σ_{w0 ∈ W_uv} ( [{u,w0} ∈ Ew(F)] + [{v,w0} ∈ Ew(F)] )` — the
    number of `Ew` edges joining `u` or `v` to a common neighbour of both.
    That `K = K_A + K_B` is therefore **not** a definition: it is the
    assertion that the `K_A`/`K_B` split of those edges is exhaustive and
    exclusive, and it is proved as Lemma 3.7(i).
  - `Slack_c(u,v) := R_c(u,v) − B(u,v)`.
- **`Σ(F)`** := `Σ_{{u,v} ∈ Ew(F)} [ Slack_c(u,v) − K_B(u,v) ]`.
- **`D(F)`** := `|E0(F)| + |Ew(F)| − |A(F)|`; and
  **`D_inc(u,v)`** := `D(F) − D(F − {u,v})`, where **`F − {u,v}` deletes both
  vertices** and all incident edges. Every quantity is always computed in the
  ambient graph named, never in a subgraph.
- Shorthand: **`Nw(x)`** := `{t : {x,t} ∈ Ew(F)}`, `dw(x) := |Nw(x)|`;
  **`D2(x)`** := `{s : s ≠ x, xs ∉ E, codeg(x,s) ≥ 1}`, so that
  `D2(x) = {s : {x,s} ∈ A(F)}`.

> **Proposition 2.1 (symmetry of the witness condition).** The condition
> "`x ≠ y`, `xy ∉ E`, `N(x) ∩ N(y) = {z}`" is symmetric in `x` and `y`; what
> is asymmetric is only which edge it witnesses:
>
>     y ∈ Wit_x(z)  ⟺  x ∈ Wit_y(z),
>
> and either membership gives `z ∈ N(x) ∩ N(y)`. (A codegree-1 non-adjacent
> pair thus certifies **two** witness relations simultaneously.)
>
> *Proof.* Each clause of the condition is symmetric under swapping `x` and
> `y`, and `z ∈ N(x) ∩ N(y)` is part of the set equality. The edge witnessed
> by `y ∈ Wit_x(z)` is `{x,z}`; the edge witnessed by `x ∈ Wit_y(z)` is
> `{y,z}`. ∎

---

## 3. The reduction: from Theorem Σ to Theorem A and Corollary B

Throughout this section `{u,v}` is an **edge** of `F` and `F′ := F − {u,v}`
(both vertices deleted).

> **Proposition 3.1 (D-normal form).** For every graph `F` on `n` vertices,
> `Φ(F) = C(n,2) + D(F)`. Consequently Theorem A is equivalent to:
> `D(F) ≤ ⌊n/2⌋` for every graph `F`.
>
> *Proof.* The non-adjacent pairs split into those of codegree `≥ 1` — that
> is, exactly `A(F)` — and those of codegree 0. Hence
>
>     disj(F) = |E0(F)| + [ C(n,2) − e(F) − |A(F)| ].
>
> With `X(F) = |Ew(F)|`,
>
>     Φ = e + disj + X = C(n,2) + |E0| + |Ew| − |A| = C(n,2) + D(F).
>
> For the equivalence, `⌊n²/2⌋ − C(n,2) = ⌊n/2⌋` for both parities. ∎

> **Proposition 3.2 (criticality inventory).** In a D2C graph `G`, every edge
> lies in `E0(G) ∪ Ew(G)`; hence `Φ(G) = 2·e(G)`.
>
> *Proof.* Let `{u,v} ∈ E(G)`. Since `diam(G − uv) > 2` — here,
> exceptionally, we delete the **edge** only — there is a pair `{x,y}` with
> `dist_G(x,y) ≤ 2` every `≤2`-path of which, in `G`, uses the edge `uv`. A
> 2-path `x–m–y` uses `uv` only if `{x,m}` or `{m,y}` equals `{u,v}`, so `x`
> or `y` lies in `{u,v}`; likewise the 1-path `{x,y}` uses `uv` only if
> `{x,y} = {u,v}`.
>
> *Case 1: `{x,y} = {u,v}`.* A 2-path `u–w–v` never uses the edge `uv`, so
> none exists: `codeg(u,v) = 0` and `{u,v} ∈ E0(G)`.
>
> *Case 2: WLOG `x = u`, `y ∉ {u,v}`.* If `uy ∈ E` then the 1-path `u–y`
> does not use `uv`, a contradiction; so `uy ∉ E` and, `G` having diameter 2,
> `dist_G(u,y) = 2`. Every 2-path `u–m–y` uses `uv`; since `m ≠ u` and
> `y ∉ {u,v}`, the only possibility is `m = v`. Hence
> `N(u) ∩ N(y) = {v}`: `y` is a witness at `u` for `{u,v}`. If
> `codeg(u,v) = 0` then `{u,v} ∈ E0(G)`; otherwise `{u,v} ∈ Ew(G)`.
>
> In all cases `{u,v} ∈ E0 ∪ Ew`, and `E0`, `Ew` are disjoint by definition,
> so `|E0| + |Ew| = e(G)`. Now by Proposition 3.1's count,
> `Φ = e + [|E0| + (C(n,2) − e − |A|)] + |Ew|`; and in a diameter-2 graph
> every non-adjacent pair has a common neighbour, so `C(n,2) − e = |A|`.
> Hence `Φ = e + |E0| + |Ew| = 2e`. ∎

> **Corollary B, from Theorem A.** For a D2C graph `G` on `n` vertices,
> `2e = Φ ≤ ⌊n²/2⌋`, so `e ≤ ⌊ ⌊n²/2⌋ / 2 ⌋ = ⌊n²/4⌋`. ∎

### 3.3 Deletion bookkeeping: further per-pair quantities

For an unordered vertex pair `P` let

>     c(P,F) := +1 if P ∈ E0(F) ∪ Ew(F),  −1 if P ∈ A(F),  0 otherwise,

so that `D(F) = Σ_P c(P,F)`. For an edge `{u,v}`, with categories as in §2:

- **`S(u,v)`** := `Σ_{w ∉ {u,v}} [ c({u,w},F) + c({v,w},F) ]` — the net
  `D`-contribution of the pairs touching exactly one of `u`, `v`;
- **`U_a(u,v)`** := `#{w ∈ category (a) : codeg(u,w) ≥ 1, Wit({u,w}) = ∅}`,
  the edges from `u` to its private neighbours that are neither `E0` nor
  `Ew`; **`U_b(u,v)`** symmetrically at `v`;
- **`R⁺(u,v)`** := `#{(w0,x) : w0 ∈ W_uv, x ∈ category (a) ∪ category (b),
  w0x ∉ E, and N(w0) ∩ N(x) = {u} if x ∈ (a), = {v} if x ∈ (b)}`.

> **Lemma 3.4 (deletion decomposition).** For any graph `F` and any edge
> `{u,v}`,
>
>     D(F) − D(F′) = c({u,v},F) + S(u,v) + Σ_P [ c(P,F) − c(P,F′) ],
>
> the last sum running over the **remote** pairs `P` (both vertices outside
> `{u,v}`).
>
> *Proof.* `D(F) = Σ_P c(P,F)` over all unordered vertex pairs of `F`. Those
> pairs split into `{u,v}` itself; the pairs touching exactly one of `u,v`,
> contributing `S(u,v)`; and the remote pairs. The pairs of `F′` are exactly
> the remote pairs, evaluated in `F′`. Subtract. ∎

> **Lemma 3.5 (remote transitions and rebates).**
> **(i)** For every remote pair `P`,
> `c(P,F) − c(P,F′) ≤ [ P ∈ B(u,v) ]` — that is, `≤ 0` unless `P` is a
> B-edge of the pair, where it is `≤ 1`.
> **(ii)** The `R⁺(u,v)` index pairs `{w0,x}` are pairwise distinct remote
> **non**-edges with `c(P,F) − c(P,F′) = −1` exactly.
>
> *Proof of (i).* Vertex deletion never adds adjacencies and never adds
> common neighbours: for remote `x,y`, `N_{F′}(x) = N_F(x) ∖ {u,v}`, so
> `codeg_{F′}(x,y) = |N_F(x) ∩ N_F(y) ∖ {u,v}| ≤ codeg_F(x,y)`.
>
> *`P` a non-edge:* `c ∈ {−1, 0}` according as `codeg ≥ 1` or `= 0`, and
> codegree can only shrink, so the only transitions are `−1 → −1`,
> `−1 → 0` and `0 → 0`, of differences `0, −1, 0` — all `≤ 0`.
>
> *`P` an edge:*
> - `codeg_F(P) = 0`: then `codeg_{F′}(P) = 0` and `c = +1` on both sides;
>   difference 0.
> - `codeg_F(P) ≥ 1`, `codeg_{F′}(P) = 0`: then `c(P,F′) = +1` (`P` is an
>   `E0` edge of `F′`) while `c(P,F) ≤ +1`; difference `≤ 0`.
> - `codeg_F(P) ≥ 1`, `codeg_{F′}(P) ≥ 1`: then `c = [P witnessed]` on both
>   sides, and the difference is `+1` only if `P` is witnessed in `F` and
>   unwitnessed in `F′`.
>   **Witness survival.** If `y ∉ {u,v}` witnesses `P = {w,z}` at `w` in `F`
>   — so `yw ∉ E` and `N_F(w) ∩ N_F(y) = {z}` — then in `F′` we still have
>   `yw ∉ E`, and
>   `N_{F′}(w) ∩ N_{F′}(y) = (N_F(w) ∩ N_F(y)) ∖ {u,v} = {z} ∖ {u,v} = {z}`,
>   since `z` is remote; so `y` still witnesses `P` in `F′`. Hence a `+1`
>   transition requires `∅ ≠ Wit_F(P) ⊆ {u,v}` with `P` remote and in
>   `Ew(F)` — precisely `P ∈ B(u,v)`.
>
> *Proof of (ii).* Remoteness: `w0 ∈ W_uv` and `x ∈ (a) ∪ (b)` all lie
> outside `{u,v}`. The pair is a non-edge of codegree `≥ 1` in `F`: for
> `x ∈ (a)`, `u ∈ N(w0)` (as `w0 ∈ W_uv`) and `u ∈ N(x)` (as
> `(a) ⊆ N(u)`); so `c(P,F) = −1`. In `F′`,
> `codeg_{F′}(w0,x) = |{u} ∖ {u,v}| = 0`, so `c(P,F′) = 0`, and the
> difference is `−1`. Distinctness: the unordered pair `{w0,x}` determines
> its roles, since `W_uv` and `(a) ∪ (b)` are disjoint parts of the
> partition, so distinct index pairs give distinct unordered pairs. These
> pairs are non-edges, hence disjoint from the B-edges of (i). ∎

> **Theorem 3.6 (refined deletion bound).** For any graph `F` and **any**
> edge `{u,v}`,
>
>     D(F) − D(F − {u,v})  ≤  1 + S(u,v) + B(u,v) − R⁺(u,v).
>
> *Proof.* Lemma 3.4, together with Lemma 3.5(i) summed over the remote
> pairs and Lemma 3.5(ii)'s `R⁺` distinct pairs each contributing exactly
> `−1` and none of them a B-edge, gives
> `Σ_remote ≤ B(u,v) − R⁺(u,v)`; and `c({u,v},F) ≤ +1` always. ∎
>
> No minimality, no selection rule, and no `Ew`-membership of `{u,v}` is
> used.

> **Lemma 3.7 (bookkeeping identities).** For any graph `F` and any edge
> `{u,v}`:
> **(i)** `K = K_A + K_B`: a `K`-counted edge `{x,w0}` lies in `Ew(F)` and
> is therefore witnessed at `x` or at `w0`; "witnessed at `w0`" (`K_A`) and
> "witnessed at `x` but not at `w0`" (`K_B`) are exhaustive and exclusive.
> **(ii)** `R⁺(u,v) ≥ K_A(u,v)`.
> **(iii)** *(the S-identity)*
> `S(u,v) = −U_a(u,v) − U_b(u,v) − R_c(u,v) + K(u,v)`.
>
> *Proof of (ii).* Let `{x,w0}` be a `K_A` edge — `x ∈ {u,v}`,
> `w0 ∈ W_uv`, witnessed at `w0` — and let `y` be a witness at `w0`, so
> `yw0 ∉ E` and `N(w0) ∩ N(y) = {x}`. Then `y ∈ N(x)`, since
> `x ∈ N(w0) ∩ N(y)`. Writing `x′` for the other element of `{u,v}`: `y` is
> not adjacent to `x′`, for `x′ ∈ N(w0)` (as `w0 ∈ W_uv`) and `y ∈ N(x′)`
> would put `x′ ∈ N(w0) ∩ N(y) = {x}`, i.e. `x′ = x`; and `y ≠ x′` since
> `x′ ∈ N(w0)` while `y ∉ N(w0)`. Hence `y ∈ category (a)` if `x = u`, and
> `y ∈ category (b)` if `x = v`, and `(w0,y)` satisfies `R⁺`'s membership
> clause verbatim.
>
> The map `(x,w0) ↦ (w0, y(x,w0))` — where `y(x,w0)` is a fixed chosen
> witness at `w0` for the edge `{x,w0}`, the choice being indexed by the
> `K_A` **edge** — is injective: `w0` is the first coordinate, and `y`
> determines `x` as the unique element of `N(w0) ∩ N(y)`, so distinct `K_A`
> edges give distinct index pairs.
>
> *Proof of (iii).* Group `S`'s sum by the category partition of
> `V ∖ {u,v}`.
> - `w ∈ (d) = W_uv`: both `{u,w}` and `{v,w}` are edges, and each has
>   codegree `≥ 1` — the other of `u,v` is a common neighbour, e.g.
>   `v ∈ N(u) ∩ N(w)` for the edge `{u,w}`, since `{u,v} ∈ E` and
>   `w ∈ N(v)`. So `c({u,w}) = [{u,w} ∈ Ew]`, likewise at `v`; these terms
>   sum to `K(u,v)`.
> - `w ∈ (c)`: both `{u,w}` and `{v,w}` are non-edges, contributing
>   `−[codeg ≥ 1] = −[∈ A(F)]` each; these terms sum to `−R_c(u,v)`.
> - `w ∈ (a)`: `{u,w}` is an edge; `{v,w}` is a non-edge of codegree `≥ 1`
>   automatically (`u ∈ N(v) ∩ N(w)`), contributing `−1`. And
>   `c({u,w}) = +1` unless `{u,w}` is unclassified (codegree `≥ 1`, no
>   witness), where it is 0 — that is, `c({u,w}) = 1 − [w counted by U_a]`.
>   Net per `w`: `−[w counted by U_a]`; summed, `−U_a(u,v)`. Category (b)
>   symmetrically gives `−U_b(u,v)`. ∎

> **Corollary 3.8 (per-edge sufficiency).** For any graph and any edge,
>
>     D_inc(u,v)  ≤  1 − (Slack_c − K_B) − U_a − U_b − (R⁺ − K_A)
>                 ≤  1 − (Slack_c(u,v) − K_B(u,v)),
>
> hence `Slack_c ≥ K_B ⟹ D_inc ≤ 1`.
>
> *Proof.* Substitute Lemma 3.7(iii) into Theorem 3.6:
>
>     D_inc ≤ 1 + (−U_a − U_b − R_c + K) + B − R⁺
>           = 1 − U_a − U_b − (R_c − B) + K_A + K_B − R⁺
>           = 1 − (Slack_c − K_B) − U_a − U_b − (R⁺ − K_A),
>
> using `Slack_c := R_c − B` and 3.7(i). All of `U_a`, `U_b` and
> `R⁺ − K_A` are `≥ 0` — the first two as cardinalities, the third by
> 3.7(ii). ∎
>
> The induction of §3.11 consumes only the `Ew`-scoped instance of this
> corollary (Proposition 3.10 supplies `Ew` edges), but the statement holds,
> as proved, for arbitrary edges.

> **Theorem 3.9 (the `E0` case).** For any graph `F` and any `E0` edge
> `{u,v}` — that is, `codeg(u,v) = 0` — we have
> `D(F) − D(F − {u,v}) ≤ 1`.
>
> *Proof.* Since `codeg(u,v) = 0` we have `W_uv = ∅`, so category (d) is
> empty and `K = K_A = K_B = 0`. By Theorem 3.6 (dropping `R⁺ ≥ 0`) and
> 3.7(iii),
>
>     D_inc ≤ 1 + S + B = 1 − U_a − U_b − R_c + B ≤ 1 + (B − R_c),
>
> so it remains to prove **`B(u,v) ≤ R_c(u,v)`**.
>
> *The injection.* Let `e = {w,z} ∈ B(u,v)`: remote, in `Ew(F)`, with
> `∅ ≠ Wit(e) ⊆ {u,v}`. Choose `x ∈ {u,v}` a witness of `e` — canonically,
> `x = u` if `u ∈ Wit(e)`, else `x = v`. A vertex witnesses `e` at exactly
> one endpoint (a witness is adjacent to the far endpoint and non-adjacent
> to the near one); say `x` witnesses `e` at `w`, so `xw ∉ E` and
> `N(x) ∩ N(w) = {z}`.
>
> Then `w ∈ category (c)`: `w ∉ N(x)` is given, and `w ∈ N(x′)` — with `x′`
> the other of `u,v` — would give `x′ ∈ N(x) ∩ N(w) = {z}` (note
> `x′ ∈ N(x)` since `{u,v} ∈ E`), i.e. `x′ = z`, contradicting
> `z ∉ {u,v}`. And `{x,w} ∈ A(F)`: it is a non-edge with `z ∈ N(x) ∩ N(w)`.
> So `(x,w)` is one of the `R_c(u,v)` instances.
>
> *Injectivity.* From `(x,w)` recover `z` as the unique element of
> `N(x) ∩ N(w)`, hence `e = {w,z}`; so distinct B-edges yield distinct
> instances. Hence `B ≤ R_c` and `D_inc ≤ 1`. ∎

> **Proposition 3.10 (pigeonhole).** If `Σ(F) ≥ 0` and `Ew(F) ≠ ∅`, then
> some `{u,v} ∈ Ew(F)` has `Slack_c(u,v) ≥ K_B(u,v)`.
>
> *Proof.* A finite non-empty sum of strictly negative integers is
> negative. ∎

### 3.11 Proof of Theorem A, assuming Theorem Σ

By Proposition 3.1 it suffices to prove `D(F) ≤ ⌊n/2⌋` for every graph `F`,
which we do by strong induction on `n`.

**Base `n ≤ 1`:** there are no pairs, so `D = 0 ≤ ⌊n/2⌋`.

**Step `n ≥ 2`:** exactly one of the following holds.

1. **`E0(F) ≠ ∅`.** Take any `E0` edge `{u,v}`. Theorem 3.9 gives
   `D_inc ≤ 1`, so by the induction hypothesis applied to the graph
   `F − {u,v}` on `n − 2` vertices,
   `D(F) ≤ 1 + D(F − {u,v}) ≤ 1 + ⌊(n−2)/2⌋ = ⌊n/2⌋`,
   the last equality using `n ≥ 2`.
2. **`E0(F) = ∅` and `Ew(F) = ∅`.** Every edge then has codegree `≥ 1` and
   no witness, so no edge contributes `+1`, and
   `D(F) = −|A(F)| ≤ 0 ≤ ⌊n/2⌋` directly.
3. **`E0(F) = ∅` and `Ew(F) ≠ ∅`.** Theorem Σ applies to `F`, since it
   assumes only `E0(F) = ∅` — in particular no connectedness, so
   disconnection during the induction is harmless. Proposition 3.10 yields
   an `Ew` edge with `Slack_c ≥ K_B`; Corollary 3.8 gives `D_inc ≤ 1` for
   that edge; conclude as in case 1. ∎

---

## 4. Proof of Theorem Σ

Throughout this section `F` is a finite simple graph with **`E0(F) = ∅`**,
i.e. every edge has codegree `≥ 1`. Connectedness is never used.

### 4.1 Re-indexing: three unit types

Define:

- **R-unit**: a triple `(x,s,t)` with `s ∈ D2(x)`, `t ∈ Nw(x)`,
  `t ∉ N[s]`.
- **B-unit**: a pair `(e,f)` with `e, f ∈ Ew(F)` vertex-disjoint and
  `Wit(e) ⊆ f`.
- **K-unit**: a pair `((x,z),t)` with `{x,z} ∈ Ew(F)`, `Wit_x(z) ≠ ∅`,
  `Wit_z(x) = ∅`, and `t ∈ Nw(x) ∩ N(z)`.

> **Identity 4.1.** `Σ(F) = #R − #B − #K`. The equality moreover holds
> **pairwise** against the three per-pair sums.
>
> - **`#R = Σ_{Ew} R_c`.** Bijection: an R-unit `(x,s,t)` corresponds to the
>   pair `{x,t}` (an `Ew` edge, since `t ∈ Nw(x)`) together with the
>   category-(c) `A`-instance `(x,s)`. Indeed `t ∉ N[s] ⟺ s ∉ N[t]`, and
>   "`s ∉ N(x)`, `s ∉ N(t)`, `s ∉ {x,t}`, `{x,s} ∈ A`" is precisely
>   "`s ∈ category (c) of {x,t}` and `{x,s} ∈ A`".
> - **`#B = Σ_{Ew} B`.** For fixed `f = {u,v} ∈ Ew`, the edges `e` with
>   `e ∩ f = ∅` and `Wit(e) ⊆ f` are by definition the `B(u,v)`-counted
>   edges.
> - **`#K = Σ_{Ew} K_B`.** For a fixed ordered edge `(x,z)` carrying a
>   witness at `x` and none at `z`, the pairs `{u,v}` in which `{x,z}` is a
>   `K_B` edge are exactly the pairs `{x,t}` with `t ∈ Nw(x)` (the pair must
>   be an `Ew` edge) and `z ∈ W_{x,t}`, i.e. `t ∈ N(z)`. ∎

So it suffices to construct an **injection** `φ` from
`(B-units ⊔ K-units)` into R-units.

### 4.2 Four elementary facts

**(P1)** For fixed `x` the sets `Wit_x(z)`, `z ∈ N(x)`, are pairwise
disjoint: `y ∈ Wit_x(z)` determines `z` as the unique common neighbour of
`x` and `y`.

**(P2)** If `y ∈ Wit_x(z)`, then every `t ∈ N(x) ∖ {z}` satisfies
`t ∉ N[y]`. *(Here `t ≠ y` since `y ∉ N(x)`; and `t ∈ N(y)` would put
`t ∈ N(x) ∩ N(y) = {z}`.)*

**(P3)** If `y ∈ Wit_x(z)` and `t ∈ Nw(x) ∩ N(z)`, then **both** `(x,y,t)`
and `(t,y,x)` are R-units.

*Proof.* `t ≠ z` since `z ∉ N(z)`, so `t ∈ N(x) ∖ {z}` and `t ∉ N[y]` by
(P2). For `(x,y,t)`: `y ∈ D2(x)`, since `xy ∉ E` and `z` is a common
neighbour; `t ∈ Nw(x)`; `t ∉ N[y]`. For `(t,y,x)`: `x ∈ Nw(t)` because
`{x,t} ∈ Ew`; `y ∈ D2(t)` since `ty ∉ E` by (P2) and `z ∈ N(t) ∩ N(y)`; and
`x ∉ N[y]` since `xy ∉ E` and `x ≠ y`. ∎

**(P4) (exception lemma).** If `e = {a,b} ∈ Ew` and `Wit(e) = f` for an edge
`f` disjoint from `e`, then both witnesses lie at the **same** endpoint of
`e`.

*Proof.* Say `Wit(e) = {p,q}` with `p ∈ Wit_a(b)` and `q ∈ Wit_b(a)`. Then
`N(q) ∩ N(b) = {a}` gives `a ∈ N(q)`; and `q ∈ N(p)` since `f = {p,q}` is an
edge. Hence `q ∈ N(p) ∩ N(a) = {b}` — the witness condition of `p` at `a` —
i.e. `q = b`, contradicting `e ∩ f = ∅`. ∎

*(Note also: a vertex witnesses `e` at exactly one endpoint —
`y ∈ Wit_a(b)` forces `yb ∈ E` while `y ∈ Wit_b(a)` forces `yb ∉ E` — so
`|Wit(e)|` counts witness incidences with no double counting.)*

### 4.3 The assignment φ

**Choice convention.** Fix, for every ordered pair `(x,z)` with
`Wit_x(z) ≠ ∅`, a choice `y(x,z) ∈ Wit_x(z)`; canonically, the
minimum-index witness. **No property of this choice is used anywhere in the
argument** — see the choice-independence proposition at the end of §4.5.

**Order convention.** The 2-witness B-branch below picks "a free slot", so
`φ` becomes one definite map only after an order is fixed: all K-targets and
1-witness-B targets are placed first, then the 2-witness B-units are
processed in lexicographic order of `(e,f)`, each taking the
lexicographically smallest free slot in its two columns. §4.6 shows that the
column pairs of distinct 2-witness B-units are disjoint and that each
contains a free slot after the first stage, so **every** admissible order
yields an injective map with identical counts; the convention, like the
witness choice, is pure bookkeeping.

- **K-unit** `κ = ((x,z),t)`. Put `y := y(x,z)`.
  - **(T) "transfer"**: if `Wit({y,z}) = {x}`, then `φ(κ) := (t,y,x)`.
  - **(D) "direct"**: otherwise, `φ(κ) := (x,y,t)`.

  Both targets are R-units by (P3).

  *(The (T) test is well posed. The pair `{y,z}` is an edge: `y ∈ Wit_x(z)`
  gives `z ∈ N(x) ∩ N(y)`. It is moreover automatically in `Ew(F)` — it is
  witnessed, by `x`, via Proposition 2.1, and has codegree `≥ 1` by
  `E0`-freeness. So no "`{y,z} ∈ Ew`" clause is needed in the branch
  condition; stating one would create a phantom case. The same argument
  shows `{y(x,z), z} ∈ Ew` always; the branch test asks only whether `x` is
  its **only** witness.)*

- **B-unit** `β = (e,f)` with `|Wit(e)| = 1`. Say `Wit(e) = {x0}`, with
  `x0` witnessing at the endpoint `y` of `e = {y,z}`, and `f = {x0,s}` with
  `s` the other endpoint of `f`. Then `φ(β) := (x0,y,s)`.

  *(The endpoint `y` is uniquely determined by `x0` and `e`, so this is a
  definition and not a choice: a vertex witnesses an edge at exactly one of
  its endpoints, since `x0 ∈ Wit_y(z)` forces `x0 z ∈ E` whereas
  `x0 ∈ Wit_z(y)` would force `x0 z ∉ E` — the note at the end of §4.2.)*

  This is an R-unit: `y ∈ Wit_{x0}(z)` by Proposition 2.1, so `y ∈ D2(x0)`;
  `s ∈ Nw(x0)`; and `s ≠ z` by disjointness of `e` and `f`, so `s ∉ N[y]` by
  (P2).

- **B-unit** `β = (e,f)` with `|Wit(e)| = 2`. Then `Wit(e) = f` (since
  `Wit(e) ⊆ f` and `|f| = 2`), `f` is an `Ew` edge disjoint from `e`, and by
  (P4) both witnesses sit at one endpoint `y` of `e = {y,z}`: `f = {p,v}`
  with `p, v ∈ Wit_y(z)`. Then `φ(β) :=` any R-unit of the form `(p,y,∗)` or
  `(v,y,∗)` not already used; §4.6 proves one exists. *(`|Wit(e)| ≥ 3` is
  impossible for a B-unit, since `Wit(e) ⊆ f` and `|f| = 2`.)*

### 4.4 The codeg invariant

Call `(p,y,∗)` a **column** when `p ∈ Wit_y(z)` — equivalently, by
Proposition 2.1, when `y ∈ Wit_p(z)`. Then `z` is the unique common
neighbour of `p` and `y`, i.e. `codeg(p,y) = 1`.

> **INVARIANT.** Writing any `φ`-target as a triple `(c1,c2,c3)`:
> - every **B1-target** `(x0,y,s)` and every **(D)-target** `(x,y,t)` has
>   `codeg(c1,c2) = 1` — they lie in the genuine columns `(x0,y,∗)`,
>   `(x,y,∗)`;
> - every **(T)-target** `(t,y,x)` has `codeg(t,y) ≥ 2`.
>
> *Proof of the (T) half.* `ty ∉ E` by (P2), and `z ∈ N(t) ∩ N(y)`, so
> `codeg(t,y) ≥ 1`. If `codeg(t,y) = 1` then `N(t) ∩ N(y) = {z}`, so
> `t ∈ Wit_y(z)`: `t` witnesses `{y,z}` at `y`, whence
> `t ∈ Wit({y,z}) = {x}` by the (T) branch condition, i.e. `t = x`. That is
> impossible, since `t ∈ Nw(x) ⊆ N(x)` while `x ∉ N(x)`. ∎

A (T)-target therefore lies in **no** column, and any lemma about columns
must not be applied to it in isolation.

### 4.5 Column contents and injectivity

**(L1)** The R-units in the column `(p,y,∗)`, where `p ∈ Wit_y(z)`, are
exactly the `(p,y,s)` for `s ∈ Nw(p) ∖ {z}`.

*Proof.* For `s ∈ N(p)` we have `s ∉ N[y] ⟺ s ≠ z`, by (P2) applied to
`y ∈ Wit_p(z)` in one direction and `z ∈ N(y)` in the other. And
`z ∈ Nw(p)` always: the edge `{p,z}` is witnessed at `p` by `y`, via
Proposition 2.1, and has codegree `≥ 1` by `E0`-freeness. So the column has
exactly `dw(p) − 1` slots. ∎

**(L2)** Suppose a `φ`-target equals `(p,y,s)`, where `(p,y,∗)` is a column
with unique common neighbour `z`. Then:

1. if it is a **B1-target**: `Wit({y,z}) = {p}`;
2. if it is a **(D)-target**: it is `φ(((p,z),s))` with `y(p,z) = y`, and
   `Wit({y,z}) ≠ {p}`;
3. if it is a **(T)-target**: `Wit({y,z}) = {s}`.

*Proof.* **1.** A B1-target is `(x0,y0,s0)` with `x0 ∈ Wit_{y0}(z0)` and
`Wit({y0,z0}) = {x0}`; matching coordinates gives `x0 = p`, `y0 = y`, and
`z0 = z`, since `z0` is the unique common neighbour of `p` and `y`.
**2.** A (D)-target is `(x,y′,t)` with `y′ = y(x,z′) ∈ Wit_x(z′)` and the
(T) condition false; matching gives `x = p` and `y′ = y`, so
`N(p) ∩ N(y) = {z′} = {z}`. **3.** A (T)-target is `(t′,y′,x′)` with
`y′ ∈ Wit_{x′}(z′)`, `Wit({y′,z′}) = {x′}` and `t′ ∈ Nw(x′) ∩ N(z′)`;
matching gives `t′ = p`, `y′ = y`, `x′ = s`. Now `y ∈ Wit_s(z′)` means
`N(s) ∩ N(y) = {z′}`, so `z′ ∈ N(y)`; and `t′ = p ∈ N(z′)` gives
`z′ ∈ N(p)`. So `z′ ∈ N(p) ∩ N(y) = {z}` — using the column's singleton,
available by hypothesis here — hence `z′ = z` and `Wit({y,z}) = {s}`. ∎

*(L2.3's hypothesis — a (T)-target lying in a column — is unsatisfiable in
isolation, by the invariant. The clause is substantive only **jointly**, when
equality with a B1- or (D)-target is assumed for contradiction and the other
side supplies the column property. That is exactly, and only, how it is used
below.)*

**(L3) `φ` is injective on K-units and 1-witness B-units.**

*Same kind.* A B1-target `(x0,y,s)` determines its unit: `z` is the unique
common neighbour of `x0` and `y`, then `e = {y,z}` and `f = {x0,s}`. A
(D)-target `(x,y,t)` determines `((x,z),t)` with `z = cn(x,y)`. A (T)-target
`(t,y,x)` determines `((x,z),t)` with `z = cn(x,y)` — well defined because
`y = y(x,z) ∈ Wit_x(z)` makes `codeg(x,y) = 1`; note that this recovery
reads coordinates 2 and 3, and needs no column. For (D)/(D), equal triples
give the same `(x,z)` and the same `t`, and the chosen witness agrees
automatically because `y(·,·)` is a function; (T)/(T) is thereby a same-kind
case, fully handled by the recovery.

*Across kinds* — three cases, each drawing its singleton from the B1 or (D)
side:

- **B1 vs (D):** both targets lie in genuine columns; if they are equal,
  (L2.1) gives `Wit({y,z}) = {p}` and (L2.2) gives `Wit({y,z}) ≠ {p}` — a
  contradiction.
- **B1 vs (T):** immediate from the invariant, `codeg(c1,c2)` being 1 on the
  B1 side and `≥ 2` on the (T) side. *(Alternatively: the B1 side supplies
  `p ∈ Wit_y(z)`, hence the singleton `N(p) ∩ N(y) = {z}`; then (L2.3)
  yields `Wit({y,z}) = {s}` while (L2.1) yields `{p}`, so `s = p` —
  impossible, since `s ∈ Nw(p) ⊆ N(p)` and `p ∉ N(p)`.)*
- **(D) vs (T):** immediate from the invariant. *(Alternatively: the (D)
  side supplies `y ∈ Wit_p(z)`, hence `p ∈ Wit_y(z)` by Proposition 2.1 and
  the singleton; (L2.3) then forces `Wit({y,z}) = {s}`; but
  `p ∈ Wit_y(z) ⊆ Wit({y,z}) = {s}` gives `s = p`, impossible as above.)* ∎

> **Choice-independence proposition.** Every step of §§4.3–4.6 uses exactly
> three properties of the choice function: **(α)** `y(x,z) ∈ Wit_x(z)`;
> **(β)** the (T)/(D) branch test is evaluated at that same chosen `y`;
> **(γ)** `y(·,·)` is a function of the ordered edge `(x,z)` — used in the
> (D)/(D) same-kind recovery and in (L2.2) and §4.6's bound, where "the
> (D)-targets in column `(p,y,∗)`" exist only if `y(p,z) = y`. No
> minimality, index order, or other property of the choice appears anywhere.
> Hence the proof is valid for an **arbitrary** fixed choice function;
> "minimum-index" is pure convention.

### 4.6 (L4): every 2-witness B-unit has a private free slot

Let `β = (e,f)` with `e = {y,z}` and `Wit(e) = f = {p,v}`, where
`p, v ∈ Wit_y(z)` (§4.3, via (P4)). Consider the two columns `(p,y,∗)` and
`(v,y,∗)`; these are genuine columns, since `p, v ∈ Wit_y(z)`.

1. **No B1-target lies in either column.** By (L2.1) that would force
   `Wit({y,z}) = {p}` (respectively `{v}`), but `|Wit({y,z})| = 2`.
2. **No (T)-target lies in either column.** Immediate from the invariant of
   §4.4: column targets have `codeg(c1,c2) = 1`, whereas (T)-targets have
   `≥ 2`. *(Equivalently: the columns being genuine, (L2.3) would force
   `|Wit({y,z})| = 1`.)*
3. **The (D)-targets in the column `(p,y,∗)` number at most
   `|Nw(p) ∩ N(z)|`.** By (L2.2) they are among the `φ(((p,z),s))` for
   `s ∈ Nw(p) ∩ N(z)` — and there are none at all unless `y(p,z) = y` and
   `(p,z)` has no witness at `z`. Same at `v`.
4. By (L1) the column `(p,y,∗)` has `|Nw(p) ∖ {z}|` slots, so its free slots
   number at least
   `|Nw(p) ∖ {z}| − |Nw(p) ∩ N(z)| = |Nw(p) ∖ N[z]|` (using `z ∉ N(z)`);
   same at `v`.
5. **Distinct 2-witness B-units have pairwise disjoint column pairs.** A
   shared column `(p,y,∗)` determines `z = cn(p,y)`, hence `e = {y,z}`,
   hence `f = Wit(e)` — the same unit. *(Two 2-witness B-units sharing the
   witness **edge** `f` but with different `e`'s have different hubs
   `z ≠ z′` and hence different columns; their free slots are physically
   disjoint, so there is no double-spending of Lemma A.)*
6. **Lemma A**, below, applied to the `Ew` edge `{p,v} = f` and the common
   neighbour `z ∈ N(p) ∩ N(v)` — available since `p, v ∈ Wit_y(z) ⊆ N(z)` —
   gives `|Nw(p) ∖ N[z]| + |Nw(v) ∖ N[z]| ≥ 1`.

So after all B1- and K-targets have been placed, each 2-witness B-unit finds
at least one free slot in its own private column pair, and the greedy
assignment succeeds regardless of order. ∎

> ### LEMMA A
> Let `F` be a graph with `E0(F) = ∅`, let `{p,v} ∈ Ew(F)`, and let
> `z ∈ N(p) ∩ N(v)`. Then `|Nw(p) ∖ N[z]| + |Nw(v) ∖ N[z]| ≥ 1`.
>
> *Proof.* Suppose `Nw(p) ⊆ N[z]` and `Nw(v) ⊆ N[z]`. The edge `{p,v}` lies
> in `Ew`, so it has a witness; the hypothesis is symmetric in `p` and `v`,
> so we may assume there is a witness `u` at `p`: `u ≠ p`, `up ∉ E`,
> `N(p) ∩ N(u) = {v}`.
>
> 1. `v ∈ N(u)`.
> 2. `u ∉ N[z]`: indeed `u ≠ z`, since `z ∈ N(p)` while `u ∉ N(p)`; and
>    `uz ∈ E` would give `z ∈ N(p) ∩ N(u) = {v}`, i.e. `z = v`, contradicting
>    `z ∈ N(v)`.
> 3. `{u,v} ∈ Ew(F)`: by Proposition 2.1, `u ∈ Wit_p(v)` gives
>    `p ∈ Wit_u(v)` — so `p` is a witness at `u` for the edge `{u,v}`, an
>    edge by step 1 — and `codeg(u,v) ≥ 1` because `E0(F) = ∅`. **This is
>    the proof's single essential use of `E0`-freeness.**
> 4. Hence `u ∈ Nw(v) ⊆ N[z]`, contradicting step 2. ∎

### 4.7 Conclusion

`φ` is well defined (§4.3, (P3), (L4)) and injective ((L3); the B1- and
K-targets are pairwise distinct, and none equals a 2-witness B-target, since
the latter are chosen among **unused** slots; distinct 2-witness B-targets
are distinct by (L4).5). Hence `#R ≥ #B + #K`, and by Identity 4.1,
**`Σ(F) ≥ 0`**. ∎

### 4.8 Hypothesis accounting

**`E0(F) = ∅` is used exactly three times**, all three instances of the same
one-line upgrade — *"an edge that is witnessed and has codegree `≥ 1` lies in
`Ew`"* — at three distinct load-bearing places, none of them cosmetic:

1. **Lemma A, step 3.** Without it Lemma A is false. The smallest of many
   counterexamples among graphs with an `E0` edge has 4 vertices: the star
   `K_{1,3}` centred at `3` plus the edge `{0,2}` (graph6 `CV`). There
   `Ew = {{0,3},{2,3}}`, `Nw(0) = Nw(2) = {3}`, `Nw(3) = {0,2}`, and the
   conclusion fails at both `Ew` edges, with value 0.
2. **The (T)/(D) branch test** (the note in §4.3). Without it (L2.2) is
   **false** — (D)-targets appear in columns with `Wit({y,z}) = {p}` —
   the smallest counterexample being at `n = 5` (graph6 `DUw`). That is, the
   truth value of a stated lemma changes, not merely a convenience.
3. **(L1)'s slot count**, namely `z ∈ Nw(p)`. It fails directly without
   `E0`-freeness, already on the path `P3` (graph6 `BW`): there the column
   `(0,1,∗)` has unique common neighbour `2`, but `{0,2}` is an `E0` edge,
   so `z ∉ Nw(p)` and (L1)'s count is wrong.

Connectedness is never used. No selection rule, no minimality hypothesis and
no per-pair Hall argument appears anywhere; the (T) branch moves charge
between different vertices' columns, and that is essential (§5.3).

### 4.9 A worked hard instance

The following 16-vertex graph is the smallest instance known to us with a
**negative** per-edge summand. In graph6 it is

>     OfzHewQcNqEQCXS`aV?`k

(21 characters; the fifteenth and twentieth are backquotes). Its adjacency
lists are:

     0: 1 3 4 5 7 9 10             8: 3 6 9 12 14 15
     1: 0 3 4 5 7 10 13            9: 0 3 8 11 14 15
     2: 3 4 6 10 11               10: 0 1 2 3 4 7 14
     3: 0 1 2 6 7 8 9 10          11: 2 3 6 9 12 13 15
        11 12 13 14 15            12: 3 7 8 11 13 15
     4: 0 1 2 5 7 10              13: 1 3 6 11 12
     5: 0 1 4 7                   14: 3 6 8 9 10
     6: 2 3 8 11 13 14            15: 3 8 9 11 12
     7: 0 1 3 4 5 10 12

It has 51 edges and is `E0`-free. The edge `{4,5}` has `codeg = 3`,
`R_c = 11`, `B = 6`, `K_A = 0` and `K_B = 6`, so `Slack_c − K_B = −1`, and
indeed `D_inc(4,5) = +2 > 1`: the per-edge certificate genuinely fails at
`{4,5}`, and `D_inc` sits exactly on Corollary 3.8's composed bound.

Nevertheless `Σ(F) = +111`. There are 170 R-units, 25 B-units and 34
K-units, so Identity 4.1 reads `170 − 25 − 34 = 111`; and the assignment `φ`
places 28 (D)-targets, 6 (T)-targets, 22 B1-targets and 3 two-witness-B
targets — 59 distinct R-units, leaving `170 − 59 = 111 = Σ(F)` free. The
three two-witness B-units here are "ideal columns" of the pair `{4,5}` — the
local deficit mechanism — each rescued by Lemma A's free slot.

This instance refuted every locally-paying variant of Theorem Σ that we
tried; see §5.3.

---

## 5. Tightness, and closing remarks

### 5.1 Where Theorem Σ is tight

`min Σ = 0` for every `n` with `5 ≤ n ≤ 10`, verified exhaustively over the
connected `E0`-free graphs with `Ew ≠ ∅`. Since Theorem Σ gives `Σ ≥ 0`, the
value 0 is a genuine minimum; and it is attained for **every** `n ≥ 5` if
disconnected graphs are admitted, as `Σ` is additive over components and the
butterfly `F_2` (which is `E0`-free with `Ew ≠ ∅` and has `Σ = 0`) may be
padded with isolated vertices. Two distinct mechanisms realise the value 0:

1. **Vacuous tightness — the friendship graphs (windmills) `F_k`, `k ≥ 2`.**
   The hub is universal, so category (c) is empty for every pair, no two `Ew`
   edges are disjoint, and `Nw(x) ∩ N(z)` is empty for every K-candidate:
   `#R = #B = #K = 0` and `φ` is the empty map.
2. **Full-capacity tightness** — connected `E0`-free graphs on which `φ` is a
   **perfect bijection** onto the R-units, every column exactly full. The two
   smallest have 6 vertices (graph6 `EElw`, `EUzW`); there are 9 at `n = 7`,
   61 at `n = 8` and 555 at `n = 9`. On all of them every K-unit takes the
   (T) branch, and the transfer targets exactly exhaust the codegree-`≥2`
   triples. In `EElw` — the triangle `3-4-5` with rim vertices `0,1,2`
   attached to its three edges — six B1-units fill the six codegree-1 columns
   and six K-units transfer onto the six codegree-`≥2` triples: `Σ = 0` with
   zero slack anywhere.

Two structural facts locate **all** the slack of the proof. First,
**B1-targets fill their columns exactly full in every graph**: a
unique-witness B-edge `e = {y,z}` with `Wit(e) = {x0}` generates exactly
`dw(x0) − 1` B-units, and by (L1) the column `(x0,y,∗)` has exactly
`dw(x0) − 1` slots. Second, **Lemma A's bound is achieved** —
configurations with `|Nw(p) ∖ N[z]| + |Nw(v) ∖ N[z]| = 1` occur, already at
`n = 5`. The codegree invariant of §4.4 is therefore the single load-bearing
seam of the whole assignment: it is exactly what keeps (T)-targets off the
always-full B1 columns.

For Theorem A itself: perfect matchings and `K_{n/2,n/2}` attain
`D = ⌊n/2⌋`, hence `Φ = ⌊n²/2⌋`. *(For a perfect matching every pair of
vertices has disjoint neighbourhoods, so `disj = C(n,2)`, `X = 0` and
`Φ = n/2 + C(n,2) = n²/2`. For `K_{n/2,n/2}` every edge has codegree 0 and
every non-edge codegree `n/2`, so `D = n²/4 − 2·C(n/2,2) = n/2`.)*

### 5.2 Per-edge deficits are real and unbounded

The per-edge certificate `Slack_c ≥ K_B` of Corollary 3.8 **fails** on
individual edges. The 16-vertex instance of §4.9 has an edge with
`Slack_c − K_B = −1` and `D_inc = +2`. Moreover an explicit *t-column gadget*
family — vertices `u`, `v`, hubs `h_1 … h_t`, columns `w_1 … w_t` and four
auxiliary vertices `p, p2, q, r`, so `n = 2t + 6`; edges `u–v`; `u,v–h_i` for
all `i`; the hub clique; `h_i–w_i`; `u–p`, `u–p2`, `p–p2`; `q–p`, `q–p2`,
`q–h_i`; `r–h_i`, `r–w_i`, `r–q` — achieves `Slack_c − K_B = 4 − t` at the
edge `{u,v}`, an arbitrarily large **local** deficit, while `Σ` grows as
`Θ(t²)`.

The global sum pays local deficits from elsewhere. This is why Theorem Σ is
stated, and provable, only in aggregate.

### 5.3 Failed strengthenings, recorded to save the reader the search

Each of the following natural strengthenings of Theorem Σ is **false**, with
small or moderate counterexamples:

1. every **per-edge** form — both orientations of any single edge summed —
   fails at the §4.9 instance;
2. every **fixed selection rule** of the form "the edge minimising or
   maximising a given local statistic has `D_inc ≤ 1`" fails; seven distinct
   rules were refuted, the last at `n = 16–25`;
3. a **per-pair matching** (Hall-type) version of the injection, confined to
   each edge's own R-units, fails on the tight instances of §5.1.2.

The transfer branch — paying at a **different** vertex — is therefore not an
artefact of our proof: some cross-edge payment is forced. This is the
finite, internal counterpart of Loh and Ma's construction [LM16], which rules
out the local certificate one would most like to have.

### 5.4 Open questions

1. **Unconditional Σ.** Theorem Σ's hypothesis `E0(F) = ∅` is essential to
   the **proof** — each of the three uses in §4.8 has an explicit
   counterexample when it is dropped, starting at `n = 3–5` — but apparently
   not to the **truth**: `Σ(F) ≥ 0` holds exhaustively on all 197,960
   connected graphs with `E0 ≠ ∅` and `Ew ≠ ∅` up to `n = 9`, with minimum
   exactly 0, even though Lemma A itself fails on 77.5% of them. The
   unconditional statement *"`Σ(F) ≥ 0` whenever `Ew(F) ≠ ∅`"* is left open.
   It is **not** needed for Corollary B: the `E0 ≠ ∅` branch of the induction
   is discharged by Theorem 3.9 before Theorem Σ is ever invoked.
2. **A non-bipartite refinement.** The conjectured extremal family for the
   problem restricted to **non-bipartite** D2C graphs is the balanced
   twin-expansions of the 5-cycle, with `⌊(n−1)²/4⌋ + 1` edges (a conjecture
   of Balbuena, Hansberg, Haynes and Henning, as cited in [DFH19]; open in
   general, proved for triangle-free graphs). Whether the present machinery
   — which is exact on windmills and on the full-capacity family — can be
   sharpened to that bound is open; the behaviour of `Σ` on `C_5` expansions
   is a natural first probe.
3. **The equality characterisation (MS-eq).** Not addressed here; see §1.5
   for what is and is not established, and for why an all-`n` bound does not
   by itself discharge Füredi's stability analysis.

---

## 6. Formal verification

The result of this paper has been formalised in the Lean 4 proof assistant.
The formalisation is the file `Erdos742.lean` accompanying this paper in the
same repository; it is self-contained apart from mathlib.

- **Axiom status.** `#print axioms` on the main theorem reports
  `[propext, Classical.choice, Quot.sound]` — the three standard axioms of
  Lean's classical foundation. No `sorryAx`, and no additional axiom.
- **What is formalised.** The Lean main theorem is machine-checked to be the
  `erdos_742` statement of the `google-deepmind/formal-conjectures`
  repository, with that statement's `answer(…) ↔` wrapper instantiated. Since
  mathlib's `SimpleGraph.diam` is `ℕ`-valued and returns `0` on a
  disconnected graph, "`diam(G − e) > 2`" is not literally expressible as a
  numeric inequality there; the file therefore *proves* the bridge between
  the criticality predicate used in the formalisation and the one used in
  this paper, rather than assuming it.
- **The single `sorry`.** The Lean file contains exactly one unproved
  declaration, and it is a **negative** statement — the assertion of §5.3
  that the per-edge form of Theorem Σ is false, which is established by
  counterexample search and is not transcribed into Lean. It is an input to
  nothing: it is not reachable from the main theorem, whose axiom status
  above is stated with that declaration in the file.
- **Transcription fidelity.** The correspondence between the prose of this
  paper and the Lean text is documented in the repository, including known
  minor divergences — places where a Lean statement is deliberately narrower
  than, or differently packaged from, the paper statement it is named for.
  Those divergences concern the *presentation*; they do not touch the chain
  from the axioms to the main theorem. The validity of the formalised
  theorem rests on the Lean kernel and on the fidelity of the formal
  statement to the problem, not on the prose of this paper.

**Status.** This is a *claimed* proof. It has been extensively
machine-audited and formalised, and it has **not** yet been peer-reviewed by
human mathematicians. Readers should treat it accordingly.

---

## Appendix A. Verification record

**Nothing in this appendix is part of the proof. It is a check on the
proof.**

**No step of the proof closes by exhaustion.** Every statement in §§2–4 is
proved by hand from the definitions, and the only external theorem the paper
mentions — Mantel's — is a *consequence* (§1.2), not an input. A reader who
distrusts every computation reported below loses nothing but reassurance.
The machine results that are not merely confirmatory are confined to
statements that nothing depends on: the tightness counts of §5.1, the
negative results of §5.3, the counterexamples of §4.8 (all of which are
small enough to verify by hand — `CV` has 4 vertices, `DUw` 5, `BW` 3), and
the numbers reported for the §4.9 instance.

**Theorem Σ and the assignment `φ`.** Five independent implementations —
written from the prose, with no shared code between any two, each first
validated against the standard enumeration counts A000088/A001349 and
against fixed reference instances — verified, per graph: the re-indexing
Identity 4.1 against the per-pair definition of `Σ`; that every `φ`-target
is an R-unit; pairwise distinctness of all targets; the codegree invariant
on every placed target; (L1) column membership; column-pair disjointness;
(L4) free-slot existence; and `#free R-units = Σ(F)`.

Populations: all 50,283 connected `E0`-free graphs with `Ew ≠ ∅` on `n ≤ 9`
vertices; all 2,403,312 such graphs on `n = 10` (three independent pipelines
agreeing on the census total 2,453,595 for `n ≤ 10`); the §4.9 instance;
about 700 adversarial constructions (random graphs repaired to
`E0`-freeness, up to `n = 60`; bridge grafts; simulated-annealing
`Σ`-minimisers at `n = 12…25`); and the gadget family of §5.2 to `t = 12`.
**Zero failures.** One implementation ran every graph under both a
minimum- and a maximum-index witness-choice function; another enumerated
**all** admissible choice functions on 1,672 of the 1,835 in-scope 8-vertex
graphs (241,815 functions, three greedy orders each) and ran about 1.45
million randomised choice/order combinations at `n = 9`. `min Σ = 0` at
every `n ∈ [5,10]`, and `Σ` is additive over components (verified on all
`E0`-free graphs with `n ≤ 8`, including disconnected ones).

**Lemma A separately:** exhaustively for `n ≤ 9`; on 1,906 random
`E0`-free graphs with `n = 12…60`; and exhaustively at `n = 10`
(19,682,018 witness instances). The `E0`-freeness controls fire exactly as
described in §4.8: dropping the hypothesis produces Lemma-A violations
(6,912 connected graphs at `n ≤ 8`, the smallest being `CV` at `n = 4`),
(L2.2) violations (from `DUw`, `n = 5`), and saturated two-witness
configurations with no free slot (from `n = 8`).

**Theorem A directly:** `D(F) ≤ ⌊n/2⌋` verified on all 2,131,018 labelled
graphs with `2 ≤ n ≤ 7`, and on all unlabelled graphs with `n = 8, 9, 10` —
connected **and** disconnected — that is 12,346 + 274,668 + 12,005,168
graphs, the last matching A000088(10) exactly. Zero violations, with
`max D = 5 = ⌊10/2⌋` attained at `n = 10`.

**Corollary 3.8's composed inequality directly**, with `D_inc` computed by
actual deletion of both vertices and Lemma 3.7's identities asserted per
pair: every `Ew` edge of every connected `E0`-free graph with `Ew ≠ ∅` at
`n = 8, 9, 10` — 9,070 + 267,777 + 14,564,197 edges — zero violations;
exactly tight on 16.0% of the `n = 10` instances and on the §4.9 instance's
edge `{4,5}`.

**Corollary B directly:** `Φ = 2e` and `e ≤ ⌊n²/4⌋` verified on all 52
diameter-2-critical graphs with `n ≤ 8`; the D2C enumeration counts of
[KS21] reproduce independently at those orders.

**An independent re-check performed for the present write-up**, with fresh
code written from this paper's text alone: Theorem A on all unlabelled
graphs with `n ≤ 8` (11, 34, 156, 1044, 12346 graphs at `n = 4…8`, matching
A000088), maximum margin `D − ⌊n/2⌋ = 0` at every order; and Identity 4.1,
`φ`'s well-definedness, injectivity, free-slot existence and
`#free = Σ ≥ 0` on all connected `E0`-free graphs with `Ew ≠ ∅` at
`n = 5…9` — 2, 12, 127, 1835 and 48,307 graphs respectively, totalling
50,283 for `n ≤ 9` and so reproducing the census above. Zero failures;
`min Σ = 0` at each order. The §4.9 instance was re-derived from its graph6
string and every number quoted for it in §4.9 reproduced exactly.

**On proof assistants.** Corollary B has been formalised in Lean 4 and
machine-checked; the formalisation, its axiom status, its one unproved
negative declaration, and the known divergences between it and this paper's
prose are described in §6. That formalisation is the definitive verification
of the result; everything else in this appendix is corroboration.

Per §0, the honest summary of the computational checks above is *"no
counterexample found"*, and for the hand arguments *"no gap found after
several independent passes"* — never *"gap-free"*.

---

## Appendix B. Note on the citations

Citations in this paper carry different weights, and we state them rather
than let a uniform bibliography imply a uniform standard.

- **[Fü92] — consulted in the original.** The quotations in §1.2 and §1.5
  are verbatim, with page numbers. Füredi's Lemma 2.1 (p. 83) and the
  definition of `disj F` (p. 82) are as quoted, and the interface statement
  quoted in §1.5 is from p. 87.
- **[F87] — consulted in the original.** Fan states his Conjecture (p. 235)
  *with* the equality clause, but his Theorem carries no equality clause in
  any of its three parts, and he closes the small-order case with an
  explicit Remark (p. 240): *"It can be checked in inequality (7) that for
  `n = 26` it is true that `e ⩽ [¼n²]`. But in both cases (`n ⩽ 24` and
  `n = 26`) we only prove affirmatively the first part of the conjecture."*
  Here *"the first part"* is the inequality, the second part of the
  conjecture being the uniqueness clause. **[F87] therefore supplies
  (MS-eq) at no `n`.** This also reconciles two secondary reports that
  appear to disagree: the publisher's abstract gives *"(i) `e ⩽ [¼n²]` for
  `n ⩽ 24`, and (ii) `e < ¼n² + (n² − 16.2n + 56)/320` (`< 0.2532n²`), for
  `n ⩾ 25`"*, while Füredi writes at [Fü92, p. 82] that *"Fan [6] proved
  affirmatively the first part of the Conjecture 1.1 for `n ≤ 24` and for
  `n = 26`."* The `n = 26` case is the Remark above rather than part (i) of
  the Theorem, so both reports are accurate.
- **[DFH19] — consulted in the original** (the arXiv and journal versions
  agree on the passages we mention). Our use of it here is purely
  terminological: Definition 5's notion of a critical pair, cited in §1.2 to
  locate our witness relation in the literature, and the attribution of the
  non-bipartite conjecture in §5.4. **No result of [DFH19] is used in any
  proof in this paper.**
- **[P75], [CH79], [HHY11], [HW03], [KS21], [LM16] — secondary
  attributions.** These are reported as they appear in the survey
  literature; we have not re-checked them against the originals. **None of
  them is used in any proof in this paper**, and the reader should take the
  history of §1.1 as orientation rather than as an audited record.
- **⚠ The dominating-edge class.** The published
  Haynes–Henning–van der Merwe–Yeo results on graphs with a dominating edge
  are, as published, for graphs of **even order**. We have not located a
  manuscript completing the odd case, and we make no claim that the class is
  fully settled in the literature. Nothing here depends on it.

---

## References

[BHHH] C. Balbuena, A. Hansberg, T. W. Haynes, M. A. Henning, the
non-bipartite conjecture (`⌊(n−1)²/4⌋ + 1`) as cited in [DFH19]. **Open**;
proved for triangle-free graphs.
*(We know this conjecture only as cited in [DFH19]; exact bibliographic
details are not pinned down here.)*

[CH79] L. Caccetta, R. Häggkvist, *On diameter critical graphs*, Discrete
Math. **28** (1979) 223–229.

[DFH19] A. Dailly, F. Foucaud, A. Hansberg, *Strengthening the Murty–Simon
conjecture on diameter 2 critical graphs*, Discrete Math. **342**(11) (2019)
3142–3159, DOI 10.1016/j.disc.2019.06.023, arXiv:1812.08420.

[F87] G. Fan, *On diameter 2-critical graphs*, Discrete Math. **67** (1987)
235–240.

[Fü92] Z. Füredi, *The maximum number of edges in a minimal graph of
diameter 2*, J. Graph Theory **16** (1992) 81–98.

[HHY11] T. W. Haynes, M. A. Henning, A. Yeo, *A proof of a conjecture on
diameter 2-critical graphs whose complements are claw-free*, Discrete Optim.
**8** (2011) 495–501.

[HW03] D. Hanson, P. Wang, *A note on extremal total domination edge
critical graphs*, Util. Math. **63** (2003) 89–96.

[KS21] M. Kirchweger, S. Szeider, *SAT modulo symmetries for graph
generation*, CP 2021; extended version ACM Trans. Comput. Log. **25** (2024).

[LM16] P.-S. Loh, J. Ma, *Diameter critical graphs*, J. Combin. Theory
Ser. B **117** (2016) 34–58.

[M07] W. Mantel, *Problem 28*, Wiskundige Opgaven **10** (1907) 60–61.

[P75] J. Plesník, *Critical graphs of given diameter*, Acta Fac. Rerum
Natur. Univ. Comenian. Math. **30** (1975) 71–93.

*(Except where Appendix B states otherwise, the venue data above is compiled
from secondary sources and has not been re-checked against the primary
sources.)*
