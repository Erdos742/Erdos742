# The equality clause of the Murty–Simon conjecture

**Author:** Claude Code

This proof was found, written, and formalized by a multi-agent AI research
campaign (Claude, Anthropic); its Lean formalization (§E.6.1) is the
campaign's machine-checked record, and the verification of the formal
statement is deliberately independent of that provenance.

**Companion paper.** This is Part II of a two-part work. Part I,
*"Every diameter-2-critical graph on `n` vertices has at most `⌊n²/4⌋`
edges"* (`paper-742-inequality.md`, Lean-verified as
`Erdos742.lean`), proves the inequality clause (MS-ineq) — Erdős
Problem #742 as posed — and is cited throughout below as a black box; none of
its proofs are restated. This paper proves the **equality** clause (MS-eq):
that `K_{⌈n/2⌉,⌊n/2⌋}` is the *unique* graph attaining that bound. (MS-eq) is
not part of Erdős #742 and Part I explicitly does not address it (Part I §1.5).

**Provenance.** (MS-eq) is **[CH79, Conjecture 1]** (Caccetta–Häggkvist,
*Discrete Math.* **28** (1979), 223–229), attributed there to Murty and Simon
via private communication. The witness/criticality apparatus this paper
inherits from Part I is, at origin, **[CH79] p. 224's "extremal triple"**
construction (1979) — not [DFH19, Definition 5] (2019), which restates it
decades later. Citations below follow this provenance.

---

## Abstract

We prove the equality clause of the Murty–Simon conjecture: among
diameter-2-critical (D2C) graphs on `n ≥ 3` vertices, the balanced complete
bipartite graph `K_{⌈n/2⌉,⌊n/2⌋}` is the *unique* graph attaining
`⌊n²/4⌋` edges. Building on Part I's inequality machinery as a black box, we
show that the equality class of Part I's central quantity `D` — the graphs
`F` with `D(F) = ⌊n/2⌋` — is exactly the class `𝓑` of disjoint unions of
balanced complete bipartite graphs with at most one component of odd order.
The proof is a two-vertex-deletion induction, identical in shape to Part I's
own induction for the inequality: an exact identity for the deletion
increment `D_inc`, evaluated in closed form on `𝓑`, forces every tight
two-vertex extension of a member of `𝓑` back into `𝓑`. Combined with Part I's
own scope lemma relating `D` to the D2C edge count, this yields (MS-eq). No
part of the proof depends on any enumeration; the bound is fully explicit and
elementary, exactly as in Part I.

---

## §E.0. Preliminaries

This paper is written to be **statement-complete against Part I as a black
box**: every Part I definition and result used below is restated verbatim
here, with its Part I citation, so that this paper is readable and verifiable
without re-deriving Part I's proofs. Nothing in Part I is modified,
generalized, or re-proved here.

We open with the exact scope of what the argument below pays for, stated
once and to be taken at face value throughout:

> *"(STEP) itself uses no Theorem Σ, no Theorem A, no Theorem 3.9, not
> TA-TF-EQ; the corollary inherits Part I's whole stack — Theorem Σ included
> — exactly once, through the induction. prover-sigma's diagnosis is NOT
> refuted."*

(Here "(STEP)" names the technical heart of this paper, §E.4 below;
"the corollary" names the induction of §E.5 that consumes it; and
"prover-sigma" names the campaign seat whose dependency diagnosis the
quoted sentence addresses. The sentence says precisely which of Part I's
results are spent, and where: not in the technical heart, but once, in the
induction that assembles it into the `n`-vertex statement.)

### E.0.1 Definitions (restated verbatim from Part I, with citation)

`F` is a finite simple graph; `V(F)` its vertex set, `n := |V(F)|`, `E(F)` its
edge set, `e(F) := |E(F)|`. `N(x)` is the open neighbourhood of `x`,
`d(x) := |N(x)|`. `codeg(x,y) := |N(x) ∩ N(y)|` for any unordered pair
(edge or not). [Part I §2, printed verbatim.]

* **Diameter-2-critical (D2C).** `G` has diameter exactly `2`, and for every
  edge `e ∈ E(G)`, `diam(G − e) > 2`. [Part I §1.1.]
* **Witness.** For an edge `{x,z} ∈ E(F)`, a *witness at `x`* is a vertex
  `y ≠ x` with `xy ∉ E` and `N(x) ∩ N(y) = {z}`. `Wit_x(z)` is the set of
  such `y`; `Wit(e) := Wit_a(b) ∪ Wit_b(a)` for `e = {a,b}`. [Part I §2.]
* **`E0(F)`, `Ew(F)`, `A(F)`.** `E0(F)` := edges of codegree `0`. `Ew(F)` :=
  edges of codegree `≥ 1` with `Wit(e) ≠ ∅`. `A(F)` := non-edges `{x,s}` with
  `codeg(x,s) ≥ 1`. A pair in neither `E0(F) ∪ Ew(F)` nor `A(F)` — i.e. an
  edge of codegree `≥ 1` with no witness — is **unclassified**. [Part I §2.]
* **`c(P,F)`, `D(F)`, `D_inc`.** For an unordered pair `P`,
  `c(P,F) := +1` if `P ∈ E0(F) ∪ Ew(F)`, `−1` if `P ∈ A(F)`, `0` if
  unclassified. `D(F) := Σ_P c(P,F) = |E0(F)| + |Ew(F)| − |A(F)|`. For an
  edge `{u,v}`, `D_inc(u,v) := D(F) − D(F − {u,v})`, where `F − {u,v}`
  deletes **both** vertices and all incident edges. [Part I §2, §3.3.]
* **`S(u,v)`, `U_a(u,v)`, `U_b(u,v)`, `R_c(u,v)`, `K(u,v)`.** For an edge
  `{u,v}`, partition `V(F) ∖ {u,v}` into categories (a) `N(u) ∖ N[v]`,
  (b) `N(v) ∖ N[u]`, (d) `W_{uv} := N(u) ∩ N(v)`, (c) the rest.
  `S(u,v) := Σ_{w ∉ {u,v}} [c({u,w},F) + c({v,w},F)]`.
  `U_a(u,v) := #{w ∈ (a) : codeg(u,w) ≥ 1, Wit({u,w}) = ∅}` (unclassified
  private neighbours of `u`); `U_b(u,v)` symmetrically at `v`.
  `R_c(u,v) := Σ_{w ∈ (c)} ([{u,w} ∈ A(F)] + [{v,w} ∈ A(F)])`.
  `K(u,v) := Σ_{w_0 ∈ W_{uv}} ([{u,w_0} ∈ Ew(F)] + [{v,w_0} ∈
  Ew(F)])`. [Part I §2, §3.3.]

Two symbols are genuinely new to this paper — everything else above is
Part I's own vocabulary, unrenamed. Both are attached to a fixed extension
configuration: `H` a graph on `V(H)`, `u,v ∉ V(H)`, `F` on `V(H) ∪ {u,v}`
with `{u,v} ∈ E(F)`, `N_F(u) = {v} ∪ S`, `N_F(v) = {u} ∪ T` for some
`S,T ⊆ V(H)` (arbitrary a priori).

* **`W(u,v)`** := the number of `H`-edges with both ends in `S`, or both ends
  in `T`, that are unclassified in `F` (union charging: an edge inside
  `S ∩ T` is charged once).
* **`Z(u,v)`** := the number of **non-adjacent** pairs `{x,y}` of `V(H)`
  with `codeg_H(x,y) = 0` **and** (`{x,y} ⊆ S` or `{x,y} ⊆ T`), union
  charging as for `W`. *(This is the repaired form — see the remark at the
  end of §E.3.1.)*

We also write `χ := [{u,v} is unclassified in F]`, so
`c({u,v},F) = 1 − χ`.

### E.0.2 The eight consumed results (restated verbatim from Part I, with citation)

Every result below is **proved in Part I**, Lean-verified with no `sorry`
(declaration names in brackets), and is used here strictly as a black box.

1. **Theorem A, `D`-form (Part I Theorem A + Proposition 3.1).**
   *For every graph `F` on `n` vertices, `D(F) ≤ ⌊n/2⌋`.*
   (Part I states Theorem A as `Φ(F) ≤ ⌊n²/2⌋`; Proposition 3.1 proves
   `Φ(F) = C(n,2) + D(F)` and that this makes Theorem A equivalent to the
   `D`-form above. [Part I §3, Theorem A + Prop. 3.1; Lean
   `row19_theorem_A`, `row02_D_normal_form`.])
2. **Proposition 3.2 (criticality inventory).** *In a D2C graph `G`, every
   edge lies in `E0(G) ∪ Ew(G)`; hence `Φ(G) = 2·e(G)`.*
   [Part I §3.2, Prop. 3.2; Lean `row03b_phi_eq_two_e`.]
3. **Lemma 3.4 (deletion decomposition).** *For any graph `F` and any edge
   `{u,v}`,*
   `D(F) − D(F′) = c({u,v},F) + S(u,v) + Σ_P [c(P,F) − c(P,F′)]`,
   *the last sum over remote pairs `P` (both vertices outside `{u,v}`),
   `F′ := F − {u,v}`.* [Part I §3.3, Lemma 3.4; Lean
   `row04_deletion_decomposition`.]
4. **Lemma 3.7(iii) (the `S`-identity).** *For any graph `F` and any edge
   `{u,v}`,*
   `S(u,v) = −U_a(u,v) − U_b(u,v) − R_c(u,v) + K(u,v)`.
   [Part I §3.3, Lemma 3.7(iii); Lean `row07iii_S_identity`.]
5. **Theorem 3.9 (the `E0` case).** *For any graph `F` and any `E0` edge
   `{u,v}` (`codeg(u,v) = 0`), `D_inc(u,v) ≤ 1`.*
   [Part I §3, Thm. 3.9; Lean `row09_E0_case`.]
6. **Theorem Σ.** *Let `F` be a finite simple graph with `E0(F) = ∅`. Then*
   `Σ(F) := Σ_{{u,v} ∈ Ew(F)} [Slack_c(u,v) − K_B(u,v)] ≥ 0`.
   [Part I §1.2/§4, Theorem Σ; Lean `row18_theorem_Sigma`.]
7. **Proposition 3.10 (pigeonhole).** *If `Σ(F) ≥ 0` and `Ew(F) ≠ ∅`, some
   `{u,v} ∈ Ew(F)` has `Slack_c(u,v) ≥ K_B(u,v)`.* [Part I §3, Prop. 3.10;
   Lean `row10_pigeonhole`.]
8. **Corollary 3.8 (per-edge sufficiency).** *For any graph and any edge,
   `Slack_c(u,v) ≥ K_B(u,v) ⟹ D_inc(u,v) ≤ 1`.*
   [Part I §3, Cor. 3.8; Lean `row08_cor`.]

Nothing else from Part I is used below. These eight results enter as
Part I's published, Lean-verified statements only: none was re-derived by
the reviewers of this paper's campaign, whose review covered §E.1–§E.6.
The corollary chain therefore inherits Part I's whole stack — Theorem Σ
included — on the terms Part I established for it, exactly once, through
the induction of §E.5.

---

## §E.1. The family `𝓑`, and its tightness

> **Definition (the family `𝓑`).** `H ∈ 𝓑` iff `H` is a disjoint union of
> components `C_i = K_{X_i,Y_i}` (complete bipartite, parts `X_i,Y_i`,
> `a_i := |X_i| ≥ b_i := |Y_i|`, `a_i − b_i ∈ {0,1}` — "balanced"), with
> **at most one** `C_i` of odd order. `K_1 = K_{1,0}` (`b_i = 0`) is admitted
> as a degenerate balanced complete bipartite component.

The `K_1`-in-family convention is a definitional choice, not a derived fact:
Part I's own convention for `K_{a,b}` requires `a,b ≥ 1` (§1.2); `𝓑` widens
this by declaration to admit `K_1`, because the induction of §E.5 needs it as
a legitimate base case, and `D(K_1) = 0 = ⌊1/2⌋` so nothing is broken by
admitting it.

We record the tightness of `𝓑` in two statements, deliberately kept separate
— the first is the one actually consumed downstream, and it is *not* a
special case that can be skipped in favour of the second.

> **FACT E.1a (single-class tightness).** *For a single balanced complete
> bipartite graph `K_{a,b}` (`a ≥ b ≥ 0`, `a − b ≤ 1`), `D(K_{a,b}) =
> ⌊(a+b)/2⌋`.*
>
> *Proof.* Every edge of `K_{a,b}` has codegree `0` (the two endpoints lie
> in different parts, and a complete bipartite graph has no edges inside a
> part to serve as a common neighbour), so `E0 = ab`, `Ew = ∅`. Every
> non-edge is a same-part pair: two vertices of `X` have common neighbourhood
> `Y`, of size `b`; two vertices of `Y` have common neighbourhood `X`, of
> size `a ≥ b ≥ 0`. So `A = C(a,2) + C(b,2)` (with the convention `C(0,2)=0`,
> covering `K_1` automatically). Hence
>
> `D(K_{a,b}) = ab − C(a,2) − C(b,2) = (a+b)/2 − (a−b)²/2`,
>
> which equals `(a+b)/2` if `a = b` and `(a+b−1)/2` if `a − b = 1` — i.e.
> `⌊(a+b)/2⌋` in both cases. This is the step where **balance** is used;
> nothing about an odd-component count enters. ∎

> **FACT E.1b (family tightness, general).** *For `H ∈ 𝓑` on `m` vertices,
> `D(H) = ⌊m/2⌋`.*
>
> *Proof, in three separately-attributed currencies — do not conflate them.*
> **(a) `D` is additive over connected components, unconditionally, with no
> hypothesis at all.** A pair of codegree `≥ 1` has a common neighbour, so
> both its ends lie in one component: `A(H)` contains no cross-component
> pair. A witness `y` at `x` for `{x,z}` satisfies `N(x) ∩ N(y) = {z} ≠
> ∅`, so `y` has a neighbour in `x`'s component and lies in it: `E0` and
> `Ew` are computed component-wise too. Hence `D(⊔_i C_i) = Σ_i D(C_i)`.
> **(b) `D(K_{a_i,b_i}) = ⌊(a_i+b_i)/2⌋`, by FACT E.1a — this is where
> balance is spent, component by component.**
> **(c) The `≤ 1`-odd-component clause converts `Σ_i ⌊m_i/2⌋` into `⌊m/2⌋`,
> and nothing else does this job.** `Σ_i ⌊m_i/2⌋ = (m − #odd(H))/2`, while
> `⌊m/2⌋ = (m − (m mod 2))/2`; since `#odd(H) ≡ m mod 2` always (a sum
> of orders has the parity of its number of odd summands), the two agree
> **iff `#odd(H) ≤ 1`.** ∎

Facts E.1a and E.1b are logically independent statements — E.1a is not "the
`m_i = m`, one-component instance" of E.1b's proof folded away; it is the
half of E.1b's proof, (a)+(b) restricted to one component, that §E.6 below
needs on its own, applied to a single *connected* D2C graph, without ever
summing over components. Both facts are elementary computations with no
further dependency.

---

## §E.2. Supply and tight-deletion

> **LEMMA SUPPLY.** *Every graph `F` on `n ≥ 2` vertices with `D(F) =
> ⌊n/2⌋` has an edge `{u,v}` with `D_inc(u,v) ≤ 1`.*
>
> *Proof.* If `E0(F) ≠ ∅`, take any `E0` edge: Theorem 3.9 (E.0.2 item 5)
> gives `D_inc ≤ 1` directly. If `E0(F) = ∅` and `Ew(F) = ∅`, every edge has
> codegree `≥ 1` and no witness, so `D(F) = −|A(F)| ≤ 0 < 1 ≤ ⌊n/2⌋` for
> `n ≥ 2` — contradicting `D(F) = ⌊n/2⌋`, so this branch cannot occur.
> Otherwise `E0(F) = ∅ ≠ Ew(F)`: Theorem Σ (item 6) gives `Σ(F) ≥ 0`,
> Proposition 3.10 (item 7) gives an `Ew` edge with `Slack_c ≥ K_B`,
> Corollary 3.8 (item 8) gives `D_inc ≤ 1` for that edge. ∎

> **LEMMA TIGHT-DEL.** *If `D(F) = ⌊n/2⌋`, `n ≥ 2`, and `{u,v} ∈ E(F)`
> has `D_inc(u,v) ≤ 1`, then `D_inc(u,v) = 1` and `D(F − {u,v}) =
> ⌊(n−2)/2⌋`.*
>
> *Proof.* `⌊n/2⌋ = D(F) = D_inc(u,v) + D(F − {u,v}) ≤ 1 + ⌊(n−2)/2⌋ =
> ⌊n/2⌋`, the middle inequality by Theorem A's `D`-form (item 1) applied to
> the `(n−2)`-vertex graph `F − {u,v}`, the final equality by `n ≥ 2`. Every
> inequality in this chain is therefore an equality. ∎

Together, LEMMA SUPPLY and LEMMA TIGHT-DEL say: a tight graph on `n ≥ 2`
vertices always has an edge whose two-vertex deletion is tight on `n − 2`
vertices, with the increment across that edge exactly `1`. This is the
supply the induction of §E.5 runs on.

---

## §E.3. The increment identity, witness criteria, and saturation

Fix, for the rest of §E.3–§E.4, `H ∈ 𝓑` on `m` vertices, and an extension
`F` on `V(H) ∪ {u,v}` as in §E.0.1: `{u,v} ∈ E(F)`, `N_F(u) = {v} ∪
S`, `N_F(v) = {u} ∪ T`, `S,T ⊆ V(H)` arbitrary. Write `n := m+2`.

### E.3.1 The identity

> **THE INCREMENT IDENTITY.** *For `H ∈ 𝓑` and any `S,T ⊆ V(H)`:*
>
> `D_inc(u,v) = 1 − χ − W(u,v) − Z(u,v) − R_c(u,v) − U_a(u,v) − U_b(u,v) +
> K(u,v)`.

*Proof.* Substitute Lemma 3.7(iii) (E.0.2 item 4) into Lemma 3.4 (item 3),
using `c({u,v},F) = 1 − χ`:

`D_inc(u,v) = (1−χ) + (−U_a(u,v) − U_b(u,v) − R_c(u,v) + K(u,v)) +
Σ_{remote} [c(P,F) − c(P,H)]`.

This leaves exactly one new fact to prove: the remote sum evaluates in
closed form.

> **LEMMA REM.** *For `H ∈ 𝓑` and `F` as above,*
> `Σ_{remote pairs P ⊆ V(H)} [c(P,F) − c(P,H)] = −(W(u,v) + Z(u,v))`.
>
> *Proof.* Split the remote pairs `P ⊆ V(H)` into three kinds.
> **(i) `H`-edges.** Every component of `H` is complete bipartite, so every
> `H`-edge has `codeg_H = 0`: it lies in `E0(H)`, `c(P,H) = +1`. In `F`, its
> codegree is `[both ends ∈ S] + [both ends ∈ T]`; it keeps `c(P,F) = +1`
> unless both ends lie in `S` (or both in `T`) *and* it becomes unclassified
> in `F` — the total drop, summed over all such `P`, is exactly `W(u,v)` by
> definition of `W`.
> **(ii) `H`-non-edges with `codeg_H ≥ 1`.** These lie in `A(H)` (`c(P,H) =
> −1`) and, since deleting `u,v` never adds a common neighbour, remain in
> `A(F)` (`c(P,F) = −1`): drop `0`.
> **(iii) `H`-non-edges with `codeg_H = 0`.** By definition these are
> exactly the pairs counted by `Z(u,v)` once we ask whether both ends lie in
> `S` or both in `T`: unclassified/absent in `H` (`c(P,H) = 0`, since a
> codegree-`0` non-edge is neither in `E0` — it is not an edge — nor in `A`),
> and in `F` such a pair drops to `c(P,F) = −1` exactly when both ends lie in
> `S` or both in `T` (its codegree becomes `≥ 1` there, via `u` or `v`, with
> no witness available among `{u,v}` alone since a codegree-1 pair with
> common neighbour `u` or `v` and no other common neighbour has no witness
> unless one of `u,v` has a witness elsewhere — and even where a witness
> exists the pair is then counted in `Ew`, not counted by `Z`'s definition,
> which is unconditional on witnessing: `Z` counts the pair regardless, and
> the corresponding `c`-value used on the `F`-side of the drop is what the
> case analysis needs — see the remark below). Summed, the total drop is
> `Z(u,v)`. ∎

> ⚠ **Remark on `Z` (the repaired form — use only this reading).** `Z(u,v)`
> is defined as: non-adjacent pairs `{x,y}` of `V(H)` with `codeg_H(x,y) =
> 0` **and** (`{x,y} ⊆ S` or `{x,y} ⊆ T`). A superseded reading defined
> `Z` as *cross-component* pairs at this generality, on the (false, off-family)
> justification that a same-component codegree-`0` non-edge cannot exist for
> triangle-free `H` in general. It is false in general — `P_4` (path
> `0–1–2–3`) is triangle-free and connected, and `{0,3}` is a non-adjacent,
> same-component pair with `codeg_{P_4}(0,3) = 0`. **On `𝓑` specifically**
> (every `H` in this paper, since `H ∈ 𝓑` is a standing hypothesis
> throughout §E.3–§E.4), the two readings *coincide*: inside a component
> `C_i = K_{X_i,Y_i}`, the only codegree-`0` non-edges are same-part pairs
> with `b_i = 0`, i.e. a `K_1` component, which has no internal pair at all
> — so `Z(u,v)` computed by either reading is identically the count of
> cross-component pairs with both ends in `S` or both in `T`, on `𝓑`. Every
> statement below uses this coincidence implicitly by working exclusively on
> `H ∈ 𝓑`; a reader generalizing this paper's `H` beyond `𝓑` must re-derive
> `Z` from the definition above, not from "cross-component pairs".

This completes the proof of the increment identity. ∎

### E.3.2 Witness criteria

> **LEMMA K-u (the merged criterion).** *Let `w ∈ S` (the statement for
> `w ∈ T` is symmetric, `S ↔ T`, `u ↔ v`). Then `{u,w}` is not
> unclassified in `F` (i.e. `{u,w} ∈ E0(F) ∪ Ew(F)`) iff at least one of:*
> **(a)** *codegree `0`:* `|S ∩ N_H(w)| + [w ∈ T] = 0`;
> **(b)** *witness at `u`:* `∃ p ∈ V(H) ∖ (S∪T)` with `N_H(p) ∩ S = {w}`;
> **(c)** *witness at `w`, via `v`:* `w ∉ T` and `N_H(w) ∩ T = ∅`;
> **(d)** *witness at `w`, via `S`:* `∃ q ∈ S ∖ {w}` in a **different
> component of `H` from `w`**, with (`w ∉ T` or `q ∉ T`).
>
> *Proof.* `codeg_F(u,w) = |N_F(u) ∩ N_F(w)| = |S ∩ N_H(w)| + [w ∈ T]`
> (`N_F(u) ∩ N_F(w) = (S ∩ N_H(w)) ∪ ({v} if w ∈ T)`) — this is clause
> (a), codegree `0` meaning `{u,w} ∈ E0(F)`, unconditionally not
> unclassified. Now suppose `codeg_F(u,w) ≥ 1`; a witness is either at `u`
> or at `w`. *At `u`:* `p ∉ N_F[u] = {u,v} ∪ S`, i.e. `p ∈ V(H) ∖ S`, and
> `N_F(u) ∩ N_F(p) = (S ∩ N_H(p)) ∪ ({v} if p ∈ T)`; requiring this to
> equal `{w} ⊆ V(H)` kills `p ∈ T` and leaves exactly `p ∉ S∪T`,
> `N_H(p)∩S = {w}` — clause (b). *At `w`:* `q ∉ N_F[w]` with
> `N_F(w) ∩ N_F(q) = {u}`; `u ∈ N_F(q)` forces `q ∈ S ∪ {v}`. For
> `q = v`: `v ∉ N_F(w)` iff `w ∉ T`, and then
> `N_F(w) ∩ N_F(v) = (N_H(w) ∩ T) ∪ {u}` (`u` is common since `w ∈ S`);
> requiring this to be `{u}` gives `N_H(w) ∩ T = ∅` — clause (c). For
> `q ∈ S ∖ {w}`: `q ∉ N_H(w)` and
> `N_F(w) ∩ N_F(q) = (N_H(w) ∩ N_H(q)) ∪ {u} ∪ ({v} if w,q ∈ T)`, so
> `q ∉ T` (or `w ∉ T`) and `N_H(w) ∩ N_H(q) = ∅`. **Inside one component of
> `H` these last two conditions are jointly impossible**: if `q` lies in the
> other part of the component from `w`, `q` is adjacent to `w`, contradicting
> `q ∉ N_H(w)`; if `q` lies in the same part, `N_H(q) = N_H(w)`, which is
> empty only when the component is `K_1` — but then `q = w`, excluded. So
> the condition holds only **across components**, giving clause (d)
> (family-reduced form; the underlying general condition is `q ∉ N_H(w)`,
> `N_H(w) ∩ N_H(q) = ∅`, which the paragraph above shows is equivalent to
> "different component" precisely because every component of `H ∈ 𝓑` is
> complete bipartite). ∎
>
> *Specializations, exact matches to the historical un-merged criteria.*
> `w ∈ S ∩ T` kills (a) (`w ∈ T` already makes the indicator `≥ 1`) and (c)
> (`w ∉ T` fails), and turns (d)'s guard into `q ∉ T` — this is **(K1)**.
> `w ∈ S ∖ T` makes (d)'s guard vacuous (`w ∉ T` always holds) — this is
> **(K2)**.

> **LEMMA K3 (`{u,v}` itself).** *`χ = 0` (`{u,v}` not unclassified) iff
> `S ∩ T = ∅`, or `∃ p ∈ T ∖ S` with `N_H(p) ∩ S = ∅`, or `∃ p ∈ S ∖ T` with
> `N_H(p) ∩ T = ∅`.*
>
> *Proof.* `codeg_F(u,v) = |S ∩ T|`, so `{u,v} ∈ E0(F)` (hence not
> unclassified) iff `S ∩ T = ∅` — the first clause. Otherwise a witness at
> `u` is `p ∉ N_F[u] = {u,v}∪S`, i.e. `p ∈ V(H) ∖ S`, with
> `N_F(u) ∩ N_F(p) = (S ∩ N_H(p)) ∪ ({v} if p ∈ T)` equal to `{v}`,
> i.e. `p ∈ T ∖ S` (so the `{v}` term fires) and `S ∩ N_H(p) = ∅` — the
> second clause. Symmetrically at `v` for the third. ∎

> **LEMMA PST-W (witnessing an `H`-edge).** *Let `{x,y} ∈ E(H)`, `x ∈
> X_i`, `y ∈ Y_i` (component `C_i = K_{X_i,Y_i}` of `H`), with
> `codeg_F(x,y) ≥ 1` (i.e. both ends in `S`, or both in `T`). Then `{x,y}`
> is witnessed in `F` iff*
> `b_i = 1` and `∃ p ∈ X_i ∖ {x}` with (`p∉S` or `x∉S`) and (`p∉T` or
> `x∉T`),
> *or symmetrically `a_i = 1` and `∃ q ∈ Y_i ∖ {y}` with (`q∉S` or `y∉S`)
> and (`q∉T` or `y∉T`).*
>
> *Proof.* A witness at `x` must be adjacent to `y`, hence lies in
> `X_i ∪ {u,v}`; `u` is excluded (if `x ∈ S` then `u ∼ x`) and `v` is
> excluded (`codeg_F(x,y) ≥ 1` forces `x,y` both in `S` or both in `T`; if
> the latter, `v ∼ x`). For `p ∈ X_i ∖ {x}`,
> `N_F(x) ∩ N_F(p) = Y_i ∪ ({u} if x,p ∈ S) ∪ ({v} if x,p ∈ T)`,
> which equals `{y}` exactly when `Y_i = {y}` (i.e. `b_i = 1`) and
> neither bracketed term fires, i.e. `(p∉S or x∉S)` and `(p∉T or x∉T)`.
> Symmetrically at `y`. ∎
>
> **The special case doing all the work in §E.4:** if `x,y ∈ S` and `x ∈ T`
> (i.e. `x ∈ S∩T`), the witnessing `p` must avoid **both** `S` and `T`.

> **LEMMA SWALLOW.** *If a component `C` of `H` satisfies `V(C) ⊆ S` or
> `V(C) ⊆ T`, every edge of `C` is unclassified in `F`; consequently
> `W(u,v) = 0` forces every such component to be `K_1` (edgeless).*
>
> *Proof (direct, without LEMMA PST-W).* Say `V(C) ⊆ S` and `{x,y} ∈
> E(C)`. Then `u ∈ N_F(x) ∩ N_F(y)`, so `codeg_F(x,y) ≥ 1`. A witness `p`
> at `x` satisfies `y ∈ N_F(p)`, so `p ∈ N_H(y) ∪ {u} ∪ ({v} if y∈T)`.
> `p = u`: adjacent to `x` (`x ∈ S`) — excluded, a witness must be
> non-adjacent to the vertex it witnesses at. `p = v`: if `x ∈ T` then
> `v ∼ x` — excluded; if `x ∉ T` then `u ∈ N_F(x) ∩ N_F(v)` and `u ≠ y`, so
> `N_F(x)∩N_F(v) ≠ {y}` — excluded. `p ∈ N_H(y) ⊆ V(C) ⊆ S`: then
> `u ∈ N_F(x) ∩ N_F(p)` and `u ≠ y` — excluded. Symmetrically at `y`. No
> candidate witness survives, so `{x,y}` is unclassified. Since `W(u,v) =
> 0` counts none, `C` has no edge: `C = K_1`. ∎

### E.3.3 The charging bound and saturation

> **LEMMA PST-L2.** *`K(u,v) ≤ Z(u,v) + R_c(u,v)`, and therefore, combining
> with the increment identity,*
> `D_inc(u,v) ≤ 1 − χ − W(u,v) − U_a(u,v) − U_b(u,v) ≤ 1`.
>
> *Proof.* Fix `w ∈ S ∩ T`. Since `v ∈ N_F(u) ∩ N_F(w)` (both `u∼v` and
> `v∼w`, the latter as `w ∈ T`), `codeg_F(u,w) ≥ 1`; by LEMMA K-u, `{u,w}`
> is not unclassified iff the p-route (b) or the q-route (d) holds
> (`w ∈ S∩T` kills (a) and (c)). Write `A_u := {w ∈ S∩T : {u,w} not
> unclassified}`, `A_v` symmetrically; then, since `K(u,v)` sums exactly
> the "not unclassified" indicators over `w ∈ S∩T` at both `u` and `v`,
> `K(u,v) = |A_u| + |A_v|`.
>
> **q-route ⟹ `Z`.** For `w ∈ A_u` served by `q_w ∈ S∖T` in a different
> component, `{w,q_w}` is a cross-component pair inside `S`, hence counted
> by `Z(u,v)` (§E.3.1's remark); distinct `w` give distinct pairs (`q_w`
> determines `w`'s component, and `w` is recovered as the unique element of
> `S∩T` in the pair). For `w ∈ A_v` served by `q'_w ∈ T∖S`, `{w,q'_w}` is a
> cross-component pair inside `T`. A chosen `u`-pair never coincides with a
> chosen `v`-pair: `q_w ∈ S∖T` and `q'_{w'} ∈ T∖S` are always distinct
> vertices, and `w ∈ S∩T` is neither `S∖T` nor `T∖S`, so `{w,q_w} =
> {w',q'_{w'}}` would force `w = q'_{w'}`, impossible. Hence
> `#(q-route)≤ Z(u,v)`.
>
> **p-route ⟹ `R_c`.** If `p` serves `w ∈ A_u` via the p-route, `p ∉ S∪T`,
> `N_H(p) ∩ S = {w} ≠ ∅`, and, since `w ∈ T`, also `w ∈ N_H(p) ∩ T`, so
> `N_H(p) ∩ T ≠ ∅` too: `p` contributes `2` to `R_c(u,v) = Σ_{p∉S∪T}
> ([N_H(p)∩S≠∅] + [N_H(p)∩T≠∅])`. The map `w ↦ p_w` is injective (`p_w` is
> determined by `w` as the unique vertex with `N_H(p_w)∩S = {w}`); the same
> `p`-set can serve the `v`-side identically. Hence `#(p-route,u) +
> #(p-route,v) ≤ 2·#{such p} ≤ R_c(u,v)`.
>
> Summing, `K(u,v) = |A_u|+|A_v| ≤ Z(u,v) + R_c(u,v)`; substituting into the
> increment identity and dropping `−Z − R_c + K ≤ 0` gives the displayed
> bound, and since `χ, W, U_a, U_b ≥ 0` this is `≤ 1`. ∎

> **LEMMA SAT.** *If `D_inc(u,v) = 1` then `χ = W(u,v) = U_a(u,v) =
> U_b(u,v) = 0` and `K(u,v) = Z(u,v) + R_c(u,v)`; if moreover `S ∩ T = ∅`
> then also `Z(u,v) = R_c(u,v) = 0`. This is an **equivalence** with
> `D_inc(u,v) = 1`, given the increment identity and LEMMA PST-L2 — it is
> not a one-directional implication.*
>
> *Proof.* LEMMA PST-L2 gives `1 = D_inc(u,v) ≤ 1 − χ − W − U_a − U_b`
> (using `K ≤ Z+R_c`), and all four subtracted terms are `≥ 0`, forcing all
> four to be `0`; substituting back into the increment identity then forces
> `K = Z + R_c` (the inequality `K ≤ Z+R_c` becomes equality). If `S∩T = ∅`
> then `K(u,v) = 0` trivially (the defining sum is empty), so `Z = R_c = 0`
> too. Conversely, if all these vanishings hold, the increment identity
> reads `D_inc = 1 − 0 − 0 − Z − R_c − 0 − 0 + (Z+R_c) = 1`. ∎

---

## §E.4. `(STEP-del)`: the classification

> **`(STEP-del)`.** *Let `H ∈ 𝓑` on `m` vertices, `F` an extension of `H`
> by `u,v` as in §E.3, and suppose `D_inc(u,v) = 1`. Then `F ∈ 𝓑`.*
>
> *Equivalence with the deletion-form hypothesis.* By LEMMA TIGHT-DEL
> (§E.2), if `D(F) = ⌊(m+2)/2⌋` and `H := F − {u,v} ∈ 𝓑` (so `D(H) =
> ⌊m/2⌋` by FACT E.1b), then `D_inc(u,v) = 1` automatically — this is the
> only fact about `D(H) = ⌊m/2⌋` the proof below uses. Conversely
> `D_inc(u,v) = 1` and `D(H) = ⌊m/2⌋` give `D(F) = ⌊(m+2)/2⌋` by definition
> of `D_inc`. The two formulations enumerate the same objects; **this
> equivalence is load-bearing and must not be dropped** when citing the
> evidence gathered for either form.

We split on `S ∩ T`.

### E.4.1 Case `S ∩ T = ∅`: THEOREM PST-A (two-clause, exclusive)

By hypothesis `codeg_F(u,v) = |S∩T| = 0`, so `{u,v} ∈ E0(F)` and `χ = 0`;
also `K(u,v) = 0` (empty sum). The increment identity reads
`D_inc(u,v) = 1 − W − Z − R_c − U_a − U_b`, a sum of five non-negative
terms subtracted from `1`; `D_inc(u,v) = 1` therefore forces

`W(u,v) = Z(u,v) = R_c(u,v) = U_a(u,v) = U_b(u,v) = 0`.

Reading these off:
* `Z = 0`: no cross-component pair lies inside `S`, none inside `T` — **`S`
  lies in a single component of `H` and `T` lies in a single component**.
* `R_c = 0`: `N_H(S) ⊆ S∪T` and `N_H(T) ⊆ S∪T` — **`S∪T` is a union of
  connected components of `H`.**
* `W = 0`: every `H`-edge inside `S`, and every one inside `T`, is
  witnessed in `F`.
* `U_a = U_b = 0`: every `w ∈ S` (here `S∖T = S`, `T∖S=T` since `S∩T=∅`) has
  `{u,w}` not unclassified, every `w ∈ T` has `{v,w}` not unclassified.

> **THEOREM PST-A.** *Up to swapping `u` and `v`, exactly one of:*
> **(i)** `S = T = ∅`;
> **(ii)** `{S,T} = {X_i,Y_i}` for a unique component `C_i =
> K_{X_i,Y_i}` of `H` (the degenerate `C_i = K_1` case is this clause's
> `b_i = 0` instance: `S = X_i`, `T = ∅`).
> *In both cases `F` is a disjoint union of balanced complete bipartite
> graphs with at most one odd component.*

*Proof.* **Case 1: `S = ∅` or `T = ∅`.** Say `T = ∅`. If `S = ∅` we are in
(i). Otherwise `S` lies in one component `C` (by `Z=0`), and `N_H(S) ⊆ S∪T
= S` (by `R_c=0`), so `S` is a union of components of `C`; `C` is connected
and `S ≠ ∅`, so `S = V(C)`. If `C` had an edge `{x,y}`, then `x,y ∈ S`,
`x,y ∉ T`, and LEMMA PST-W would need a `p ∈ X_C ∖ S = ∅` or a `q ∈ Y_C ∖ S
= ∅` — impossible, so the edge is unwitnessed, contradicting `W = 0`. Hence
`C` has no edge: `C = K_1`, and `{S,T} = {X_C,∅} = {V(C),∅}`, clause
(ii)'s `b_i=0` instance.

**Case 2: `S,T ≠ ∅` in different components `C_S ≠ C_T`.** As in Case 1,
`S = V(C_S)` and `C_S = K_1`; symmetrically `C_T = K_1`. But then `H` has
**two** odd (order-`1`) components — contradicting the family hypothesis
that `H ∈ 𝓑` has at most one. This branch cannot occur.

**Case 3: `S,T ≠ ∅` in the same component `C = K_{X,Y}`.** `R_c=0` gives
`S ⊔ T = V(C)` (`C` connected, `S∪T ≠ ∅`, and `C = K_1` is impossible since
`S,T` are disjoint and non-empty). *Sub-claim: `S ⊆ X` or `S ⊆ Y`.* Suppose
`x ∈ S∩X`, `y' ∈ S∩Y`. Then `codeg_F(u,x) = |S ∩ N_H(x)| = |S∩Y| ≥ 1` (as
`y' ∈ S∩Y`), so `U_a = 0` forces `{u,x}` witnessed; by LEMMA K-u's routes
(specialized as (K2), since `x∈S∖T`): the p-route is impossible (a `p`
witnessing at `u` must be adjacent to `x`, hence lie in `C`, but `C ⊆ S∪T`
leaves `V(H)∖(S∪T)` untouched by `C`); the q-route is impossible (`Z=0`
puts all of `S` in one component, so no `q ∈ S` lies in a different
component from `x`); so the surviving alternative is `N_H(x) ∩ T = Y ∩ T =
∅`, i.e. **`Y ⊆ S`**. The same argument at `y' ∈ S∩Y` gives **`X ⊆ S`**, so
`S = V(C)` and `T = ∅` — contradicting `T ≠ ∅`. This proves the sub-claim;
the same argument (with `u↔v`, `S↔T`) gives `T ⊆ X` or `T ⊆ Y`. Since
`S ⊔ T = V(C) = X ⊔ Y` and both `S,T` are non-empty, they cannot sit inside
the same part, so `{S,T} = {X,Y}`: clause (ii), general case.

**Exclusivity.** (i) forces `S∪T = ∅`; (ii) forces `S∪T = V(C_i) ≠ ∅` —
disjoint. Uniqueness of `C_i` in (ii): `S∪T = V(C_i)` determines the
component.

**The conclusion, uniformly.** In (i), the new component of `F` is `K_2 =
K_{1,1}`. In (ii), it is `K_{X_i∪{v}, Y_i∪{u}}` — complete bipartite,
parts of sizes `a_i+1` and `b_i+1`, with `|(a_i+1)−(b_i+1)| = |a_i−b_i| ≤ 1`
— **balanced**. All other components of `H` are untouched components of
`F`. ∎

**Observation (parity).** If `H` has at most one odd component, then
`#odd(F) = #odd(H)` for **every** `(S,T)`, no case split needed: the
`F`-component containing `u,v` has order `2 + Σ(orders of the H-components
met by S∪T)`, whose parity is that of the number `k` of **odd**
`H`-components absorbed into it; `k ≤ 1` by hypothesis, and `#odd(F) =
#odd(H) − k + (k mod 2) = #odd(H)` (removing `k` odd components and adding
one component whose own parity is `k mod 2`). (An earlier draft boxed this
as LEMMA PARITY; it is recorded as an observation because it needs no case
split and, in the Lean development, no counterpart at all — the `≤ 1`-odd
clause of `F`'s family witness falls out of the witness constructions
directly; §E.6.1.)

By THEOREM PST-A, `F`'s components are all balanced complete bipartite; by
the parity observation, `F` has the same number of odd components as `H`,
i.e. at most one. So `F ∈ 𝓑` in this case.

### E.4.2 Case `S ∩ T ≠ ∅`: THEOREM PST-B — this case is impossible

Assume `R := S ∩ T ≠ ∅`. By LEMMA SAT, `χ = W = U_a = U_b = 0` and
`K(u,v) = Z(u,v) + R_c(u,v)`.

**The `q`-maximising assignment.** For each `w ∈ R`, `{u,w}` is not
unclassified (`U_a = 0`), so by LEMMA K-u (as (K1), since `w ∈ S∩T`) either
the p-route or the q-route holds. Put `A_u^q := {w ∈ R : ∃ q ∈ S∖T in a
different component from w}` (every such `w` qualifies for the q-route)
and `A_u^p := {w ∈ R : {u,w} not unclassified} ∖ A_u^q`; for
`w ∈ A_u^p` the p-route must hold (since `w` is not served by the q-route
by construction), so choose `p_w ∈ V(H)∖(S∪T)` with `N_H(p_w)∩S = {w}`
and set `P_u := {p_w : w ∈ A_u^p}`. Symmetrically at `v`: `A_v^q, A_v^p,
P_v`. Then:

* `|P_u| = |A_u^p|` — the map `w ↦ p_w` is injective, since `p_w` determines
  `{w}` as `N_H(p_w)∩S`.
* Every `p ∈ P_u ∪ P_v` lies outside `S∪T` and meets both `S` and `T` in its
  `H`-neighbourhood — the vertex `w` it serves lies in `R ⊆ S∩T`, so
  `N_H(p) ∩ S ∋ w` and `N_H(p) ∩ T ∋ w` — so `p` contributes exactly `2` to
  `R_c(u,v)`.
* The chosen cross-component pairs `{w,q_w}` (`w ∈ A_u^q`, `q_w ∈ S∖T`)
  and `{w,q'_w}` (`w ∈ A_v^q`, `q'_w ∈ T∖S`) are `|A_u^q| + |A_v^q|`
  pairwise distinct pairs, each counted by `Z(u,v)`. *(Distinctness: two
  `u`-pairs sharing a pair would force some `w = q_{w_2} ∈ S∖T`, against
  `w ∈ R ⊆ T`; a `u`-pair equal to a `v`-pair would force `q_w = q'_{w'}`
  (impossible: one lies in `S∖T`, the other in `T∖S`) or `w = q'_{w'} ∉ S`
  against `w ∈ R ⊆ S`.)*

Therefore

`K(u,v) = (|A_u^p| + |A_u^q|) + (|A_v^p| + |A_v^q|) = (|P_u|+|P_v|) +
(|A_u^q|+|A_v^q|) ≤ 2|P_u ∪ P_v| + Z(u,v) ≤ R_c(u,v) + Z(u,v)`,

and LEMMA SAT's equality `K = Z + R_c` forces **every link in this chain to
be an equality**:

* **(E-a)** `|P_u| + |P_v| = 2|P_u ∪ P_v|`, i.e. **`P_u = P_v =: P`** —
  from `|P_u ∪ P_v| = |P_u|+|P_v|−|P_u∩P_v|`, the equality gives
  `|P_u|+|P_v| = 2|P_u∩P_v| ≤ 2min(|P_u|,|P_v|)`, forcing `P_u = P_v`.
* **(E-b)** `R_c(u,v) = 2|P|`, i.e. **every `p ∉ S∪T` outside `P` has
  `N_H(p) ∩ (S∪T) = ∅`.**
* **(E-c)** `Z(u,v) = |A_u^q| + |A_v^q|`, i.e. **every cross-component pair
  inside `S` or inside `T` is one of the chosen pairs**, and (since the
  chosen pairs are already pairwise distinct) each `w ∈ R` lies in **at
  most one** such pair (it has at most one chosen pair — the one attesting
  its own membership in `A_u^q` or `A_v^q`, if any).

**Three structural consequences.**

1. **`S ≠ T`.** `χ = 0` with `S∩T ≠ ∅` forces, by LEMMA K3, a witness
   `p_0 ∈ T∖S` or `p_0 ∈ S∖T` — either way `S ≠ T`.
2. **Every cross-component pair inside `S` has exactly one end in `R`**,
   the other in `S∖T` — a chosen `v`-pair has an end in `T∖S`, so cannot lie
   inside `S` — **and each `w ∈ R` lies in at most one such pair** (E-c).
   Symmetrically for `T`.
3. **`S` meets at most two components of `H`, and so does `T`, with `R`
   inside exactly one of them.** Three vertices of `S` in three distinct
   components would need pairwise-different labels drawn from the two
   labels `{R, S∖T}` (consequence 2) — impossible. `R = S∩T` is exactly
   the `R`-labelled part of `S`, hence lies in one component `C_1`.
   Moreover, if `S` meets a second component `C_2`, every `w ∈ R` is paired
   with *every* element of `S ∩ C_2` (each such element is the unique
   partner labelling `w`'s pair — since `w` has at most one chosen pair, and
   the pairing is between `R` and `S∖T`), forcing **`|S ∩ C_2| = 1`**, i.e.
   `S = R ⊔ {q}` with `q ∈ S∖T`.

So exactly three cases remain, indexed by `(r_S,r_T) ∈ {1,2}²` (`r` =
number of components each of `S,T` meets).

> **⚠ THE HYPOTHESIS LEDGER, tracked through the rest of this proof.**
> The hypotheses on `H` (`H ∈ 𝓑`: triangle-free components,
> complete-bipartite components, at most one odd component, balance) are
> each spent at a specific, named point: **triangle-free** is spent once,
> globally, in LEMMA REM (§E.3.1(i)) — every `H`-edge is `E0`. **Complete
> bipartite** is spent in every codegree computation and in LEMMA PST-W /
> LEMMA K-u's route (d). **At most one odd component** is spent in Case 2
> above (in THEOREM PST-A), in the parity observation (its `k ≤ 1`), and
> in Cases (2,1) and (2,2) below. **Balance** is spent at four sites:
> (i) Case `(1,1)`'s `|Y|=1 ⟹ |X| ≤ 2` squeeze below; (ii) THEOREM
> PST-A's "`|(a_i+1) − (b_i+1)| ≤ 1`" conclusion; and (iii)/(iv) LEMMA
> K-u's route (d) and LEMMA SWALLOW's component collapse. Sites (iii) and
> (iv) are a correction ordered by the formalization's dependency trace
> (audit finding F-1, `transcription-audit-s14.md`; an earlier
> ledger listed only (i) and (ii)): in this paper's presentation the two
> steps are closed by the connectedness of components (an empty-part
> component is a single vertex *because* components are connected), but
> in the Lean development's intrinsic definition of `𝓑` — whose classes
> are not assumed connected — the balance clause is what forces an
> empty-part class to be a singleton, and it is load-bearing at exactly
> those two sites (`lemma_Ku`, `lemma_swallow_component`). A reader
> transporting this proof to any class-based formulation must carry
> balance at all four sites.

**Case `(1,1)`: `S,T` both inside one component `C = K_{X,Y}`.** Then
`S ∪ T ⊆ C` and `Z(u,v) = 0` (no cross-component pair can exist). By
consequence 1 and the `u↔v` symmetry of the whole configuration, assume WLOG
`∃ p_0 ∈ S∖T` with `N_H(p_0) ∩ T = ∅`. Pick `w ∈ R`. Then `w ∈ T`, so
`w ∉ N_H(p_0)`: `p_0` and `w` are non-adjacent vertices of a complete
bipartite component, hence in the **same part**, say `X`; and `p_0 ≠ w`
(`w∈T`, `p_0∉T`), so **`|X| ≥ 2`**. Also `N_H(p_0) = Y`, so `Y ∩ T = ∅`,
i.e. `T ⊆ X`, and `R ⊆ T ⊆ X`.

*`Y ∩ S = ∅` too.* Suppose `y ∈ Y∩S`. The `H`-edge `{w,y}` has both ends
in `S` (`w ∈ X`, and since `S ⊇ {w,p_0} ⊆ X` and `y ∈ Y∩S`, `codeg_F(w,y)
≥ 1` as both lie in `S`), so `W = 0` forces a witness; by LEMMA PST-W, at
`w` it needs `|Y| = 1` **and** `p ∈ X∖(S∪T)` (`w ∈ S∩T`); but `|Y|=1`
forces `|X| ≤ 2` **by balance**, so `X = {w,p_0} ⊆ S` and `X∖(S∪T) = ∅` —
this route fails. At `y` it needs `|X| = 1`, contradicting `|X| ≥ 2`. So
`{w,y}` is unwitnessed, contradicting `W = 0`. Hence `Y ⊆ V(H)∖(S∪T)`.

If `Y ≠ ∅`, take `y ∈ Y`: `N_H(y) = X ⊇ {w}` meets `S`, so by (E-b)
`y ∈ P`, meaning `N_H(y)∩S` and `N_H(y)∩T` are the **same singleton**; but
`N_H(y)∩S = X∩S = S` and `N_H(y)∩T = X∩T = T` (`S ⊆ X` as shown above), so
`S = T` — contradicting consequence 1. If `Y = ∅`, `C` is edgeless and
connected, i.e. `C = K_1`, `|X|=1` — contradicting `|X| ≥ 2`.
**Case `(1,1)` is empty.** ∎

**Case `(2,1)` (and its mirror `(1,2)`).** `S = R ⊔ {q}` with `q ∈ S∖T`
in a component `C_2 ≠ C_1 ⊇ R`, and `T ⊆ C_1`. Every `w ∈ R` has the
q-route at `u` (via `q`), so `A_u^q = R`, `A_u^p = ∅`, i.e. `P_u = ∅`; by
(E-a), `P_v = P_u = ∅`, so `A_v^p = ∅`; and `A_v^q = ∅` (a `q'` for the
`v`-side would need to lie in `T∖S ⊆ C_1`, the same component as `w ∈ R`,
so it can't serve a q-route which requires a *different* component). Hence
by (E-b), `R_c(u,v) = 2|P| = 0`, i.e. **`N_H(S∪T) ⊆ S∪T`: `S∪T` is a union
of connected components of `H`.** Intersecting with `C_2` gives
`V(C_2) = {q}`, so **`C_2 = K_1`**; intersecting with `C_1` gives
`V(C_1) = R ∪ T = T`. Every edge of `C_1` lies inside `T`, and LEMMA PST-W's
two routes both require a vertex of `C_1` outside `T` — none exist (`C_1 ⊆
T`) — so every edge of `C_1` is unwitnessed, giving `W(u,v) ≥ e(C_1)`. With
`W = 0`, `C_1` has no edge: **`C_1 = K_1`**. But `K_1` has odd order, and
`C_1 ≠ C_2` are now **two** odd components of `H` — contradicting
"at most one odd component". **Case `(2,1)` is empty.** ∎

**Case `(2,2)`.** `S = R ⊔ {q}` (`q ∈ C_2`), `T = R ⊔ {q'}`
(`q' ∈ C_2'`), `R ⊆ C_1`, `C_2,C_2' ≠ C_1`. As in Case `(2,1)`, both
q-routes are available (each `w∈R` served across from its own side), so
`P = ∅` and `R_c(u,v) = 0`, hence `S∪T` is a union of components:
`V(C_1) = R`, and `(S∪T)∩C_2 ∋ q`.

* If `C_2 ≠ C_2'`: `V(C_2) = {q}`, `V(C_2') = {q'}` — two `K_1`
  components — excluded by "at most one odd component".
* If `C_2 = C_2'`: `V(C_2) = {q,q'}`, `C_2` connected, so **`C_2 = K_2`**.
  All edges of `C_1` lie inside `S` (indeed `R = V(C_1) ⊆ S∩T`), and
  LEMMA PST-W's routes each need a vertex of `C_1` outside `S` — none — so
  `W(u,v) ≥ e(C_1)`, forcing **`C_1 = K_1`**, `R = {w}` for a single
  vertex `w`. Now test `χ` by LEMMA K3: the only candidate in `T∖S` is
  `q'`, and `N_H(q') = {q} ⊆ S ≠ ∅`, so that clause fails; the only
  candidate in `S∖T` is `q`, and `N_H(q) = {q'} ⊆ T ≠ ∅`, so that clause
  fails too. Both routes fail, so `χ = 1` — contradicting `χ = 0` from
  LEMMA SAT. **Case `(2,2)` is empty.** ∎

All three cases are empty, so **`S ∩ T ≠ ∅` never has `D_inc(u,v) = 1`.**
This closes `(STEP-del)`: combined with §E.4.1, every tight two-vertex
extension `F` of `H ∈ 𝓑` has `S ∩ T = ∅` and is again in `𝓑`.

---

## §E.5. The characterisation, by induction

> **THEOREM TA-CHAR.** *For every graph `F` on `n` vertices,*
> `D(F) = ⌊n/2⌋` **iff** `F ∈ 𝓑`.
>
> *Proof.* `⟸`: FACT E.1b, applied component-wise (that fact's own proof
> already sums over components; nothing further is needed for this
> direction). `⟹`: strong induction on `n`. **Base cases `n=0` and `n=1`**
> (both needed, not just one): the empty graph and `K_1` are both in `𝓑`
> trivially, and both tight (`D = 0 = ⌊0/2⌋`, resp. `⌊1/2⌋`). **Inductive
> step, `n ≥ 2`:** `F` tight `⟹` (LEMMA SUPPLY) some edge `{u,v}` has
> `D_inc(u,v) ≤ 1` `⟹` (LEMMA TIGHT-DEL) `D_inc(u,v) = 1` and `H := F −
> {u,v}` is tight on `n−2` vertices `⟹` (induction hypothesis) `H ∈ 𝓑`
> `⟹` (`(STEP-del)`, §E.4, applicable since `H ∈ 𝓑` and `D_inc(u,v) = 1`
> are exactly its hypotheses) `F ∈ 𝓑`. ∎

**Remark (machine validation).** The `⟹` direction of TA-CHAR, and
everything it consumes — the family `𝓑`, LEMMA SUPPLY, LEMMA TIGHT-DEL,
`(STEP-del)` in full, and the induction itself — is machine-checked in Lean;
§E.6.1 records the exact scope of the verification, including the one
direction of the theorem above whose statement has no Lean counterpart
(the `⟸` direction as stated, which rests on the general FACT E.1b; §E.6's
own proof does not route through it).

---

## §E.6. (MS-eq)

> **THEOREM (MS-eq).** *Let `n ≥ 3` and let `G` be a diameter-2-critical
> graph on `n` vertices. Then*
> `e(G) = ⌊n²/4⌋` **if and only if** `G` is isomorphic to
> `K_{⌈n/2⌉,⌊n/2⌋}`.
>
> *Proof.* By Proposition 3.2 (E.0.2 item 2), `Φ(G) = 2e(G)`. By Proposition
> 3.1 (used inside item 1's statement of Theorem A), `Φ(G) = C(n,2) +
> D(G)`. Hence `D(G) = 2e(G) − C(n,2)`, and
>
> `⌊n/2⌋ − D(G) = ⌊n/2⌋ − 2e(G) + C(n,2) = ⌊n²/2⌋ − 2e(G) = 2(⌊n²/4⌋ −
> e(G))`
>
> (`⌊n²/2⌋ = 2⌊n²/4⌋` for both parities of `n`), so
>
> `D(G) = ⌊n/2⌋ ⟺ e(G) = ⌊n²/4⌋`.
>
> By THEOREM TA-CHAR, `D(G) = ⌊n/2⌋ ⟺ G ∈ 𝓑`. A D2C graph is **connected**:
> diameter `2` means every pair of vertices is joined by a path of length
> `≤ 2`, in particular by a walk, so `G` is connected (machine-checked as
> `isDiameter2Critical_preconnected`; §E.6.1). A connected member of
> `𝓑` is a single component, i.e. a single balanced complete bipartite graph
> `K_{a,b}` with `a+b=n`, `|a−b|≤1` — necessarily `{a,b} = {⌈n/2⌉,
> ⌊n/2⌋}`, the unique such pair. Hence
>
> `e(G) = ⌊n²/4⌋ ⟺ G ∈ 𝓑 ⟺ G` is a connected member of `𝓑` `⟺ G ≅
> K_{⌈n/2⌉,⌊n/2⌋}`. ∎

**Note on the proof's use of §E.1.** The direction `G ≅ K_{⌈n/2⌉,⌊n/2⌋}
⟹ e(G) = ⌊n²/4⌋` used above needs `D(G) = ⌊n/2⌋` for this *specific*,
connected `G` — i.e. FACT E.1a (§E.1), not the general multi-component FACT
E.1b. We state this explicitly because it is the one dependency the Lean
formalization's trace surfaced that the write-up architecture's dependency
list did not originally separate out: the
single-class instance of tightness is what (MS-eq) actually needs at this
last step, distinct from the general family sum FACT E.1b that TA-CHAR's
`⟸` direction and the induction's base cases use.

**Boundary remarks, `n ∈ {1,2}`, stated separately and never folded into
the `n ≥ 3` iff above.**
* `n = 1`: the one-vertex graph `K_1` has diameter `0`, not `2`; under the
  standard convention that D2C requires diameter *exactly* `2`, no D2C graph
  exists at `n = 1`.
* `n = 2`: `K_2` (the single edge) has diameter `1`, not `2` — it is not
  diameter-2-critical. No D2C graph exists at `n = 2` either.

Both facts make the theorem's hypothesis vacuous at `n ≤ 2`; the pin to
`n ≥ 3` cannot be dropped from the *attainment-strengthened* reading above
("`K_{⌈n/2⌉,⌊n/2⌋}` is *the* extremal D2C graph") for a sharper reason than
vacuity alone: at `n = 2`, `K_{1,1} = K_2` attains `⌊4/4⌋ = 1` edge but has
diameter `1`, not `2` — so even granting `K_2` a diameter-2-critical reading
by some non-standard convention would make it a *non-example* of the
attainment claim's intended content (a D2C graph with that edge count), not
a confirming instance. The pin is therefore not merely a scoping convenience.

The attainment-strengthened reading also consumes one ingredient beyond the
iff proved above: that for `n ≥ 3` the extremal class is non-empty, i.e.
`K_{⌈n/2⌉,⌊n/2⌋}` is itself diameter-2-critical. This is Part I's [Part I
§1.1], inherited as a black box like everything else in §E.0.2; it is cited
explicitly here because the sealed campaign log's proof of the corresponding
corollary (PTA-L4) used it without citation — one of the write-up repairs
recorded against that log.

### E.6.1 Machine verification

The chain of §E.1–§E.6 is formalized in Lean 4 over mathlib, in the module
`Equality.lean` (5,764 lines, 124 top-level declarations), which
imports the frozen, Lean-verified Part I file `Erdos742.lean`
unmodified. `Equality.lean` contains zero `sorry`s and declares no axiom;
the only `sorry` in the combined build is Part I's deliberate negative
control (`row21_per_edge_form_false`), which sits on no proof path. The
top-level declaration

> `stmt6_ms_eq_iso_labelled` — for `n ≥ 3` and `G` diameter-2-critical
> (the same `IsDiameter2Critical` predicate Part I's `erdos_742` uses):
> `e(G) = ⌊n²/4⌋ ↔ Nonempty (G ≃g completeBipartiteGraph
> (Fin ((n+1)/2)) (Fin (n/2)))` — the literal labelled
> `K_{⌈n/2⌉,⌊n/2⌋}` form of the theorem above —

is proved, with both directions of the iff separately proved (neither a
restatement of the other), and
`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
for it and for every declaration on its chain — in particular `pst_a`
(§E.4.1), `pst_b` (§E.4.2), `step_del` (`(STEP-del)`), `stmt5_forward`
(TA-CHAR's `⟹` direction), and Part I's `erdos_742`, which the equality
development leaves untouched. Section-by-section counterparts: LEMMA
SUPPLY and LEMMA TIGHT-DEL are `lemma_supply`/`lemma_tight_del`; the
increment identity and LEMMA REM are `identity_assembly`/`lemma_rem`;
LEMMA K-u, LEMMA K3, LEMMA PST-W, LEMMA SWALLOW, LEMMA PST-L2, and LEMMA
SAT are `lemma_Ku`, `lemma_K3`, `lemma_PST_W`, `lemma_swallow_edge` +
`lemma_swallow_component`, `lemma_PST_L2`, `lemma_SAT`; §E.6's slack
conversion is `pta_l4_arith`, its connectivity step
`isDiameter2Critical_preconnected`, and FACT E.1a's instance
`dv_of_isBalCBUnion_connected`. The equivalence-of-enumeration paragraph
of §E.4 — flagged there as load-bearing — is in the Lean development a
proved graph isomorphism (`stepIso`), not a remark. A statement-level
transcription audit (`transcription-audit-s14.md`) compared all
124 Lean statements against the campaign's statement authority
(`extraction-statements.md`): verdict CLEAN-WITH-NOTES — zero
mismatches, every recorded deviation confirmed content-preserving.

The scope of the machine check is delimited as follows; the items below
are **not** machine-checked.

* **FACT E.1b in its multi-component generality.** The Lean development
  states and proves only the single-component instance
  (`dv_of_isBalCBUnion_connected`: a connected member of `𝓑` on `m`
  vertices has `D = ⌊m/2⌋`, i.e. FACT E.1a). The general family sum
  stands in this paper as mathematics (§E.1) with no Lean declaration
  attached. (MS-eq) does not need it: the `⟸` direction of §E.6's iff is
  machine-checked through the connected case, which suffices because a
  D2C graph is connected (`isDiameter2Critical_preconnected`).
* **TA-CHAR's `⟸` direction as stated.** It rests on the general FACT
  E.1b and has no Lean counterpart; only the `⟹` direction
  (`stmt5_forward`) is machine-checked. As just noted, §E.6's own `⟸`
  bypasses it.
* **The parity observation of §E.4.1 and THEOREM PST-A's two-clause
  classification.** Neither has a Lean declaration of its own; both are
  proof-internal in the Lean route (`pst_a` proves the membership
  conclusion directly, and the `≤ 1`-odd clause of `F`'s family witness
  falls out of the witness constructions without a separate parity
  lemma). They are cited in this paper as mathematics only.

The Lean development is a second verified presentation, not a
transcription of §E.3–§E.4's prose; at several points it takes a route
of its own. Where §E.4.1 argues "up to swapping `u` and `v`", the Lean
proves one orientation and transports it across a proved `S ↔ T` swap
isomorphism; PST-B's saturation bookkeeping is packaged into a single
tightness lemma (`pst_b_tight`, carrying (E-a)/(E-b)/(E-c) together with
the chosen-pair partner functions); the `(r_S,r_T)` case split is run on
equivalence-class membership rather than a component count; and Case
`(1,1)`'s opening WLOG is not taken (both LEMMA K3 disjuncts are consumed
jointly). Each divergence is recorded in the formalization log
(`lean-equality.md`); none changes any statement. Separately from
the machine check, §E.3–§E.4's prose proof passed a four-read human
review (author, referee, two independent blind hostile readers, zero
mathematical breaks). The two presentations were produced under a reading
firewall and verified against a common statement file, not against each
other.

---

## §E.7. Independent confirmations and by-products

This section is deliberately off the spine above: nothing in §E.1–§E.6 cites
anything below, and nothing below is needed for (MS-eq).

**`THEOREM PST-RED` (a reformulation, not used).** `(STEP-del)` is
equivalent to the purely local statement "a tight two-vertex extension of a
member of `𝓑` is triangle-free" — `F` contains a triangle iff `S∩T ≠ ∅`, or
`S` spans an `H`-edge, or `T` does, and §E.4 shows a tight extension has
none of these. This reformulation converts the target into a single local
negation, but it was **not used** to prove `(STEP-del)` above; §E.4's
classification proof is self-contained and does not route through it.

**`TA-TF-EQ` (the friendship-paradox route, an independent proof avoiding
Theorem Σ).** The equality class of Theorem A restricted to *triangle-free*
graphs can be proved directly, by an argument that never invokes Theorem Σ
— a different route to (part of) the same conclusion, recorded because it
isolates exactly how much of Theorem Σ the triangle-free case needs
(none of it). It is
not part of the critical path above: the induction of §E.5 never restricts
to triangle-free graphs, and `(STEP-del)`'s proof does not invoke it.

**`TA-ID`, `Λ`, and related local reformulations.** An alternative
elementary reformulation of Theorem A's local bookkeeping exists and was
useful during the discovery process, but is consumed by nothing above.

**`PROP-A` (open).** Whether Theorem Σ's hard case can itself be reduced to
a purely local statement is, at the time of writing, an *open question* —
not a theorem, not a conjecture claimed here, and not needed by anything
above. If true, it would simplify Part I's own §4; it is recorded here only
as a pointer for a reader interested in shortening Part I, not as part of
this paper's content.

---

No part of the proof of (MS-eq) above depends on any enumeration or
computer search: §E.1–§E.6 are a closed chain of finitely many algebraic
identities and case exhaustions, each verified by direct argument. Every
computational census the underlying research campaign ran (tight-graph
counts, near-extremal bands, and the like) touches only the campaign's
*evidence* for this theorem's discovery and audit — never its mathematics.

## References

[CH79] L. Caccetta, R. Häggkvist, *On diameter critical graphs*, Discrete
Math. **28** (1979) 223–229.

[DFH19] A. Dailly, F. Foucaud, A. Hansberg, *Strengthening the Murty–Simon
conjecture on diameter 2 critical graphs*, Discrete Math. **342**(11) (2019)
3142–3159, DOI 10.1016/j.disc.2019.06.023, arXiv:1812.08420.

[Part I] *Every diameter-2-critical graph on `n` vertices has at most
`⌊n²/4⌋` edges*, this repository (`paper-742-inequality.md`; Lean-verified
as `Erdos742.lean`).
