/-
Erdős #742, Part II (equality): a diameter-2-critical graph on n ≥ 3 vertices has
e(G) = ⌊n²/4⌋ if and only if G ≅ K_{⌈n/2⌉,⌊n/2⌋}.

This file is the concatenation of Erdos742.lean (Part I, the inequality, frozen) and
Equality.lean (Part II), in that order — the two files in this repository compile as a
single unit. Toolchain: Lean v4.33.0-rc1, mathlib commit ae0d973.
Top-level result: `Erdos742.Campaign.stmt6_ms_eq_iso_labelled`
(#print axioms: [propext, Classical.choice, Quot.sound]).
-/

/-
# Erdős Problem #742 (Murty–Simon), the inequality — a Lean 4 formalization

Every diameter-2-critical graph on `n` vertices has at most `⌊n²/4⌋` edges.

## Provenance of the statement

`Erdos742.erdos_742`, at the end of this file, is the statement of `erdos_742`
in Google DeepMind's `formal-conjectures` repository
(`FormalConjectures/ErdosProblems/742.lean`), with `import
FormalConjecturesUtil` replaced by `import Mathlib`, the `@[category …]`
attributes dropped, and the `answer(sorry) ↔` wrapper instantiated — that
wrapper is the repository's open-problem idiom, and "solving" the entry means
instantiating `answer` with `True`, leaving the right-hand side to be proved.
The statement is:

```
theorem erdos_742 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4
```

`(Fintype.card V) ^ 2 / 4` is natural-number division, i.e. `⌊n²/4⌋`.

The upstream predicate `IsDiameter2Critical` is phrased with mathlib's
`SimpleGraph.diam`, which is `ℕ`-valued and is `0` on a *disconnected* graph.
That is not literally the textbook condition `diam(G − e) > 2`, so the two are
not interchangeable by definition; `isD2C_iff_isDiameter2Critical` in Part 2
**proves** that they agree.  That bridge theorem is what makes the rest of the
file a proof of the upstream statement rather than of a lookalike.

⚠ Scope: only the **inequality** is formalized here.  The equality clause —
that `K_{⌈n/2⌉,⌊n/2⌋}` is the unique extremal graph — is not part of the
upstream formal statement and is not addressed anywhere in this file.

## Structure

* **Part 0** — the upstream predicate `IsDiameter2Critical`.
* **Part 1** — the notions the proof runs on: `Within2`, `IsD2C`, witnesses,
  `E0`, `Ew`, `A`, `disj`, `Φ`, `D`, the per-pair quantities and `Σ`.
* **Part 2** — the bridge, together with the `F − {u,v}` two-vertex-deletion
  transport layer (Part 2.7) that the deletion bounds are proved in.
* **Part 3** — the 21 load-bearing statements of the accompanying paper proof,
  stated in dependency order.  All are proved except row 21, noted below.
* **Part 4** — the two ends joined: `erdos_742` follows from row 20 and the
  bridge.

## Axiom status

    #print axioms Erdos742.erdos_742
    [propext, Classical.choice, Quot.sound]

No `sorryAx`, no `native_decide`, no added axiom.  This certifies that the
*Lean* proof has no gaps; it certifies nothing about whether each Lean
statement faithfully transcribes the paper statement it is named for.

The file contains exactly one `sorry`, in `row21_per_edge_form_false`.  That
statement is **negative** — it asserts that a proposed per-edge strengthening
of Theorem Σ is false — and it is an input to nothing: no declaration on the
path to `erdos_742` mentions it.

## Toolchain

Lean v4.33.0-rc1, mathlib ae0d973.
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos742

open SimpleGraph

/-! ##############################################################
    ## Part 0. The target statement (transcribed from upstream) ##
    ############################################################## -/

section Upstream

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is diameter-2-critical if it has diameter `2` and removing any edge
increases the diameter beyond `2`.

Transcribed from `google-deepmind/formal-conjectures`,
`FormalConjectures/ErdosProblems/742.lean`.

Note that `SimpleGraph.diam` is `ℕ`-valued and is `0` on a *disconnected*
graph, so the clause `(G.deleteEdges {e}).diam ≠ 2` covers both "the diameter
grows" and "the graph falls apart".  `isD2C_iff_isDiameter2Critical` below
checks that this really does agree with the paper's `diam(G − e) > 2`. -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

end Upstream

/-! **The target.**  Upstream states it as `answer(sorry) ↔ ∀ …`; the
`answer(…) ↔` wrapper is their open-problem idiom, and instantiating `answer`
with `True` reduces it to the right-hand side.  The transcription is the
theorem `Erdos742.erdos_742`, and it is declared at the *end* of this file
(Part 4) rather than here, because it is **proved** — from `row20` plus the
bridge — and so must come after them.  Its statement is verbatim:

```
theorem erdos_742 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4
```

`(Fintype.card V) ^ 2 / 4` is natural-number division, i.e. `⌊n²/4⌋`.
It is Corollary B of the accompanying paper proof. -/

/-! #####################################################
    ## Part 1. The definitions the proof runs on        ##
    ##################################################### -/

namespace Campaign

variable {V : Type*}

/-! ### 1.1 Distance-2 language, and the D2C notion used throughout -/

/-- `Within2 G x y` : `x` and `y` are joined in `G` by a walk of length `≤ 2`.
This is the elementary, walk-free form of "`dist(x,y) ≤ 2`" that the paper
uses throughout (see the proof of Proposition 3.2). -/
def Within2 (G : SimpleGraph V) (x y : V) : Prop :=
  x = y ∨ G.Adj x y ∨ ∃ m, G.Adj x m ∧ G.Adj m y

/-- The diameter-2 condition in the form used here: everything is within
distance `2`, and *some* pair is genuinely at distance `2` (i.e. the graph is
not complete and has at least two vertices). -/
def IsD2 (G : SimpleGraph V) : Prop :=
  (∀ x y, Within2 G x y) ∧ ∃ x y, x ≠ y ∧ ¬ G.Adj x y

/-- The diameter-2-critical condition, stated as the paper uses it: a graph
`G` of diameter 2 is D2C if `diam(G − e) > 2` for every edge `e`, unwound via
the criticality certificate used in the proof of Proposition 3.2 — for each
edge there is a pair whose every `≤2`-path uses that edge. -/
def IsD2C (G : SimpleGraph V) : Prop :=
  IsD2 G ∧ ∀ e ∈ G.edgeSet, ∃ x y, ¬ Within2 (G.deleteEdges {e}) x y

/-! ### 1.2 Witnesses -/

/-- `y` is a **witness at `x`** for the edge `{x,z}`: `y ≠ x`, `xy ∉ E`, and
`N(x) ∩ N(y) = {z}`. -/
def IsWitAt (G : SimpleGraph V) (x z y : V) : Prop :=
  y ≠ x ∧ ¬ G.Adj x y ∧ G.commonNeighbors x y = {z}

/-- `Wit_x(z)`, the set of witnesses at `x` for the edge `{x,z}`. -/
def WitAt (G : SimpleGraph V) (x z : V) : Set V := {y | IsWitAt G x z y}

/-- `Wit(e) = Wit_a(b) ∪ Wit_b(a)` for `e = {a,b}`.  Manifestly symmetric in
`a` and `b` (see `wit_comm`). -/
def Wit (G : SimpleGraph V) (a b : V) : Set V := WitAt G a b ∪ WitAt G b a

/-- `codeg(u,v) = |N(u) ∩ N(v)|`. -/
noncomputable def codeg (G : SimpleGraph V) (u v : V) : ℕ :=
  (G.commonNeighbors u v).ncard

/-! ### 1.3 The three pair classes, `Φ` and `D` -/

/-- `E0(F)` : the edges of codegree `0`. -/
def E0 (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u,v) ∧ G.Adj u v ∧ G.commonNeighbors u v = ∅}

/-- `Ew(F)` : the edges of codegree `≥ 1` that carry a witness. -/
def Ew (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u,v) ∧ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty ∧
        (Wit G u v).Nonempty}

/-- `A(F)` : the NON-edges of codegree `≥ 1`. -/
def Anon (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u,v) ∧ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty}

/-- `disj(F)` : unordered pairs (adjacent or not) with `N(u) ∩ N(v) = ∅`.
This is Füredi's `disj F` ([Fü92, p. 82]) verbatim. -/
def Disj (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u,v) ∧ u ≠ v ∧ G.commonNeighbors u v = ∅}

/-- `X(F)` : the witnessed edges of codegree `≥ 1`.  The paper notes
`X(F) = |Ew(F)|` identically, so we take that as the definition. -/
noncomputable def X (G : SimpleGraph V) : ℕ := (Ew G).ncard

/-- `Φ(F) := e(F) + disj(F) + X(F)`. -/
noncomputable def Phi (G : SimpleGraph V) : ℕ :=
  G.edgeSet.ncard + (Disj G).ncard + X G

/-- `D(F) := |E0(F)| + |Ew(F)| − |A(F)|`, an *integer*. -/
noncomputable def Dv (G : SimpleGraph V) : ℤ :=
  ((E0 G).ncard : ℤ) + ((Ew G).ncard : ℤ) - ((Anon G).ncard : ℤ)

/-- `Nw(x) := {t : {x,t} ∈ Ew(F)}`. -/
def Nw (G : SimpleGraph V) (x : V) : Set V := {t | s(x,t) ∈ Ew G}

/-- `D2(x) := {s : s ≠ x, xs ∉ E, codeg(x,s) ≥ 1} = {s : {x,s} ∈ A(F)}`. -/
def D2set (G : SimpleGraph V) (x : V) : Set V := {t | s(x,t) ∈ Anon G}

/-! ### 1.4 Per-pair quantities for an edge `{u,v}`

The four categories of `V ∖ {u,v}`:
(a) `N(u) ∖ N[v]`, (b) `N(v) ∖ N[u]`, (d) `W_uv = N(u) ∩ N(v)`,
(c) the rest (adjacent to neither `u` nor `v`). -/

/-- Category (c) of the edge `{u,v}`: vertices adjacent to neither endpoint. -/
def catC (G : SimpleGraph V) (u v : V) : Set V :=
  {w | w ≠ u ∧ w ≠ v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w}

/-- Category (a) of the edge `{u,v}`: `N(u) ∖ N[v]`.  (Category (b) is
`catA G v u`.) -/
def catA (G : SimpleGraph V) (u v : V) : Set V :=
  {w | G.Adj u w ∧ w ≠ v ∧ ¬ G.Adj v w}

/-- `W_uv := N(u) ∩ N(v)` — category (d). -/
def Wuv (G : SimpleGraph V) (u v : V) : Set V := G.commonNeighbors u v

/-- `R_c(u,v) := #{(x,w) : x ∈ {u,v}, w ∈ category (c), {x,w} ∈ A(F)}`. -/
noncomputable def Rc (G : SimpleGraph V) (u v : V) : ℕ :=
  {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ catC G u v ∧ s(p.1, p.2) ∈ Anon G}.ncard

/-- `B(u,v) := #{edges {w,z} ∈ Ew(F), w,z ∉ {u,v}, Wit({w,z}) ⊆ {u,v}}` —
the remote `Ew`-edges all of whose witnesses lie in the pair. -/
noncomputable def Bc (G : SimpleGraph V) (u v : V) : ℕ :=
  {e : Sym2 V | e ∈ Ew G ∧ ∃ w z, e = s(w,z) ∧ w ≠ u ∧ w ≠ v ∧ z ≠ u ∧ z ≠ v ∧
      Wit G w z ⊆ ({u, v} : Set V)}.ncard

/-- `K_A(u,v)` : pairs `(x,w0)` with `x ∈ {u,v}`, `w0 ∈ W_uv`, `{x,w0} ∈ Ew(F)`
and `{x,w0}` witnessed **at `w0`**. -/
noncomputable def KA (G : SimpleGraph V) (u v : V) : ℕ :=
  {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ Wuv G u v ∧ s(p.1, p.2) ∈ Ew G ∧
      (WitAt G p.2 p.1).Nonempty}.ncard

/-- `K_B(u,v)` : as `KA`, but witnessed at `x` and **not** at `w0`. -/
noncomputable def KB (G : SimpleGraph V) (u v : V) : ℕ :=
  {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ Wuv G u v ∧ s(p.1, p.2) ∈ Ew G ∧
      (WitAt G p.1 p.2).Nonempty ∧ WitAt G p.2 p.1 = ∅}.ncard

/-- `K(u,v) := K_A(u,v) + K_B(u,v)`. -/
noncomputable def Kc (G : SimpleGraph V) (u v : V) : ℕ := KA G u v + KB G u v

/-- `U_a(u,v)` : the category-(a) neighbours `w` of `u` for which `{u,w}` is
neither an `E0` nor an `Ew` edge.  (`U_b(u,v) = Ua G v u`.) -/
noncomputable def Ua (G : SimpleGraph V) (u v : V) : ℕ :=
  {w | w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅}.ncard

/-- `R⁺(u,v)` : the guaranteed rebate pairs of the refined deletion bound. -/
noncomputable def Rplus (G : SimpleGraph V) (u v : V) : ℕ :=
  {p : V × V | p.1 ∈ Wuv G u v ∧ ¬ G.Adj p.1 p.2 ∧
      ((p.2 ∈ catA G u v ∧ G.commonNeighbors p.1 p.2 = {u}) ∨
       (p.2 ∈ catA G v u ∧ G.commonNeighbors p.1 p.2 = {v}))}.ncard

open scoped Classical in
/-- `c(P,F)` : `+1` on `E0 ∪ Ew`, `−1` on `A`, `0` otherwise; so
`D(F) = Σ_P c(P,F)`. -/
noncomputable def cwt (G : SimpleGraph V) (P : Sym2 V) : ℤ :=
  if P ∈ E0 G ∪ Ew G then 1 else if P ∈ Anon G then -1 else 0

open scoped Classical in
/-- `S(u,v) := Σ_{w ∉ {u,v}} [c({u,w},F) + c({v,w},F)]`. -/
noncomputable def Sc [Fintype V] (G : SimpleGraph V) (u v : V) : ℤ :=
  ∑ w ∈ Finset.univ.filter (fun w => w ≠ u ∧ w ≠ v),
    (cwt G s(u,w) + cwt G s(v,w))

/-- `Slack_c(u,v) := R_c(u,v) − B(u,v)`. -/
noncomputable def Slackc (G : SimpleGraph V) (u v : V) : ℤ :=
  (Rc G u v : ℤ) - (Bc G u v : ℤ)

/-- The `Σ`-summand `Slack_c(u,v) − K_B(u,v)` as a function of an ordered
pair.  It is symmetric (`sigmaTerm_comm`, proved below), which is what makes
`Σ` a well-defined sum over *unordered* pairs. -/
noncomputable def sigmaTerm (G : SimpleGraph V) (u v : V) : ℤ :=
  Slackc G u v - (KB G u v : ℤ)

/-! ####################################################
    ## Part 2. THE BRIDGE — the load-bearing theorems ##
    #################################################### -/

/-! ### 2.1 `Within2` is `edist ≤ 2` -/

theorem within2_iff_edist_le_two {G : SimpleGraph V} {x y : V} :
    Within2 G x y ↔ G.edist x y ≤ 2 := by
  constructor
  · rintro (rfl | h | ⟨m, h1, h2⟩)
    · simp
    · exact le_trans (edist_le_one_iff_adj_or_eq.mpr (Or.inl h)) (by norm_num)
    · exact le_trans (G.edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))) (by simp)
  · intro h
    by_contra hc
    rw [Within2] at hc
    obtain ⟨hne, hadj, hcn⟩ :
        x ≠ y ∧ ¬ G.Adj x y ∧ ∀ m, ¬ (G.Adj x m ∧ G.Adj m y) :=
      ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr (Or.inl h)),
        fun m h => hc (Or.inr (Or.inr ⟨m, h⟩))⟩
    have hempty : G.commonNeighbors x y = ∅ := by
      ext m
      simp only [mem_commonNeighbors, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact hcn m ⟨h1, h2.symm⟩
    exact absurd h (not_le.mpr (two_lt_edist_iff.mpr ⟨hne, hadj, hempty⟩))

/-! ### 2.2 `IsD2` is `ediam = 2`, and `diam = 2` is `ediam = 2` -/

theorem ediam_eq_two_iff_isD2 {G : SimpleGraph V} :
    G.ediam = 2 ↔ IsD2 G := by
  constructor
  · intro h
    refine ⟨fun x y => within2_iff_edist_le_two.mpr (le_trans edist_le_ediam h.le), ?_⟩
    by_contra hc
    have hc' : ∀ u v : V, u ≠ v → G.Adj u v := by
      intro u v huv
      by_contra hadj
      exact hc ⟨u, v, huv, hadj⟩
    have h1 : G.ediam ≤ 1 := by
      refine ediam_le_iff.mpr fun u v => ?_
      rcases eq_or_ne u v with rfl | hne
      · simp
      · exact edist_le_one_iff_adj_or_eq.mpr (Or.inl (hc' u v hne))
    rw [h] at h1
    norm_num at h1
  · rintro ⟨hall, x, y, hne, hadj⟩
    have hle : G.ediam ≤ 2 :=
      ediam_le_iff.mpr fun u v => within2_iff_edist_le_two.mp (hall u v)
    have hge : (2 : ℕ∞) ≤ G.ediam := by
      refine le_trans ?_ (edist_le_ediam (u := x) (v := y))
      have h0 : G.edist x y ≠ 0 := fun hc => hne (edist_eq_zero_iff.mp hc)
      have h1 : G.edist x y ≠ 1 := fun hc => hadj (edist_eq_one_iff_adj.mp hc)
      rw [← one_add_one_eq_two]
      refine Order.add_one_le_of_lt (lt_of_le_of_ne ?_ (Ne.symm h1))
      exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h0)
    exact le_antisymm hle hge

theorem diam_eq_two_iff_ediam_eq_two {G : SimpleGraph V} :
    G.diam = 2 ↔ G.ediam = 2 := by
  have hd : G.diam = G.ediam.toNat := rfl
  rw [hd, ENat.toNat_eq_iff (by norm_num : (2 : ℕ) ≠ 0)]
  norm_num

theorem diam_ne_two_iff_ediam_ne_two {G : SimpleGraph V} :
    G.diam ≠ 2 ↔ G.ediam ≠ 2 :=
  not_congr diam_eq_two_iff_ediam_eq_two

/-! ### 2.3 The bridge

`SimpleGraph.diam` is `ℕ`-valued with `diam = 0` on a disconnected graph, so
`(G.deleteEdges {e}).diam ≠ 2` is *not* literally the paper's
`diam(G − e) > 2`.  The two do agree, but only because deleting an edge from a
diameter-`2` graph can never make the extended diameter smaller; that is what
`ediam_anti` supplies below. -/

/-- **THE BRIDGE.**  The D2C notion used in this file coincides with the
upstream `Erdos742.IsDiameter2Critical`.  Proved; no `sorry`. -/
theorem isD2C_iff_isDiameter2Critical {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    IsD2C G ↔ Erdos742.IsDiameter2Critical G := by
  constructor
  · rintro ⟨hd2, hcrit⟩
    refine ⟨diam_eq_two_iff_ediam_eq_two.mpr (ediam_eq_two_iff_isD2.mpr hd2), ?_⟩
    intro e he
    obtain ⟨x, y, hxy⟩ := hcrit e he
    rw [diam_ne_two_iff_ediam_ne_two]
    intro hc
    exact hxy (within2_iff_edist_le_two.mpr (le_trans edist_le_ediam hc.le))
  · rintro ⟨hdiam, hcrit⟩
    have hed : G.ediam = 2 := diam_eq_two_iff_ediam_eq_two.mp hdiam
    refine ⟨ediam_eq_two_iff_isD2.mp hed, ?_⟩
    intro e he
    have hne := (diam_ne_two_iff_ediam_ne_two).mp (hcrit e he)
    -- deleting an edge cannot decrease the extended diameter
    have hge : (2 : ℕ∞) ≤ (G.deleteEdges {e}).ediam := by
      rw [← hed]; exact ediam_anti (G.deleteEdges_le {e})
    have hgt : (2 : ℕ∞) < (G.deleteEdges {e}).ediam := lt_of_le_of_ne hge (Ne.symm hne)
    by_contra hc
    have hc' : ∀ u v, Within2 (G.deleteEdges {e}) u v := by
      intro u v
      by_contra h
      exact hc ⟨u, v, h⟩
    have hle : (G.deleteEdges {e}).ediam ≤ 2 :=
      ediam_le_iff.mpr fun u v => within2_iff_edist_le_two.mp (hc' u v)
    exact absurd hle (not_le.mpr hgt)

/-! ### 2.4 Well-definedness of the pair classes (Proposition 2.1's real content)

`E0`, `Ew`, `Anon`, `Disj` are defined as sets of `Sym2 V` by an existential
over *ordered* representatives.  The following membership characterisations
say that those definitions mean what they are meant to mean; each consumes the
symmetry of the defining condition, which for `Ew` is exactly Proposition 2.1
(row 1). -/

theorem wit_comm (G : SimpleGraph V) (a b : V) : Wit G a b = Wit G b a := by
  simp [Wit, Set.union_comm]

/-- **Proposition 2.1 (symmetry of the witness condition)** — row 1.
Proved; no `sorry`. -/
theorem isWitAt_symm (G : SimpleGraph V) (x z y : V) :
    IsWitAt G x z y ↔ IsWitAt G y z x := by
  unfold IsWitAt
  rw [G.commonNeighbors_symm x y]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, fun h => h2 h.symm, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, fun h => h2 h.symm, h3⟩

theorem mem_E0_iff (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ E0 G ↔ G.Adj u v ∧ G.commonNeighbors u v = ∅ := by
  constructor
  · rintro ⟨a, b, hab, hadj, hcn⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, hcn⟩
    · exact ⟨hadj.symm, by rwa [G.commonNeighbors_symm]⟩
  · rintro ⟨h1, h2⟩; exact ⟨u, v, rfl, h1, h2⟩

theorem mem_Ew_iff (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ Ew G ↔ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty ∧
      (Wit G u v).Nonempty := by
  constructor
  · rintro ⟨a, b, hab, hadj, hcn, hw⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, hcn, hw⟩
    · exact ⟨hadj.symm, by rwa [G.commonNeighbors_symm], by rwa [wit_comm]⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨u, v, rfl, h1, h2, h3⟩

theorem mem_Anon_iff (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ Anon G ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty := by
  constructor
  · rintro ⟨a, b, hab, hne, hadj, hcn⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hadj, hcn⟩
    · exact ⟨hne.symm, fun h => hadj h.symm, by rwa [G.commonNeighbors_symm]⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨u, v, rfl, h1, h2, h3⟩

theorem mem_Disj_iff (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ Disj G ↔ u ≠ v ∧ G.commonNeighbors u v = ∅ := by
  constructor
  · rintro ⟨a, b, hab, hne, hcn⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hcn⟩
    · exact ⟨hne.symm, by rwa [G.commonNeighbors_symm]⟩
  · rintro ⟨h1, h2⟩; exact ⟨u, v, rfl, h1, h2⟩

/-- `E0` and `Ew` are disjoint (used in Proposition 3.2).  Proved. -/
theorem E0_disjoint_Ew (G : SimpleGraph V) : Disjoint (E0 G) (Ew G) := by
  rw [Set.disjoint_left]
  rintro e he0 hew
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_E0_iff] at he0
    rw [mem_Ew_iff] at hew
    exact absurd he0.2 (Set.nonempty_iff_ne_empty.mp hew.2.1)

/-! ### 2.5 `Σ` is well defined

Each of `R_c`, `B` and `K_B` is invariant under swapping the two endpoints of
the pair — the defining conditions are literally symmetric in `u` and `v` — so
the `Σ`-summand descends to `Sym2 V`. -/

theorem rc_comm (G : SimpleGraph V) (u v : V) : Rc G u v = Rc G v u := by
  unfold Rc catC
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  tauto

theorem bc_comm (G : SimpleGraph V) (u v : V) : Bc G u v = Bc G v u := by
  unfold Bc
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.pair_comm u v]
  constructor
  · rintro ⟨h1, w, z, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, w, z, h2, h4, h3, h6, h5, h7⟩
  · rintro ⟨h1, w, z, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, w, z, h2, h4, h3, h6, h5, h7⟩

theorem kb_comm (G : SimpleGraph V) (u v : V) : KB G u v = KB G v u := by
  unfold KB Wuv
  congr 1
  ext p
  simp only [Set.mem_setOf_eq, mem_commonNeighbors]
  tauto

theorem sigmaTerm_comm (G : SimpleGraph V) (u v : V) :
    sigmaTerm G u v = sigmaTerm G v u := by
  unfold sigmaTerm Slackc
  rw [rc_comm G u v, bc_comm G u v, kb_comm G u v]

/-- `Σ`'s summand, as a genuine function of the unordered pair. -/
noncomputable def sigmaTermS (G : SimpleGraph V) : Sym2 V → ℤ :=
  Sym2.lift ⟨sigmaTerm G, sigmaTerm_comm G⟩

open scoped Classical in
/-- `Σ(F) := Σ_{{u,v} ∈ Ew(F)} [Slack_c(u,v) − K_B(u,v)]`.
(`Ew(F) = ∅` makes this an empty sum, hence `0`.) -/
noncomputable def Sig [Fintype V] (G : SimpleGraph V) : ℤ :=
  ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), sigmaTermS G e

/-! ### 2.6 `D_inc`, and the two-vertex deletion

`D_inc(u,v) := D(F) − D(F − {u,v})`, where `F − {u,v}` deletes **both
vertices**.  We realise `F − {u,v}` as the induced subgraph on the subtype
`{w // w ≠ u ∧ w ≠ v}`. -/

/-- `F − {u,v}` : both vertices deleted. -/
abbrev delPair (G : SimpleGraph V) (u v : V) :
    SimpleGraph {w : V // w ≠ u ∧ w ≠ v} :=
  G.induce {w : V | w ≠ u ∧ w ≠ v}

/-- `D_inc(u,v) := D(F) − D(F − {u,v})`. -/
noncomputable def Dinc (G : SimpleGraph V) (u v : V) : ℤ :=
  Dv G - Dv (delPair G u v)

/-! ##################################################################
    ##  Part 2.7 — THE `F − {u,v}` TRANSPORT LAYER                   ##
    ################################################################## -/

section Transport

/-! ### 2.7.1 `F − {u,v}` : adjacency and common neighbours -/

/-- Adjacency in `F − {u,v}` is adjacency in `F` of the underlying vertices. -/
@[simp] theorem delPair_adj (G : SimpleGraph V) (u v : V)
    (a b : {w : V // w ≠ u ∧ w ≠ v}) :
    (delPair G u v).Adj a b ↔ G.Adj (a : V) (b : V) := Iff.rfl

/-- Common neighbours in `F − {u,v}` are those of `F`, pulled back along the
inclusion: vertex deletion never adds a common neighbour. -/
theorem delPair_commonNeighbors (G : SimpleGraph V) (u v : V)
    (a b : {w : V // w ≠ u ∧ w ≠ v}) :
    (delPair G u v).commonNeighbors a b =
      Subtype.val ⁻¹' (G.commonNeighbors (a : V) (b : V)) := by
  ext t
  simp [SimpleGraph.mem_commonNeighbors]

/-- `N_{F'}(a) ∩ N_{F'}(b) = (N_F(a) ∩ N_F(b)) ∖ {u,v}` — the image form. -/
theorem val_image_delPair_commonNeighbors (G : SimpleGraph V) (u v : V)
    (a b : {w : V // w ≠ u ∧ w ≠ v}) :
    Subtype.val '' ((delPair G u v).commonNeighbors a b) =
      G.commonNeighbors (a : V) (b : V) \ ({u, v} : Set V) := by
  ext t
  simp only [delPair_commonNeighbors, Set.mem_image, Set.mem_preimage, Set.mem_sdiff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨t', ht1, ht2⟩, hmem, rfl⟩
    refine ⟨hmem, ?_⟩
    rintro (h | h)
    exacts [ht1 h, ht2 h]
  · rintro ⟨hmem, hne⟩
    exact ⟨⟨t, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩, hmem, rfl⟩

/-- Deletion cannot create a common neighbour. -/
theorem commonNeighbors_nonempty_of_delPair {G : SimpleGraph V} {u v : V}
    {a b : {w : V // w ≠ u ∧ w ≠ v}}
    (h : ((delPair G u v).commonNeighbors a b).Nonempty) :
    (G.commonNeighbors (a : V) (b : V)).Nonempty := by
  obtain ⟨t, ht⟩ := h
  rw [delPair_commonNeighbors] at ht
  exact ⟨(t : V), ht⟩

/-! ### 2.7.2 `Sym2.map Subtype.val` : the pair transport -/

/-- The pair transport is injective. -/
theorem sym2map_val_injective (u v : V) :
    Function.Injective
      (Sym2.map (Subtype.val : {w : V // w ≠ u ∧ w ≠ v} → V)) :=
  Sym2.map.injective Subtype.val_injective

@[simp] theorem sym2map_val_mk (u v : V) (a b : {w : V // w ≠ u ∧ w ≠ v}) :
    Sym2.map (Subtype.val) s(a, b) = s((a : V), (b : V)) := rfl

/-- The image of the pair transport is exactly the set of **remote** pairs. -/
theorem exists_sym2map_iff {u v : V} (P : Sym2 V) :
    (∃ e : Sym2 {w : V // w ≠ u ∧ w ≠ v}, Sym2.map Subtype.val e = P) ↔
      (u ∉ P ∧ v ∉ P) := by
  constructor
  · rintro ⟨e, rfl⟩
    induction e using Sym2.ind with
    | _ a b =>
      simp only [sym2map_val_mk, Sym2.mem_iff]
      refine ⟨?_, ?_⟩
      · rintro (h | h); exacts [a.2.1 h.symm, b.2.1 h.symm]
      · rintro (h | h); exacts [a.2.2 h.symm, b.2.2 h.symm]
  · intro h
    induction P using Sym2.ind with
    | _ x y =>
      simp only [Sym2.mem_iff, not_or] at h
      obtain ⟨⟨hxu, hyu⟩, hxv, hyv⟩ := h
      exact ⟨s(⟨x, fun h => hxu h.symm, fun h => hxv h.symm⟩,
              ⟨y, fun h => hyu h.symm, fun h => hyv h.symm⟩), rfl⟩

/-! ### 2.7.3 `c(·,F)` vanishes on the diagonal -/

/-- A diagonal "pair" lies in none of the three classes, so it is weighted `0`.
This is what lets a sum over *all* of `Sym2 V` stand in for the paper's sum
over unordered pairs of DISTINCT vertices. -/
@[simp] theorem cwt_diag (G : SimpleGraph V) (x : V) : cwt G s(x, x) = 0 := by
  have h1 : s(x, x) ∉ E0 G := by
    rintro ⟨a, b, hab, hadj, -⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact G.irrefl hadj
  have h2 : s(x, x) ∉ Ew G := by
    rintro ⟨a, b, hab, hadj, -⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact G.irrefl hadj
  have h3 : s(x, x) ∉ Anon G := by
    rintro ⟨a, b, hab, hne, -⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne rfl
  simp [cwt, h1, h2, h3]

/-! ### 2.7.4 Summing `c(·,F)` over `Sym2 V` gives `D(F)`

`D(F) = Σ_P c(P,F)` over ALL unordered pairs.  Note this uses only the
*definitions* of `D` and `c`, **not** Proposition 3.1. -/

/-- `Σ_x [x ∈ s] = |s|`, the bridge from `Set.ncard` to a `Finset` sum. -/
theorem sum_ite_mem_eq_ncard {α : Type*} [Fintype α] (s : Set α)
    [DecidablePred (· ∈ s)] :
    ∑ x : α, (if x ∈ s then (1 : ℤ) else 0) = (s.ncard : ℤ) := by
  rw [Finset.sum_boole]
  congr 1
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

open scoped Classical in
/-- `c(P,F)` split into its three indicator pieces.  Uses `E0 ∩ Ew = ∅` and the
fact that `A` consists of non-edges while `E0 ∪ Ew` consists of edges. -/
theorem cwt_eq_indicators (G : SimpleGraph V) (P : Sym2 V) :
    cwt G P = (if P ∈ E0 G then (1 : ℤ) else 0) + (if P ∈ Ew G then 1 else 0)
      - (if P ∈ Anon G then 1 else 0) := by
  classical
  have hEA : P ∈ E0 G → P ∉ Anon G := by
    rintro ⟨a, b, rfl, hadj, -⟩ ⟨c, d, hcd, -, hnadj, -⟩
    rw [Sym2.eq_iff] at hcd
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hnadj hadj, hnadj hadj.symm]
  have hWA : P ∈ Ew G → P ∉ Anon G := by
    rintro ⟨a, b, rfl, hadj, -⟩ ⟨c, d, hcd, -, hnadj, -⟩
    rw [Sym2.eq_iff] at hcd
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hnadj hadj, hnadj hadj.symm]
  have hEW : P ∈ E0 G → P ∉ Ew G := fun h h' =>
    (Set.disjoint_left.mp (E0_disjoint_Ew G)) h h'
  unfold cwt
  by_cases h0 : P ∈ E0 G
  · rw [if_pos (Set.mem_union_left _ h0), if_pos h0, if_neg (hEW h0), if_neg (hEA h0)]
    ring
  · by_cases hw : P ∈ Ew G
    · rw [if_pos (Set.mem_union_right _ hw), if_neg h0, if_pos hw, if_neg (hWA hw)]
      ring
    · have hnu : P ∉ E0 G ∪ Ew G := by rintro (h | h); exacts [h0 h, hw h]
      rw [if_neg hnu, if_neg h0, if_neg hw]
      by_cases ha : P ∈ Anon G
      · rw [if_pos ha, if_pos ha]; ring
      · rw [if_neg ha, if_neg ha]; ring

/-- **`D(F) = Σ_{P ∈ Sym2 V} c(P,F)`.** -/
theorem Dv_eq_sum_cwt [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Dv G = ∑ P : Sym2 V, cwt G P := by
  classical
  simp only [cwt_eq_indicators, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_ite_mem_eq_ncard]
  rfl

/-! ### 2.7.5 The three-way split of a sum over `Sym2 V`

`Sym2 V = {u,v} ⊔ (pairs meeting {u,v} in exactly one vertex) ⊔ (remote pairs)`,
and the remote pairs are the image of `Sym2 (V ∖ {u,v})` under the transport.
This is the combinatorial core of the deletion decomposition. -/

variable {M : Type*} [AddCommMonoid M]

/-- Pairs containing `u` are indexed by their other endpoint, bijectively
(including the diagonal pair `s(u,u)`). -/
theorem sum_filter_mem_sym2 [Fintype V] [DecidableEq V] (f : Sym2 V → M) (u : V) :
    ∑ P ∈ Finset.univ.filter (fun P : Sym2 V => u ∈ P), f P = ∑ w : V, f s(u, w) := by
  classical
  have hinj : ∀ a ∈ (Finset.univ : Finset V), ∀ b ∈ (Finset.univ : Finset V),
      s(u, a) = s(u, b) → a = b := by
    intro a _ b _ h
    rcases Sym2.eq_iff.mp h with ⟨-, hab⟩ | ⟨hub, hau⟩
    · exact hab
    · exact hau.trans hub
  have himg : Finset.univ.filter (fun P : Sym2 V => u ∈ P)
      = Finset.image (fun w => s(u, w)) Finset.univ := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Sym2.mem_iff_exists]
    exact ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  rw [himg, Finset.sum_image hinj]

/-- Pairs meeting `{u,v}` in `v` only are indexed by their other endpoint,
which ranges over `V ∖ {u}`. -/
theorem sum_filter_mem_sym2' [Fintype V] [DecidableEq V] (f : Sym2 V → M)
    {u v : V} (huv : u ≠ v) :
    ∑ P ∈ Finset.univ.filter (fun P : Sym2 V => u ∉ P ∧ v ∈ P), f P
      = ∑ w ∈ Finset.univ.filter (fun w => w ≠ u), f s(v, w) := by
  classical
  have hinj : ∀ a ∈ Finset.univ.filter (fun w : V => w ≠ u),
      ∀ b ∈ Finset.univ.filter (fun w : V => w ≠ u), s(v, a) = s(v, b) → a = b := by
    intro a _ b _ h
    rcases Sym2.eq_iff.mp h with ⟨-, hab⟩ | ⟨hvb, hav⟩
    · exact hab
    · exact hav.trans hvb
  have himg : Finset.univ.filter (fun P : Sym2 V => u ∉ P ∧ v ∈ P)
      = Finset.image (fun w => s(v, w)) (Finset.univ.filter (fun w => w ≠ u)) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hu, hv⟩
      obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hv
      simp only [Sym2.mem_iff, not_or] at hu
      exact ⟨b, fun h => hu.2 h.symm, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, by simp⟩
      simp only [Sym2.mem_iff, not_or]
      exact ⟨huv, fun h => hb h.symm⟩
  rw [himg, Finset.sum_image hinj]

/-- The remote pairs are the image of `Sym2 {w // w ≠ u ∧ w ≠ v}`. -/
theorem sum_filter_remote_sym2 [Fintype V] [DecidableEq V] (f : Sym2 V → M) (u v : V) :
    ∑ P ∈ Finset.univ.filter (fun P : Sym2 V => u ∉ P ∧ v ∉ P), f P
      = ∑ e : Sym2 {w : V // w ≠ u ∧ w ≠ v}, f (Sym2.map Subtype.val e) := by
  classical
  have himg : Finset.univ.filter (fun P : Sym2 V => u ∉ P ∧ v ∉ P)
      = Finset.image (Sym2.map Subtype.val) (Finset.univ :
          Finset (Sym2 {w : V // w ≠ u ∧ w ≠ v})) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact (exists_sym2map_iff P).symm
  rw [himg, Finset.sum_image (fun a _ b _ h => sym2map_val_injective u v h)]

/-- **The split.**  For any `f : Sym2 V → M` vanishing on the diagonal and any
`u ≠ v`, the sum over `Sym2 V` splits as `{u,v}` + incident + remote. -/
theorem sum_sym2_split [Fintype V] [DecidableEq V] (f : Sym2 V → M)
    (hdiag : ∀ x, f s(x, x) = 0) {u v : V} (huv : u ≠ v) :
    ∑ P : Sym2 V, f P
      = f s(u, v)
        + (∑ w ∈ Finset.univ.filter (fun w => w ≠ u ∧ w ≠ v), (f s(u, w) + f s(v, w)))
        + ∑ e : Sym2 {w : V // w ≠ u ∧ w ≠ v}, f (Sym2.map Subtype.val e) := by
  classical
  set T : Finset V := Finset.univ.filter (fun w => w ≠ u ∧ w ≠ v) with hTdef
  -- `V = {u} ⊔ {v} ⊔ T`
  have hvT : v ∉ T := by simp [hTdef]
  have huvT : u ∉ insert v T := by
    simp only [Finset.mem_insert, hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    push_neg
    exact ⟨huv, fun h => absurd rfl h⟩
  have hunivV : (Finset.univ : Finset V) = insert u (insert v T) := by
    ext w
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, hTdef, Finset.mem_filter,
      true_and]
    by_cases h : w = u
    · exact Or.inl h
    · by_cases h' : w = v
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨h, h'⟩)
  have hfilterU : Finset.univ.filter (fun w : V => w ≠ u) = insert v T := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hTdef]
    constructor
    · intro h
      by_cases h' : w = v
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact fun h => huv h.symm
      · exact h
  -- split off `u ∈ P`, then `v ∈ P`
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Sym2 V))
        (fun P => u ∈ P) f,
      ← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun P : Sym2 V => ¬ u ∈ P)) (fun P => v ∈ P) f,
      Finset.filter_filter, Finset.filter_filter,
      sum_filter_mem_sym2 f u]
  have e1 : ∑ P ∈ Finset.univ.filter (fun P : Sym2 V => ¬ u ∈ P ∧ v ∈ P), f P
      = ∑ w ∈ Finset.univ.filter (fun w => w ≠ u), f s(v, w) :=
    sum_filter_mem_sym2' f huv
  have e2 : ∑ P ∈ Finset.univ.filter (fun P : Sym2 V => ¬ u ∈ P ∧ ¬ v ∈ P), f P
      = ∑ e : Sym2 {w : V // w ≠ u ∧ w ≠ v}, f (Sym2.map Subtype.val e) :=
    sum_filter_remote_sym2 f u v
  rw [e1, e2, hfilterU, hunivV, Finset.sum_insert huvT, Finset.sum_insert hvT,
    Finset.sum_insert hvT, hdiag u, hdiag v, Finset.sum_add_distrib]
  abel

/-- `S(u,v)` written with the same `Finset.filter` instance that `sum_sym2_split`
produces.  (`Sc` is declared under `open scoped Classical`, so its filter carries
a different — propositionally equal, but not syntactically equal — `Decidable`
instance; `abel` and `linarith` treat the two sums as distinct atoms without
this bridge.) -/
theorem Sc_eq_sum [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    Sc G u v = ∑ w ∈ Finset.univ.filter (fun w => w ≠ u ∧ w ≠ v),
      (cwt G s(u, w) + cwt G s(v, w)) := by
  unfold Sc
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-! ### 2.7.6 Witness survival

The single line of *mathematics* in the whole transport layer: a witness that
avoids `u` and `v` is still a witness after `u` and `v` are deleted, because
`N(w) ∩ N(y) = {z}` and `z` is itself remote, so removing `u` and `v` removes
nothing from the intersection. -/

/-- **Witness survival.**  If `y ∉ {u,v}` witnesses `{a,b}` at `a` in `F`, then
`y` still witnesses it at `a` in `F − {u,v}`.  (`a`, `b` are already remote,
being of the deleted-pair subtype.) -/
theorem delPair_witAt (G : SimpleGraph V) {u v : V}
    {a b : {w : V // w ≠ u ∧ w ≠ v}} {y : V}
    (hy : y ∈ WitAt G (a : V) (b : V)) (hyu : y ≠ u) (hyv : y ≠ v) :
    (⟨y, hyu, hyv⟩ : {t : V // t ≠ u ∧ t ≠ v}) ∈ WitAt (delPair G u v) a b := by
  obtain ⟨hya, hadj, hcn⟩ := hy
  refine ⟨fun h => hya (congrArg Subtype.val h), hadj, ?_⟩
  rw [delPair_commonNeighbors]
  ext t
  simp only [Set.mem_preimage, hcn, Set.mem_singleton_iff, Subtype.ext_iff]

/-! ### 2.7.7 Evaluating `c(·,F)` by edge/non-edge -/

open scoped Classical in
/-- On a non-edge, `c` is `−1` exactly on `A(F)`. -/
theorem cwt_of_not_adj (G : SimpleGraph V) {x y : V} (hn : ¬ G.Adj x y) :
    cwt G s(x, y) = if s(x, y) ∈ Anon G then -1 else 0 := by
  have h1 : s(x, y) ∉ E0 G := fun h => hn ((mem_E0_iff G x y).mp h).1
  have h2 : s(x, y) ∉ Ew G := fun h => hn ((mem_Ew_iff G x y).mp h).1
  unfold cwt
  rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h])]

open scoped Classical in
/-- On an edge, `c` is `+1` exactly on `E0 ∪ Ew`. -/
theorem cwt_of_adj (G : SimpleGraph V) {x y : V} (ha : G.Adj x y) :
    cwt G s(x, y) = if s(x, y) ∈ E0 G ∪ Ew G then 1 else 0 := by
  have h3 : s(x, y) ∉ Anon G := fun h => ((mem_Anon_iff G x y).mp h).2.1 ha
  unfold cwt
  by_cases h : s(x, y) ∈ E0 G ∪ Ew G
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h3]

/-- `c(·,F) ≤ 1` always — the `c({u,v},F) ≤ +1` step of the refined deletion
bound. -/
theorem cwt_le_one (G : SimpleGraph V) (P : Sym2 V) : cwt G P ≤ 1 := by
  unfold cwt
  split
  · exact le_refl 1
  · split <;> norm_num

/-! ### 2.7.8 Remote transitions -/

/-- `B(u,v)` as a *set*; `Bc` is its cardinality by definition. -/
def BSet (G : SimpleGraph V) (u v : V) : Set (Sym2 V) :=
  {e : Sym2 V | e ∈ Ew G ∧ ∃ w z, e = s(w,z) ∧ w ≠ u ∧ w ≠ v ∧ z ≠ u ∧ z ≠ v ∧
      Wit G w z ⊆ ({u, v} : Set V)}

theorem Bc_eq_ncard_BSet [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    Bc G u v = (BSet G u v).ncard := rfl

open scoped Classical in
/-- **Remote transitions.**  For every remote pair `P`,
`c(P,F) − c(P,F′) ≤ [P ∈ B(u,v)]`.  The `+1` transition can happen only for a
remote `Ew`-edge all of whose witnesses lie in `{u,v}` — which is exactly a
`B`-edge — and that is where witness survival is used. -/
theorem remote_transition_le (G : SimpleGraph V) {u v : V}
    (e : Sym2 {w : V // w ≠ u ∧ w ≠ v}) :
    cwt G (Sym2.map Subtype.val e) - cwt (delPair G u v) e
      ≤ if Sym2.map Subtype.val e ∈ BSet G u v then 1 else 0 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [sym2map_val_mk]
    have hR0 : (0 : ℤ) ≤ if s((a : V), (b : V)) ∈ BSet G u v then (1 : ℤ) else 0 := by
      split <;> norm_num
    by_cases hadj : G.Adj (a : V) (b : V)
    · -- P is an EDGE of F, hence of F′
      have hadj' : (delPair G u v).Adj a b := hadj
      rw [cwt_of_adj G hadj, cwt_of_adj (delPair G u v) hadj']
      by_cases h2 : s(a, b) ∈ E0 (delPair G u v) ∪ Ew (delPair G u v)
      · rw [if_pos h2]
        have : (if s((a : V), (b : V)) ∈ E0 G ∪ Ew G then (1 : ℤ) else 0) ≤ 1 := by
          split <;> norm_num
        linarith
      · rw [if_neg h2]
        by_cases h1 : s((a : V), (b : V)) ∈ E0 G ∪ Ew G
        · -- the only `+1` transition: it forces a `B`-edge
          have hcn' : ((delPair G u v).commonNeighbors a b).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]
            intro hemp
            exact h2 (Or.inl ((mem_E0_iff _ a b).mpr ⟨hadj', hemp⟩))
          have hcnG : (G.commonNeighbors (a : V) (b : V)).Nonempty :=
            commonNeighbors_nonempty_of_delPair hcn'
          have hEw : s((a : V), (b : V)) ∈ Ew G := by
            rcases h1 with h | h
            · exact absurd ((mem_E0_iff G _ _).mp h).2
                (Set.nonempty_iff_ne_empty.mp hcnG)
            · exact h
          have hwit' : ¬ (Wit (delPair G u v) a b).Nonempty := fun hn =>
            h2 (Or.inr ((mem_Ew_iff _ a b).mpr ⟨hadj', hcn', hn⟩))
          have hB : s((a : V), (b : V)) ∈ BSet G u v := by
            refine ⟨hEw, (a : V), (b : V), rfl, a.2.1, a.2.2, b.2.1, b.2.2, ?_⟩
            intro y hy
            by_contra hyuv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hyuv
            refine hwit' ⟨⟨y, hyuv.1, hyuv.2⟩, ?_⟩
            rcases hy with hy | hy
            · exact Or.inl (delPair_witAt G hy hyuv.1 hyuv.2)
            · exact Or.inr (delPair_witAt G hy hyuv.1 hyuv.2)
          rw [if_pos h1, if_pos hB]
          norm_num
        · rw [if_neg h1]; linarith
    · -- P is a NON-EDGE of F, hence of F′; the transition is always `≤ 0`
      have hadj' : ¬ (delPair G u v).Adj a b := hadj
      rw [cwt_of_not_adj G hadj, cwt_of_not_adj (delPair G u v) hadj']
      have key : s(a, b) ∈ Anon (delPair G u v) → s((a : V), (b : V)) ∈ Anon G := by
        intro h
        rw [mem_Anon_iff] at h ⊢
        exact ⟨fun hh => h.1 (Subtype.ext hh), hadj,
          commonNeighbors_nonempty_of_delPair h.2.2⟩
      by_cases h2 : s(a, b) ∈ Anon (delPair G u v)
      · rw [if_pos h2, if_pos (key h2)]; linarith
      · rw [if_neg h2]; split <;> linarith

/-! ### 2.7.9 The guaranteed rebates -/

/-- `R⁺(u,v)` as a *set* of index pairs; `Rplus` is its cardinality by
definition. -/
def RSet (G : SimpleGraph V) (u v : V) : Set (V × V) :=
  {p : V × V | p.1 ∈ Wuv G u v ∧ ¬ G.Adj p.1 p.2 ∧
      ((p.2 ∈ catA G u v ∧ G.commonNeighbors p.1 p.2 = {u}) ∨
       (p.2 ∈ catA G v u ∧ G.commonNeighbors p.1 p.2 = {v}))}

theorem Rplus_eq_ncard_RSet [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) : Rplus G u v = (RSet G u v).ncard := rfl

/-- Both coordinates of an `R⁺` index pair avoid `u` and `v`. -/
theorem RSet_remote (G : SimpleGraph V) {u v : V} {p : V × V}
    (hp : p ∈ RSet G u v) :
    (p.1 ≠ u ∧ p.1 ≠ v) ∧ (p.2 ≠ u ∧ p.2 ≠ v) := by
  obtain ⟨hw0, -, hcase⟩ := hp
  obtain ⟨hu1, hv1⟩ := hw0
  refine ⟨⟨hu1.ne', hv1.ne'⟩, ?_⟩
  rcases hcase with ⟨⟨ha, hne, -⟩, -⟩ | ⟨⟨ha, hne, -⟩, -⟩
  · exact ⟨ha.ne', hne⟩
  · exact ⟨hne, ha.ne'⟩

/-- An `R⁺` index pair is a genuine (unequal) non-edge. -/
theorem RSet_ne (G : SimpleGraph V) {u v : V} {p : V × V} (hp : p ∈ RSet G u v) :
    p.1 ≠ p.2 := by
  obtain ⟨hw0, -, hcase⟩ := hp
  rcases hcase with ⟨⟨-, -, hnv⟩, -⟩ | ⟨⟨-, -, hnu⟩, -⟩
  · exact fun h => hnv (h ▸ hw0.2)
  · exact fun h => hnu (h ▸ hw0.1)

/-- In `F`, an `R⁺` pair is an `A`-non-edge, so `c = −1`. -/
theorem RSet_cwt (G : SimpleGraph V) {u v : V} {p : V × V} (hp : p ∈ RSet G u v) :
    cwt G s(p.1, p.2) = -1 := by
  classical
  have hne := RSet_ne G hp
  obtain ⟨-, hnadj, hcase⟩ := hp
  have hcn : (G.commonNeighbors p.1 p.2).Nonempty := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨_, rfl⟩
  rw [cwt_of_not_adj G hnadj, if_pos ((mem_Anon_iff G p.1 p.2).mpr ⟨hne, hnadj, hcn⟩)]

/-- After deleting `u` and `v` the `R⁺` pair's only common neighbour is
gone, so `c = 0` — the rebate is exactly `−1`. -/
theorem RSet_cwt_delPair (G : SimpleGraph V) {u v : V}
    {a b : {w : V // w ≠ u ∧ w ≠ v}} (hp : ((a : V), (b : V)) ∈ RSet G u v) :
    cwt (delPair G u v) s(a, b) = 0 := by
  classical
  have hnadj : ¬ G.Adj (a : V) (b : V) := hp.2.1
  have hnadj' : ¬ (delPair G u v).Adj a b := hnadj
  have hemp : ((delPair G u v).commonNeighbors a b) = ∅ := by
    rw [delPair_commonNeighbors]
    ext t
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    rcases hp.2.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> intro ht
    · exact t.2.1 ht
    · exact t.2.2 ht
  rw [cwt_of_not_adj _ hnadj', if_neg]
  intro hA
  exact absurd hemp (Set.nonempty_iff_ne_empty.mp ((mem_Anon_iff _ a b).mp hA).2.2)

/-! ### 2.7.10 The two counting bijections -/

theorem ncard_eq_card_filter {α : Type*} [Fintype α] (s : Set α)
    [DecidablePred (· ∈ s)] : s.ncard = (Finset.univ.filter (· ∈ s)).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

open scoped Classical in
/-- The remote pairs lying in `B(u,v)` are in bijection with `B(u,v)` itself,
via the transport.  (Every `B`-edge is remote by definition.) -/
theorem card_filter_BSet [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    (Finset.univ.filter (fun e : Sym2 {w : V // w ≠ u ∧ w ≠ v} =>
        Sym2.map Subtype.val e ∈ BSet G u v)).card = Bc G u v := by
  classical
  rw [Bc_eq_ncard_BSet, ncard_eq_card_filter]
  refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
  · intro e he
    simpa using (Finset.mem_filter.mp he).2
  · intro e1 _ e2 _ h
    exact sym2map_val_injective u v h
  · intro P hP
    obtain ⟨hEw, w, z, rfl, hwu, hwv, hzu, hzv, hsub⟩ := (Finset.mem_filter.mp hP).2
    refine ⟨s(⟨w, hwu, hwv⟩, ⟨z, hzu, hzv⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sym2map_val_mk]
    exact ⟨hEw, w, z, rfl, hwu, hwv, hzu, hzv, hsub⟩

open scoped Classical in
/-- The `R⁺` index pairs are in bijection with the remote pairs they span.
This is the "pairwise distinct" step: `W_uv` and categories (a)/(b) are
disjoint, so the unordered pair `{w0,x}` remembers which coordinate was which. -/
theorem card_filter_RSet [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    (Finset.univ.filter (fun e : Sym2 {w : V // w ≠ u ∧ w ≠ v} =>
        ∃ a b : {w : V // w ≠ u ∧ w ≠ v}, e = s(a, b) ∧
          ((a : V), (b : V)) ∈ RSet G u v)).card = Rplus G u v := by
  classical
  rw [Rplus_eq_ncard_RSet, ncard_eq_card_filter]
  refine (Finset.card_bij
    (fun p hp => s(⟨p.1, (RSet_remote G (Finset.mem_filter.mp hp).2).1⟩,
                   ⟨p.2, (RSet_remote G (Finset.mem_filter.mp hp).2).2⟩)) ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, _, rfl, (Finset.mem_filter.mp hp).2⟩
  · intro p1 h1 p2 h2 h
    have hp1 := (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    rcases Sym2.eq_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Prod.ext (congrArg Subtype.val hx) (congrArg Subtype.val hy)
    · -- the crossed case is impossible: `W_uv` and (a)∪(b) are disjoint
      exfalso
      have e1 : p1.1 = p2.2 := congrArg Subtype.val hx
      rcases hp2.2.2 with ⟨⟨-, -, hnv⟩, -⟩ | ⟨⟨-, -, hnu⟩, -⟩
      · exact hnv (e1 ▸ hp1.1.2)
      · exact hnu (e1 ▸ hp1.1.1)
  · intro e he
    obtain ⟨a, b, rfl, hab⟩ := (Finset.mem_filter.mp he).2
    exact ⟨((a : V), (b : V)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩

/-! ### 2.7.11 The summation step of the refined deletion bound -/

open scoped Classical in
/-- **`Σ_remote [c(P,F) − c(P,F′)] ≤ B(u,v) − R⁺(u,v)`** — the remote
transition bound summed over the remote pairs, with the `R⁺` pairs each
contributing exactly `−1` and none of them a `B`-edge (they are non-edges;
`B`-edges are edges). -/
theorem sum_remote_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    ∑ e : Sym2 {w : V // w ≠ u ∧ w ≠ v},
      (cwt G (Sym2.map Subtype.val e) - cwt (delPair G u v) e)
      ≤ (Bc G u v : ℤ) - (Rplus G u v : ℤ) := by
  classical
  set f : Sym2 {w : V // w ≠ u ∧ w ≠ v} → ℤ :=
    fun e => cwt G (Sym2.map Subtype.val e) - cwt (delPair G u v) e with hfdef
  set B : Finset (Sym2 {w : V // w ≠ u ∧ w ≠ v}) :=
    Finset.univ.filter (fun e => Sym2.map Subtype.val e ∈ BSet G u v) with hBdef
  set R : Finset (Sym2 {w : V // w ≠ u ∧ w ≠ v}) :=
    Finset.univ.filter (fun e => ∃ a b : {w : V // w ≠ u ∧ w ≠ v}, e = s(a, b) ∧
      ((a : V), (b : V)) ∈ RSet G u v) with hRdef
  have hBcard : (B.card : ℤ) = (Bc G u v : ℤ) := by
    rw [hBdef]; exact_mod_cast card_filter_BSet G u v
  have hRcard : (R.card : ℤ) = (Rplus G u v : ℤ) := by
    rw [hRdef]; exact_mod_cast card_filter_RSet G u v
  have hmemB : ∀ e, e ∈ B ↔ Sym2.map Subtype.val e ∈ BSet G u v := by
    intro e; rw [hBdef]; simp
  have hmemR : ∀ e, e ∈ R ↔ ∃ a b : {w : V // w ≠ u ∧ w ≠ v}, e = s(a, b) ∧
      ((a : V), (b : V)) ∈ RSet G u v := by
    intro e; rw [hRdef]; simp
  have hRval : ∀ e ∈ R, f e = -1 := by
    intro e he
    obtain ⟨a, b, rfl, hab⟩ := (hmemR e).mp he
    simp only [hfdef, sym2map_val_mk]
    rw [RSet_cwt_delPair G hab, RSet_cwt G hab]
    ring
  have hBval : ∀ e ∈ B, f e ≤ 1 := by
    intro e he
    have h := remote_transition_le G e
    rw [if_pos ((hmemB e).mp he)] at h
    exact h
  have hOval : ∀ e ∉ B, f e ≤ 0 := by
    intro e he
    have h := remote_transition_le G e
    rw [if_neg (fun hh => he ((hmemB e).mpr hh))] at h
    exact h
  have hdisj : Disjoint B R := by
    rw [Finset.disjoint_left]
    intro e heB heR
    obtain ⟨a, b, rfl, hab⟩ := (hmemR e).mp heR
    have hB := (hmemB _).mp heB
    rw [sym2map_val_mk] at hB
    exact hab.2.1 ((mem_Ew_iff G _ _).mp hB.1).1
  have hsub : B ∪ R ⊆ Finset.univ := Finset.subset_univ _
  have hsplit : ∑ e, f e
      = (∑ e ∈ B, f e + ∑ e ∈ R, f e) + ∑ e ∈ Finset.univ \ (B ∪ R), f e := by
    rw [← Finset.sum_union hdisj]
    exact (Finset.sum_sdiff hsub).symm.trans (add_comm _ _)
  have h1 : ∑ e ∈ B, f e ≤ (B.card : ℤ) :=
    (Finset.sum_le_sum hBval).trans (by simp)
  have h2 : ∑ e ∈ R, f e = -(R.card : ℤ) := by
    rw [Finset.sum_congr rfl hRval]; simp
  have h3 : ∑ e ∈ Finset.univ \ (B ∪ R), f e ≤ 0 := by
    refine Finset.sum_nonpos fun e he => hOval e ?_
    exact fun h => (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ h)
  rw [hsplit]
  linarith

end Transport

/-! ##################################################################
    ## Part 3. The 21 load-bearing statements of the paper proof     ##
    ##                                                               ##
    ## In dependency order.  Each is labelled with its row number,   ##
    ## and each docstring says what the statement asserts and what   ##
    ## the proof consumes.                                           ##
    ################################################################## -/

section Skeleton

variable [Fintype V] [DecidableEq V]

/-- **Row 1 — Proposition 2.1 (witness symmetry).**
★ PROVED above as `isWitAt_symm`; restated here as row 1 of the list. -/
theorem row01_witness_symmetry (G : SimpleGraph V) (x z y : V) :
    IsWitAt G x z y ↔ IsWitAt G y z x := isWitAt_symm G x z y

/-- **Row 11 — the four elementary facts (P1)–(P4).**
(P1): for fixed `x` the sets `Wit_x(z)` are pairwise disjoint, because
`y ∈ Wit_x(z)` determines `z` as the unique common neighbour of `x` and `y`.
(P2)–(P4) are stated further below, where the notions their conclusions
mention have been defined.  ★ PROVED; no `sorry`. -/
theorem row11_P1 (G : SimpleGraph V) (x z z' : V) (h : z ≠ z') :
    Disjoint (WitAt G x z) (WitAt G x z') := by
  rw [Set.disjoint_left]
  rintro y ⟨-, -, hcn⟩ ⟨-, -, hcn'⟩
  rw [hcn] at hcn'
  exact h (by simpa using hcn')

/-- (P2): if `y ∈ Wit_x(z)` then every `t ∈ N(x) ∖ {z}` satisfies `t ∉ N[y]`.
★ PROVED; no `sorry`. -/
theorem row11_P2 (G : SimpleGraph V) {x z y t : V} (h : y ∈ WitAt G x z)
    (ht : G.Adj x t) (htz : t ≠ z) : t ≠ y ∧ ¬ G.Adj t y := by
  obtain ⟨-, hxy, hcn⟩ := h
  refine ⟨?_, ?_⟩
  · rintro rfl; exact hxy ht
  · intro hty
    have hmem : t ∈ G.commonNeighbors x y := ⟨ht, hty.symm⟩
    rw [hcn] at hmem
    exact htz hmem

/-! #### Row 2's helpers — the two partitions Proposition 3.1 counts with

Prop 3.1's proof needs exactly one auxiliary class, the **codegree-`0`
non-edges** `Z0`.  With it the paper's two sentences become two disjoint-union
identities: `disj(F) = E0(F) ⊔ Z0(F)` (a codegree-`0` pair of distinct
vertices either is or is not an edge) and
`{off-diagonal pairs} = E(F) ⊔ A(F) ⊔ Z0(F)` (the paper's *"the non-adjacent
pairs split into those with codeg ≥ 1 (exactly `A(F)`) and those with
codeg 0"*).  `Φ = C(n,2) + D` is then cardinal arithmetic. -/

/-- `Z0(F)` : the non-adjacent pairs of distinct vertices with codegree `0`. -/
def Z0 (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ a b, e = s(a,b) ∧ a ≠ b ∧ ¬ G.Adj a b ∧ G.commonNeighbors a b = ∅}

theorem mem_Z0_iff (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ Z0 G ↔ u ≠ v ∧ ¬ G.Adj u v ∧ G.commonNeighbors u v = ∅ := by
  constructor
  · rintro ⟨a, b, hab, hne, hadj, hcn⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hadj, hcn⟩
    · exact ⟨hne.symm, fun h => hadj h.symm, by rwa [G.commonNeighbors_symm]⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨u, v, rfl, h1, h2, h3⟩

/-- `disj(F) = E0(F) ∪ Z0(F)`. -/
theorem Disj_eq_E0_union_Z0 (G : SimpleGraph V) : Disj G = E0 G ∪ Z0 G := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [mem_Disj_iff, Set.mem_union, mem_E0_iff, mem_Z0_iff]
    constructor
    · rintro ⟨hne, hcn⟩
      by_cases h : G.Adj a b
      · exact Or.inl ⟨h, hcn⟩
      · exact Or.inr ⟨hne, h, hcn⟩
    · rintro (⟨h, hcn⟩ | ⟨hne, -, hcn⟩)
      · exact ⟨h.ne, hcn⟩
      · exact ⟨hne, hcn⟩

theorem E0_disjoint_Z0 (G : SimpleGraph V) : Disjoint (E0 G) (Z0 G) := by
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he0 hz0
    exact ((mem_Z0_iff G a b).mp hz0).2.1 ((mem_E0_iff G a b).mp he0).1

theorem Anon_disjoint_Z0 (G : SimpleGraph V) : Disjoint (Anon G) (Z0 G) := by
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro ha hz
    have h1 := ((mem_Anon_iff G a b).mp ha).2.2
    rw [((mem_Z0_iff G a b).mp hz).2.2] at h1
    exact Set.not_nonempty_empty h1

theorem edgeSet_disjoint_Anon_union_Z0 (G : SimpleGraph V) :
    Disjoint G.edgeSet (Anon G ∪ Z0 G) := by
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he hmem
    rcases hmem with h | h
    · exact ((mem_Anon_iff G a b).mp h).2.1 he
    · exact ((mem_Z0_iff G a b).mp h).2.1 he

/-- The off-diagonal pairs split as `E(F) ⊔ (A(F) ⊔ Z0(F))`. -/
theorem offDiag_split (G : SimpleGraph V) :
    {e : Sym2 V | ¬ e.IsDiag} = G.edgeSet ∪ (Anon G ∪ Z0 G) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [Set.mem_setOf_eq, Sym2.mk_isDiag_iff, Set.mem_union, Set.mem_union,
      SimpleGraph.mem_edgeSet, mem_Anon_iff, mem_Z0_iff]
    constructor
    · intro hne
      by_cases h : G.Adj a b
      · exact Or.inl h
      · rcases Set.eq_empty_or_nonempty (G.commonNeighbors a b) with hcn | hcn
        · exact Or.inr (Or.inr ⟨hne, h, hcn⟩)
        · exact Or.inr (Or.inl ⟨hne, h, hcn⟩)
    · rintro (h | ⟨hne, -, -⟩ | ⟨hne, -, -⟩)
      · exact h.ne
      · exact hne
      · exact hne

/-- `#{off-diagonal pairs} = C(n,2)` — mathlib's `Sym2.natCard_subtype_not_diag`. -/
theorem ncard_offDiag (V : Type*) [Fintype V] :
    {e : Sym2 V | ¬ e.IsDiag}.ncard = (Fintype.card V).choose 2 := by
  have h : {e : Sym2 V | ¬ e.IsDiag}.ncard = Nat.card {a : Sym2 V // ¬ a.IsDiag} :=
    (Nat.card_coe_set_eq _).symm
  rw [h, Sym2.natCard_subtype_not_diag, Nat.card_eq_fintype_card]

/-- **Row 2 — Proposition 3.1 (D-normal form): `Φ(F) = C(n,2) + D(F)`.**
Consequently Theorem A (`Φ ≤ ⌊n²/2⌋`) is equivalent to `D(F) ≤ ⌊n/2⌋`.

★ PROVED; no `sorry`, and no other row is used — only the definitions, the
`Z0` split above and mathlib's count of the off-diagonal `Sym2` pairs.
`Φ = e + disj + X` with `X = |Ew|` (a definition here, as the paper notes),
`disj = |E0| + |Z0|`, and `C(n,2) = e + |A| + |Z0|`; substituting gives
`Φ = e + |E0| + |Z0| + |Ew| = C(n,2) + |E0| + |Ew| − |A| = C(n,2) + D`.
Note the equivalence clause of Prop 3.1 (`⌊n²/2⌋ − C(n,2) = ⌊n/2⌋`) is *not*
part of the transcribed statement; it is carried separately as
`sq_div_two_eq`. -/
theorem row02_D_normal_form (G : SimpleGraph V) :
    (Phi G : ℤ) = ((Fintype.card V).choose 2 : ℤ) + Dv G := by
  classical
  have hD : (Disj G).ncard = (E0 G).ncard + (Z0 G).ncard := by
    rw [Disj_eq_E0_union_Z0,
      Set.ncard_union_eq (E0_disjoint_Z0 G) (Set.toFinite _) (Set.toFinite _)]
  have hO : (Fintype.card V).choose 2
      = G.edgeSet.ncard + ((Anon G).ncard + (Z0 G).ncard) := by
    rw [← ncard_offDiag V, offDiag_split G,
      Set.ncard_union_eq (edgeSet_disjoint_Anon_union_Z0 G) (Set.toFinite _)
        (Set.toFinite _),
      Set.ncard_union_eq (Anon_disjoint_Z0 G) (Set.toFinite _) (Set.toFinite _)]
  unfold Phi X Dv
  rw [hD, hO]
  push_cast
  ring

/-! #### Row 3's helpers — the two cases of Proposition 3.2's certificate -/

/-- `Within2` is symmetric.  (It is *stated* asymmetrically — `∃ m, Adj x m ∧
Adj m y` — so the symmetry is a lemma, not a `rfl`.) -/
theorem within2_comm (G : SimpleGraph V) (x y : V) :
    Within2 G x y ↔ Within2 G y x := by
  unfold Within2
  constructor <;>
  · rintro (rfl | h | ⟨m, h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr ⟨m, h2.symm, h1.symm⟩)

/-- **Proposition 3.2, Case 1.**  If the criticality certificate for the edge
`{u,v}` is the pair `{u,v}` itself, then `codeg(u,v) = 0`.  Verbatim the
paper: *"a 2-path `u–w–v` never uses the edge `uv`, so none exists"* — a common
neighbour `m` yields a `2`-path `u–m–v` both of whose edges differ from `uv`
(`m ≠ v` because `Adj v m`, `m ≠ u` because `Adj u m`, `u ≠ v` because
`Adj u v`), so it survives in `G − uv`. -/
theorem row03_case1 (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (h : ¬ Within2 (G.deleteEdges {s(u,v)}) u v) : G.commonNeighbors u v = ∅ := by
  refine Set.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨m, hum, hvm⟩
  refine h (Or.inr (Or.inr ⟨m, ?_, ?_⟩)) <;>
    rw [SimpleGraph.deleteEdges_adj] <;>
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
  · exact ⟨hum, fun _ h => absurd h hvm.ne', fun h => absurd h huv.ne⟩
  · exact ⟨hvm.symm, fun h => absurd h hum.ne', fun h => absurd h hvm.ne'⟩

/-- **Proposition 3.2, Case 2.**  If the criticality certificate for the edge
`{a,b}` is a pair `(a,w)` with `aw ∉ E`, then `w` is a witness at `a` for
`{a,b}`.  Verbatim the paper: *"Every 2-path `a–m–w` uses `ab`, forcing
`m = b`; hence `N(a) ∩ N(w) = {b}`"*.  The `⊇` half needs a `2`-path to exist
at all — that is where the diameter-`2` hypothesis `hall` is consumed, and it
is the only place in this row where it is. -/
theorem row03_witness (G : SimpleGraph V) {a b w : V} (hab : G.Adj a b)
    (hall : ∀ p q : V, Within2 G p q) (hnadj : ¬ G.Adj a w)
    (h : ¬ Within2 (G.deleteEdges {s(a,b)}) a w) : w ∈ WitAt G a b := by
  have haw : a ≠ w := fun he => h (Or.inl he)
  have hsub : ∀ m ∈ G.commonNeighbors a w, m = b := by
    rintro m ⟨ham, hwm⟩
    by_contra hmb
    refine h (Or.inr (Or.inr ⟨m, ?_, ?_⟩)) <;>
      rw [SimpleGraph.deleteEdges_adj] <;>
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
    · exact ⟨ham, fun _ h => hmb h, fun h => absurd h hab.ne⟩
    · exact ⟨hwm.symm, fun h => absurd h ham.ne', fun h => absurd h hmb⟩
  obtain ⟨m, ham, hmw⟩ : ∃ m, G.Adj a m ∧ G.Adj m w := by
    rcases hall a w with he | hadj | hm
    · exact absurd he haw
    · exact absurd hadj hnadj
    · exact hm
  have hmb : m = b := hsub m ⟨ham, hmw.symm⟩
  subst hmb
  refine ⟨haw.symm, hnadj, ?_⟩
  apply Set.Subset.antisymm
  · intro t ht; exact hsub t ht
  · rintro t rfl; exact ⟨hab, hmw.symm⟩

/-- **Row 3 — Proposition 3.2 (criticality inventory).**
In a D2C graph every edge lies in `E0 ∪ Ew`.
This is the *only* place in Part I where the D2C hypothesis is used, which is
exactly why the bridge of Part 2 has to be proved.

★ PROVED; no `sorry`.  It is the only row whose proof goes through the Part 2
bridge (`isD2C_iff_isDiameter2Critical`).  The paper's dichotomy is reorganised
very slightly: instead of "Case 1 ⟹ `E0`, Case 2 ⟹ `E0` or `Ew`", we split
first on `codeg(u,v) = 0` (which gives `E0` outright), so that the certificate
analysis only ever has to produce a *witness*.  In the residual branch the
certificate pair `{x,y}` is either an edge — then `{x,y} = {u,v}` and
`row03_case1` contradicts `codeg ≠ 0` — or a non-edge, and then the `2`-path
`x–m–y` it must still have in `G` uses `uv`, which puts `x` or `y` in `{u,v}`
and makes the *other* endpoint a witness by `row03_witness`.  All four
placements (`x = u`, `x = v`, `y = u`, `y = v`) occur and are handled; the
`y`-side ones go through `within2_comm`, the `v`-side ones through
`Sym2.eq_swap` and `Wit = Wit_a ∪ Wit_b`. -/
theorem row03a_criticality_inventory (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeSet ⊆ E0 G ∪ Ew G := by
  have hD2C := (isD2C_iff_isDiameter2Critical G).mpr hG
  have hall : ∀ p q : V, Within2 G p q := hD2C.1.1
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    have huv : G.Adj u v := he
    by_cases hcn : G.commonNeighbors u v = ∅
    · exact Or.inl ((mem_E0_iff G u v).mpr ⟨huv, hcn⟩)
    refine Or.inr ((mem_Ew_iff G u v).mpr
      ⟨huv, Set.nonempty_iff_ne_empty.mpr hcn, ?_⟩)
    -- the two ways a certificate endpoint can sit in `{u,v}`
    have step : ∀ w : V, ¬ G.Adj u w →
        ¬ Within2 (G.deleteEdges {s(u,v)}) u w → (Wit G u v).Nonempty :=
      fun w hn hw => ⟨w, Or.inl (row03_witness G huv hall hn hw)⟩
    have step' : ∀ w : V, ¬ G.Adj v w →
        ¬ Within2 (G.deleteEdges {s(u,v)}) v w → (Wit G u v).Nonempty := by
      intro w hn hw
      rw [Sym2.eq_swap] at hw
      exact ⟨w, Or.inr (row03_witness G huv.symm hall hn hw)⟩
    obtain ⟨x, y, hxy⟩ := hD2C.2 s(u,v) he
    by_cases hadj : G.Adj x y
    · -- the certificate pair is an EDGE, so it *is* `{u,v}` — the paper's Case 1
      exfalso
      have hs : s(x,y) = s(u,v) := by
        by_contra hne
        exact hxy (Or.inr (Or.inl (by
          rw [SimpleGraph.deleteEdges_adj]; exact ⟨hadj, by simpa using hne⟩)))
      rw [Sym2.eq_iff] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcn (row03_case1 G huv hxy)
      · refine hcn ?_
        rw [G.commonNeighbors_symm]
        exact row03_case1 G huv.symm (by rwa [Sym2.eq_swap] at hxy)
    · -- the certificate pair is a NON-edge — the paper's Case 2
      have hxyne : x ≠ y := fun he' => hxy (Or.inl he')
      obtain ⟨m, hxm, hmy⟩ : ∃ m, G.Adj x m ∧ G.Adj m y := by
        rcases hall x y with he' | ha | hm
        · exact absurd he' hxyne
        · exact absurd ha hadj
        · exact hm
      have huse : s(x,m) = s(u,v) ∨ s(m,y) = s(u,v) := by
        by_contra hc
        push_neg at hc
        refine hxy (Or.inr (Or.inr ⟨m, ?_, ?_⟩)) <;>
          rw [SimpleGraph.deleteEdges_adj]
        · exact ⟨hxm, by simpa using hc.1⟩
        · exact ⟨hmy, by simpa using hc.2⟩
      rcases huse with h | h <;> rw [Sym2.eq_iff] at h
      · rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact step y hadj hxy
        · exact step' y hadj hxy
      · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact step' x (fun hc => hadj hc.symm)
            (fun hc => hxy ((within2_comm _ _ _).mp hc))
        · exact step x (fun hc => hadj hc.symm)
            (fun hc => hxy ((within2_comm _ _ _).mp hc))

/-! #### Row 3's two halves, joined

`row03b` is not an independent statement: it is derived from `row03a` by the
four small facts below. -/

/-- `E0(F) ⊆ E(F)`: an `E0` pair is by definition an edge. -/
theorem row03_E0_subset_edgeSet (G : SimpleGraph V) : E0 G ⊆ G.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact ((mem_E0_iff G u v).mp he).1

/-- `Ew(F) ⊆ E(F)`: an `Ew` pair is by definition an edge. -/
theorem row03_Ew_subset_edgeSet (G : SimpleGraph V) : Ew G ⊆ G.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact ((mem_Ew_iff G u v).mp he).1

/-- On a D2C graph `disj(F) = E0(F)`: a codegree-`0` pair *must* be an edge,
because diameter `2` gives a non-adjacent distinct pair a common neighbour.
★ Consumes the bridge (`isD2C_iff_isDiameter2Critical`), which is proved. -/
theorem row03_Disj_eq_E0 (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) : Disj G = E0 G := by
  have hall : ∀ x y : V, Within2 G x y :=
    ((isD2C_iff_isDiameter2Critical G).mpr hG).1.1
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_Disj_iff, mem_E0_iff]
    constructor
    · rintro ⟨hne, hcn⟩
      refine ⟨?_, hcn⟩
      rcases hall u v with rfl | hadj | ⟨m, h1, h2⟩
      · exact absurd rfl hne
      · exact hadj
      · exfalso
        have hm : m ∈ G.commonNeighbors u v := ⟨h1, h2.symm⟩
        rw [hcn] at hm
        exact hm
    · rintro ⟨hadj, hcn⟩
      exact ⟨hadj.ne, hcn⟩

/-- On a D2C graph the edge set is *exactly* `E0 ⊔ Ew`.  `⊆` is `row03a`;
`⊇` is the two inclusions above. -/
theorem row03_edgeSet_eq_E0_union_Ew (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) : G.edgeSet = E0 G ∪ Ew G :=
  Set.Subset.antisymm (row03a_criticality_inventory G hG)
    (Set.union_subset (row03_E0_subset_edgeSet G) (row03_Ew_subset_edgeSet G))

/-- **Row 3 (second half) — `Φ(G) = 2·e(G)` on a D2C graph.**
★ PROVED **from `row03a`** — no new `sorry`.  `Φ = e + disj + X` with
`X = |Ew|`; on a D2C graph `disj = E0` (`row03_Disj_eq_E0`) and
`e = |E0| + |Ew|` (`row03a` + disjointness of `E0` and `Ew`), so
`Φ = e + |E0| + |Ew| = e + e`. -/
theorem row03b_phi_eq_two_e (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) :
    Phi G = 2 * G.edgeSet.ncard := by
  have hsplit : G.edgeSet.ncard = (E0 G).ncard + (Ew G).ncard := by
    rw [row03_edgeSet_eq_E0_union_Ew G hG,
      Set.ncard_union_eq (E0_disjoint_Ew G) (Set.toFinite _) (Set.toFinite _)]
  unfold Phi X
  rw [row03_Disj_eq_E0 G hG, hsplit]
  ring

/-- **Row 4 — Lemma 3.4 (deletion decomposition).**
`D(F) − D(F′) = c({u,v},F) + S(u,v) + Σ_{remote P} [c(P,F) − c(P,F′)]`;
the remote pairs of `F` are exactly the pairs of `F′`, transported along
`Sym2.map Subtype.val`.

★ PROVED; no `sorry`.  From `Dv_eq_sum_cwt` (`D = Σ_P c`, the *definition* of
`D` rearranged) and `sum_sym2_split` (the partition of `Sym2 V` into
`{u,v}` ⊔ incident ⊔ remote) in Part 2.7.

Note on inputs: Proposition 3.1 (the D-normal form, row 2) is **not** used
here.  The decomposition rests on `D(F) = Σ_P c(P,F)` over all unordered vertex
pairs, which is the *definition* of `D` together with the definition of `c`,
not the normal form `Φ = C(n,2) + D`.  Machine-confirmed: this proof term does
not mention `row02_D_normal_form`.  Row 4's inputs are the definitions
alone. -/
theorem row04_deletion_decomposition (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    Dinc G u v = cwt G s(u,v) + Sc G u v +
      ∑ e : Sym2 {w : V // w ≠ u ∧ w ≠ v},
        (cwt G (Sym2.map Subtype.val e) - cwt (delPair G u v) e) := by
  rw [Dinc, Dv_eq_sum_cwt G, Dv_eq_sum_cwt (delPair G u v),
    sum_sym2_split (cwt G) (cwt_diag G) huv.ne, Finset.sum_sub_distrib, Sc_eq_sum]
  abel

/-- **Row 5 — Lemma 3.5(i) (remote transitions) and (ii) (rebates).**
Stated here in its load-bearing special case, *witness-survival*: a witness
outside `{u,v}` for a remote edge survives the deletion of `u` and `v`.

★ PROVED; no `sorry`.  It is `delPair_witAt` of Part 2.7.

⚠ **This declaration carries only one case of Lemma 3.5.**  Lemma 3.5 is the
remote-transition bound (i) PLUS the guaranteed-rebate statement (ii);
witness-survival is one case of one of (i)'s four cases.  The two remaining
clauses are what row 6 actually consumes, and they are stated and proved in
Part 2.7 as

* `remote_transition_le` — (i): `c(P,F) − c(P,F′) ≤ [P ∈ B(u,v)]` for every
  remote `P` (all four transition cases);
* `RSet_remote` / `RSet_ne` / `RSet_cwt` / `RSet_cwt_delPair` /
  `card_filter_RSet` — (ii): the `R⁺` pairs are pairwise distinct remote
  non-edges each contributing exactly `−1`.

**`row06` below is proved from those, not from `row05_witness_survival`.**  The
declaration is kept, with its transcribed statement unchanged, as the entry
for row 5. -/
theorem row05_witness_survival (G : SimpleGraph V) {u v w z y : V}
    (hy : y ∈ WitAt G w z) (hyu : y ≠ u) (hyv : y ≠ v)
    (hwu : w ≠ u) (hwv : w ≠ v) (hzu : z ≠ u) (hzv : z ≠ v) :
    (⟨y, hyu, hyv⟩ : {t : V // t ≠ u ∧ t ≠ v}) ∈
      WitAt (delPair G u v) ⟨w, hwu, hwv⟩ ⟨z, hzu, hzv⟩ :=
  delPair_witAt G (a := ⟨w, hwu, hwv⟩) (b := ⟨z, hzu, hzv⟩) hy hyu hyv

/-- **Row 6 — Theorem 3.6 (refined deletion bound).**
`D(F) − D(F−{u,v}) ≤ 1 + S(u,v) + B(u,v) − R⁺(u,v)` for ANY edge.
(No minimality, no selection, no `Ew`-membership of `{u,v}` is used.)

★ PROVED; no `sorry`.  From `row04` (the deletion decomposition), plus
`sum_remote_le` (the remote transitions summed, with the rebates), plus
`c({u,v},F) ≤ +1`.

Inputs are Lemmas 3.4 and 3.5 at the paper's granularity — but see row 5
above: `3.5` means both of its clauses, of which the row-5 declaration carries
only the witness-survival case.  This proof therefore cites
`remote_transition_le` and the `RSet_*` family rather than
`row05_witness_survival` itself. -/
theorem row06_refined_deletion_bound (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    Dinc G u v ≤ 1 + Sc G u v + (Bc G u v : ℤ) - (Rplus G u v : ℤ) := by
  have h4 := row04_deletion_decomposition G huv
  have h5 := sum_remote_le G u v
  have h6 := cwt_le_one G s(u,v)
  linarith

/-- **Row 7(i) — `K = K_A + K_B`.**
True by definition here; the mathematical content (that the split is
exhaustive and exclusive) is discharged in `row07i_K_split_exhaustive`. -/
theorem row07i_K_split (G : SimpleGraph V) (u v : V) :
    Kc G u v = KA G u v + KB G u v := rfl

/-- The content of 7(i): an `Ew` edge `{x,w0}` — in particular a `K`-counted
one — is witnessed at `w0` (`K_A`) or at `x` but not at `w0` (`K_B`),
exclusively and exhaustively.  ★ PROVED; no `sorry`.

★ **On the hypotheses.**  The statement takes `Ew`-membership alone.  The two
conditions that make `{x,w0}` *`K`-counted* — `x = u ∨ x = v` and
`w0 ∈ W_uv` — are context in the source, not premises: the paper proves
exhaustiveness in one sentence, "a K-counted edge `{x,w0}` is in `Ew(F)`, hence
witnessed at `x` or at `w0`", consuming `Ew`-membership only.  Carrying the
`K`-counting hypotheses would merely weaken the lemma, so they are dropped, and
the `K`-counted case is the instance `x ∈ {u,v}`, `w0 ∈ W_uv`.

⚠ **A note on `row07i_K_split` above**, which is `rfl` *because `Kc` is defined
in this file as `KA + KB`.*  The paper's `K = K_A + K_B` is a claim about
**cardinalities** — that `K_A` and `K_B` partition the set of `K`-counted
pairs, where `K(u,v)` there is the independent count
`Σ_{w0 ∈ W_uv} [{u,w0} ∈ Ew] + [{v,w0} ∈ Ew]`.  Defining `Kc` as the sum
absorbs that partition into a definition, so `row07i_K_split` itself carries no
content.  The partition is nevertheless *proved*, as
`row07i_K_split_exhaustive` here and `ncard_split_KA_KB` below, and it is those
that row 7(iii) consumes — see the note there. -/
theorem row07i_K_split_exhaustive (G : SimpleGraph V) {x w0 : V}
    (he : s(x, w0) ∈ Ew G) :
    ((WitAt G w0 x).Nonempty ∧ ¬ ((WitAt G x w0).Nonempty ∧ WitAt G w0 x = ∅)) ∨
    (¬ (WitAt G w0 x).Nonempty ∧ (WitAt G x w0).Nonempty ∧ WitAt G w0 x = ∅) := by
  by_cases hA : (WitAt G w0 x).Nonempty
  · exact Or.inl ⟨hA, fun hc => (Set.not_nonempty_iff_eq_empty.mpr hc.2) hA⟩
  · have hempty : WitAt G w0 x = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    have hw2 : (Wit G x w0).Nonempty := ((mem_Ew_iff G x w0).mp he).2.2
    rw [Wit, hempty, Set.union_empty] at hw2
    exact Or.inr ⟨hA, hw2, hempty⟩

/-- The category step of 7(ii), stated symmetrically in the two endpoints of
the edge so that `x = u` and `x = v` are the *same* lemma.  If `y` witnesses
the edge `{x,w0}` at `w0` and `w0 ∈ W_uv` (so `x'` — the other endpoint — is
also adjacent to `w0`), then `y` lies in the category (a) of `x` relative
to `x'`.

The paper's proof of 3.7(ii) verbatim: `y ∈ N(x)` because
`x ∈ N(w0) ∩ N(y)`; `y ∉ N(x')` because `x' ∈ N(w0)`, so `x' ∈ N(y)` would put
`x' ∈ N(w0) ∩ N(y) = {x}`; and `y ≠ x'` because `x' ∈ N(w0)` while
`y ∉ N(w0)`. -/
theorem row07ii_witness_catA (G : SimpleGraph V) {x x' w0 y : V}
    (hxx' : G.Adj x x') (hw0 : G.Adj x' w0) (hy : y ∈ WitAt G w0 x) :
    y ∈ catA G x x' := by
  obtain ⟨hyne, hnadj, hcn⟩ := hy
  have hxmem : x ∈ G.commonNeighbors w0 y := by rw [hcn]; exact rfl
  rw [G.mem_commonNeighbors] at hxmem
  refine ⟨hxmem.2.symm, ?_, ?_⟩
  · rintro rfl; exact hnadj hw0.symm
  · intro hadj
    have hmem : x' ∈ G.commonNeighbors w0 y :=
      G.mem_commonNeighbors.mpr ⟨hw0.symm, hadj.symm⟩
    rw [hcn] at hmem
    exact hxx'.ne' hmem

/-- **Row 7(ii) — `R⁺(u,v) ≥ K_A(u,v)`.**

★ PROVED; no `sorry`, and no other row is used — only the definitions and
`row07ii_witness_catA`.  The paper's injection `(x,w0) ↦ (w0, y(x,w0))` is
realised by `choose!` on the `K_A` membership clause `(WitAt G w0 x).Nonempty`,
which is exactly the paper's "a fixed chosen witness at `w0` for the edge
`{x,w0}`".  Injectivity is the paper's argument verbatim: the first coordinate
of the image is `w0`, and the *second* is pinned by `N(w0) ∩ N(y) = {x}`, which
recovers `x`; so the two extra facts carried out of `choose!`
(`(f p).1 = p.2` and `N((f p).1) ∩ N((f p).2) = {p.1}`) are precisely what
injectivity needs. -/
theorem row07ii_Rplus_ge_KA (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    KA G u v ≤ Rplus G u v := by
  classical
  have key : ∀ p : V × V, ∃ q : V × V,
      p ∈ {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ Wuv G u v ∧
        s(p.1, p.2) ∈ Ew G ∧ (WitAt G p.2 p.1).Nonempty} →
      (q ∈ {q : V × V | q.1 ∈ Wuv G u v ∧ ¬ G.Adj q.1 q.2 ∧
        ((q.2 ∈ catA G u v ∧ G.commonNeighbors q.1 q.2 = {u}) ∨
         (q.2 ∈ catA G v u ∧ G.commonNeighbors q.1 q.2 = {v}))} ∧
        q.1 = p.2 ∧ G.commonNeighbors q.1 q.2 = {p.1}) := by
    rintro ⟨x, w0⟩
    by_cases hp : ((x, w0) : V × V) ∈ {p : V × V | (p.1 = u ∨ p.1 = v) ∧
        p.2 ∈ Wuv G u v ∧ s(p.1, p.2) ∈ Ew G ∧ (WitAt G p.2 p.1).Nonempty}
    · obtain ⟨hx, hw0, -, y, hy⟩ := hp
      have hw0' : G.Adj u w0 ∧ G.Adj v w0 := G.mem_commonNeighbors.mp hw0
      obtain ⟨hyne, hnadj, hcn⟩ := hy
      refine ⟨(w0, y), fun _ => ⟨⟨hw0, hnadj, ?_⟩, rfl, hcn⟩⟩
      rcases hx with rfl | rfl
      · exact Or.inl ⟨row07ii_witness_catA G huv hw0'.2 ⟨hyne, hnadj, hcn⟩, hcn⟩
      · exact Or.inr ⟨row07ii_witness_catA G huv.symm hw0'.1 ⟨hyne, hnadj, hcn⟩, hcn⟩
    · exact ⟨(x, w0), fun h => absurd h hp⟩
  choose f hf using key
  unfold KA Rplus
  refine Set.ncard_le_ncard_of_injOn f (fun p hp => (hf p hp).1) ?_ (Set.toFinite _)
  intro p hp q hq h
  have h2 : p.2 = q.2 := by rw [← (hf p hp).2.1, ← (hf q hq).2.1, h]
  have h1 : p.1 = q.1 := by
    have e1 := (hf p hp).2.2
    rw [h] at e1
    exact Set.singleton_injective (e1.symm.trans (hf q hq).2.2)
  exact Prod.ext h1 h2

/-! #### Row 7(iii)'s helpers

The S-identity is proved by grouping `S`'s sum along the four-category
partition of `V ∖ {u,v}`.  Three kinds of lemma are needed:

* **counting** — `ncard_pair_split` turns each `x ∈ {u,v}` index count
  (`R_c`, `K_A`, `K_B`) into two counts over the *second* coordinate, and
  `sum_ite_eq_ncard_of_subset` turns a `Finset` sum of indicators into an
  `ncard`;
* **the `K` normalisation** — `ncard_split_KA_KB` proves `K = K_A + K_B`
  **as a cardinality statement** on the second-coordinate counts, from
  `row07i_K_split_exhaustive`;
* **the per-category value of `c`** — `cwt_catD`, `cwt_catA_near`,
  `cwt_catA_far`, one per category bullet of the proof. -/

/-- `#{a | P a}` as a `Finset.card`, with no decidability-instance friction:
`ext`/`simp` bridges the two instances rather than `congr`. -/
theorem ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] : ({a | P a} : Set α).ncard = (Finset.univ.filter P).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

/-- A sum of indicators over a `filter` containing the support is the `ncard` of
the support.

⚠ **Both `Decidable` instances are PLAIN IMPLICITS, deliberately.**  `Sc` is
declared under `open scoped Classical in`, so its `Finset.filter` and the `if`s
produced by `row07iii_pointwise` carry `Classical.propDecidable`, which is
*propositionally* but not *syntactically* the instance that `[DecidablePred _]`
would synthesize from `[DecidableEq V]`.  Making them instance-implicit here
makes the whole lemma fail to `rw`.  As plain implicits they are unified out of
the goal instead, and the bridge is free. -/
theorem sum_ite_filter_eq_ncard {α : Type*} [Fintype α] {Q : α → Prop}
    {instQ : DecidablePred Q} {P : α → Prop} {instP : DecidablePred P}
    (hPQ : ∀ a, P a → Q a) :
    ∑ a ∈ Finset.univ.filter Q, (if P a then (1:ℤ) else 0)
      = (({a | P a} : Set α).ncard : ℤ) := by
  rw [Finset.sum_subset (Finset.subset_univ _)
      (fun a _ ha => if_neg (fun hp =>
        ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hPQ a hp⟩))),
    Finset.sum_boole, @ncard_setOf_eq_card_filter α _ P instP]

/-- A count of index pairs `(x,w)` with `x ∈ {u,v}` splits into the two counts
over `w`.  (`u ≠ v` is what makes the two halves disjoint.) -/
theorem ncard_pair_split {u v : V} (hne : u ≠ v) (P : V → V → Prop) :
    {p : V × V | (p.1 = u ∨ p.1 = v) ∧ P p.1 p.2}.ncard
      = {w | P u w}.ncard + {w | P v w}.ncard := by
  classical
  have hinj : ∀ a : V, Function.Injective (fun w : V => (a, w)) := by
    intro a b c h; simpa using h
  have hset : {p : V × V | (p.1 = u ∨ p.1 = v) ∧ P p.1 p.2}
      = (fun w => (u, w)) '' {w | P u w} ∪ (fun w => (v, w)) '' {w | P v w} := by
    ext p
    obtain ⟨x, w⟩ := p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl | rfl, hP⟩
      · exact Or.inl ⟨w, hP, rfl, rfl⟩
      · exact Or.inr ⟨w, hP, rfl, rfl⟩
    · rintro (⟨w', hw, rfl, rfl⟩ | ⟨w', hw, rfl, rfl⟩)
      · exact ⟨Or.inl rfl, hw⟩
      · exact ⟨Or.inr rfl, hw⟩
  have hdisj : Disjoint ((fun w => (u, w)) '' {w | P u w})
      ((fun w => (v, w)) '' {w | P v w}) := by
    rw [Set.disjoint_left]
    rintro p ⟨w, -, rfl⟩ ⟨w', -, h⟩
    exact hne (congrArg Prod.fst h).symm
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (hinj u), Set.ncard_image_of_injective _ (hinj v)]

/-- **`K = K_A + K_B`, as a CARDINALITY statement.**  For a fixed
`x ∈ {u,v}` the `K_A`-counted and `K_B`-counted `w`'s partition the
`K`-counted ones — the independent count `#{w ∈ W_uv : {x,w} ∈ Ew}` that is the
paper's summand for `K(u,v)`.  Proved from `row07i_K_split_exhaustive`, which
is the mathematical content of row 7(i). -/
theorem ncard_split_KA_KB (G : SimpleGraph V) (u v x : V) :
    {w | w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G w x).Nonempty}.ncard
    + {w | w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G x w).Nonempty ∧
        WitAt G w x = ∅}.ncard
    = {w | w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G}.ncard := by
  classical
  have hdisj : Disjoint {w | w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G w x).Nonempty}
      {w | w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G x w).Nonempty ∧
        WitAt G w x = ∅} := by
    rw [Set.disjoint_left]
    rintro w ⟨-, -, hne⟩ ⟨-, -, -, hemp⟩
    exact (Set.not_nonempty_iff_eq_empty.mpr hemp) hne
  rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  congr 1
  ext w
  constructor
  · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases row07i_K_split_exhaustive G h2 with ⟨hA, -⟩ | ⟨-, hB1, hB2⟩
    · exact Or.inl ⟨h1, h2, hA⟩
    · exact Or.inr ⟨h1, h2, hB1, hB2⟩

/-- `R_c(u,v)` as two second-coordinate counts. -/
theorem Rc_eq_sum_ncard (G : SimpleGraph V) {u v : V} (hne : u ≠ v) :
    Rc G u v = {w | w ∈ catC G u v ∧ s(u,w) ∈ Anon G}.ncard
      + {w | w ∈ catC G u v ∧ s(v,w) ∈ Anon G}.ncard :=
  ncard_pair_split hne (fun x w => w ∈ catC G u v ∧ s(x,w) ∈ Anon G)

/-- `K(u,v) = K_A + K_B` in the second-coordinate form the S-identity's proof
produces. -/
theorem Kc_eq_sum_ncard (G : SimpleGraph V) {u v : V} (hne : u ≠ v) :
    Kc G u v = {w | w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G}.ncard
      + {w | w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G}.ncard := by
  have hA : KA G u v =
      {w | w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G ∧ (WitAt G w u).Nonempty}.ncard
      + {w | w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G ∧ (WitAt G w v).Nonempty}.ncard :=
    ncard_pair_split hne
      (fun x w => w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G w x).Nonempty)
  have hB : KB G u v =
      {w | w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G ∧ (WitAt G u w).Nonempty ∧
          WitAt G w u = ∅}.ncard
      + {w | w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G ∧ (WitAt G v w).Nonempty ∧
          WitAt G w v = ∅}.ncard :=
    ncard_pair_split hne
      (fun x w => w ∈ Wuv G u v ∧ s(x,w) ∈ Ew G ∧ (WitAt G x w).Nonempty ∧
        WitAt G w x = ∅)
  have h1 := ncard_split_KA_KB G u v u
  have h2 := ncard_split_KA_KB G u v v
  rw [Kc, hA, hB]
  omega

open scoped Classical in
/-- The category-(d) case: for `w ∈ W_uv` the edge `{u,w}` has codegree
`≥ 1` (namely `v`), so it cannot be an `E0` edge and `c({u,w}) = [{u,w} ∈ Ew]`. -/
theorem cwt_catD (G : SimpleGraph V) {u v w : V} (huv : G.Adj u v)
    (hvw : G.Adj v w) (huw : G.Adj u w) :
    cwt G s(u,w) = if s(u,w) ∈ Ew G then (1:ℤ) else 0 := by
  have hne : s(u,w) ∉ E0 G := by
    intro h
    have hv : v ∈ G.commonNeighbors u w := ⟨huv, hvw.symm⟩
    rw [((mem_E0_iff G u w).mp h).2] at hv
    exact hv
  rw [cwt_of_adj G huw]
  by_cases hw : s(u,w) ∈ Ew G
  · rw [if_pos (Set.mem_union_right _ hw), if_pos hw]
  · rw [if_neg (by rintro (h | h); exacts [hne h, hw h]), if_neg hw]

open scoped Classical in
/-- The category-(a) case, near end: `c({u,w}) = +1` unless `{u,w}` is
"unclassified" (codegree `≥ 1`, no witness), which is exactly the `U_a` clause. -/
theorem cwt_catA_near (G : SimpleGraph V) {u w : V} (huw : G.Adj u w) :
    cwt G s(u,w) = 1 - (if (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅
      then (1:ℤ) else 0) := by
  rw [cwt_of_adj G huw]
  by_cases h1 : (G.commonNeighbors u w).Nonempty
  · by_cases h2 : Wit G u w = ∅
    · have hA : s(u,w) ∉ E0 G ∪ Ew G := by
        rintro (h | h)
        · exact (Set.nonempty_iff_ne_empty.mp h1) ((mem_E0_iff G u w).mp h).2
        · exact (Set.not_nonempty_iff_eq_empty.mpr h2) ((mem_Ew_iff G u w).mp h).2.2
      have hB : (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅ := ⟨h1, h2⟩
      rw [if_neg hA, if_pos hB]
      ring
    · have hA : s(u,w) ∈ E0 G ∪ Ew G := Set.mem_union_right _
        ((mem_Ew_iff G u w).mpr ⟨huw, h1, Set.nonempty_iff_ne_empty.mpr h2⟩)
      have hB : ¬ ((G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅) :=
        fun hc => h2 hc.2
      rw [if_pos hA, if_neg hB]
      ring
  · have hA : s(u,w) ∈ E0 G ∪ Ew G := Set.mem_union_left _
      ((mem_E0_iff G u w).mpr ⟨huw, Set.not_nonempty_iff_eq_empty.mp h1⟩)
    have hB : ¬ ((G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅) :=
      fun hc => h1 hc.1
    rw [if_pos hA, if_neg hB]
    ring

/-- The category-(a) case, far end: `{v,w}` is a non-edge whose codegree is
`≥ 1` AUTOMATICALLY, since `u ∈ N(v) ∩ N(w)`.  So it contributes exactly `−1`. -/
theorem cwt_catA_far (G : SimpleGraph V) {u v w : V} (huv : G.Adj u v)
    (huw : G.Adj u w) (hvw : ¬ G.Adj v w) (hwv : w ≠ v) :
    cwt G s(v,w) = -1 := by
  classical
  rw [cwt_of_not_adj G hvw, if_pos]
  exact (mem_Anon_iff G v w).mpr
    ⟨fun h => hwv h.symm, hvw, ⟨u, huv.symm, huw.symm⟩⟩

open scoped Classical in
/-- **The pointwise content of the S-identity.**  For `w ∉ {u,v}`, the summand
of `S(u,v)` equals the six indicators the four category cases produce.  The
four categories are the four cases of `(Adj u w, Adj v w)`. -/
theorem row07iii_pointwise (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    {w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    cwt G s(u,w) + cwt G s(v,w) =
      ((if w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G then (1:ℤ) else 0)
        + (if w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G then (1:ℤ) else 0))
      - ((if w ∈ catC G u v ∧ s(u,w) ∈ Anon G then (1:ℤ) else 0)
        + (if w ∈ catC G u v ∧ s(v,w) ∈ Anon G then (1:ℤ) else 0))
      - (if w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅
          then (1:ℤ) else 0)
      - (if w ∈ catA G v u ∧ (G.commonNeighbors v w).Nonempty ∧ Wit G v w = ∅
          then (1:ℤ) else 0) := by
  by_cases huw : G.Adj u w <;> by_cases hvw : G.Adj v w
  · -- category (d): `w ∈ W_uv`; both `{u,w}` and `{v,w}` are `codeg ≥ 1` edges
    have hd : w ∈ Wuv G u v := ⟨huw, hvw⟩
    have E1 : (if w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G then (1:ℤ) else 0)
        = (if s(u,w) ∈ Ew G then (1:ℤ) else 0) := by
      by_cases h : s(u,w) ∈ Ew G
      · rw [if_pos ⟨hd, h⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.2), if_neg h]
    have E2 : (if w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G then (1:ℤ) else 0)
        = (if s(v,w) ∈ Ew G then (1:ℤ) else 0) := by
      by_cases h : s(v,w) ∈ Ew G
      · rw [if_pos ⟨hd, h⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.2), if_neg h]
    have E3 : (if w ∈ catC G u v ∧ s(u,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.1 huw)
    have E4 : (if w ∈ catC G u v ∧ s(v,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.1 huw)
    have E5 : (if w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧
        Wit G u w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => h.1.2.2 hvw)
    have E6 : (if w ∈ catA G v u ∧ (G.commonNeighbors v w).Nonempty ∧
        Wit G v w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => h.1.2.2 huw)
    rw [E1, E2, E3, E4, E5, E6, cwt_catD G huv hvw huw,
      cwt_catD G huv.symm huw hvw]
    ring
  · -- category (a): `w ∈ N(u) ∖ N[v]`
    have ha : w ∈ catA G u v := ⟨huw, hwv, hvw⟩
    have E1 : (if w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => hvw h.1.2)
    have E2 : (if w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => hvw h.1.2)
    have E3 : (if w ∈ catC G u v ∧ s(u,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.1 huw)
    have E4 : (if w ∈ catC G u v ∧ s(v,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.1 huw)
    have E5 : (if w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧
        Wit G u w = ∅ then (1:ℤ) else 0)
        = (if (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅
            then (1:ℤ) else 0) := by
      by_cases hc : (G.commonNeighbors u w).Nonempty ∧ Wit G u w = ∅
      · rw [if_pos ⟨ha, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    have E6 : (if w ∈ catA G v u ∧ (G.commonNeighbors v w).Nonempty ∧
        Wit G v w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => hvw h.1.1)
    rw [E1, E2, E3, E4, E5, E6, cwt_catA_near G huw,
      cwt_catA_far G huv huw hvw hwv]
    ring
  · -- category (b): `w ∈ N(v) ∖ N[u]`
    have hb : w ∈ catA G v u := ⟨hvw, hwu, huw⟩
    have E1 : (if w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => huw h.1.1)
    have E2 : (if w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => huw h.1.1)
    have E3 : (if w ∈ catC G u v ∧ s(u,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.2 hvw)
    have E4 : (if w ∈ catC G u v ∧ s(v,w) ∈ Anon G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => h.1.2.2.2 hvw)
    have E5 : (if w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧
        Wit G u w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => huw h.1.1)
    have E6 : (if w ∈ catA G v u ∧ (G.commonNeighbors v w).Nonempty ∧
        Wit G v w = ∅ then (1:ℤ) else 0)
        = (if (G.commonNeighbors v w).Nonempty ∧ Wit G v w = ∅
            then (1:ℤ) else 0) := by
      by_cases hc : (G.commonNeighbors v w).Nonempty ∧ Wit G v w = ∅
      · rw [if_pos ⟨hb, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    rw [E1, E2, E3, E4, E5, E6, cwt_catA_near G hvw,
      cwt_catA_far G huv.symm hvw huw hwu]
    ring
  · -- category (c): adjacent to neither
    have hc : w ∈ catC G u v := ⟨hwu, hwv, huw, hvw⟩
    have E1 : (if w ∈ Wuv G u v ∧ s(u,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => huw h.1.1)
    have E2 : (if w ∈ Wuv G u v ∧ s(v,w) ∈ Ew G then (1:ℤ) else 0) = 0 :=
      if_neg (fun h => huw h.1.1)
    have E3 : (if w ∈ catC G u v ∧ s(u,w) ∈ Anon G then (1:ℤ) else 0)
        = (if s(u,w) ∈ Anon G then (1:ℤ) else 0) := by
      by_cases h : s(u,w) ∈ Anon G
      · rw [if_pos ⟨hc, h⟩, if_pos h]
      · rw [if_neg (fun hk => h hk.2), if_neg h]
    have E4 : (if w ∈ catC G u v ∧ s(v,w) ∈ Anon G then (1:ℤ) else 0)
        = (if s(v,w) ∈ Anon G then (1:ℤ) else 0) := by
      by_cases h : s(v,w) ∈ Anon G
      · rw [if_pos ⟨hc, h⟩, if_pos h]
      · rw [if_neg (fun hk => h hk.2), if_neg h]
    have E5 : (if w ∈ catA G u v ∧ (G.commonNeighbors u w).Nonempty ∧
        Wit G u w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => huw h.1.1)
    have E6 : (if w ∈ catA G v u ∧ (G.commonNeighbors v w).Nonempty ∧
        Wit G v w = ∅ then (1:ℤ) else 0) = 0 := if_neg (fun h => hvw h.1.1)
    rw [E1, E2, E3, E4, E5, E6, cwt_of_not_adj G huw, cwt_of_not_adj G hvw]
    split_ifs <;> ring

/-- **Row 7(iii) — the S-identity.**
`S(u,v) = −U_a(u,v) − U_b(u,v) − R_c(u,v) + K(u,v)`.

★ PROVED; no `sorry`, and no other row is used except
`row07i_K_split_exhaustive` (which is itself proved).  The proof is the four
category bullets: `row07iii_pointwise` is the per-`w` identity, and the six
resulting indicator sums are the six `ncard`s that `K`, `R_c`, `U_a`, `U_b`
are.

★ **Why defining `Kc` as `KA + KB` does not make this circular.**  What the
S-identity needs is that `K_A + K_B` equals the *independent* count
`Σ_{w0 ∈ W_uv} [{u,w0} ∈ Ew] + [{v,w0} ∈ Ew]` — the paper's `K(u,v)` — and
that is exactly what `ncard_split_KA_KB` PROVES here, from
`row07i_K_split_exhaustive`.  The partition is discharged, not assumed. -/
theorem row07iii_S_identity (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    Sc G u v = -(Ua G u v : ℤ) - (Ua G v u : ℤ) - (Rc G u v : ℤ)
                + (Kc G u v : ℤ) := by
  classical
  unfold Sc
  -- ⚠ `Finset.mem_filter.mp hw` does NOT typecheck here: `Sc`'s filter carries
  -- `Classical.propDecidable` and the elaborator synthesizes the `DecidableEq V`
  -- instance instead.  `simpa` unifies the two; see `sum_ite_filter_eq_ncard`.
  rw [Finset.sum_congr rfl (fun w hw => by
    have hw' : w ≠ u ∧ w ≠ v := by simpa using hw
    exact row07iii_pointwise G huv hw'.1 hw'.2)]
  have h1 : ∀ a : V, (a ∈ Wuv G u v ∧ s(u,a) ∈ Ew G) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.1.ne', ha.1.2.ne'⟩
  have h2 : ∀ a : V, (a ∈ Wuv G u v ∧ s(v,a) ∈ Ew G) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.1.ne', ha.1.2.ne'⟩
  have h3 : ∀ a : V, (a ∈ catC G u v ∧ s(u,a) ∈ Anon G) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.1, ha.1.2.1⟩
  have h4 : ∀ a : V, (a ∈ catC G u v ∧ s(v,a) ∈ Anon G) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.1, ha.1.2.1⟩
  have h5 : ∀ a : V, (a ∈ catA G u v ∧ (G.commonNeighbors u a).Nonempty ∧
      Wit G u a = ∅) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.1.ne', ha.1.2.1⟩
  have h6 : ∀ a : V, (a ∈ catA G v u ∧ (G.commonNeighbors v a).Nonempty ∧
      Wit G v a = ∅) → (a ≠ u ∧ a ≠ v) :=
    fun a ha => ⟨ha.1.2.1, ha.1.1.ne'⟩
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ite_filter_eq_ncard h1, sum_ite_filter_eq_ncard h2,
    sum_ite_filter_eq_ncard h3, sum_ite_filter_eq_ncard h4,
    sum_ite_filter_eq_ncard h5, sum_ite_filter_eq_ncard h6,
    Rc_eq_sum_ncard G huv.ne, Kc_eq_sum_ncard G huv.ne, Ua, Ua]
  push_cast
  ring

/-- **Row 8 — Corollary 3.8 (per-edge sufficiency).**
`D_inc ≤ 1 − (Slack_c − K_B) − U_a − U_b − (R⁺ − K_A) ≤ 1 − (Slack_c − K_B)`,
for ANY edge.
★ PROVED from rows 6, 7(ii), 7(iii) — no new `sorry`.  Substituting 7(iii)
into 6 and dropping the nonnegative `U_a`, `U_b` and `R⁺ − K_A` (the latter by
7(ii)) is exactly the displayed chain, and it is pure linear arithmetic
over `ℤ`. -/
theorem row08_per_edge_sufficiency (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    Dinc G u v ≤ 1 - sigmaTerm G u v := by
  have h6 := row06_refined_deletion_bound G huv
  have h7iii := row07iii_S_identity G huv
  have hKA : (KA G u v : ℤ) ≤ (Rplus G u v : ℤ) := by
    exact_mod_cast row07ii_Rplus_ge_KA G huv
  have hUa : (0 : ℤ) ≤ (Ua G u v : ℤ) := Int.natCast_nonneg _
  have hUb : (0 : ℤ) ≤ (Ua G v u : ℤ) := Int.natCast_nonneg _
  rw [Kc] at h7iii
  push_cast at h7iii
  rw [sigmaTerm, Slackc]
  linarith

/-- Row 8's consumable form: `Slack_c ≥ K_B ⟹ D_inc ≤ 1`.
★ PROVED from `row08_per_edge_sufficiency` (no new `sorry`): unfolding
`sigmaTerm = Slack_c − K_B`, the hypothesis says `sigmaTerm ≥ 0`. -/
theorem row08_cor (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (h : (KB G u v : ℤ) ≤ Slackc G u v) : Dinc G u v ≤ 1 := by
  have h8 := row08_per_edge_sufficiency G huv
  rw [sigmaTerm] at h8
  linarith

/-- The "`w` is in category (c)" step of Theorem 3.9's injection, stated
symmetrically in the two endpoints so `x = u` and `x = v` are one lemma.
If `x` witnesses `{w,z}` at `w` then `w` is adjacent to neither `x` nor the
other endpoint `x'`: the first is the witness condition, and `x' ∈ N(w)` would
give `x' ∈ N(w) ∩ N(x) = {z}`, i.e. `x' = z`, which `z ∉ {u,v}` forbids. -/
theorem row09_catC_step (G : SimpleGraph V) {x x' w z : V} (hxx' : G.Adj x x')
    (hnadj : ¬ G.Adj w x) (hcn : G.commonNeighbors w x = {z}) (hz : z ≠ x') :
    ¬ G.Adj x w ∧ ¬ G.Adj x' w := by
  refine ⟨fun h => hnadj h.symm, fun h => ?_⟩
  have hmem : x' ∈ G.commonNeighbors w x :=
    G.mem_commonNeighbors.mpr ⟨h.symm, hxx'⟩
  rw [hcn] at hmem
  exact hz hmem.symm

/-- One branch of Theorem 3.9's injection: given that the chosen pair-witness
`x ∈ {u,v}` witnesses the `B`-edge `e = {w,z}` **at `w`**, the image
`(x,w)` is one of the `R_c(u,v)` instances, and it remembers `z` — hence `e` —
as the unique element of `N(x) ∩ N(w)`. -/
theorem row09_step (G : SimpleGraph V) {u v w z x : V} {e : Sym2 V}
    (he : e = s(w,z)) (huv : G.Adj u v) (hxuv : x = u ∨ x = v)
    (hx : x ∈ WitAt G w z) (hzu : z ≠ u) (hzv : z ≠ v)
    (hwu : w ≠ u) (hwv : w ≠ v) :
    ∃ p : V × V,
      p ∈ {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ catC G u v ∧
            s(p.1, p.2) ∈ Anon G} ∧
      ∃ z', e = s(p.2, z') ∧ G.commonNeighbors p.1 p.2 = {z'} := by
  obtain ⟨hxw, hnadj, hcn⟩ := hx
  have hcn' : G.commonNeighbors x w = {z} := by rw [G.commonNeighbors_symm]; exact hcn
  refine ⟨(x, w), ⟨hxuv, ⟨hwu, hwv, ?_, ?_⟩, ?_⟩, z, he, hcn'⟩
  · rcases hxuv with rfl | rfl
    · exact (row09_catC_step G huv hnadj hcn hzv).1
    · exact (row09_catC_step G huv.symm hnadj hcn hzu).2
  · rcases hxuv with rfl | rfl
    · exact (row09_catC_step G huv hnadj hcn hzv).2
    · exact (row09_catC_step G huv.symm hnadj hcn hzu).1
  · exact (mem_Anon_iff G x w).mpr
      ⟨hxw, fun h => hnadj h.symm, by rw [hcn']; exact ⟨z, rfl⟩⟩

/-- The injection `B ≤ R_c` that row 9 turns on.  (Declared *before* row 9
because row 9 is derived from it.)

★ PROVED; no `sorry`, and no other row is used.  This is Theorem 3.9's
displayed injection verbatim: pick a witness `x ∈ Wit(e) ⊆ {u,v}`, note it
witnesses `e` at exactly one endpoint — say `w` — and map `e ↦ (x,w)`.  The two
`Wit = WitAt ∪ WitAt` branches are the *same* argument applied to `s(w,z)` and
to `s(z,w)`, which is why `row09_step` takes the pair equation `he` as a
parameter.

⚠ **The hypothesis `h0 : N(u) ∩ N(v) = ∅` is not used.**  The injection
`B(u,v) ↪ R_c(u,v)` holds for *any* edge `{u,v}`; `codeg(u,v) = 0` is context
in Theorem 3.9 — it is what kills `K` and `R⁺` in the surrounding argument —
not a premise of the injection.  The statement is left as transcribed rather
than strengthened, since the weaker form is what `row09_E0_case` consumes. -/
theorem row09_B_le_Rc (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (h0 : G.commonNeighbors u v = ∅) : Bc G u v ≤ Rc G u v := by
  classical
  have key : ∀ e : Sym2 V, ∃ p : V × V, e ∈ BSet G u v →
      (p ∈ {p : V × V | (p.1 = u ∨ p.1 = v) ∧ p.2 ∈ catC G u v ∧
            s(p.1, p.2) ∈ Anon G} ∧
       ∃ z', e = s(p.2, z') ∧ G.commonNeighbors p.1 p.2 = {z'}) := by
    intro e
    by_cases he : e ∈ BSet G u v
    · obtain ⟨hEw, w, z, rfl, hwu, hwv, hzu, hzv, hsub⟩ := he
      obtain ⟨x, hx⟩ := ((mem_Ew_iff G w z).mp hEw).2.2
      have hxuv : x = u ∨ x = v := by
        rcases hsub hx with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hx with hx | hx
      · obtain ⟨p, hp⟩ := row09_step G rfl huv hxuv hx hzu hzv hwu hwv
        exact ⟨p, fun _ => hp⟩
      · obtain ⟨p, hp⟩ := row09_step G (Sym2.eq_swap) huv hxuv hx hwu hwv hzu hzv
        exact ⟨p, fun _ => hp⟩
    · exact ⟨(u, u), fun h => absurd h he⟩
  choose f hf using key
  rw [Bc_eq_ncard_BSet, Rc]
  refine Set.ncard_le_ncard_of_injOn f (fun e he => (hf e he).1) ?_ (Set.toFinite _)
  intro e1 h1 e2 h2 h
  obtain ⟨z1, hz1, hc1⟩ := (hf e1 h1).2
  obtain ⟨z2, hz2, hc2⟩ := (hf e2 h2).2
  rw [h] at hc1
  have hz : z1 = z2 := Set.singleton_injective (hc1.symm.trans hc2)
  rw [hz1, hz2, h, hz]

/-- **Row 9 — Theorem 3.9 (the `E0` case).**
For ANY `E0` edge (`codeg(u,v) = 0`): `D(F) − D(F−{u,v}) ≤ 1`.
The proof turns on the injection `B(u,v) ↪ R_c(u,v)` (`row09_B_le_Rc`).

★ PROVED from rows 6, 7(iii) and `row09_B_le_Rc` — no new `sorry`.  The paper's
proof of Theorem 3.9 reads "By Theorem 3.6 (with R⁺ ≥ 0 dropped) and 3.7(iii)",
so row 9's input set is {6, 7(iii), injection}.  The
`W_uv = ∅ ⟹ K_A = K_B = 0` step the paper states in one clause is the
`hKA0`/`hKB0` block below. -/
theorem row09_E0_case (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (h0 : G.commonNeighbors u v = ∅) : Dinc G u v ≤ 1 := by
  have h6 := row06_refined_deletion_bound G huv
  have h7iii := row07iii_S_identity G huv
  have hB := row09_B_le_Rc G huv h0
  -- `codeg(u,v) = 0` empties category (d), so `K_A = K_B = 0`.
  have hKA0 : KA G u v = 0 := by
    rw [KA, Set.ncard_eq_zero (Set.toFinite _)]
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hp2, -⟩
    rw [Wuv, h0] at hp2
    exact hp2
  have hKB0 : KB G u v = 0 := by
    rw [KB, Set.ncard_eq_zero (Set.toFinite _)]
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hp2, -⟩
    rw [Wuv, h0] at hp2
    exact hp2
  have hRp : (0 : ℤ) ≤ (Rplus G u v : ℤ) := Int.natCast_nonneg _
  have hUa : (0 : ℤ) ≤ (Ua G u v : ℤ) := Int.natCast_nonneg _
  have hUb : (0 : ℤ) ≤ (Ua G v u : ℤ) := Int.natCast_nonneg _
  have hBR : (Bc G u v : ℤ) ≤ (Rc G u v : ℤ) := by exact_mod_cast hB
  rw [Kc, hKA0, hKB0] at h7iii
  push_cast at h7iii
  linarith

/-- **Row 10 — Proposition 3.10 (pigeonhole).**
If `Σ(F) ≥ 0` and `Ew(F) ≠ ∅` then some `Ew` edge has `Slack_c ≥ K_B`.
(A finite non-empty sum of strictly negative integers is negative.)
★ PROVED (no new `sorry`). -/
theorem row10_pigeonhole (G : SimpleGraph V) (hs : 0 ≤ Sig G)
    (hne : (Ew G).Nonempty) :
    ∃ u v, s(u,v) ∈ Ew G ∧ (KB G u v : ℤ) ≤ Slackc G u v := by
  classical
  by_contra hc
  push_neg at hc
  -- `hc : ∀ u v, s(u,v) ∈ Ew G → Slack_c(u,v) < K_B(u,v)`, i.e. every summand < 0.
  rw [Sig] at hs
  obtain ⟨e0, he0⟩ := hne
  have hTne : (Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G)).Nonempty :=
    ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he0⟩⟩
  have hneg : ∀ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G),
      sigmaTermS G e < 0 := by
    intro e he
    have heEw : e ∈ Ew G := (Finset.mem_filter.mp he).2
    clear he
    induction e using Sym2.ind with
    | _ u v =>
      have h1 := hc u v heEw
      have h2 : sigmaTermS G s(u,v) = sigmaTerm G u v := rfl
      rw [h2, sigmaTerm, Slackc] at *
      linarith
  have hzero : ((0 : ℤ)) =
      ∑ _e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), (0 : ℤ) := by simp
  have hlt := Finset.sum_lt_sum_of_nonempty hTne hneg
  rw [← hzero] at hlt
  exact absurd hs (not_le.mpr hlt)

/-! ### Rows 12–17: the internals of Theorem Σ. -/

/-- An **R-unit**: a triple `(x,s,t)` with `s ∈ D2(x)`, `t ∈ Nw(x)`,
`t ∉ N[s]`. -/
def RUnits (G : SimpleGraph V) : Set (V × V × V) :=
  {p | p.2.1 ∈ D2set G p.1 ∧ p.2.2 ∈ Nw G p.1 ∧ p.2.2 ≠ p.2.1 ∧
       ¬ G.Adj p.2.2 p.2.1}

/-- A **B-unit**: a pair `(e,f)` of vertex-disjoint `Ew`-edges with
`Wit(e) ⊆ f`. -/
def BUnits (G : SimpleGraph V) : Set (Sym2 V × Sym2 V) :=
  {q | q.1 ∈ Ew G ∧ q.2 ∈ Ew G ∧ (∀ w, w ∈ q.1 → w ∉ q.2) ∧
       ∀ a b, q.1 = s(a,b) → Wit G a b ⊆ {w | w ∈ q.2}}

/-- A **K-unit**: `((x,z),t)` with `{x,z} ∈ Ew(F)`, `Wit_x(z) ≠ ∅`,
`Wit_z(x) = ∅`, and `t ∈ Nw(x) ∩ N(z)`. -/
def KUnits (G : SimpleGraph V) : Set ((V × V) × V) :=
  {q | s(q.1.1, q.1.2) ∈ Ew G ∧ (WitAt G q.1.1 q.1.2).Nonempty ∧
       WitAt G q.1.2 q.1.1 = ∅ ∧ q.2 ∈ Nw G q.1.1 ∧ G.Adj q.1.2 q.2}

/-! #### The `E0`-freeness upgrade, and `Nw(x) ∖ N[z]`

`E0(F) = ∅` is used **exactly three times, and all three are the same one-line
upgrade**: "an edge that is witnessed and has codegree `≥ 1` lies in `Ew`" —
where, under `E0 = ∅`, the codegree side is automatic.  That upgrade is
`Ew_of_witnessed` below; the three call sites are (L1)'s slot count
(`row14_L1_slot_count`), LEMMA A step 3 (`row16_lemma_A_step`), and the (T)/(D)
branch test.  Factoring it once makes the hypothesis accounting *checkable*:
`hE0` is consumed by exactly the rows that route through this lemma. -/

/-- **The `E0`-freeness upgrade.**  With `E0(F) = ∅`, an edge that carries a
witness is an `Ew` edge — the codegree-`≥ 1` clause comes for free, since an
edge of codegree `0` would lie in the empty set `E0(F)`. -/
theorem Ew_of_witnessed (G : SimpleGraph V) (hE0 : E0 G = ∅) {a b : V}
    (hadj : G.Adj a b) (hw : (Wit G a b).Nonempty) : s(a,b) ∈ Ew G := by
  rw [mem_Ew_iff]
  refine ⟨hadj, ?_, hw⟩
  rw [Set.nonempty_iff_ne_empty]
  intro hcn
  have hmem : s(a,b) ∈ E0 G := (mem_E0_iff G a b).mpr ⟨hadj, hcn⟩
  rw [hE0] at hmem
  exact hmem

/-- `Nw(x) ∖ N[z]`, the **free-slot set**.
`N[z] = N(z) ∪ {z}`, so `t ∉ N[z]` unfolds to `t ≠ z ∧ ¬ G.Adj t z` — the same
convention `RUnits` already uses for its own `t ∉ N[s]` clause, kept identical
on purpose so the two can be matched without a bridging lemma. -/
def NwOut (G : SimpleGraph V) (x z : V) : Set V :=
  {t | t ∈ Nw G x ∧ t ≠ z ∧ ¬ G.Adj t z}

/-! #### Row 11's remaining halves: (P3) and (P4)

Row 11 is the four elementary facts (P1)–(P4); `row11_P1` and `row11_P2` are
stated above, and (P3) and (P4) follow here.

(P3) is what makes `φ`'s two K-branches *land in `RUnits` at all*, and (P4) is
what puts both witnesses of a 2-witness B-unit at one endpoint.  Row 15 cannot
be stated, let alone proved, without them.

They are placed here rather than beside `row11_P1`/`row11_P2` for a file-order
reason only: (P3)'s conclusion mentions `RUnits`, which is defined above in
this section and not at row 11. -/

/-- **(P3)** — row 11, third fact.
If `y ∈ Wit_x(z)` and `t ∈ Nw(x) ∩ N(z)`, then **both** `(x,y,t)` and `(t,y,x)`
are R-units.  ★ PROVED; no `sorry`.

★ The asymmetry is the point, and it is what makes the (T) branch of `φ`
possible at all: the *same* data `(x,y,t)` yields a legitimate R-unit in
**two different columns** — one based at `x`, one based at `t`.  This
cross-vertex movement of charge is essential; every "locally paying" variant of
Theorem Σ is refuted by it. -/
theorem row11_P3 (G : SimpleGraph V) {x z y t : V} (hy : y ∈ WitAt G x z)
    (ht : t ∈ Nw G x) (htz : G.Adj z t) :
    (x, y, t) ∈ RUnits G ∧ (t, y, x) ∈ RUnits G := by
  obtain ⟨hyx, hxy, hcn⟩ := hy
  have hxt : G.Adj x t := ((mem_Ew_iff G x t).mp ht).1
  -- `t ≠ z` because `z ∉ N(z)`.
  have htne : t ≠ z := (G.ne_of_adj htz).symm
  -- (P2) = row 11: `t ∈ N(x) ∖ {z}` lies outside `N[y]`.
  obtain ⟨htny, htnadj⟩ :=
    row11_P2 G (show y ∈ WitAt G x z from ⟨hyx, hxy, hcn⟩) hxt htne
  -- `z ∈ N(x) ∩ N(y)`.
  have hzmem : z ∈ G.commonNeighbors x y := by rw [hcn]; rfl
  obtain ⟨hxz, hyz⟩ := (mem_commonNeighbors G).mp hzmem
  -- `y ∈ D2(x)`: `xy ∉ E` and `z` is a common neighbour.
  have hyD2x : y ∈ D2set G x := by
    rw [D2set, Set.mem_setOf_eq, mem_Anon_iff]
    exact ⟨Ne.symm hyx, hxy, ⟨z, hzmem⟩⟩
  -- `x ∈ Nw(t)`: the same `Ew` edge, read from the other end.
  have hxNwt : x ∈ Nw G t := by
    rw [Nw, Set.mem_setOf_eq, Sym2.eq_swap]; exact ht
  -- `y ∈ D2(t)`: `ty ∉ E` by (P2), and `z ∈ N(t) ∩ N(y)`.
  have hyD2t : y ∈ D2set G t := by
    rw [D2set, Set.mem_setOf_eq, mem_Anon_iff]
    exact ⟨htny, htnadj, ⟨z, (mem_commonNeighbors G).mpr ⟨htz.symm, hyz⟩⟩⟩
  exact ⟨⟨hyD2x, ht, htny, htnadj⟩, ⟨hyD2t, hxNwt, Ne.symm hyx, hxy⟩⟩

/-- **(P4), the exception lemma** — row 11, fourth fact.
★ PROVED; no `sorry`.

In the paper: if `e = {a,b} ∈ Ew` and `Wit(e) = f` for an edge `f` disjoint
from `e`, then both witnesses lie at the same endpoint of `e`; the proof
derives `q = b` and contradicts `e ∩ f = ∅`.

★ **Transcribed in its SHARP form, `q = b`, not in the contrapositive form
with the disjointness hypothesis carried.**  `{a,b} ∈ Ew`, `Wit(e) = f` and
`e ∩ f = ∅` are all *unused* by the actual argument, which consumes only the
two witness memberships and the edge `pq`.  The disjointness is what makes
`q = b` absurd **at the call site**, and is supplied there (`row11_P4_ne`). -/
theorem row11_P4 (G : SimpleGraph V) {a b p q : V}
    (hp : p ∈ WitAt G a b) (hq : q ∈ WitAt G b a) (hpq : G.Adj p q) : q = b := by
  obtain ⟨hpa, hap, hcnp⟩ := hp
  obtain ⟨hqb, hbq, hcnq⟩ := hq
  -- `a ∈ N(q)`, from the witness condition of `q` at `b`: `N(b) ∩ N(q) = {a}`.
  have hamem : a ∈ G.commonNeighbors b q := by rw [hcnq]; rfl
  obtain ⟨hba, hqa⟩ := (mem_commonNeighbors G).mp hamem
  -- Then `q ∈ N(a) ∩ N(p) = {b}` — the witness condition of `p` at `a`.
  have hmem : q ∈ G.commonNeighbors a p := (mem_commonNeighbors G).mpr ⟨hqa.symm, hpq⟩
  rw [hcnp, Set.mem_singleton_iff] at hmem
  exact hmem

/-- **(P4) in the paper's stated form**: for an edge `f = {p,q}` disjoint from
`e = {a,b}`, the two witnesses cannot sit at opposite endpoints of `e`.
Immediate from `row11_P4`.  ★ PROVED; no `sorry`. -/
theorem row11_P4_ne (G : SimpleGraph V) {a b p q : V}
    (hp : p ∈ WitAt G a b) (hq : q ∈ WitAt G b a) (hpq : G.Adj p q)
    (hdisj : q ≠ b) : False :=
  hdisj (row11_P4 G hp hq hpq)

/-! #### Row 12 — Identity 4.1, and the three fibre counts it rests on

Identity 4.1 is proved by three bijections, one per unit type.  Each of them is
a **fibration over the `Ew` edges**: every unit canonically determines an `Ew`
edge, and the fibre over `{u,v}` is exactly the set counted by `R_c(u,v)`,
`B(u,v)`, `K_B(u,v)`.

★ The fibre maps, which the paper's prose leaves implicit:
an R-unit `(x,s,t) ↦ {x,t}` (an `Ew` edge because `t ∈ Nw(x)`);
a B-unit `(e,f) ↦ f`; a K-unit `((x,z),t) ↦ {x,t}`.
In the R and K cases injectivity on a fibre is `Sym2.congr_right`: the edge
`{x,t}` together with the *ordered* first coordinate `x` determines `t`. -/

/-- `R_c`, `B` and `K_B` as functions of the UNORDERED pair.  All three are
symmetric (`rc_comm`, `bc_comm`, `kb_comm`), which is exactly what licenses
writing `Σ_{Ew} R_c` — a sum indexed by edges, not by ordered pairs.
Introduced so that Identity 4.1's three *pairwise* clauses can be stated in the
paper's own form; see `row12_R_pairwise` and friends below. -/
noncomputable def RcS (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨Rc G, rc_comm G⟩

/-- `B(u,v)` as a function of the unordered pair. -/
noncomputable def BcS (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨Bc G, bc_comm G⟩

/-- `K_B(u,v)` as a function of the unordered pair. -/
noncomputable def KBS (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨KB G, kb_comm G⟩

open scoped Classical in
/-- **Fibrewise counting over `Ew(F)`.**  If `f` sends every element of `s` to
an `Ew` edge, then `|s|` is the sum over `Ew(F)` of the fibre cardinalities.
This is `Finset.card_eq_sum_card_fiberwise` in the file's `Set.ncard` idiom. -/
theorem ncard_eq_sum_fiber_Ew {α : Type*} [Fintype α] (G : SimpleGraph V)
    (s : Set α) (f : α → Sym2 V) (hf : ∀ a ∈ s, f a ∈ Ew G) :
    s.ncard = ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G),
      {a | a ∈ s ∧ f a = e}.ncard := by
  classical
  rw [ncard_eq_card_filter s,
    Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G))
      (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf a (by simpa using ha)⟩)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [ncard_setOf_eq_card_filter]
  congr 1
  ext a
  simp

open scoped Classical in
/-- **Identity 4.1's first bijection, fibrewise: `#R = Σ_{Ew} R_c`.**
In the paper: an R-unit `(x,s,t)` corresponds to the pair `{x,t}` (an `Ew`
edge, since `t ∈ Nw(x)`) together with the category-(c) `A`-instance `(x,s)`.
The fibre of `{u,v}` is the `R_c(u,v)`-counted set exactly.

★ The equivalence `t ∉ N[s] ⟺ s ∉ N[t]` is what makes the forward direction
work: an R-unit records `s ∉ N[t]` (`t ≠ s`, `¬ t ∼ s`) at the *far* endpoint,
while category (c) asks for `s ∉ N[u]` and `s ∉ N[v]` at *both*; the near half
comes from `s ∈ D2(x)` (`{x,s} ∈ A`, so `x ≠ s` and `¬ x ∼ s`). -/
theorem row12_fiber_R (G : SimpleGraph V) {u v : V} (hEw : s(u,v) ∈ Ew G) :
    {p : V × V × V | p ∈ RUnits G ∧ s(p.1, p.2.2) = s(u,v)}.ncard = Rc G u v := by
  classical
  have hinj : Set.InjOn (fun p : V × V × V => (p.1, p.2.1))
      {p : V × V × V | p ∈ RUnits G ∧ s(p.1, p.2.2) = s(u,v)} := by
    rintro ⟨x, a, t⟩ ⟨-, h1⟩ ⟨x', a', t'⟩ ⟨-, h2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : t = t' := Sym2.congr_right.mp (h1.trans h2.symm)
    rw [ht]
  rw [← Set.ncard_image_of_injOn hinj, Rc]
  congr 1
  ext q
  obtain ⟨x, a⟩ := q
  constructor
  · rintro ⟨⟨x0, a0, t⟩, ⟨⟨hD2, hNw, hts, hnadj⟩, he⟩, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hA : s(x0, a0) ∈ Anon G := hD2
    obtain ⟨hxa, hnxa, -⟩ := (mem_Anon_iff G x0 a0).mp hA
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl,
        ⟨fun h => hxa h.symm, fun h => hts h.symm, hnxa, hnadj⟩, hA⟩
    · exact ⟨Or.inr rfl,
        ⟨fun h => hts h.symm, fun h => hxa h.symm, hnadj, hnxa⟩, hA⟩
  · rintro ⟨hx, ⟨hcu, hcv, hcnu, hcnv⟩, hA⟩
    rcases hx with rfl | rfl
    · exact ⟨(x, a, v), ⟨⟨hA, hEw, fun h => hcv h.symm, hcnv⟩, rfl⟩, rfl⟩
    · refine ⟨(x, a, u), ⟨⟨hA, ?_, fun h => hcu h.symm, hcnu⟩, ?_⟩, rfl⟩
      · show s(x, u) ∈ Ew G
        rw [Sym2.eq_swap]; exact hEw
      · show s(x, u) = s(u, x)
        exact Sym2.eq_swap

open scoped Classical in
/-- **Identity 4.1's second bijection, fibrewise: `#B = Σ_{Ew} B`.**
For fixed `f = {u,v} ∈ Ew`, the edges `e` with `e ∩ f = ∅` and `Wit(e) ⊆ f` are
by definition the `B(u,v)`-counted edges — i.e. the fibre map is the second
coordinate and the fibre is `B(u,v)` verbatim. -/
theorem row12_fiber_B (G : SimpleGraph V) {u v : V} (hEw : s(u,v) ∈ Ew G) :
    {q : Sym2 V × Sym2 V | q ∈ BUnits G ∧ q.2 = s(u,v)}.ncard = Bc G u v := by
  classical
  -- The BUnits-membership of `(s(w,z), s(u,v))`, in the form both directions want.
  have key : ∀ w z : V, s(w,z) ∈ Ew G → w ≠ u → w ≠ v → z ≠ u → z ≠ v →
      Wit G w z ⊆ ({u, v} : Set V) → (s(w,z), s(u,v)) ∈ BUnits G := by
    intro w z hwz hwu hwv hzu hzv hsub
    refine ⟨hwz, hEw, ?_, ?_⟩
    · intro y hy
      rw [Sym2.mem_iff] at hy ⊢
      rcases hy with rfl | rfl
      · exact fun h => h.elim hwu hwv
      · exact fun h => h.elim hzu hzv
    · intro a b hab y hy
      have hy' : y ∈ Wit G w z := by
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hy
        · rwa [wit_comm]
      have := hsub hy'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rw [Set.mem_setOf_eq, Sym2.mem_iff]
      exact this
  have hinj : Set.InjOn (fun q : Sym2 V × Sym2 V => q.1)
      {q : Sym2 V × Sym2 V | q ∈ BUnits G ∧ q.2 = s(u,v)} := by
    rintro ⟨e1, f1⟩ ⟨-, h1⟩ ⟨e2, f2⟩ ⟨-, h2⟩ h
    simp only at h h1 h2
    rw [h, h1, h2]
  rw [← Set.ncard_image_of_injOn hinj, Bc]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ w z =>
    constructor
    · rintro ⟨⟨e0, f0⟩, ⟨⟨he0, -, hdis, hsub⟩, hf⟩, hq⟩
      simp only at hf hq
      subst hq
      subst hf
      have hw : ¬ (w = u ∨ w = v) := by
        have := hdis w (Sym2.mem_iff.mpr (Or.inl rfl))
        rwa [Sym2.mem_iff] at this
      have hz : ¬ (z = u ∨ z = v) := by
        have := hdis z (Sym2.mem_iff.mpr (Or.inr rfl))
        rwa [Sym2.mem_iff] at this
      push_neg at hw hz
      refine ⟨he0, w, z, rfl, hw.1, hw.2, hz.1, hz.2, ?_⟩
      intro y hy
      have := hsub w z rfl hy
      rw [Set.mem_setOf_eq, Sym2.mem_iff] at this
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    · rintro ⟨heEw, w', z', hwz, hwu, hwv, hzu, hzv, hsub⟩
      rcases Sym2.eq_iff.mp hwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(s(w,z), s(u,v)), ⟨key w z heEw hwu hwv hzu hzv hsub, rfl⟩, rfl⟩
      · refine ⟨(s(w,z), s(u,v)), ⟨key w z heEw hzu hzv hwu hwv ?_, rfl⟩, rfl⟩
        rwa [wit_comm]

open scoped Classical in
/-- **Identity 4.1's third bijection, fibrewise: `#K = Σ_{Ew} K_B`.**
For a fixed ordered edge `(x,z)` carrying a witness at `x` and none at `z`, the
pairs `{u,v}` in which `{x,z}` is a `K_B` edge are exactly the pairs `{x,t}`
with `t ∈ Nw(x)` and `z ∈ W_{x,t}`, i.e. `t ∈ N(z)`.
So the fibre map is `((x,z),t) ↦ {x,t}` and the fibre over `{u,v}` is the
`K_B(u,v)`-counted set of index pairs `(x,z)`. -/
theorem row12_fiber_K (G : SimpleGraph V) {u v : V} (hEw : s(u,v) ∈ Ew G) :
    {q : (V × V) × V | q ∈ KUnits G ∧ s(q.1.1, q.2) = s(u,v)}.ncard = KB G u v := by
  classical
  have hinj : Set.InjOn (fun q : (V × V) × V => q.1)
      {q : (V × V) × V | q ∈ KUnits G ∧ s(q.1.1, q.2) = s(u,v)} := by
    rintro ⟨⟨x, z⟩, t⟩ ⟨-, h1⟩ ⟨⟨x', z'⟩, t'⟩ ⟨-, h2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : t = t' := Sym2.congr_right.mp (h1.trans h2.symm)
    rw [ht]
  rw [← Set.ncard_image_of_injOn hinj, KB]
  congr 1
  ext q
  obtain ⟨x, z⟩ := q
  constructor
  · rintro ⟨⟨⟨x0, z0⟩, t⟩, ⟨⟨hEwxz, hwit, hemp, hNw, hadj⟩, he⟩, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hxz : G.Adj x0 z0 := ((mem_Ew_iff G x0 z0).mp hEwxz).1
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, (mem_commonNeighbors G).mpr ⟨hxz, hadj.symm⟩,
        hEwxz, hwit, hemp⟩
    · exact ⟨Or.inr rfl, (mem_commonNeighbors G).mpr ⟨hadj.symm, hxz⟩,
        hEwxz, hwit, hemp⟩
  · rintro ⟨hx, hz, hEwxz, hwit, hemp⟩
    obtain ⟨hzu, hzv⟩ := (mem_commonNeighbors G).mp hz
    rcases hx with rfl | rfl
    · exact ⟨((x, z), v), ⟨⟨hEwxz, hwit, hemp, hEw, hzv.symm⟩, rfl⟩, rfl⟩
    · refine ⟨((x, z), u), ⟨⟨hEwxz, hwit, hemp, ?_, hzu.symm⟩, ?_⟩, rfl⟩
      · show s(x, u) ∈ Ew G
        rw [Sym2.eq_swap]; exact hEw
      · show s(x, u) = s(u, x)
        exact Sym2.eq_swap

/-- **Row 12 — Identity 4.1 (re-indexing, three unit types).**
`Σ(F) = #R − #B − #K`, and pairwise: `#R = Σ_{Ew} R_c`, `#B = Σ_{Ew} B`,
`#K = Σ_{Ew} K_B`.
★ PROVED; no `sorry`.

This declaration is the AGGREGATE clause; the three *pairwise* clauses are
`row12_R_pairwise`, `row12_B_pairwise`, `row12_K_pairwise`, immediately below.

The per-edge bijections are `row12_fiber_R`, `row12_fiber_B`,
`row12_fiber_K` above, each in the fibrewise form `ncard_eq_sum_fiber_Ew`
consumes.  This declaration is the assembly: sum the three over `Ew(F)` and
match the summand against `Σ`'s own, which is `R_c − B − K_B` by definition of
`Slack_c` and `sigmaTerm`.

★ Note what the proof does **not** need: no hypothesis at all.  Identity 4.1 is
a re-indexing, valid for every graph — `E0(F) = ∅` is nowhere used, and neither
is criticality. -/
theorem row12_identity_4_1 (G : SimpleGraph V) :
    Sig G = ((RUnits G).ncard : ℤ) - ((BUnits G).ncard : ℤ)
              - ((KUnits G).ncard : ℤ) := by
  classical
  -- Each unit type fibres over `Ew(F)`; the three fibre maps are those above.
  have hR := ncard_eq_sum_fiber_Ew G (RUnits G) (fun p => s(p.1, p.2.2))
    (fun p hp => hp.2.1)
  have hB := ncard_eq_sum_fiber_Ew G (BUnits G) (fun q => q.2)
    (fun q hq => hq.2.1)
  have hK := ncard_eq_sum_fiber_Ew G (KUnits G) (fun q => s(q.1.1, q.2))
    (fun q hq => hq.2.2.2.1)
  -- Pointwise on an `Ew` edge, the three fibres are `R_c`, `B`, `K_B`.
  have hpt : ∀ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G),
      sigmaTermS G e
        = (({p : V × V × V | p ∈ RUnits G ∧ s(p.1, p.2.2) = e}.ncard : ℤ))
          - (({q : Sym2 V × Sym2 V | q ∈ BUnits G ∧ q.2 = e}.ncard : ℤ))
          - (({q : (V × V) × V | q ∈ KUnits G ∧ s(q.1.1, q.2) = e}.ncard : ℤ)) := by
    intro e he
    have heEw : e ∈ Ew G := (Finset.mem_filter.mp he).2
    clear he
    induction e using Sym2.ind with
    | _ u v =>
      rw [row12_fiber_R G heEw, row12_fiber_B G heEw, row12_fiber_K G heEw]
      show sigmaTerm G u v = _
      rw [sigmaTerm, Slackc]
  have hsum : ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), sigmaTermS G e
      = ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G),
          ((({p : V × V × V | p ∈ RUnits G ∧ s(p.1, p.2.2) = e}.ncard : ℤ))
            - (({q : Sym2 V × Sym2 V | q ∈ BUnits G ∧ q.2 = e}.ncard : ℤ))
            - (({q : (V × V) × V | q ∈ KUnits G ∧ s(q.1.1, q.2) = e}.ncard : ℤ))) :=
    Finset.sum_congr rfl hpt
  rw [Sig, hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hR, hB, hK]
  push_cast
  ring

/-! #### Row 12's three PAIRWISE clauses

`Σ(F) = #R − #B − #K` holds moreover pairwise, against the three per-pair
sums.  The three clauses below are the *proof* of the aggregate clause above
rather than content beyond it; they are stated separately because the paper
states them separately. -/

open scoped Classical in
/-- **`#R = Σ_{Ew} R_c`** — Identity 4.1's first pairwise clause. -/
theorem row12_R_pairwise (G : SimpleGraph V) :
    (RUnits G).ncard
      = ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), RcS G e := by
  classical
  rw [ncard_eq_sum_fiber_Ew G (RUnits G) (fun p => s(p.1, p.2.2))
    (fun p hp => hp.2.1)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have heEw : e ∈ Ew G := (Finset.mem_filter.mp he).2
  clear he
  induction e using Sym2.ind with
  | _ u v => exact row12_fiber_R G heEw

open scoped Classical in
/-- **`#B = Σ_{Ew} B`** — Identity 4.1's second pairwise clause. -/
theorem row12_B_pairwise (G : SimpleGraph V) :
    (BUnits G).ncard
      = ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), BcS G e := by
  classical
  rw [ncard_eq_sum_fiber_Ew G (BUnits G) (fun q => q.2) (fun q hq => hq.2.1)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have heEw : e ∈ Ew G := (Finset.mem_filter.mp he).2
  clear he
  induction e using Sym2.ind with
  | _ u v => exact row12_fiber_B G heEw

open scoped Classical in
/-- **`#K = Σ_{Ew} K_B`** — Identity 4.1's third pairwise clause. -/
theorem row12_K_pairwise (G : SimpleGraph V) :
    (KUnits G).ncard
      = ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ Ew G), KBS G e := by
  classical
  rw [ncard_eq_sum_fiber_Ew G (KUnits G) (fun q => s(q.1.1, q.2))
    (fun q hq => hq.2.2.2.1)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have heEw : e ∈ Ew G := (Finset.mem_filter.mp he).2
  clear he
  induction e using Sym2.ind with
  | _ u v => exact row12_fiber_K G heEw

/-- **Row 13 — the codegree INVARIANT.**
A column `(p,y,∗)` has `codeg(p,y) = 1`; a (T)-target `(t,y,x)` has
`codeg(t,y) ≥ 2`, hence lies in no column.
★ PROVED; no `sorry`.  This is the **first** of the invariant's two clauses;
the second — the (T)-target bound — is `row13_T_target_codeg_ge_two` below. -/
theorem row13_codeg_invariant (G : SimpleGraph V) {p y z : V}
    (h : p ∈ WitAt G y z) : codeg G p y = 1 := by
  obtain ⟨-, -, hcn⟩ := h
  rw [codeg, G.commonNeighbors_symm, hcn, Set.ncard_singleton]

/-- **Row 13, SECOND CLAUSE — the (T)-target bound `codeg(t,y) ≥ 2`.**
★ PROVED; no `sorry`.

A (T)-target is the triple `(t,y,x)` arising from a K-unit `((x,z),t)` whose
chosen witness is `y`, in the branch where the (T) test fires.  Every
ingredient of that description is already available here:

| the paper's phrase | Lean |
|---|---|
| `y = y(x,z) ∈ Wit_x(z)` (the chosen witness) | `hy : y ∈ WitAt G x z` |
| `t ∈ Nw(x)` (part of "κ is a K-unit") | `ht : t ∈ Nw G x` |
| `t ∈ N(z)` (part of "κ is a K-unit") | `htz : G.Adj z t` |
| (T) branch test `Wit({y,z}) = {x}` | `hT : Wit G y z = {x}` |
| conclusion `codeg(t,y) ≥ 2` | `2 ≤ codeg G t y` |

★ **The choice function `y(·,·)` is the one piece of `φ`-vocabulary involved,
and it is eliminated rather than guessed**: `hy` quantifies over *every*
`y ∈ Wit_x(z)`, so this statement covers the (T)-target of every admissible
choice function at once.  That is licensed by the paper's remark that no
property of the choice is used anywhere in the argument, and by the
choice-independence proposition (row 17); the paper's proof of this clause
indeed uses no property of `y` beyond `y ∈ Wit_x(z)`.

⚠ **Hypothesis accounting.**  A K-unit `((x,z),t)` carries four conditions:
`{x,z} ∈ Ew(F)`, `Wit_x(z) ≠ ∅`, `Wit_z(x) = ∅`, `t ∈ Nw(x) ∩ N(z)`.  Only
`t ∈ Nw(x) ∩ N(z)` and (via `hy`) `Wit_x(z) ≠ ∅` are consumed here — the
paper's proof consumes exactly these — so `{x,z} ∈ Ew(F)` and `Wit_z(x) = ∅`
are **deliberately omitted rather than carried unused**.  The lemma is
therefore *stronger* than the invariant clause and implies it for every K-unit.

★ **Why this clause matters.**  A (T)-target does NOT lie in any column, so any
lemma about columns must not be applied to it in isolation.  Concretely, (L3)'s
cross-kind sentence "Across kinds, all three land in a column `(p,y,∗)`, and
(L2) applies" is **FALSE as stated** for (T)-targets, precisely because of the
bound proved here. -/
theorem row13_T_target_codeg_ge_two (G : SimpleGraph V) {x z y t : V}
    (hy : y ∈ WitAt G x z) (ht : t ∈ Nw G x) (htz : G.Adj z t)
    (hT : Wit G y z = {x}) :
    2 ≤ codeg G t y := by
  -- `t ∈ Nw(x)` means `{x,t} ∈ Ew(F)`; in particular `xt ∈ E`.
  have hxt : G.Adj x t := ((mem_Ew_iff G x t).mp ht).1
  -- `t ≠ z` because `z ∉ N(z)`.
  have htz' : t ≠ z := (G.ne_of_adj htz).symm
  -- (P2) (= row 11): `t ∈ N(x) ∖ {z}` lies outside `N[y]`.  Gives `ty ∉ E`.
  obtain ⟨hty, hnadj⟩ := row11_P2 G hy hxt htz'
  -- `z ∈ N(t) ∩ N(y)`.
  have hyz : G.Adj y z := by
    obtain ⟨-, -, hcn⟩ := hy
    have hmem : z ∈ G.commonNeighbors x y := by rw [hcn]; exact rfl
    exact ((mem_commonNeighbors G).mp hmem).2
  have hz : z ∈ G.commonNeighbors t y := (mem_commonNeighbors G).mpr ⟨htz.symm, hyz⟩
  -- Suppose `codeg(t,y) ≤ 1`.  It is `≥ 1` by `hz`, hence `= 1`, hence `= {z}`.
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hpos : 0 < codeg G t y :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨z, hz⟩
  have h1 : (G.commonNeighbors t y).ncard = 1 := by
    rw [codeg] at hpos hcon; omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
  have hsingle : G.commonNeighbors t y = {z} := by
    rw [ha] at hz ⊢
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
  -- Then `t` witnesses `{y,z}` at `y`, so `t ∈ Wit({y,z}) = {x}`, so `t = x`.
  have hwit : t ∈ WitAt G y z :=
    ⟨hty, fun h => hnadj h.symm, by rw [G.commonNeighbors_symm]; exact hsingle⟩
  have hmemW : t ∈ Wit G y z := Or.inl hwit
  rw [hT, Set.mem_singleton_iff] at hmemW
  -- But `t ∈ Nw(x) ⊆ N(x)` and `x ∉ N(x)`.
  exact G.irrefl (hmemW ▸ hxt)

/-- **Row 14 — (L1)–(L3): column contents and injectivity.**
(L1) is stated here: the R-units in the column `(p,y,∗)` are exactly
`(p,y,s)` for `s ∈ Nw(p) ∖ {z}`.
★★ **PROVED**; no `sorry`.

⚠ **This declaration carries only the first of (L1)'s two clauses.**  (L1)
reads:

1. "The R-units in the column `(p,y,∗)` are exactly the `(p,y,s)` for
   `s ∈ Nw(p) ∖ {z}`" — the membership characterisation.  Its proof is (P2)
   in one direction and `z ∈ N(y)` in the other.  **No `E0`-freeness.**
2. "And `z ∈ Nw(p)` always … **so the column has exactly `dw(p) − 1` slots**"
   — the slot COUNT.  This is where `E0` enters: the count fails directly
   without `E0`-freeness, already on the path `P3` (graph6 `BW`), where
   `{0,2}` is an `E0` edge, so `z ∉ Nw(p)` and the count is wrong.

Only clause 1 is stated here.  `hE0` is carried into the statement anyway but
is **never used** — machine-confirmed: the proof below closes without
mentioning `hE0`, and the linter reports it as an unused variable.  It is not
dropped, because the statement is a frozen transcription and a consumer may be
written against this signature.  Clause 2 is `row14_L1_slot_count`,
immediately below, where `hE0` *is* load-bearing. -/
theorem row14_L1_column_contents (G : SimpleGraph V) (hE0 : E0 G = ∅)
    {p y z : V} (h : p ∈ WitAt G y z) (t : V) :
    (p, y, t) ∈ RUnits G ↔ (t ∈ Nw G p ∧ t ≠ z) := by
  -- `p ∈ Wit_y(z)` gives, by Proposition 2.1 (row 1), `y ∈ Wit_p(z)`:
  -- `y ≠ p`, `py ∉ E`, `N(p) ∩ N(y) = {z}`.
  obtain ⟨hyp, hpy, hcn⟩ : y ∈ WitAt G p z := (isWitAt_symm G y z p).mp h
  -- `z ∈ N(p) ∩ N(y)`; in particular `zy ∈ E`, which is the `←` direction's
  -- other half and the `→` direction's whole content.
  have hzmem : z ∈ G.commonNeighbors p y := by rw [hcn]; rfl
  obtain ⟨hpz, hyz⟩ := (mem_commonNeighbors G).mp hzmem
  constructor
  · -- `→`.  An R-unit `(p,y,t)` has `t ∈ Nw(p)` outright; `t ≠ z` because
    -- `t ∉ N[y]` while `z ∈ N(y)`.
    rintro ⟨-, hNw, htny, htnadj⟩
    refine ⟨hNw, ?_⟩
    rintro rfl
    exact htnadj hyz.symm
  · -- `←`.  Given `t ∈ Nw(p)`, `t ≠ z`: the `D2` clause is `{p,y} ∈ A(F)`,
    -- witnessed by `hyp`, `hpy` and the nonempty `N(p) ∩ N(y) = {z}`; and
    -- `t ∉ N[y]` is exactly (P2) = row 11 applied to `y ∈ Wit_p(z)`.
    rintro ⟨hNw, htz⟩
    have hpt : G.Adj p t := ((mem_Ew_iff G p t).mp hNw).1
    obtain ⟨htny, htnadj⟩ := row11_P2 G (show y ∈ WitAt G p z from ⟨hyp, hpy, hcn⟩) hpt htz
    refine ⟨?_, hNw, htny, htnadj⟩
    rw [D2set, Set.mem_setOf_eq, mem_Anon_iff]
    exact ⟨fun hc => hyp hc.symm, hpy, ⟨z, hzmem⟩⟩

/-- **Row 14, SECOND CLAUSE — (L1)'s SLOT COUNT.**
★ **PROVED**; no `sorry`.

The clause `row14_L1_column_contents` omits: `z ∈ Nw(p)` always — the edge
`{p,z}` is witnessed at `p` by `y` (Proposition 2.1) and has codegree `≥ 1` by
`E0`-freeness — **so the column `(p,y,∗)` has exactly `dw(p) − 1` slots.**

★ **`hE0` is load-bearing here and only here in row 14.**  Without it the count
is false already on the path `P3` (graph6 `BW`), where the column `(0,1,∗)` has
unique common neighbour `2` but `{0,2}` is an `E0` edge, so `z ∉ Nw(p)`.
Removing `hE0` from this statement therefore makes it FALSE — the contrast with
`row14_L1_column_contents`, where removing it changes nothing, is exactly the
difference between the two clauses.

The `= dw(p) − 1` clause is ℕ-subtraction, which is why `z ∈ Nw(p)` must be
part of the conclusion and not merely a step: without it the equation is
vacuously satisfiable in the wrong way. -/
theorem row14_L1_slot_count (G : SimpleGraph V) (hE0 : E0 G = ∅)
    {p y z : V} (h : p ∈ WitAt G y z) :
    z ∈ Nw G p ∧ {t | (p, y, t) ∈ RUnits G} = Nw G p \ {z} ∧
      {t | (p, y, t) ∈ RUnits G}.ncard = (Nw G p).ncard - 1 := by
  obtain ⟨hyp, hpy, hcn⟩ : y ∈ WitAt G p z := (isWitAt_symm G y z p).mp h
  have hzmem : z ∈ G.commonNeighbors p y := by rw [hcn]; rfl
  obtain ⟨hpz, hyz⟩ := (mem_commonNeighbors G).mp hzmem
  -- `z ∈ Nw(p)`: `{p,z}` is an edge, witnessed at `p` by `y`; `E0(F) = ∅`
  -- upgrades it to `Ew`.  ★ THE SINGLE USE OF `hE0` IN ROW 14.
  have hzNw : z ∈ Nw G p :=
    Ew_of_witnessed G hE0 hpz ⟨y, Or.inl ⟨hyp, hpy, hcn⟩⟩
  -- The column is `Nw(p) ∖ {z}`, by the first clause.
  have hset : {t | (p, y, t) ∈ RUnits G} = Nw G p \ {z} := by
    ext t
    rw [Set.mem_setOf_eq, row14_L1_column_contents G hE0 h t]
    simp [Set.mem_singleton_iff]
  refine ⟨hzNw, hset, ?_⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem hzNw]

/-! `row15_L4_private_free_slot` is stated further below rather than here: its
proof consumes `row16_lemma_A` and `row15_free_slot_of_column_pair`, both of
which are defined after this point. -/

/-- **Row 16 — LEMMA A.**
★ `E0(F) = ∅` is ESSENTIAL: without it there are 6,912 counterexamples among
the connected graphs on `n ≤ 8` vertices that have an `E0` edge.

★★ **PROVED**; no `sorry`.

The statement: let `F` be a graph with `E0(F) = ∅`, let `{p,v} ∈ Ew(F)`, and
let `z ∈ N(p) ∩ N(v)`.  Then `|Nw(p) ∖ N[z]| + |Nw(v) ∖ N[z]| ≥ 1`.

Every symbol in it — `E0`, `Ew`, `Nw`, `N[·]`, `N(·)` — is elementary
vocabulary.  `φ`, slots, columns, targets and the choice function appear
nowhere in the statement; they appear only in the *use* of the lemma, where
`Nw(p) ∖ N[z]` is read as "the free slots of the column `(p,y,∗)`".

★ **`hE0` is genuinely load-bearing here.**  The smallest counterexample
without it is the star `K_{1,3}` centred at `3` plus the edge `{0,2}` (graph6
`CV`, `n = 4`), where `Nw(0) = Nw(2) = {3}` and the conclusion fails at both
`Ew` edges with value 0.  It enters at exactly one point, step 3 of
`row16_lemma_A_step`, via `Ew_of_witnessed`. -/
theorem row16_lemma_A_step (G : SimpleGraph V) (hE0 : E0 G = ∅) {p v z u : V}
    (hu : u ∈ WitAt G p v) (hzp : G.Adj p z) (hzv : G.Adj v z) :
    u ∈ NwOut G v z := by
  obtain ⟨hup, hpu, hcn⟩ := hu
  -- Step 1: `v ∈ N(u)`, from `N(p) ∩ N(u) = {v}`.
  have hvmem : v ∈ G.commonNeighbors p u := by rw [hcn]; rfl
  have hvu : G.Adj v u := hvmem.2.symm
  -- Step 2: `u ∉ N[z]`.  First `u ≠ z`: `z ∈ N(p)` while `u ∉ N(p)`.
  have hune : u ≠ z := by rintro rfl; exact hpu hzp
  -- and `uz ∉ E`: else `z ∈ N(p) ∩ N(u) = {v}`, i.e. `z = v`, contradicting
  -- `z ∈ N(v)` by irreflexivity.
  have hunadj : ¬ G.Adj u z := by
    intro hadj
    have hzmem : z ∈ G.commonNeighbors p u := (mem_commonNeighbors G).mpr ⟨hzp, hadj⟩
    rw [hcn, Set.mem_singleton_iff] at hzmem
    rw [hzmem] at hzv
    exact G.irrefl hzv
  -- Step 3: `{u,v} ∈ Ew(F)`.  `u ∈ Wit_p(v)` gives `p ∈ Wit_u(v)` by
  -- Proposition 2.1 (row 1), so `{v,u}` is a witnessed edge; `E0(F) = ∅` then
  -- upgrades it to `Ew`.  ★ THIS IS THE SINGLE USE OF `hE0`.
  have hpwit : p ∈ WitAt G u v := (isWitAt_symm G p v u).mp ⟨hup, hpu, hcn⟩
  have hEw : s(v,u) ∈ Ew G := Ew_of_witnessed G hE0 hvu ⟨p, Or.inr hpwit⟩
  -- Step 4: hence `u ∈ Nw(v) ∖ N[z]`.
  exact ⟨hEw, hune, hunadj⟩

/-- **LEMMA A itself.**  `|Nw(p) ∖ N[z]| + |Nw(v) ∖ N[z]| ≥ 1` for an `Ew` edge
`{p,v}` and a common neighbour `z`, in an `E0`-free graph.

★ The paper argues by contradiction ("suppose `Nw(p) ⊆ N[z]` and
`Nw(v) ⊆ N[z]`") and then WLOGs on which endpoint carries the witness.  The
transcription is **direct and WLOG-free**: `row16_lemma_A_step` produces an
explicit member of `Nw(v) ∖ N[z]` from a witness at `p`, and the two branches
of `Wit(e) = Wit_p(v) ∪ Wit_v(p)` are discharged by the same lemma with `p` and
`v` (and `hzp`, `hzv`) exchanged.  The paper's "the hypothesis is symmetric in
`p` and `v`" is thereby machine-checked rather than asserted.

⚠ The hypothesis is `z ∈ N(p) ∩ N(v)`, given here as the pair `hzp`, `hzv`
rather than as `z ∈ G.commonNeighbors p v`; the two are definitionally the
same and the split form is what every call site has to hand. -/
theorem row16_lemma_A (G : SimpleGraph V) (hE0 : E0 G = ∅) {p v z : V}
    (h : s(p,v) ∈ Ew G) (hzp : G.Adj p z) (hzv : G.Adj v z) :
    1 ≤ (NwOut G p z).ncard + (NwOut G v z).ncard := by
  obtain ⟨-, -, u, hu⟩ := (mem_Ew_iff G p v).mp h
  rcases (show u ∈ WitAt G p v ∨ u ∈ WitAt G v p from hu) with hu | hu
  · have hmem := row16_lemma_A_step G hE0 hu hzp hzv
    have hpos : 0 < (NwOut G v z).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, hmem⟩
    omega
  · have hmem := row16_lemma_A_step G hE0 hu hzv hzp
    have hpos : 0 < (NwOut G p z).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, hmem⟩
    omega

/-! #### What LEMMA A buys, in column language

★★ **THIS IS THE JOIN BETWEEN ROW 14 AND ROW 16, AND IT IS `φ`-FREE.**  It is
the piece row 15 consumes, and the reason the two rows above were worth proving
before attempting `φ`.

The paper bounds the free slots of a 2-witness B-unit's column pair by six
steps.  Steps 1, 2 and 5 are statements *about `φ`-targets* and cannot be
transcribed before `φ` exists.  Steps 3, 4 and 6 are not: they say that after
discarding every slot that could *possibly* carry a (D)-target, what remains in
the column `(p,y,∗)` is exactly `Nw(p) ∖ N[z]`, and that LEMMA A makes the pair
of these non-empty.

★ **A design decision worth recording.**  The paper's step 3 bounds the
(D)-targets in a column by `|Nw(p) ∩ N(z)|` *and then subtracts*.  Formalising
that literally would require `φ` (to know which targets are (D)-targets) and
then a cardinality subtraction.  **We instead discard the whole possible-(D)
region setwise, before `φ` is defined** — an over-approximation, hence a weaker
free-slot set, and yet still non-empty by LEMMA A.  The arithmetic of steps 3–4
(`|Nw(p) ∖ {z}| − |Nw(p) ∩ N(z)| = |Nw(p) ∖ N[z]|`) becomes the *set identity*
`row15_free_slots_eq`, with no subtraction and no `φ`.  That is why `NwOut` was
defined with `RUnits`' own `∉ N[·]` convention rather than as a difference of
`Finset`s. -/

/-- The slots of the column `(p,y,∗)` that no (D)-target could occupy are
exactly `Nw(p) ∖ N[z]`.  ★ PROVED; no `sorry`.

Left-hand side: an R-unit in the column `(p,y,∗)` whose third coordinate is not
adjacent to the hub `z` — the paper's step 3, "the (D)-targets in the column
`(p,y,∗)` are among the `φ(((p,z),s))` for `s ∈ Nw(p) ∩ N(z)`", discarded
setwise.  Right-hand side: LEMMA A's quantity verbatim. -/
theorem row15_free_slots_eq (G : SimpleGraph V) (hE0 : E0 G = ∅) {p y z : V}
    (h : p ∈ WitAt G y z) :
    {t | (p, y, t) ∈ RUnits G ∧ ¬ G.Adj t z} = NwOut G p z := by
  ext t
  rw [Set.mem_setOf_eq, row14_L1_column_contents G hE0 h t, NwOut, Set.mem_setOf_eq]
  tauto

/-- **Steps 3–4–6 combined: a 2-witness B-unit's column pair always has a
slot no (D)-target can occupy.**  ★ PROVED; no `sorry`.

Hypotheses are exactly the paper's: `p, v ∈ Wit_y(z)` (the two witnesses of
`e = {y,z}`, placed at the common endpoint `y` by (P4) = `row11_P4`), and
`{p,v} ∈ Ew` (the witness edge `f`, which is an `Ew` edge by the B-unit
definition).  The paper's "the common neighbour `z ∈ N(p) ∩ N(v)` — available
since `p, v ∈ Wit_y(z) ⊆ N(z)`" is discharged below rather than assumed.

⚠ **What this does NOT do.**  It does not show the slot is *unused*; that needs
steps 1, 2 and 5, all of which quantify over `φ`-targets and so must wait for
`φ`.  What it does show is that the slot survives the only step that could have
emptied the column pair on cardinality grounds — and that step is the one
carrying the `E0` hypothesis.  ★ Together with `row11_P3` (targets land in
`RUnits`) and `row14_L1_slot_count` (columns are `dw(p) − 1` deep), this is the
complete `φ`-free content of the construction. -/
theorem row15_free_slot_of_column_pair (G : SimpleGraph V) (hE0 : E0 G = ∅)
    {y z p v : V} (hp : p ∈ WitAt G y z) (hv : v ∈ WitAt G y z)
    (hpv : s(p,v) ∈ Ew G) :
    ∃ t, ((p, y, t) ∈ RUnits G ∨ (v, y, t) ∈ RUnits G) ∧ ¬ G.Adj t z := by
  -- `z ∈ N(p)` and `z ∈ N(v)`: both witnesses lie in `N(z)`, since `z` is the
  -- unique common neighbour of `y` with each of them.
  have hzp : G.Adj p z := by
    obtain ⟨-, -, hcn⟩ := hp
    have : z ∈ G.commonNeighbors y p := by rw [hcn]; rfl
    exact ((mem_commonNeighbors G).mp this).2
  have hzv : G.Adj v z := by
    obtain ⟨-, -, hcn⟩ := hv
    have : z ∈ G.commonNeighbors y v := by rw [hcn]; rfl
    exact ((mem_commonNeighbors G).mp this).2
  -- LEMMA A: the two free-slot sets are not both empty.
  have hA := row16_lemma_A G hE0 hpv hzp hzv
  -- Pick a member of whichever is non-empty, and read it back as a slot.
  rcases Nat.eq_zero_or_pos (NwOut G p z).ncard with h0 | hpos
  · have hpos' : 0 < (NwOut G v z).ncard := by omega
    obtain ⟨t, ht⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos'
    have ht' : t ∈ {t | (v, y, t) ∈ RUnits G ∧ ¬ G.Adj t z} := by
      rw [row15_free_slots_eq G hE0 hv]; exact ht
    exact ⟨t, Or.inr ht'.1, ht'.2⟩
  · obtain ⟨t, ht⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    have ht' : t ∈ {t | (p, y, t) ∈ RUnits G ∧ ¬ G.Adj t z} := by
      rw [row15_free_slots_eq G hE0 hp]; exact ht
    exact ⟨t, Or.inl ht'.1, ht'.2⟩

/-! #### ROW 15 — the construction of `φ`.

★ **Design.**  The paper's greedy "Order convention" is NOT formalized; the
paper explicitly licenses that.  Instead every unit is given an
**admissible-target SET** depending on that unit alone, and the whole of (L3)
together with the free-slot analysis is packaged as the single statement
"admissible sets of distinct units are disjoint".  One `Classical` choice per
unit then yields `φ`, with injectivity immediate.

★ **B-unit destructuring** is handled by `BUnit_split`: the orientation
`e = s(y,z)` with all of `Wit(e)` at `y` **is unique**, so nothing is chosen —
the paper's "say `Wit(e) = {x0}`, with `x0` witnessing at the endpoint `y`" is
a theorem here, not a convention.  Its proof is (P4) = `row11_P4`. -/

/-- A vertex never witnesses the same edge at BOTH endpoints. -/
theorem witAt_not_both (G : SimpleGraph V) {a b p : V}
    (h1 : p ∈ WitAt G a b) (h2 : p ∈ WitAt G b a) : False := by
  obtain ⟨-, -, hcn⟩ := h1
  obtain ⟨-, hnb, -⟩ := h2
  have hb : b ∈ G.commonNeighbors a p := by rw [hcn]; rfl
  exact hnb ((mem_commonNeighbors G).mp hb).2.symm

/-- **(P1) read as a RECOVERY**: the hub `z` of a column `(p,y,∗)` is
determined by `p` and `y`. -/
theorem witAt_hub_unique (G : SimpleGraph V) {y p z z' : V}
    (h : p ∈ WitAt G y z) (h' : p ∈ WitAt G y z') : z = z' := by
  obtain ⟨-, -, hcn⟩ := h
  obtain ⟨-, -, hcn'⟩ := h'
  rw [hcn] at hcn'
  simpa using hcn'

/-- If nothing witnesses `{y,z}` at `z`, then `Wit({y,z}) = Wit_y(z)`. -/
theorem wit_eq_witAt (G : SimpleGraph V) {y z : V} (h : WitAt G z y = ∅) :
    Wit G y z = WitAt G y z := by
  rw [Wit, h, Set.union_empty]

/-- A singleton is never a two-element pair. -/
theorem pair_ne_singleton {a p v : V} (hpv : p ≠ v)
    (h : ({a} : Set V) = {p, v}) : False := by
  have h1 : p ∈ ({a} : Set V) := by rw [h]; simp
  have h2 : v ∈ ({a} : Set V) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h1 h2
  exact hpv (h1.trans h2.symm)

/-- Equal two-element sets give equal `Sym2` pairs.  (Needed because the
witness edge `f` is recovered as a SET and must be compared as a `Sym2`.) -/
theorem sym2_eq_of_pair_eq {p v p' v' : V} (hpv : p ≠ v)
    (h : ({p, v} : Set V) = {p', v'}) : s(p,v) = s(p',v') := by
  have hp : p = p' ∨ p = v' := by
    have hmem : p ∈ ({p, v} : Set V) := by simp
    rw [h] at hmem
    simpa using hmem
  have hv : v = p' ∨ v = v' := by
    have hmem : v ∈ ({p, v} : Set V) := by simp
    rw [h] at hmem
    simpa using hmem
  rcases hp with hp | hp <;> rcases hv with hv | hv
  · exact absurd (hp.trans hv.symm) hpv
  · rw [hp, hv]
  · rw [hp, hv, Sym2.eq_swap]
  · exact absurd (hp.trans hv.symm) hpv

/-- **B-unit destructuring.**  For a B-unit `(e,f)` there is an orientation
`e = s(y,z)` carrying **all** of `Wit(e)` at `y`, and none at `z`.
The paper states this in prose for the 1- and 2-witness cases separately; the
proof of both is (P4).  ★ The orientation is *unique* (`WitAt G z y = ∅` fails
for the swap), so no choice is made here. -/
theorem BUnit_split (G : SimpleGraph V) {q : Sym2 V × Sym2 V}
    (hq : q ∈ BUnits G) :
    ∃ y z : V, q.1 = s(y,z) ∧ WitAt G z y = ∅ ∧ (WitAt G y z).Nonempty := by
  obtain ⟨h1, h2, -, hsub⟩ := hq
  obtain ⟨u, v, hev, -, -, hwne⟩ := h1
  by_cases hu : (WitAt G u v).Nonempty
  · refine ⟨u, v, hev, ?_, hu⟩
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    obtain ⟨p, hp⟩ := hu
    have hpw : p ≠ w := by rintro rfl; exact witAt_not_both G hp hw
    have hpq2 : p ∈ q.2 := hsub u v hev (Or.inl hp)
    have hwq2 : w ∈ q.2 := hsub u v hev (Or.inr hw)
    obtain ⟨c, d, hcd, hadj, -, -⟩ := h2
    rw [hcd, Sym2.mem_iff] at hpq2 hwq2
    have hadjpw : G.Adj p w := by
      rcases hpq2 with hp1 | hp1 <;> rcases hwq2 with hw1 | hw1
      · exact absurd (hp1.trans hw1.symm) hpw
      · rw [hp1, hw1]; exact hadj
      · rw [hp1, hw1]; exact hadj.symm
      · exact absurd (hp1.trans hw1.symm) hpw
    have hwv : w ≠ v := hw.1
    exact hwv (row11_P4 G hp hw hadjpw)
  · rw [Set.not_nonempty_iff_eq_empty] at hu
    have hv : (WitAt G v u).Nonempty := by
      obtain ⟨w, hw⟩ := hwne
      rcases hw with h | h
      · rw [hu] at h; exact h.elim
      · exact ⟨w, h⟩
    exact ⟨v, u, by rw [hev, Sym2.eq_swap], hu, hv⟩

/-- **The admissible targets of a B-unit** — the two B-branches of the
construction, taken as a SET rather than as a value.

With `e = s(y,z)` the unique orientation of `BUnit_split`:

* **1-witness** (`Wit(e) = {x0}`, `f = {x0,s}`): the single target `(x0,y,s)`;
* **2-witness** (`Wit(e) = f = {p,v}`): **any** R-unit in the column pair
  `(p,y,∗) ∪ (v,y,∗)` whose third coordinate is not adjacent to the hub `z` —
  i.e. any slot of the over-approximated free-slot set `NwOut`.  ★ The paper's
  "not already used" is replaced by "provably unusable by any stage-1 target";
  that substitution is what removes the ordering, and it is discharged by
  `BAdm_KTarget_ne` and `BAdm_inj` below. -/
def BAdm (G : SimpleGraph V) (q : Sym2 V × Sym2 V) : Set (V × V × V) :=
  {r | r ∈ RUnits G ∧ ∃ y z : V, q.1 = s(y,z) ∧ WitAt G z y = ∅ ∧ r.2.1 = y ∧
        ((Wit G y z = {r.1} ∧ q.2 = s(r.1, r.2.2)) ∨
         (∃ p v : V, p ≠ v ∧ Wit G y z = {p, v} ∧ q.2 = s(p,v) ∧
            (r.1 = p ∨ r.1 = v) ∧ ¬ G.Adj r.2.2 z))}

/-- Every admissible B-target lies in a **genuine column**: its first
coordinate witnesses `{y,z}` at `y`.  (The codegree invariant, B-side.) -/
theorem BAdm_col (G : SimpleGraph V) {y z : V} {r : V × V × V} {q2 : Sym2 V}
    (hzy : WitAt G z y = ∅)
    (hcase : (Wit G y z = {r.1} ∧ q2 = s(r.1, r.2.2)) ∨
      (∃ p v : V, p ≠ v ∧ Wit G y z = {p, v} ∧ q2 = s(p,v) ∧
         (r.1 = p ∨ r.1 = v) ∧ ¬ G.Adj r.2.2 z)) : r.1 ∈ WitAt G y z := by
  rw [← wit_eq_witAt G hzy]
  rcases hcase with ⟨hs, -⟩ | ⟨p, v, -, hs, -, hpv, -⟩
  · rw [hs]; simp
  · rw [hs]; rcases hpv with h | h <;> simp [h]

/-- **`BAdm` is never empty on a B-unit** — the first B-branch is a value, and
the second is (L4), i.e. `row15_free_slot_of_column_pair`.
★ Consumes `E0(F) = ∅` (through (L1)'s slot count and LEMMA A). -/
theorem BAdm_nonempty (G : SimpleGraph V) (hE0 : E0 G = ∅)
    {q : Sym2 V × Sym2 V} (hq : q ∈ BUnits G) : (BAdm G q).Nonempty := by
  obtain ⟨y, z, hq1, hzy, hyne⟩ := BUnit_split G hq
  obtain ⟨-, h2, hdisj, hsub⟩ := hq
  have hWit : Wit G y z = WitAt G y z := wit_eq_witAt G hzy
  have hsub' : Wit G y z ⊆ {w | w ∈ q.2} := hsub y z hq1
  obtain ⟨c, d, hcd, hadjcd, -, -⟩ := id h2
  have hcdne : c ≠ d := hadjcd.ne
  have hmem2 : ∀ w : V, w ∈ q.2 ↔ (w = c ∨ w = d) := by
    intro w; rw [hcd, Sym2.mem_iff]
  have hzq1 : z ∈ q.1 := by rw [hq1, Sym2.mem_iff]; right; rfl
  by_cases hc : c ∈ Wit G y z
  · by_cases hd : d ∈ Wit G y z
    · -- 2-witness B-unit: `Wit(e) = {c,d} = f`.
      have hSet : Wit G y z = {c, d} := by
        apply Set.eq_of_subset_of_subset
        · intro w hw
          have := (hmem2 w).mp (hsub' hw)
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        · intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl
          · exact hc
          · exact hd
      rw [hWit] at hc hd
      have hEwcd : s(c,d) ∈ Ew G := by rw [← hcd]; exact h2
      obtain ⟨t, htR, htz⟩ := row15_free_slot_of_column_pair G hE0 hc hd hEwcd
      rcases htR with hR | hR
      · exact ⟨(c, y, t), hR, y, z, hq1, hzy, rfl,
          Or.inr ⟨c, d, hcdne, hSet, hcd, Or.inl rfl, htz⟩⟩
      · exact ⟨(d, y, t), hR, y, z, hq1, hzy, rfl,
          Or.inr ⟨c, d, hcdne, hSet, hcd, Or.inr rfl, htz⟩⟩
    · -- 1-witness B-unit, `Wit(e) = {c}`, `f = {c,d}`; target `(c,y,d)`.
      have hSet : Wit G y z = {c} := by
        apply Set.eq_of_subset_of_subset
        · intro w hw
          rcases (hmem2 w).mp (hsub' hw) with h | h
          · exact h
          · exact absurd (h ▸ hw) hd
        · intro w hw
          simp only [Set.mem_singleton_iff] at hw
          rw [hw]; exact hc
      rw [hWit] at hc
      have hdNw : d ∈ Nw G c := by show s(c,d) ∈ Ew G; rw [← hcd]; exact h2
      have hdz : d ≠ z := by
        intro hdz'
        refine hdisj z hzq1 ?_
        rw [hcd, Sym2.mem_iff]; right; exact hdz'.symm
      have hR : (c, y, d) ∈ RUnits G :=
        (row14_L1_column_contents G hE0 hc d).mpr ⟨hdNw, hdz⟩
      exact ⟨(c, y, d), hR, y, z, hq1, hzy, rfl, Or.inl ⟨hSet, hcd⟩⟩
  · by_cases hd : d ∈ Wit G y z
    · -- 1-witness B-unit, `Wit(e) = {d}`, `f = {d,c}`; target `(d,y,c)`.
      have hSet : Wit G y z = {d} := by
        apply Set.eq_of_subset_of_subset
        · intro w hw
          rcases (hmem2 w).mp (hsub' hw) with h | h
          · exact absurd (h ▸ hw) hc
          · exact h
        · intro w hw
          simp only [Set.mem_singleton_iff] at hw
          rw [hw]; exact hd
      rw [hWit] at hd
      have hcNw : c ∈ Nw G d := by
        show s(d,c) ∈ Ew G; rw [Sym2.eq_swap, ← hcd]; exact h2
      have hcz : c ≠ z := by
        intro hcz'
        refine hdisj z hzq1 ?_
        rw [hcd, Sym2.mem_iff]; left; exact hcz'.symm
      have hR : (d, y, c) ∈ RUnits G :=
        (row14_L1_column_contents G hE0 hd c).mpr ⟨hcNw, hcz⟩
      refine ⟨(d, y, c), hR, y, z, hq1, hzy, rfl, Or.inl ⟨hSet, ?_⟩⟩
      rw [hcd, Sym2.eq_swap]
    · exfalso
      obtain ⟨w, hw⟩ := hyne
      rw [← hWit] at hw
      rcases (hmem2 w).mp (hsub' hw) with h | h
      · exact hc (h ▸ hw)
      · exact hd (h ▸ hw)

/-! ##### The K-branch: the choice function and the (T)/(D) test -/

open scoped Classical in
/-- The choice function `y(x,z)` of the paper's **Choice convention**.
⚠ `choose!` is unusable here (the codomain is not known inhabited), so the junk
branch returns `x`; **only property (α)** — `witChoice_mem` — is ever used,
which is the choice-independence proposition (row 17) in force. -/
noncomputable def witChoice (G : SimpleGraph V) (x z : V) : V :=
  if h : (WitAt G x z).Nonempty then h.choose else x

/-- Property **(α)**: `y(x,z) ∈ Wit_x(z)`. -/
theorem witChoice_mem (G : SimpleGraph V) {x z : V}
    (h : (WitAt G x z).Nonempty) : witChoice G x z ∈ WitAt G x z := by
  classical
  have hval : witChoice G x z = h.choose := by
    simp only [witChoice]; exact dif_pos h
  rw [hval]; exact h.choose_spec

open scoped Classical in
/-- The K-branch of the construction: the **(T)/(D) test**, evaluated at the
chosen witness — property **(β)**, the step whose mis-statement makes (L2.2)
false. -/
noncomputable def KTarget (G : SimpleGraph V) (κ : (V × V) × V) : V × V × V :=
  if Wit G (witChoice G κ.1.1 κ.1.2) κ.1.2 = {κ.1.1}
  then (κ.2, witChoice G κ.1.1 κ.1.2, κ.1.1)
  else (κ.1.1, witChoice G κ.1.1 κ.1.2, κ.2)

theorem KTarget_T (G : SimpleGraph V) {x z t : V}
    (hT : Wit G (witChoice G x z) z = {x}) :
    KTarget G ((x, z), t) = (t, witChoice G x z, x) := by
  classical
  simp only [KTarget]
  exact if_pos hT

theorem KTarget_D (G : SimpleGraph V) {x z t : V}
    (hT : ¬ Wit G (witChoice G x z) z = {x}) :
    KTarget G ((x, z), t) = (x, witChoice G x z, t) := by
  classical
  simp only [KTarget]
  exact if_neg hT

/-- Both targets are R-units, by (P3). -/
theorem KTarget_mem_RUnits (G : SimpleGraph V) {κ : (V × V) × V}
    (hκ : κ ∈ KUnits G) : KTarget G κ ∈ RUnits G := by
  obtain ⟨⟨x, z⟩, t⟩ := κ
  -- ⚠ Given with EXPLICIT types: `obtain` leaves `((x,z),t).1.1` unreduced, and
  -- `omega`/`rw` then treat it as a different atom from `x`.
  have hne : (WitAt G x z).Nonempty := hκ.2.1
  have htNw : t ∈ Nw G x := hκ.2.2.2.1
  have hzt : G.Adj z t := hκ.2.2.2.2
  have hy := witChoice_mem G hne
  obtain ⟨hD, hT⟩ := row11_P3 G hy htNw hzt
  by_cases h : Wit G (witChoice G x z) z = {x}
  · rw [KTarget_T G h]; exact hT
  · rw [KTarget_D G h]; exact hD

/-- **(L3), same-kind, K-side.**  The three sub-cases are (T)/(T) and (D)/(D),
both pure recovery via (P1), and (T)/(D), which is the codegree invariant
(`row13_codeg_invariant` = 1 against `row13_T_target_codeg_ge_two` ≥ 2). -/
theorem KTarget_inj (G : SimpleGraph V) {κ κ' : (V × V) × V}
    (hκ : κ ∈ KUnits G) (hκ' : κ' ∈ KUnits G)
    (h : KTarget G κ = KTarget G κ') : κ = κ' := by
  obtain ⟨⟨x, z⟩, t⟩ := κ
  obtain ⟨⟨x', z'⟩, t'⟩ := κ'
  have hne : (WitAt G x z).Nonempty := hκ.2.1
  have htNw : t ∈ Nw G x := hκ.2.2.2.1
  have hzt : G.Adj z t := hκ.2.2.2.2
  have hne' : (WitAt G x' z').Nonempty := hκ'.2.1
  have htNw' : t' ∈ Nw G x' := hκ'.2.2.2.1
  have hzt' : G.Adj z' t' := hκ'.2.2.2.2
  have hy := witChoice_mem G hne
  have hy' := witChoice_mem G hne'
  by_cases hT : Wit G (witChoice G x z) z = {x}
  · by_cases hT' : Wit G (witChoice G x' z') z' = {x'}
    · rw [KTarget_T G hT, KTarget_T G hT'] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h3
      rw [← h2] at hy'
      have hzz : z = z' := witAt_hub_unique G hy hy'
      subst hzz; rw [h1]
    · exfalso
      rw [KTarget_T G hT, KTarget_D G hT'] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hge := row13_T_target_codeg_ge_two G hy htNw hzt hT
      have hx' : x' ∈ WitAt G (witChoice G x' z') z' :=
        (row01_witness_symmetry G x' z' (witChoice G x' z')).mp hy'
      have h1eq := row13_codeg_invariant G hx'
      rw [h1, h2] at hge
      omega
  · by_cases hT' : Wit G (witChoice G x' z') z' = {x'}
    · exfalso
      rw [KTarget_D G hT, KTarget_T G hT'] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hge := row13_T_target_codeg_ge_two G hy' htNw' hzt' hT'
      have hx : x ∈ WitAt G (witChoice G x z) z :=
        (row01_witness_symmetry G x z (witChoice G x z)).mp hy
      have h1eq := row13_codeg_invariant G hx
      -- ⚠ `h2` FIRST: `h1 : x = t'` would otherwise also rewrite the `x`
      -- inside `witChoice G x z`.
      rw [h2, h1] at h1eq
      omega
    · rw [KTarget_D G hT, KTarget_D G hT'] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1
      rw [← h2] at hy'
      have hzz : z = z' := witAt_hub_unique G hy hy'
      subst hzz; rw [h3]

/-- **(L3) across kinds** — no admissible B-target is a K-target.

* (T)-side: the codegree invariant.  A B-target lies in a genuine column, so
  `codeg(c1,c2) = 1`; a (T)-target has `codeg ≥ 2`.
* (D)-side, 1-witness B: (L2.1) against (L2.2) — the column's hub is forced
  equal to the K-unit's, and then `Wit({y,z}) = {x}` contradicts the (D)
  branch condition.
* (D)-side, 2-witness B: ★ the step that removes the ordering.  A (D)-target's
  third coordinate is adjacent to the hub `z`; every admissible 2-witness
  target's is not.  A **set inclusion**, not a count — the subtraction
  `|Nw(p) ∖ {z}| − |Nw(p) ∩ N(z)|` never has to be performed. -/
theorem BAdm_KTarget_ne (G : SimpleGraph V) {q : Sym2 V × Sym2 V}
    {κ : (V × V) × V} {r : V × V × V} (hr : r ∈ BAdm G q)
    (hκ : κ ∈ KUnits G) : r ≠ KTarget G κ := by
  obtain ⟨⟨x, z2⟩, t⟩ := κ
  have hne : (WitAt G x z2).Nonempty := hκ.2.1
  have htNw : t ∈ Nw G x := hκ.2.2.2.1
  have hzt : G.Adj z2 t := hκ.2.2.2.2
  have hy2 := witChoice_mem G hne
  obtain ⟨-, y, z, hq1, hzy, hry, hcase⟩ := hr
  have hcol : r.1 ∈ WitAt G y z := BAdm_col G hzy hcase
  intro heq
  by_cases hT : Wit G (witChoice G x z2) z2 = {x}
  · rw [KTarget_T G hT] at heq
    have h1 : r.1 = t := by rw [heq]
    have h2 : r.2.1 = witChoice G x z2 := by rw [heq]
    have hyw : y = witChoice G x z2 := hry.symm.trans h2
    have hge := row13_T_target_codeg_ge_two G hy2 htNw hzt hT
    have h1eq := row13_codeg_invariant G hcol
    rw [h1, hyw] at h1eq
    omega
  · rw [KTarget_D G hT] at heq
    have h1 : r.1 = x := by rw [heq]
    have h2 : r.2.1 = witChoice G x z2 := by rw [heq]
    have h3 : r.2.2 = t := by rw [heq]
    have hyw : y = witChoice G x z2 := hry.symm.trans h2
    have hx : x ∈ WitAt G (witChoice G x z2) z2 :=
      (row01_witness_symmetry G x z2 (witChoice G x z2)).mp hy2
    rw [h1] at hcol
    rw [← hyw] at hx
    have hzz : z = z2 := witAt_hub_unique G hcol hx
    rcases hcase with ⟨hs, -⟩ | ⟨p, v, -, -, -, -, hnadj⟩
    · rw [h1, hzz, hyw] at hs
      exact hT hs
    · rw [h3, hzz] at hnadj
      exact hnadj hzt.symm

/-- **(L3) same-kind on 1-witness B-units** — an admissible B-target determines
its B-unit.

In the paper: a B1-target `(x0,y,s)` determines its unit, since `z` is the
unique common neighbour of `x0` and `y`, then `e = {y,z}` and `f = {x0,s}`; and
a shared column `(p,y,∗)` determines `z = cn(p,y)`, hence `e = {y,z}`, hence
`f = Wit(e)` — the same unit.
★ Both recoveries are the SAME two lines here, because `BAdm` records the
column data explicitly; and the 1-vs-2-witness cross case is `pair_ne_singleton`
(the paper's `|Wit({y,z})| = 2`). -/
theorem BAdm_inj (G : SimpleGraph V) {q q' : Sym2 V × Sym2 V} {r : V × V × V}
    (hr : r ∈ BAdm G q) (hr' : r ∈ BAdm G q') : q = q' := by
  obtain ⟨-, y, z, hq1, hzy, hry, hcase⟩ := hr
  obtain ⟨-, y', z', hq1', hzy', hry', hcase'⟩ := hr'
  have hyy : y = y' := hry.symm.trans hry'
  subst hyy
  have hw : r.1 ∈ WitAt G y z := BAdm_col G hzy hcase
  have hw' : r.1 ∈ WitAt G y z' := BAdm_col G hzy' hcase'
  have hzz : z = z' := witAt_hub_unique G hw hw'
  subst hzz
  have hfst : q.1 = q'.1 := by rw [hq1, hq1']
  have hsnd : q.2 = q'.2 := by
    rcases hcase with ⟨hs, hf⟩ | ⟨p, v, hpv, hs, hf, -, -⟩
    · rcases hcase' with ⟨-, hf'⟩ | ⟨p', v', hpv', hs', -, -, -⟩
      · rw [hf, hf']
      · exact absurd (hs.symm.trans hs') (fun hh => pair_ne_singleton hpv' hh)
    · rcases hcase' with ⟨hs', -⟩ | ⟨p', v', hpv', hs', hf', -, -⟩
      · exact absurd (hs'.symm.trans hs) (fun hh => pair_ne_singleton hpv hh)
      · rw [hf, hf']
        exact sym2_eq_of_pair_eq hpv (hs.symm.trans hs')
  exact Prod.ext hfst hsnd

/-- **Row 15 — (L4): every 2-witness B-unit has a private free slot.**
Stated as its consumable consequence: the injection `φ` from
`B-units ⊔ K-units` into R-units exists.

★★ **PROVED**; no `sorry`.

The construction is the "admissible set" form described above:
`BAdm`/`KTarget` are the per-unit target sets, `BAdm_nonempty` and
`KTarget_mem_RUnits` are well-definedness, and `BAdm_inj`, `KTarget_inj`,
`BAdm_KTarget_ne` are (L3) together with the free-slot analysis.
★ The `∀ q, ∃ r, q ∈ BUnits G → …` shape and the `Sym2.ind` junk value are the
established workaround for `choose!` (`V × V × V` is not known inhabited). -/
theorem row15_L4_private_free_slot (G : SimpleGraph V) (hE0 : E0 G = ∅) :
    ∃ φ : (Sym2 V × Sym2 V) ⊕ ((V × V) × V) → V × V × V,
      Set.InjOn φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) ∧
      Set.MapsTo φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) (RUnits G) := by
  classical
  have keyB : ∀ q : Sym2 V × Sym2 V, ∃ r : V × V × V,
      q ∈ BUnits G → r ∈ BAdm G q := by
    rintro ⟨e, f⟩
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hq : ((s(a,b), f) : Sym2 V × Sym2 V) ∈ BUnits G
      · obtain ⟨r, hr⟩ := BAdm_nonempty G hE0 hq
        exact ⟨r, fun _ => hr⟩
      · exact ⟨(a, a, a), fun h => absurd h hq⟩
  choose φB hφB using keyB
  refine ⟨Sum.elim φB (KTarget G), ?_, ?_⟩
  · rintro u hu u' hu' heq
    rcases hu with ⟨q, hqB, rfl⟩ | ⟨κ, hκK, rfl⟩
    · rcases hu' with ⟨q', hqB', rfl⟩ | ⟨κ', hκK', rfl⟩
      · simp only [Sum.elim_inl] at heq
        have hmem : φB q ∈ BAdm G q' := by rw [heq]; exact hφB q' hqB'
        rw [BAdm_inj G (hφB q hqB) hmem]
      · simp only [Sum.elim_inl, Sum.elim_inr] at heq
        exact absurd heq (BAdm_KTarget_ne G (hφB q hqB) hκK')
    · rcases hu' with ⟨q', hqB', rfl⟩ | ⟨κ', hκK', rfl⟩
      · simp only [Sum.elim_inl, Sum.elim_inr] at heq
        exact absurd heq.symm (BAdm_KTarget_ne G (hφB q' hqB') hκK)
      · simp only [Sum.elim_inr] at heq
        rw [KTarget_inj G hκK hκK' heq]
  · rintro u (⟨q, hqB, rfl⟩ | ⟨κ, hκK, rfl⟩)
    · exact (hφB q hqB).1
    · exact KTarget_mem_RUnits G hκK

/-- **Row 17 — the choice-independence proposition.**
Content: nothing in the construction of `φ` depends on *which* witness
`y(x,z) ∈ Wit_x(z)` is chosen, so `φ` may be built from an arbitrary choice
function.  Formalised as: the conclusion of row 15 holds for the `φ` built from
*any* choice function, so in particular the existence statement of row 15 is
choice-free.
(Once row 15 is stated as a bare `∃ φ`, choice-independence is absorbed into
it; this row therefore has no separate Lean content and is recorded, not
stated.) -/
theorem row17_choice_independence_absorbed (G : SimpleGraph V)
    (hE0 : E0 G = ∅) :
    (∃ φ : (Sym2 V × Sym2 V) ⊕ ((V × V) × V) → V × V × V,
      Set.InjOn φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) ∧
      Set.MapsTo φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) (RUnits G)) ↔
    (∃ φ : (Sym2 V × Sym2 V) ⊕ ((V × V) × V) → V × V × V,
      Set.InjOn φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) ∧
      Set.MapsTo φ (Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G) (RUnits G)) :=
  Iff.rfl

/-- **Row 18 — THEOREM Σ.**
If `E0(F) = ∅` then `Σ(F) ≥ 0`.  Connectedness is NOT assumed;
`Ew(F) = ∅` makes `Σ` an empty sum.

This is the paper's conclusion transcribed in full:

> "`φ` is well defined (by (P3) and (L4)) and injective (by (L3) …).  Hence
> `#R ≥ #B + #K`, and by Identity 4.1, `Σ(F) ≥ 0`."

— i.e. **row 15 (the injection) + row 12 (Identity 4.1) ⟹ Theorem Σ**, and
that composition is what is machine-checked below.  Everything else the paper
proves here is upstream of one of those two.

  ★★ **PROVED**; no `sorry`.  `#print axioms row18_theorem_Sigma` reports
  `[propext, Classical.choice, Quot.sound]`.  It rests on
  `row12_identity_4_1` (Identity 4.1) and `row15_L4_private_free_slot` (the
  construction of `φ`), both of which are themselves proved and axiom-clean.

★ The arithmetic step deserves a note, because it is where the paper's one-line
"Hence `#R ≥ #B + #K`" actually lives.  Row 15 hands back an injection out of
the **disjoint union** `B-units ⊔ K-units`, realised here as a subset of a Lean
`Sum` type.  Turning that into the inequality `#B + #K ≤ #R` needs three facts
that the paper leaves implicit and Lean does not: the two images are disjoint
(`Sum.inl` and `Sum.inr` never collide), each is equinumerous with its source
(`Sum.inl`/`Sum.inr` are injective), and `RUnits` is finite.  `Set.ncard` is
`0` on infinite sets, so the finiteness side-condition is not a formality —
without it the inequality is not merely unproved but false-shaped. -/
theorem row18_theorem_Sigma (G : SimpleGraph V) (hE0 : E0 G = ∅) :
    0 ≤ Sig G := by
  -- Row 15: the injection `φ : B-units ⊔ K-units ↪ R-units`.
  obtain ⟨φ, hinj, hmaps⟩ := row15_L4_private_free_slot G hE0
  -- Its source, as a subset of the `Sum` type.
  set S : Set ((Sym2 V × Sym2 V) ⊕ ((V × V) × V)) :=
    Sum.inl '' BUnits G ∪ Sum.inr '' KUnits G with hS
  -- The two summands are disjoint: an `inl` is never an `inr`.
  have hdisj : Disjoint (Sum.inl '' BUnits G) (Sum.inr '' KUnits G) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    simp at hb
  -- Hence `|S| = #B + #K`.
  have hcardS : S.ncard = (BUnits G).ncard + (KUnits G).ncard := by
    rw [hS, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inr_injective]
  -- Injectivity into `RUnits` gives `|S| ≤ #R`, i.e. `#B + #K ≤ #R`.
  have hle : S.ncard ≤ (RUnits G).ncard :=
    Set.ncard_le_ncard_of_injOn φ hmaps hinj (Set.toFinite _)
  -- Row 12: `Σ = #R − #B − #K`.  Conclude.
  have h12 := row12_identity_4_1 G
  rw [hcardS] at hle
  omega

/-! ### Two elementary helpers used by rows 19–20.  Both proved. -/

/-- `⌊n²/2⌋ = C(n,2) + ⌊n/2⌋`, for both parities.  This is exactly the
arithmetic behind Proposition 3.1's "consequently" clause (row 2): it is what
turns the `Φ`-form of Theorem A into the `D`-form.  Proved; no `sorry`. -/
theorem sq_div_two_eq (n : ℕ) : n ^ 2 / 2 = n.choose 2 + n / 2 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 : (m + 1).choose 2 = m + m.choose 2 := by
      have h := Nat.choose_succ_succ m 1
      simpa [Nat.choose_one_right] using h
    have hpar : m ^ 2 % 2 = m % 2 := by
      rw [Nat.pow_mod]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl
    have hsq : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    rw [h1, hsq]
    omega

/-- Deleting two *distinct* vertices drops the vertex count by exactly `2`.
(The `n ≥ 2` that the induction step silently uses.)  Proved; no `sorry`. -/
theorem card_delPair_type {u v : V} (huv : u ≠ v) :
    Fintype.card {w : V // w ≠ u ∧ w ≠ v} = Fintype.card V - 2 := by
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter (fun w : V => w ≠ u ∧ w ≠ v))
      = (Finset.univ : Finset V) \ {u, v} := by
    ext w
    simp [Finset.mem_sdiff, not_or]
  have hsub : ({u, v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  rw [hf, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair huv,
    Finset.card_univ]

/-- **Row 19 — THEOREM A (= "(S)"), `D`-form: `D(F) ≤ ⌊n/2⌋`.**
Inputs: rows 9, 18, 8, 10.
Strong induction on `n`, splitting on `E0 ≠ ∅` / `E0 = ∅ ∧ Ew = ∅` /
`E0 = ∅ ∧ Ew ≠ ∅`.  No D2C hypothesis: this is a theorem about ALL graphs.

★ This is the strong-induction engine, and it is PROVED here from the four leaf
lemmas `row09_E0_case`, `row18_theorem_Sigma`, `row10_pigeonhole` and
`row08_cor`, all of which are themselves proved.  The induction has to be
stated over *all* vertex types of a fixed universe at once, because the step
deletes two vertices and therefore lands on a different type
(`{w : W // w ≠ u ∧ w ≠ v}`).

Note the base case ("`n ≤ 1`: no pairs, `D = 0`") is *not* needed as a separate
case: the trichotomy is exhaustive for every `n`, and the two branches that
recurse both exhibit an edge, which forces `n ≥ 2` on the spot. -/
theorem row19_strong_induction : ∀ (n : ℕ) {W : Type*} [Fintype W]
    [DecidableEq W] (G : SimpleGraph W), Fintype.card W = n →
    Dv G ≤ ((n / 2 : ℕ) : ℤ) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W _ _ G hcard
    -- The induction step, shared by branches 1 and 3 of the trichotomy.
    have step : ∀ (u v : W), u ≠ v → Dinc G u v ≤ 1 → Dv G ≤ ((n / 2 : ℕ) : ℤ) := by
      intro u v huv hd
      have hnt : Nontrivial W := ⟨⟨u, v, huv⟩⟩
      have hn2 : 2 ≤ n := by
        have := Fintype.one_lt_card_iff_nontrivial.mpr hnt
        omega
      have hcard2 : Fintype.card {w : W // w ≠ u ∧ w ≠ v} = n - 2 := by
        rw [card_delPair_type huv, hcard]
      have hIH := ih (n - 2) (by omega) (delPair G u v) hcard2
      rw [Dinc] at hd
      have harith : ((n - 2) / 2 : ℕ) + 1 = (n / 2 : ℕ) := by omega
      calc Dv G ≤ 1 + (((n - 2) / 2 : ℕ) : ℤ) := by linarith
        _ = (((n - 2) / 2 + 1 : ℕ) : ℤ) := by push_cast; ring
        _ = ((n / 2 : ℕ) : ℤ) := by rw [harith]
    by_cases hE0 : (E0 G).Nonempty
    · -- Branch 1: `E0(F) ≠ ∅`.  Theorem 3.9 (row 9) gives `D_inc ≤ 1`.
      obtain ⟨e, he⟩ := hE0
      obtain ⟨u, v, rfl, hadj, hcn⟩ := he
      exact step u v hadj.ne (row09_E0_case G hadj hcn)
    · have hE0e : E0 G = ∅ := Set.not_nonempty_iff_eq_empty.mp hE0
      by_cases hEw : (Ew G).Nonempty
      · -- Branch 3: `E0 = ∅`, `Ew ≠ ∅`.  Theorem Σ (row 18) + pigeonhole
        -- (row 10) + Corollary 3.8 (row 8).
        obtain ⟨u, v, hmem, hslack⟩ :=
          row10_pigeonhole G (row18_theorem_Sigma G hE0e) hEw
        have hadj : G.Adj u v := ((mem_Ew_iff G u v).mp hmem).1
        exact step u v hadj.ne (row08_cor G hadj hslack)
      · -- Branch 2: `E0 = ∅` and `Ew = ∅`, so `D(F) = −|A(F)| ≤ 0`.
        have hEwe : Ew G = ∅ := Set.not_nonempty_iff_eq_empty.mp hEw
        have hle : Dv G ≤ 0 := by
          rw [Dv, hE0e, hEwe]
          simp
        exact le_trans hle (Int.natCast_nonneg _)

/-- **Row 19 — THEOREM A, `D`-form**, specialised to a fixed vertex type. -/
theorem row19_theorem_A_D_form (G : SimpleGraph V) :
    Dv G ≤ ((Fintype.card V / 2 : ℕ) : ℤ) :=
  row19_strong_induction (Fintype.card V) G rfl

/-- **Row 19 (Φ-form) — `Φ(F) ≤ ⌊n²/2⌋` for every graph `F`.**
Equivalent to the `D`-form by row 2.  Simultaneously generalizes Mantel's
theorem and Füredi's Lemma 2.1 [Fü92, p. 83].
★ PROVED from the `D`-form + row 2 + `sq_div_two_eq`; no new `sorry`. -/
theorem row19_theorem_A (G : SimpleGraph V) :
    Phi G ≤ (Fintype.card V) ^ 2 / 2 := by
  have h2 := row02_D_normal_form G
  have hD := row19_theorem_A_D_form G
  have key : (Phi G : ℤ) ≤ (((Fintype.card V) ^ 2 / 2 : ℕ) : ℤ) := by
    rw [sq_div_two_eq, Nat.cast_add]
    linarith
  exact_mod_cast key

/-- **Row 20 — COROLLARY B (the Murty–Simon inequality).**
Inputs: rows 19, 3, 2.  This is `erdos_742` modulo `edgeFinset_card_eq_ncard`
(see Part 4).
★ PROVED from `row19_theorem_A` (Φ-form) + `row03b_phi_eq_two_e`; no new
`sorry`.  The integrality step is `⌊⌊n²/2⌋/2⌋ = ⌊n²/4⌋`.
Note that row 2 enters only *through* the Φ-form of row 19, so it is not
consumed a second time here. -/
theorem row20_corollary_B (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeSet.ncard ≤ (Fintype.card V) ^ 2 / 4 := by
  have h3 := row03b_phi_eq_two_e G hG
  have h19 := row19_theorem_A G
  rw [h3] at h19
  have h4 : (Fintype.card V) ^ 2 / 4 = (Fintype.card V) ^ 2 / 2 / 2 := by
    rw [Nat.div_div_eq_div_mul]
  omega

/-- **Row 21 — the failed strengthenings are all FALSE.**
Established by machine search for counterexamples, not by the paper proof.
⚠ This is the one row whose content is NEGATIVE, and it is **an input to
nothing**: no other declaration in this file depends on it, so nothing here
closes by exhaustion.
Stated in the form: the per-edge strengthening of Theorem Σ is false — `Σ`'s
summand can be strictly negative on an `E0`-free graph.

⚠ **This declaration carries the file's only `sorry`.**  The counterexample
search that establishes it is not transcribed into Lean, so the statement is
declared here and left unproved.  Nothing consumes it, and it is not reachable
from `erdos_742`. -/
theorem row21_per_edge_form_false :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W)
      (u v : W), E0 H = ∅ ∧ s(u,v) ∈ Ew H ∧ sigmaTerm H u v < 0 := by
  sorry

end Skeleton

end Campaign

/-! ###########################################################
    ## Part 4. The two ends joined                            ##
    ########################################################### -/

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G.edgeFinset.card` and `G.edgeSet.ncard` agree, so row 20 is literally
the upstream conclusion.  Proved. -/
theorem edgeFinset_card_eq_ncard (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card = G.edgeSet.ncard := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1

/-- **The assembly.**  Row 20 plus the bridge gives the upstream statement.
Proved. -/
theorem erdos_742_of_row20
    (h : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Erdos742.IsDiameter2Critical H → H.edgeSet.ncard ≤ (Fintype.card W) ^ 2 / 4)
    (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hH : Erdos742.IsDiameter2Critical H) :
    H.edgeFinset.card ≤ (Fintype.card W) ^ 2 / 4 := by
  rw [edgeFinset_card_eq_ncard]
  exact h W H hH

/-- **The assembly, stated with this file's own D2C predicate.**  Row 20
transfers to the upstream predicate along the bridge.  Proved. -/
theorem erdos_742_of_row20_campaign
    (h : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Campaign.IsD2C H → H.edgeSet.ncard ≤ (Fintype.card W) ^ 2 / 4)
    (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hH : Erdos742.IsDiameter2Critical H) :
    H.edgeFinset.card ≤ (Fintype.card W) ^ 2 / 4 := by
  rw [edgeFinset_card_eq_ncard]
  exact h W H ((Campaign.isD2C_iff_isDiameter2Critical H).mpr hH)

end Assembly

/-- **THE TARGET, discharged.**  This is the upstream `erdos_742` statement
(see Part 0 for the transcription provenance), proved from
`Campaign.row20_corollary_B` and `edgeFinset_card_eq_ncard`.

★★★ **AXIOM-CLEAN.**  `#print axioms Erdos742.erdos_742` reports

    [propext, Classical.choice, Quot.sound]

— **no `sorryAx`, no `native_decide`, no added axiom.**  The chain
`row15 + row12 ⟹ row18 ⟹ row19 ⟹ row20 ⟹ erdos_742`, and the definitional
bridge `isD2C_iff_isDiameter2Critical`, are all machine-checked.

⚠ **State the scope precisely.**  What is established is: *Erdős #742's
INEQUALITY is formalized.*  An axiom-clean `#print axioms` certifies that the
Lean proof has no gaps; it certifies **nothing** about whether each Lean
statement faithfully transcribes the paper statement it is named for.  Several
rows above carry explicit notes where the Lean statement is narrower than the
paper's (rows 5, 7(i) and 14 in particular), and only the rows that have been
read against the paper have been audited that way.
⚠ Also note `row21_per_edge_form_false` carries a `sorry`; it is NEGATIVE (the
failed strengthenings) and is an input to nothing — it is not reachable from
`erdos_742`. -/
theorem erdos_742 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  intro V _ _ G _ hG
  rw [edgeFinset_card_eq_ncard]
  exact Campaign.row20_corollary_B G hG

end Erdos742
/-
# Erdős Problem #742 (Murty–Simon), the equality clause

Which diameter-2-critical graphs attain the bound `e(G) = ⌊n²/4⌋`?  Answer, for
`n ≥ 3`: exactly the balanced complete bipartite graphs `K_{⌈n/2⌉,⌊n/2⌋}` —
proved here as `stmt6_ms_eq_iso_labelled`, with `stmt6_ms_eq` (the intrinsic
`IsBalCBUnion ∧ Preconnected` form) as the internal workhorse it is derived
from.

This file is compiled CONCATENATED after `Erdos742.lean` — the inequality
`e(G) ≤ ⌊n²/4⌋` for all diameter-2-critical `G`, on which the equality analysis
is built (`cat Erdos742.lean Equality.lean`).  It has no imports of its own and
re-opens the same namespace structure `Erdos742.lean` closes (`Erdos742` then
`Campaign`); every `row*` name below refers to a declaration proved there.

The top-level iff is pinned to `n ≥ 3`: the `n = 2` converse fails —
`K_{1,1} = K_2` has `⌊4/4⌋ = 1` edge but diameter `1`, not `2` — so the
attainment-strengthened reading is false at `n = 2`; the facts for `n ∈ {1,2}`
(no diameter-2-critical graph exists at all there) are stated separately, never
folded into the `n ≥ 3` iff.  The public statement is the literal isomorphism
`G ≅ K_{⌈n/2⌉,⌊n/2⌋}` via mathlib's `SimpleGraph.completeBipartiteGraph`.
-/

namespace Erdos742
namespace Campaign

/-! ###########################################################
    ## Part 5. The equality clause                            ##
    ########################################################### -/

section Equality

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The family `𝓑` (`IsBalCBUnion`)

**Design note.**  `IsBalCBUnion` must be type-polymorphic (it is stated under
the section's `variable {V : Type*} [Fintype V] [DecidableEq V]`, exactly as
`Erdos742.lean`'s `Dv`/`Sc`/etc. are, so it automatically generalises the way
`row19_strong_induction` needs) and must survive the `delPair` type change.
We use an INTRINSIC formulation: instead of an
index type for "the components", a graph is in `𝓑` iff there is a
"same-component" equivalence relation `same` and a 2-colouring `part` with

  `G.Adj a b ↔ same a b ∧ part a ≠ part b`

(so `same`-classes are exactly the disjoint pieces, and inside a class,
adjacency is complete-bipartite-by-part), each class balanced (its two
part-sizes differ by at most 1 — this is where `K_1 = K_{1,0}` enters: it is
just the `b = 0` instance, no separate case), and at most one class of odd
total size.  No index type, no `Quotient`, no decidability instance beyond
`Classical` — this is what makes it transport-friendly across `delPair`
(toy lemma below): the *same* definition, at the *same* two lines, applies
verbatim to `{w : V // w ≠ u ∧ w ≠ v}`. -/

/-- `IsBalCBUnion G` : `G` is a disjoint union of balanced complete bipartite
graphs, at most one of odd order (the family `𝓑`).
`K_1`-in-family convention: a class with `part`
value `false` unused (`b = 0`) is admitted — nothing here excludes it; the
convention is exactly the observation that "class size ≤ 1" is not itself
excluded by the definition below. -/
def IsBalCBUnion (G : SimpleGraph V) : Prop :=
  ∃ (same : V → V → Prop) (part : V → Bool),
    Equivalence same ∧
    (∀ a b, G.Adj a b ↔ same a b ∧ part a ≠ part b) ∧
    (∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1) ∧
    (∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1) ∧
    (∀ a b, Odd {c | same a c}.ncard → Odd {c | same b c}.ncard → same a b)

/-! #### Basic API -/

/-- Any graph on a subsingleton type (`0` or `1` vertices) is in `𝓑`,
witnessed by the trivial full relation.  This is the induction's `n ≤ 1` base
case, stated once here for reuse; it covers `n = 0` (empty graph) and `n = 1`
(`K_1`) simultaneously. -/
theorem isBalCBUnion_of_subsingleton {W : Type*} [Fintype W] [DecidableEq W]
    [Subsingleton W] (G : SimpleGraph W) : IsBalCBUnion G := by
  classical
  refine ⟨fun _ _ => True, fun _ => true,
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩, ?_, ?_, ?_, ?_⟩
  · intro a b
    dsimp only
    constructor
    · intro hadj
      rw [Subsingleton.elim a b] at hadj
      exact absurd hadj (G.irrefl)
    · rintro ⟨-, hne⟩
      exact absurd rfl hne
  · intro a
    dsimp only
    have h0 : {b : W | True ∧ (true : Bool) = false}.ncard = 0 := by
      have he : {b : W | True ∧ (true : Bool) = false} = ∅ := by ext b; simp
      rw [he]; exact Set.ncard_empty _
    have hle1 : {b : W | True ∧ (true : Bool) = true}.ncard ≤ 1 := by
      have hsubset : {b : W | True ∧ (true : Bool) = true} ⊆ ({a} : Set W) :=
        fun b _ => Subsingleton.elim b a
      calc {b : W | True ∧ (true : Bool) = true}.ncard
          ≤ ({a} : Set W).ncard := Set.ncard_le_ncard hsubset (Set.toFinite _)
        _ = 1 := Set.ncard_singleton a
    omega
  · intro a
    dsimp only
    have h0 : {b : W | True ∧ (true : Bool) = false}.ncard = 0 := by
      have he : {b : W | True ∧ (true : Bool) = false} = ∅ := by ext b; simp
      rw [he]; exact Set.ncard_empty _
    omega
  · intro a b _ _; trivial

/-- **Toy transport lemma.**  `IsBalCBUnion` transports
across `delPair` in the base case that matters to the induction: deleting the
two (distinct) vertices of a `2`-vertex graph lands on an EMPTY subtype, and
the same intrinsic definition — unchanged, no re-statement — proves
membership there.  This is the sanity check that `IsBalCBUnion`'s
type-polymorphic form (the section `variable`, not a fixed `V`) actually
survives the vertex-type change `delPair` performs, before anything is built
on top of it. -/
theorem isBalCBUnion_delPair_of_card_two (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) (hcard : Fintype.card V = 2) :
    IsBalCBUnion (delPair G u v) := by
  have hc0 : Fintype.card {w : V // w ≠ u ∧ w ≠ v} = 0 := by
    rw [card_delPair_type huv, hcard]
  haveI : IsEmpty {w : V // w ≠ u ∧ w ≠ v} := Fintype.card_eq_zero_iff.mp hc0
  exact isBalCBUnion_of_subsingleton (delPair G u v)

/-! #### Structural API: what `IsBalCBUnion` forces about `E0`, `Ew`, `Anon`

Every class is triangle-free (it is bipartite) and complete-bipartite-by-part,
so every edge has codegree `0` — hence `E0 G = G.edgeSet` and `Ew G = ∅`
outright.  (The `Anon G` side — the codegree-`≥1` non-edges, i.e. same-class
same-part pairs — is where the balance hypothesis is spent; that
characterisation is not needed here — `dv_of_isBalCBUnion_connected` below
derives what it needs of it directly, in the connected case.) -/

theorem IsBalCBUnion.commonNeighbors_eq_empty_of_adj {G : SimpleGraph V}
    (hG : IsBalCBUnion G) {x y : V} (hxy : G.Adj x y) :
    G.commonNeighbors x y = ∅ := by
  obtain ⟨same, part, -, hbip, -, -, -⟩ := hG
  obtain ⟨-, hpxy⟩ := (hbip x y).mp hxy
  by_contra hne
  obtain ⟨z, hzx, hzy⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨-, hpxz⟩ := (hbip x z).mp hzx
  obtain ⟨-, hpyz⟩ := (hbip y z).mp hzy
  revert hpxz hpyz hpxy
  cases part x <;> cases part y <;> cases part z <;> simp

theorem IsBalCBUnion.E0_eq_edgeSet {G : SimpleGraph V} (hG : IsBalCBUnion G) :
    E0 G = G.edgeSet := by
  ext P
  induction P using Sym2.ind with
  | _ u v =>
    rw [mem_E0_iff, SimpleGraph.mem_edgeSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hG.commonNeighbors_eq_empty_of_adj h⟩⟩

theorem IsBalCBUnion.Ew_eq_empty {G : SimpleGraph V} (hG : IsBalCBUnion G) :
    Ew G = ∅ := by
  ext P
  induction P using Sym2.ind with
  | _ u v =>
    simp only [Set.mem_empty_iff_false, iff_false, mem_Ew_iff]
    rintro ⟨hadj, hne, -⟩
    exact absurd (hG.commonNeighbors_eq_empty_of_adj hadj) (Set.nonempty_iff_ne_empty.mp hne)

/-! ### The tightness dictionary: `D(G) = ⌊n/2⌋ ↔ e(G) = ⌊n²/4⌋`, and edge supply -/

/-- **`n²/2` is always even.**  Small arithmetic helper for the slack
identity below (needed to invert `⌊n²/4⌋ = ⌊n²/2⌋/2` exactly). -/
theorem sq_div_two_even (n : ℕ) : ∃ k, n ^ 2 / 2 = k + k := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨k * k, ?_⟩
    have h1 : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [h1]; omega
  · refine ⟨k * k + k, ?_⟩
    have h1 : (2 * k + 1) ^ 2 = 4 * (k * k) + 4 * k + 1 := by ring
    rw [h1]; omega

/-- **The slack identity**: on a diameter-2-critical graph,
`D(G) = ⌊n/2⌋ ↔ e(G) = ⌊n²/4⌋` — attaining the edge bound is equivalent to the
deficiency functional `D` attaining `⌊n/2⌋`.  Built purely from
`row02_D_normal_form` and `row03b_phi_eq_two_e`, both proved in
`Erdos742.lean`. -/
theorem pta_l4_arith (G : SimpleGraph V) (hG : Erdos742.IsDiameter2Critical G) :
    Dv G = ((Fintype.card V / 2 : ℕ) : ℤ) ↔
      G.edgeSet.ncard = (Fintype.card V) ^ 2 / 4 := by
  have h2 := row02_D_normal_form G
  have h3 := row03b_phi_eq_two_e G hG
  have hsq := sq_div_two_eq (Fintype.card V)
  set n := Fintype.card V with hn
  have hPhi : (Phi G : ℤ) = 2 * (G.edgeSet.ncard : ℤ) := by
    rw [h3]; push_cast; ring
  have h4 : n ^ 2 / 4 = n ^ 2 / 2 / 2 := by rw [Nat.div_div_eq_div_mul]
  have hsqZ : ((n ^ 2 / 2 : ℕ) : ℤ) = (n.choose 2 : ℤ) + ((n / 2 : ℕ) : ℤ) := by
    exact_mod_cast hsq
  constructor
  · intro hD
    have key : 2 * (G.edgeSet.ncard : ℤ) = ((n ^ 2 / 2 : ℕ) : ℤ) := by
      rw [← hPhi, h2, hD]; linarith [hsqZ]
    have keyNat : 2 * G.edgeSet.ncard = n ^ 2 / 2 := by exact_mod_cast key
    omega
  · intro hE
    obtain ⟨k, hk⟩ := sq_div_two_even n
    have hk4 : n ^ 2 / 4 = k := by rw [h4, hk]; omega
    have keyNat : 2 * G.edgeSet.ncard = n ^ 2 / 2 := by rw [hE, hk4, hk]; omega
    have key : 2 * (G.edgeSet.ncard : ℤ) = ((n ^ 2 / 2 : ℕ) : ℤ) := by exact_mod_cast keyNat
    rw [← hPhi, h2] at key
    linarith [key, hsqZ]

/-- **Edge supply**: every graph on `n ≥ 2`
vertices with `D(F) = ⌊n/2⌋` has an edge `{u,v}` with `D_inc(u,v) ≤ 1`.  A
re-scoping of `row19_strong_induction`'s existing `by_cases` tree
(`Erdos742.lean:3511`–`3529`): branch 1 (`E0 ≠ ∅`) is `row09_E0_case`,
branch 3 (`E0 = ∅ ≠ Ew`) is `row10_pigeonhole` + `row08_cor`, branch 2
(`E0 = Ew = ∅`) is vacuous under tightness for `n ≥ 2` (a graph with no
classified edge has `D ≤ 0 < ⌊n/2⌋`). -/
theorem lemma_supply (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hD : Dv G = ((Fintype.card V / 2 : ℕ) : ℤ)) :
    ∃ u v : V, G.Adj u v ∧ Dinc G u v ≤ 1 := by
  by_cases hE0 : (E0 G).Nonempty
  · obtain ⟨e, he⟩ := hE0
    obtain ⟨u, v, rfl, hadj, hcn⟩ := he
    exact ⟨u, v, hadj, row09_E0_case G hadj hcn⟩
  · have hE0e : E0 G = ∅ := Set.not_nonempty_iff_eq_empty.mp hE0
    by_cases hEw : (Ew G).Nonempty
    · obtain ⟨u, v, hmem, hslack⟩ := row10_pigeonhole G (row18_theorem_Sigma G hE0e) hEw
      have hadj : G.Adj u v := ((mem_Ew_iff G u v).mp hmem).1
      exact ⟨u, v, hadj, row08_cor G hadj hslack⟩
    · exfalso
      have hEwe : Ew G = ∅ := Set.not_nonempty_iff_eq_empty.mp hEw
      have hle : Dv G ≤ 0 := by rw [Dv, hE0e, hEwe]; simp
      rw [hD] at hle
      have h1 : 1 ≤ Fintype.card V / 2 := by omega
      omega

/-- **Tightness survives deletion**: if `D(F) = ⌊n/2⌋`,
`n ≥ 2`, and `{u,v} ∈ E(F)` has `D_inc(u,v) ≤ 1`, then `D_inc(u,v) = 1` and
`D(F − {u,v}) = ⌊(n−2)/2⌋`.  `le_antisymm`-flavoured squeeze against
`row19_theorem_A_D_form` on the subtype (the arithmetic pattern is
`row19_strong_induction`'s inner `step`, `Erdos742.lean:3503`–`3510`). -/
theorem lemma_tight_del (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hD : Dv G = ((Fintype.card V / 2 : ℕ) : ℤ)) {u v : V} (huv : G.Adj u v)
    (hle : Dinc G u v ≤ 1) :
    Dinc G u v = 1 ∧ Dv (delPair G u v) = (((Fintype.card V - 2) / 2 : ℕ) : ℤ) := by
  have hIH := row19_theorem_A_D_form (delPair G u v)
  rw [card_delPair_type huv.ne] at hIH
  have hdef : Dinc G u v = Dv G - Dv (delPair G u v) := rfl
  have harith : ((Fintype.card V - 2) / 2 : ℕ) + 1 = (Fintype.card V / 2 : ℕ) := by omega
  have heq2 : ((Fintype.card V / 2 : ℕ) : ℤ) = Dinc G u v + Dv (delPair G u v) := by
    linarith [hD, hdef]
  have hcast : (((Fintype.card V - 2) / 2 : ℕ) : ℤ) + 1 = ((Fintype.card V / 2 : ℕ) : ℤ) := by
    exact_mod_cast harith
  exact ⟨by linarith [heq2, hcast, hIH, hle], by linarith [heq2, hcast, hIH, hle]⟩

/-! ### The deletion step and the induction

`step_del` (the deletion step) and `stmt5_forward` (the induction) appear at the
END of this file, together with `stmt6_ms_eq`/`_iso`/`_iso_labelled`: `step_del`'s
proof consumes `pst_a` and `pst_b`, which are built on `extF` — declared below —
and Lean is a single linear pass, so those five declarations must follow that
machinery. -/

/-! ### Single-class ("connected") tightness

The top-level target's BACKWARD direction
(`G ≅ K_{a,b} ⟹ e(G) = ⌊n²/4⌋`) needs `D(G) = ⌊n/2⌋` for a *connected* member
of `𝓑`, which the induction skeleton (built for the forward direction) does
not supply.  Proved directly via the degree-sum ("handshake") lemma on `G`
and on `Gᶜ` — NOT via the general multi-component tightness fact (`D(G) =
⌊n/2⌋` for an arbitrary member of `𝓑`, which needs a sum over an unbounded
number of classes and is not stated in this file) — because a connected member
of `𝓑` has exactly ONE class, so no summing over classes is needed here. -/

/-- If `(same, part)` witnesses the adjacency structure of `IsBalCBUnion` and
`x, y` are `Reachable`, they are in the same class.  (Induction on the walk:
each step is `same`, by the adjacency iff; compose by transitivity.) -/
theorem same_of_reachable {G : SimpleGraph V} {same : V → V → Prop} {part : V → Bool}
    (hbip : ∀ a b : V, G.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hequiv : Equivalence same) {x y : V} (h : G.Reachable x y) :
    same x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hequiv.refl _
  | cons hadj p ih => exact hequiv.trans ((hbip _ _).mp hadj).1 ih

/-- **The single-class tightness fact**, `D(G) = ⌊n/2⌋`,
stated directly for a connected member of
`𝓑` (whose `same` witness is forced full by `same_of_reachable`).  Route: `E0 G =
G.edgeSet`/`Ew G = ∅` (already proved), `e(G) = |X|·|Y|` and `Anon G =
Gᶜ.edgeSet` (balance ⟹ every same-part pair has a nonempty common
neighbourhood — the opposite part, shown nonempty because balance forces it
once two same-part classmates exist) with `2·|Anon G| = |X|(|X|−1) +
|Y|(|Y|−1)`, both via the degree-sum ("handshake") lemma, on `G` and on `Gᶜ`
respectively. Combines to `2·D(G) = (|X|+|Y|) − (|X|−|Y|)²`, and `|X|−|Y| ∈
{−1,0,1}` (balance) gives `= n − 0` or `n − 1` matching `⌊n/2⌋` in both
parities. -/
theorem dv_of_isBalCBUnion_connected {G : SimpleGraph V} (hG : IsBalCBUnion G)
    (hconn : G.Preconnected) :
    Dv G = ((Fintype.card V / 2 : ℕ) : ℤ) := by
  classical
  haveI : DecidableRel G.Adj := Classical.decRel _
  have hE0 : E0 G = G.edgeSet := hG.E0_eq_edgeSet
  have hEw : Ew G = (∅ : Set (Sym2 V)) := hG.Ew_eq_empty
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, -⟩ := hG
  have hsame : ∀ x y : V, same x y := fun x y => same_of_reachable hbip hequiv (hconn x y)
  have hbip' : ∀ x y : V, G.Adj x y ↔ part x ≠ part y := by
    intro x y; rw [hbip x y]; simp [hsame x y]
  rcases isEmpty_or_nonempty V with hV | hV
  · have hcard0 : Fintype.card V = 0 := Fintype.card_eq_zero
    have hEdge0 : G.edgeSet = (∅ : Set (Sym2 V)) := by
      ext P
      induction P using Sym2.ind with
      | _ u v => exact (IsEmpty.false u).elim
    have hDv0 : Dv G = 0 := by
      rw [Dv, hE0, hEw, hEdge0]
      simp [Anon]
    rw [hDv0, hcard0]; norm_num
  · obtain ⟨a₀⟩ := hV
    set X : Finset V := Finset.univ.filter (fun a => part a = true) with hXdef
    set Y : Finset V := Finset.univ.filter (fun a => part a = false) with hYdef
    have hmemX : ∀ a, a ∈ X ↔ part a = true := by intro a; simp [hXdef]
    have hmemY : ∀ a, a ∈ Y ↔ part a = false := by intro a; simp [hYdef]
    have hYcompl : Y = Finset.univ.filter (fun a : V => ¬ part a = true) := by
      ext a; rw [hmemY]
      constructor
      · intro h; simp [h]
      · intro h; simpa using h
    have hXf : Finset.univ.filter (fun a : V => part a = true) = X := hXdef.symm
    have hYf : Finset.univ.filter (fun a : V => ¬ part a = true) = Y := hYcompl.symm
    have hXY : X.card + Y.card = Fintype.card V := by
      rw [hXdef, hYcompl]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (p := fun a => part a = true)
    have hbalX : X.card ≤ Y.card + 1 := by
      have h := hbal1 a₀
      have heqX : {b : V | same a₀ b ∧ part b = true} = (X : Set V) := by
        ext b; simp [hmemX, hsame a₀ b]
      have heqY : {b : V | same a₀ b ∧ part b = false} = (Y : Set V) := by
        ext b; simp [hmemY, hsame a₀ b]
      rw [heqX, heqY, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
      exact h
    have hbalY : Y.card ≤ X.card + 1 := by
      have h := hbal2 a₀
      have heqX : {b : V | same a₀ b ∧ part b = true} = (X : Set V) := by
        ext b; simp [hmemX, hsame a₀ b]
      have heqY : {b : V | same a₀ b ∧ part b = false} = (Y : Set V) := by
        ext b; simp [hmemY, hsame a₀ b]
      rw [heqX, heqY, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
      exact h
    have hns : ∀ x, G.neighborFinset x = if part x = true then Y else X := by
      intro x
      ext y
      rw [SimpleGraph.mem_neighborFinset, hbip']
      cases hpx : part x
      · rw [if_neg (by decide), hmemX]
        cases hpy : part y <;> simp
      · rw [if_pos rfl, hmemY]
        cases hpy : part y <;> simp
    have hdeg : ∀ x, G.degree x = if part x = true then Y.card else X.card := by
      intro x; rw [SimpleGraph.degree, hns x]; split <;> rfl
    have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    have hsplit : ∑ v : V, G.degree v = X.card * Y.card + Y.card * X.card := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset V)
        (fun a => part a = true) (fun v => G.degree v)]
      have h1 : ∑ v ∈ Finset.univ.filter (fun a : V => part a = true), G.degree v
          = X.card * Y.card := by
        have step : ∑ v ∈ Finset.univ.filter (fun a : V => part a = true), G.degree v
            = ∑ _v ∈ Finset.univ.filter (fun a : V => part a = true), Y.card :=
          Finset.sum_congr rfl (fun v hv => by
            rw [hdeg v, if_pos (Finset.mem_filter.mp hv).2])
        rw [step, hXf, Finset.sum_const, smul_eq_mul]
      have h2 : ∑ v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), G.degree v
          = Y.card * X.card := by
        have step : ∑ v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), G.degree v
            = ∑ _v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), X.card :=
          Finset.sum_congr rfl (fun v hv => by
            rw [hdeg v, if_neg (Finset.mem_filter.mp hv).2])
        rw [step, hYf, Finset.sum_const, smul_eq_mul]
      rw [h1, h2]
    have he : G.edgeFinset.card = X.card * Y.card := by
      have h2e : 2 * G.edgeFinset.card = 2 * (X.card * Y.card) := by
        rw [← hsum, hsplit]; ring
      omega
    have heSet : G.edgeSet.ncard = X.card * Y.card := by
      rw [← edgeFinset_card_eq_ncard]; exact he
    have hcn_same_part : ∀ x y : V, x ≠ y → part x = part y →
        (G.commonNeighbors x y).Nonempty := by
      intro x y hxy hpxy
      cases hpx : part x
      · have hxY : x ∈ Y := by rw [hmemY, hpx]
        have hyY : y ∈ Y := by rw [hmemY, ← hpxy, hpx]
        have hpair : ({x, y} : Finset V) ⊆ Y := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl; exacts [hxY, hyY]
        have hYc2 : 2 ≤ Y.card := by
          have hle := Finset.card_le_card hpair
          rwa [Finset.card_pair hxy] at hle
        have hXc1 : 1 ≤ X.card := by omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
        rw [hmemX] at hz
        refine ⟨z, ?_, ?_⟩
        · rw [SimpleGraph.mem_neighborSet]; exact (hbip' x z).mpr (by rw [hpx, hz]; simp)
        · rw [SimpleGraph.mem_neighborSet]; exact (hbip' y z).mpr (by rw [← hpxy, hpx, hz]; simp)
      · have hxX : x ∈ X := by rw [hmemX, hpx]
        have hyX : y ∈ X := by rw [hmemX, ← hpxy, hpx]
        have hpair : ({x, y} : Finset V) ⊆ X := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl; exacts [hxX, hyX]
        have hXc2 : 2 ≤ X.card := by
          have hle := Finset.card_le_card hpair
          rwa [Finset.card_pair hxy] at hle
        have hYc1 : 1 ≤ Y.card := by omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
        rw [hmemY] at hz
        refine ⟨z, ?_, ?_⟩
        · rw [SimpleGraph.mem_neighborSet]; exact (hbip' x z).mpr (by rw [hpx, hz]; simp)
        · rw [SimpleGraph.mem_neighborSet]; exact (hbip' y z).mpr (by rw [← hpxy, hpx, hz]; simp)
    have hAnonEq : Anon G = (Gᶜ.edgeSet : Set (Sym2 V)) := by
      ext P
      induction P using Sym2.ind with
      | _ u v =>
        rw [mem_Anon_iff, SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        constructor
        · rintro ⟨hne, hnadj, -⟩; exact ⟨hne, hnadj⟩
        · rintro ⟨hne, hnadj⟩
          have hpuv : part u = part v := by
            by_contra hc
            exact hnadj ((hbip' u v).mpr hc)
          exact ⟨hne, hnadj, hcn_same_part u v hne hpuv⟩
    have hdegC : ∀ x, Gᶜ.degree x = if part x = true then X.card - 1 else Y.card - 1 := by
      intro x
      rw [SimpleGraph.degree_compl, hdeg x, ← hXY]
      cases hpx : part x
      · rw [if_neg (by decide), if_neg (by decide)]; omega
      · rw [if_pos rfl, if_pos rfl]; omega
    have hsumC : ∑ v, Gᶜ.degree v = 2 * Gᶜ.edgeFinset.card :=
      Gᶜ.sum_degrees_eq_twice_card_edges
    have hsplitC : ∑ v : V, Gᶜ.degree v =
        X.card * (X.card - 1) + Y.card * (Y.card - 1) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset V)
        (fun a => part a = true) (fun v => Gᶜ.degree v)]
      have h1 : ∑ v ∈ Finset.univ.filter (fun a : V => part a = true), Gᶜ.degree v
          = X.card * (X.card - 1) := by
        have step : ∑ v ∈ Finset.univ.filter (fun a : V => part a = true), Gᶜ.degree v
            = ∑ _v ∈ Finset.univ.filter (fun a : V => part a = true), (X.card - 1) :=
          Finset.sum_congr rfl (fun v hv => by
            rw [hdegC v, if_pos (Finset.mem_filter.mp hv).2])
        rw [step, hXf, Finset.sum_const, smul_eq_mul]
      have h2 : ∑ v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), Gᶜ.degree v
          = Y.card * (Y.card - 1) := by
        have step : ∑ v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), Gᶜ.degree v
            = ∑ _v ∈ Finset.univ.filter (fun a : V => ¬ part a = true), (Y.card - 1) :=
          Finset.sum_congr rfl (fun v hv => by
            rw [hdegC v, if_neg (Finset.mem_filter.mp hv).2])
        rw [step, hYf, Finset.sum_const, smul_eq_mul]
      rw [h1, h2]
    have h2eC : 2 * Gᶜ.edgeFinset.card = X.card * (X.card - 1) + Y.card * (Y.card - 1) := by
      rw [← hsumC, hsplitC]
    have hAnonCard : (Anon G).ncard = Gᶜ.edgeFinset.card := by
      rw [hAnonEq, ← edgeFinset_card_eq_ncard]
    have hAnon2 : 2 * (Anon G).ncard = X.card * (X.card - 1) + Y.card * (Y.card - 1) := by
      rw [hAnonCard]; exact h2eC
    have cast_mul_pred : ∀ a : ℕ, ((a * (a - 1) : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
      intro a
      cases a with
      | zero => simp
      | succ n =>
        have h1 : n + 1 - 1 = n := by omega
        push_cast [h1]; ring
    have hAnonZ2 : 2 * ((Anon G).ncard : ℤ) =
        (X.card : ℤ) * ((X.card : ℤ) - 1) + (Y.card : ℤ) * ((Y.card : ℤ) - 1) := by
      have hcast : (2 * (Anon G).ncard : ℤ) =
          ((X.card * (X.card - 1) : ℕ) : ℤ) + ((Y.card * (Y.card - 1) : ℕ) : ℤ) := by
        rw [← Nat.cast_add]; exact_mod_cast hAnon2
      rw [cast_mul_pred X.card, cast_mul_pred Y.card] at hcast
      linarith [hcast]
    have hFinal2 : 2 * Dv G = ((X.card : ℤ) + (Y.card : ℤ)) -
        ((X.card : ℤ) - (Y.card : ℤ)) ^ 2 := by
      have hDvDef : Dv G = ((E0 G).ncard : ℤ) + ((Ew G).ncard : ℤ) - ((Anon G).ncard : ℤ) := rfl
      have hE0c : ((E0 G).ncard : ℤ) = (X.card * Y.card : ℤ) := by
        rw [hE0]; exact_mod_cast heSet
      have hEwc : ((Ew G).ncard : ℤ) = 0 := by rw [hEw]; simp
      rw [hDvDef, hE0c, hEwc]
      linear_combination -hAnonZ2
    have hgoalZ : 2 * ((Fintype.card V / 2 : ℕ) : ℤ) =
        ((X.card : ℤ) + (Y.card : ℤ)) - ((X.card : ℤ) - (Y.card : ℤ)) ^ 2 := by
      have hd : X.card = Y.card ∨ X.card = Y.card + 1 ∨ Y.card = X.card + 1 := by omega
      rcases hd with h | h | h
      · rw [h]
        have hn : Fintype.card V = Y.card + Y.card := by omega
        have hdiv : (Y.card + Y.card) / 2 = Y.card := by omega
        rw [hn, hdiv]; push_cast; ring
      · rw [h]
        have hn : Fintype.card V = (Y.card + 1) + Y.card := by omega
        have hdiv : ((Y.card + 1) + Y.card) / 2 = Y.card := by omega
        rw [hn, hdiv]; push_cast; ring
      · rw [h]
        have hn : Fintype.card V = X.card + (X.card + 1) := by omega
        have hdiv : (X.card + (X.card + 1)) / 2 = X.card := by omega
        rw [hn, hdiv]; push_cast; ring
    linarith [hFinal2, hgoalZ]

/-! ### From the induction to the equality characterization -/

/-- A walk-of-length-`≤2` witness (`Within2`) is a `Reachable` witness. -/
theorem within2_reachable {x y : V} {G : SimpleGraph V} (h : Within2 G x y) :
    G.Reachable x y := by
  rcases h with rfl | hadj | ⟨m, h1, h2⟩
  · exact SimpleGraph.Reachable.refl x
  · exact hadj.reachable
  · exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)⟩

/-- **Diameter-2-critical ⟹ connected.**  `Erdos742.lean`'s D2C/`Within2` API
has no lemma for this, so it is added here, proved
directly from `IsD2`'s `∀ x y, Within2 G x y` clause via the bridge. -/
theorem isDiameter2Critical_preconnected {G : SimpleGraph V}
    (hG : Erdos742.IsDiameter2Critical G) : G.Preconnected := by
  have hD2C := (isD2C_iff_isDiameter2Critical G).mpr hG
  exact fun x y => within2_reachable (hD2C.1.1 x y)

/-! `stmt6_ms_eq` — appears at the end of this file, see the linear-pass note above. -/

/-! ### `stmt6_ms_eq_iso` — the literal isomorphism corollary (the public statement uses
`G ≅ K_{⌈n/2⌉,⌊n/2⌋}` via mathlib's `SimpleGraph.completeBipartiteGraph`; `stmt6_ms_eq`
above is the internal workhorse it is derived from).  Route: `Equiv.sumCompl` +
`Fintype.equivFin` build the vertex bijection; `RelIso.mk` (anonymous constructor for
`≃g`) checks adjacency; `completeBipartiteGraphCongr` relabels the two part-types to the
canonical `Fin a`/`Fin b` form.  The canonical-label question (which of `a,b` is the
`⌈⌉`/`⌊⌋` one) is sidestepped: an existential
over `a,b` with `a+b=n ∧ (a=b ∨ a=b+1 ∨ b=a+1)`, rather than committing to an order. -/

/-- **A graph isomorphism transports `IsBalCBUnion` backward along the iso.**  General,
reusable: pulls the `(same,part)` witness of `H`'s membership in `𝓑` back through
`φ : G ≃g H` to witness `G`'s own membership, via `same' x y := same (φ x) (φ y)`,
`part' x := part (φ x)`.  The three `ncard`-valued clauses (the two balance bounds, the
`≤1`-odd clause) transport because `φ`'s underlying `Equiv` sends each relevant class
bijectively (`Set.ncard_preimage_of_injective_subset_range`, `φ` total and injective). -/
theorem IsBalCBUnion.map_iso {G : SimpleGraph V} {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (φ : G ≃g H) (hH : IsBalCBUnion H) : IsBalCBUnion G := by
  classical
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  have hpre : ∀ s : Set W, (φ.toEquiv ⁻¹' s).ncard = s.ncard := by
    intro s
    exact Set.ncard_preimage_of_injective_subset_range φ.toEquiv.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ s)
  refine ⟨fun a b => same (φ a) (φ b), fun a => part (φ a),
    ⟨fun a => hequiv.refl _, fun h => hequiv.symm h, fun h1 h2 => hequiv.trans h1 h2⟩,
    fun a b => by dsimp only; rw [← φ.map_rel_iff, hbip], ?_, ?_, ?_⟩
  · intro a
    have h1 := hbal1 (φ a)
    have heq1 : {b : V | same (φ a) (φ b) ∧ part (φ b) = true} =
        φ.toEquiv ⁻¹' {b : W | same (φ a) b ∧ part b = true} := by ext b; simp
    have heq2 : {b : V | same (φ a) (φ b) ∧ part (φ b) = false} =
        φ.toEquiv ⁻¹' {b : W | same (φ a) b ∧ part b = false} := by ext b; simp
    rw [heq1, heq2, hpre, hpre]
    exact h1
  · intro a
    have h2 := hbal2 (φ a)
    have heq1 : {b : V | same (φ a) (φ b) ∧ part (φ b) = true} =
        φ.toEquiv ⁻¹' {b : W | same (φ a) b ∧ part b = true} := by ext b; simp
    have heq2 : {b : V | same (φ a) (φ b) ∧ part (φ b) = false} =
        φ.toEquiv ⁻¹' {b : W | same (φ a) b ∧ part b = false} := by ext b; simp
    rw [heq1, heq2, hpre, hpre]
    exact h2
  · intro a b hOa hOb
    have heqA : {c : V | same (φ a) (φ c)} = φ.toEquiv ⁻¹' {c : W | same (φ a) c} := by
      ext c; simp
    have heqB : {c : V | same (φ b) (φ c)} = φ.toEquiv ⁻¹' {c : W | same (φ b) c} := by
      ext c; simp
    rw [heqA, hpre] at hOa
    rw [heqB, hpre] at hOb
    exact hodd (φ a) (φ b) hOa hOb

/-! `stmt6_ms_eq_iso` — appears at the end of this file (its construction note above,
and `IsBalCBUnion.map_iso` which it uses, both stay here). -/

/-! ### `stmt6_ms_eq_iso_labelled` — the literal public statement
(`G ≅ K_{⌈n/2⌉,⌊n/2⌋}` with the parts explicitly
labelled, not the existential `∃ a b` form of `stmt6_ms_eq_iso`). Derived by the arithmetic fact
`a+b=n ∧ (a=b ∨ a=b+1 ∨ b=a+1) ⟹ {a,b} = {⌈n/2⌉,⌊n/2⌋}` (`⌈n/2⌉ := (n+1)/2` exactly, Nat
division), a straight `omega` computation once the case is fixed; the one case where the
existential witness has the parts in the wrong order (`b=a+1`, i.e. the SMALLER part first) is
corrected via `completeBipartiteGraph_swap` below. -/

/-- **Swap symmetry of `completeBipartiteGraph`.**  Swapping the two part-types is a graph
isomorphism, via `Equiv.sumComm` checked directly against the `isLeft`/`isRight` adjacency
formula. Small, reusable, not specific to this file's `Fin`-indexed use. -/
def completeBipartiteGraph_swap (α β : Type*) :
    completeBipartiteGraph α β ≃g completeBipartiteGraph β α := by
  refine ⟨Equiv.sumComm α β, ?_⟩
  intro x y
  rcases x with x | x <;> rcases y with y | y <;> simp [completeBipartiteGraph_adj]

/-! `stmt6_ms_eq_iso_labelled` — appears at the end of this file. -/

/-! ### Boundary remarks, `n ∈ {1,2}` (stated separately, never folded into
the `n ≥ 3` iff above): `K_1` (`n = 1`) has diameter `0`, not `2`, and `K_2` (`n = 2`) has
diameter `1`, not `2` — no diameter-2-critical graph exists at either `n = 1` or `n = 2`. -/

/-- **`n = 1` boundary fact.**  No graph on `1` vertex is diameter-2-critical: `IsD2`'s
"some pair at distance `2`" clause needs a distinct pair, and a `1`-vertex type has none. -/
theorem boundary_n1_no_d2c (G : SimpleGraph V) (hn : Fintype.card V = 1) :
    ¬ Erdos742.IsDiameter2Critical G := by
  intro hD
  rw [← isD2C_iff_isDiameter2Critical] at hD
  obtain ⟨⟨-, x, y, hxy, -⟩, -⟩ := hD
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hxy (Subsingleton.elim x y)

/-- **`n = 2` boundary fact.**  No graph on `2` vertices is diameter-2-critical: the only two
graphs on `2` labelled vertices are `K_2` (diameter `1`: the one pair is adjacent, so `IsD2`'s
"some non-adjacent pair" clause fails) and `2K_1` (diameter `∞`: the one pair is at distance
`> 2`, so `IsD2`'s "everything within `2`" clause fails, witnessed directly since a length-`2`
walk between the pair would need a third vertex, and there is none). -/
theorem boundary_n2_no_d2c (G : SimpleGraph V) (hn : Fintype.card V = 2) :
    ¬ Erdos742.IsDiameter2Critical G := by
  classical
  intro hD
  rw [← isD2C_iff_isDiameter2Critical] at hD
  obtain ⟨⟨hall, x, y, hxy, hnadj⟩, -⟩ := hD
  have hVxy : ∀ z : V, z = x ∨ z = y := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hzx, hzy⟩ := hc
    have hnmem1 : y ∉ ({z} : Finset V) := by simpa using hzy.symm
    have hnmem2 : x ∉ (insert y ({z} : Finset V)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hxy, hzx.symm⟩
    have h3 : ({x, y, z} : Finset V).card = 3 := by
      show (insert x (insert y ({z} : Finset V))).card = 3
      rw [Finset.card_insert_of_notMem hnmem2, Finset.card_insert_of_notMem hnmem1,
        Finset.card_singleton]
    have h3le : ({x, y, z} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
    omega
  obtain ⟨m, hxm, hmy⟩ := ((hall x y).resolve_left hxy).resolve_left hnadj
  rcases hVxy m with rfl | rfl
  · exact G.irrefl hxm
  · exact hnadj hxm

/-! ### The extension configuration

The analysis of a tight edge lives in the extension configuration: fix `H` on a
vertex type `W`, adjoin two NEW vertices
`u, v ∉ V(H)` with `{u,v} ∈ E(F)`, `N_F(u) = {v} ∪ S`, `N_F(v) = {u} ∪ T` for
arbitrary `S, T ⊆ V(H)`.  Realised here as `W ⊕ Bool`, `u := Sum.inr true`,
`v := Sum.inr false` — this is DIFFERENT machinery from `delPair` (which REMOVES
two vertices from a fixed type); the bridge between the two views is `stepIso`,
near the end of the file. -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `extF H S T` : the extension graph `F = H + u + v`. -/
def extF (H : SimpleGraph W) (S T : Set W) : SimpleGraph (W ⊕ Bool) :=
  SimpleGraph.fromRel (fun x y => match x, y with
    | Sum.inl a, Sum.inl b => H.Adj a b
    | Sum.inl a, Sum.inr true => a ∈ S
    | Sum.inl a, Sum.inr false => a ∈ T
    | Sum.inr true, Sum.inr false => True
    | _, _ => False)

theorem extF_adj_inl_inl (H : SimpleGraph W) (S T : Set W) (a b : W) :
    (extF H S T).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := by
  rw [extF, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h; exact ⟨fun he => h.ne (Sum.inl.inj he), Or.inl h⟩

theorem extF_adj_inl_inr_true (H : SimpleGraph W) (S T : Set W) (a : W) :
    (extF H S T).Adj (Sum.inl a) (Sum.inr true) ↔ a ∈ S := by
  rw [extF, SimpleGraph.fromRel_adj]
  simp only [reduceCtorEq, ne_eq, not_false_eq_true, true_and]
  constructor
  · rintro (h | h)
    · exact h
    · exact h.elim
  · intro h; exact Or.inl h

theorem extF_adj_inr_true_inl (H : SimpleGraph W) (S T : Set W) (a : W) :
    (extF H S T).Adj (Sum.inr true) (Sum.inl a) ↔ a ∈ S := by
  rw [SimpleGraph.adj_comm]; exact extF_adj_inl_inr_true H S T a

theorem extF_adj_inl_inr_false (H : SimpleGraph W) (S T : Set W) (a : W) :
    (extF H S T).Adj (Sum.inl a) (Sum.inr false) ↔ a ∈ T := by
  rw [extF, SimpleGraph.fromRel_adj]
  simp only [reduceCtorEq, ne_eq, not_false_eq_true, true_and]
  constructor
  · rintro (h | h)
    · exact h
    · exact h.elim
  · intro h; exact Or.inl h

theorem extF_adj_inr_false_inl (H : SimpleGraph W) (S T : Set W) (a : W) :
    (extF H S T).Adj (Sum.inr false) (Sum.inl a) ↔ a ∈ T := by
  rw [SimpleGraph.adj_comm]; exact extF_adj_inl_inr_false H S T a

theorem extF_adj_uv (H : SimpleGraph W) (S T : Set W) :
    (extF H S T).Adj (Sum.inr true) (Sum.inr false) := by
  rw [extF, SimpleGraph.fromRel_adj]
  exact ⟨fun he => Bool.noConfusion (Sum.inr.inj he), Or.inl trivial⟩

/-! ### The two counting symbols `W` and `Z`

`W` counts `H`-edges that become unclassified in `F`; `Z` counts `H`-non-edges of
`codeg_H = 0` that lie inside `S` or `T`.  **`Z` counts ALL codegree-`0` non-edges
inside `S` or `T`, same-component ones included** — the narrower "cross-component
pairs only" reading would be false off the family `𝓑` (`P_4`'s `{0,3}` is a
same-component codegree-`0` non-edge in a connected triangle-free graph).
Both definitions use UNION
CHARGING: a pair inside `S ∩ T` is charged once, not twice (the `∨`, not counted separately
per side). -/

/-- The pair-set underlying `W(u,v)` (factored out so proofs can name membership directly,
rather than only through `Wcount`'s `.ncard`): the `H`-edges with both ends in `S`, or both
ends in `T` (union charging), that are unclassified in `F = extF H S T`. -/
def WPairs (H : SimpleGraph W) (S T : Set W) : Set (Sym2 W) :=
  {e | ∃ x y, e = s(x, y) ∧ H.Adj x y ∧ ((x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
    Sym2.map (Sum.inl : W → W ⊕ Bool) e ∉ E0 (extF H S T) ∪ Ew (extF H S T)}

/-- **`W(u,v)`**: the number of `H`-edges with both ends in `S`, or both
ends in `T` (union charging), that are unclassified in `F = extF H S T`. -/
noncomputable def Wcount (H : SimpleGraph W) (S T : Set W) : ℕ := (WPairs H S T).ncard

/-- The pair-set underlying `Z(u,v)` — **note: NOT restricted to cross-component
pairs**: the non-adjacent pairs `{x,y}` of `V(H)` with
`codeg_H(x,y) = 0` and (`{x,y} ⊆ S` or `{x,y} ⊆ T`), union charging. On `H ∈ 𝓑` specifically
this and the cross-component reading coincide (inside a class of `𝓑`, a non-adjacent pair
shares a part and hence has a common neighbour whenever the opposite part is nonempty); that
coincidence is not used here — this definition is stated at the wider generality, so it
stays correct if `H` is ever generalised beyond `𝓑`. -/
def ZPairs (H : SimpleGraph W) (S T : Set W) : Set (Sym2 W) :=
  {e | ∃ x y, e = s(x, y) ∧ x ≠ y ∧ ¬ H.Adj x y ∧ H.commonNeighbors x y = ∅ ∧
    ((x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))}

/-- **`Z(u,v)`**. See `ZPairs` for the underlying set and
the generality note (`P_4`'s `{0,3}` is a same-component codegree-`0` non-edge in a
connected triangle-free graph — a "cross-component pairs only" reading would be false off
the family `𝓑`). -/
noncomputable def Zcount (H : SimpleGraph W) (S T : Set W) : ℕ := (ZPairs H S T).ncard

/-- Membership bridge for `WPairs`, in the style of `mem_E0_iff`/`mem_Ew_iff`/`mem_Anon_iff`
(`Erdos742.lean`'s own pattern for `∃ x y, e = s(x,y) ∧ …`-shaped sets). The third conjunct is
stated via `s(Sum.inl x, Sum.inl y)` (not `Sym2.map (Sum.inl) s(x,y)`, though the two are `rfl`
-equal) so it matches what `cwt_of_adj`/`extF_adj_inl_inl` produce at the use site verbatim. -/
theorem mem_WPairs_iff (H : SimpleGraph W) (S T : Set W) (x y : W) :
    s(x, y) ∈ WPairs H S T ↔
      H.Adj x y ∧ ((x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
        s(Sum.inl x, Sum.inl y) ∉ E0 (extF H S T) ∪ Ew (extF H S T) := by
  constructor
  · rintro ⟨a, b, hab, ha, hst, hcl⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hst, hcl⟩
    · exact ⟨ha.symm, hst.imp And.symm And.symm, hcl⟩
  · rintro ⟨ha, hst, hcl⟩
    exact ⟨x, y, rfl, ha, hst, hcl⟩

/-- Membership bridge for `ZPairs`, mirroring `mem_Anon_iff`'s own `commonNeighbors_symm`
handling of the swapped representative. -/
theorem mem_ZPairs_iff (H : SimpleGraph W) (S T : Set W) (x y : W) :
    s(x, y) ∈ ZPairs H S T ↔
      x ≠ y ∧ ¬ H.Adj x y ∧ H.commonNeighbors x y = ∅ ∧
        ((x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) := by
  constructor
  · rintro ⟨a, b, hab, hne, hnadj, hcn, hst⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hnadj, hcn, hst⟩
    · exact ⟨hne.symm, fun h => hnadj h.symm, by rwa [H.commonNeighbors_symm],
        hst.imp And.symm And.symm⟩
  · rintro ⟨hne, hnadj, hcn, hst⟩
    exact ⟨x, y, rfl, hne, hnadj, hcn, hst⟩

/-! ### The remote-pair lemma -/

/-- **The remote-pair lemma.**  For `H ∈ 𝓑` and `F = extF H S T`, the remote-pair sum of the
`c`-drop (`c(P,F) − c(P,H)`, over all pairs `P` of `V(H)`) evaluates in closed form as
`−(W+Z)`.  Feeds `row04_deletion_decomposition` by rewrite.  Three-way
case split on each pair `P = {x,y}`: `x = y` (drop `0`
trivially, `cwt_diag` both sides); `H`-edge (drop `0` unless `codeg_F(x,y) ≥ 1`, i.e. both
ends in `S` or `T`, in which case the drop is exactly `[unclassified]` — counted by `W`);
`H`-non-edge (drop `0` if `codeg_H ≥ 1` already, since `commonNeighbors_H ⊆ commonNeighbors_F`
keeps it in `Anon` on both sides; drop `[bothST]` if `codeg_H = 0` — counted by `Z`). Needs
only `H ∈ 𝓑`'s triangle-free/codegree-`0`-edges consequence
(`IsBalCBUnion.commonNeighbors_eq_empty_of_adj`), no witness-chasing at all. -/
theorem lemma_rem (H : SimpleGraph W) (hH : IsBalCBUnion H) (S T : Set W) :
    ∑ P : Sym2 W, (cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) P) - cwt H P) =
      -((Wcount H S T : ℤ) + (Zcount H S T : ℤ)) := by
  classical
  have hcn_none : ∀ x y : W, H.commonNeighbors x y = ∅ → ¬ (x ∈ S ∧ y ∈ S) →
      ¬ (x ∈ T ∧ y ∈ T) →
      (extF H S T).commonNeighbors (Sum.inl x) (Sum.inl y) = ∅ := by
    intro x y hHempty hS hT
    ext p
    simp only [Set.mem_empty_iff_false, iff_false, SimpleGraph.mem_commonNeighbors]
    rintro ⟨h1, h2⟩
    rcases p with z | b
    · rw [extF_adj_inl_inl] at h1 h2
      have hz : z ∈ H.commonNeighbors x y := H.mem_commonNeighbors.mpr ⟨h1, h2⟩
      rw [hHempty] at hz; exact hz
    · cases b with
      | true => rw [extF_adj_inl_inr_true] at h1 h2; exact hS ⟨h1, h2⟩
      | false => rw [extF_adj_inl_inr_false] at h1 h2; exact hT ⟨h1, h2⟩
  have hcn_some : ∀ x y : W, (H.commonNeighbors x y).Nonempty →
      ((extF H S T).commonNeighbors (Sum.inl x) (Sum.inl y)).Nonempty := by
    rintro x y ⟨z, hz⟩
    rw [SimpleGraph.mem_commonNeighbors] at hz
    exact ⟨Sum.inl z, (extF H S T).mem_commonNeighbors.mpr
      ⟨(extF_adj_inl_inl H S T x z).mpr hz.1, (extF_adj_inl_inl H S T y z).mpr hz.2⟩⟩
  have hpt_edge : ∀ x y : W, H.Adj x y →
      cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y)) - cwt H s(x, y) =
        if s(x, y) ∈ WPairs H S T then (-1 : ℤ) else 0 := by
    intro x y hadj
    have hmap : Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y) = s(Sum.inl x, Sum.inl y) := rfl
    have hH1 : cwt H s(x, y) = 1 := by
      have hmemE0 : s(x, y) ∈ E0 H ∪ Ew H :=
        Set.mem_union_left _ ((mem_E0_iff H x y).mpr
          ⟨hadj, hH.commonNeighbors_eq_empty_of_adj hadj⟩)
      rw [cwt_of_adj H hadj, if_pos hmemE0]
    have hF1 : (extF H S T).Adj (Sum.inl x) (Sum.inl y) := (extF_adj_inl_inl H S T x y).mpr hadj
    rw [hmap, hH1, cwt_of_adj (extF H S T) hF1, mem_WPairs_iff]
    by_cases hST : (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)
    · by_cases hcl : s(Sum.inl x, Sum.inl y) ∈ E0 (extF H S T) ∪ Ew (extF H S T)
      · rw [if_pos hcl, if_neg (fun h => h.2.2 hcl)]; ring
      · rw [if_neg hcl, if_pos ⟨hadj, hST, hcl⟩]; ring
    · have hE0 : s(Sum.inl x, Sum.inl y) ∈ E0 (extF H S T) :=
        (mem_E0_iff (extF H S T) (Sum.inl x) (Sum.inl y)).mpr
          ⟨hF1, hcn_none x y (hH.commonNeighbors_eq_empty_of_adj hadj)
            (fun h => hST (Or.inl h)) (fun h => hST (Or.inr h))⟩
      rw [if_pos (Set.mem_union_left _ hE0), if_neg (fun h => hST h.2.1)]; ring
  have hpt_nonedge : ∀ x y : W, x ≠ y → ¬ H.Adj x y →
      cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y)) - cwt H s(x, y) =
        if s(x, y) ∈ ZPairs H S T then (-1 : ℤ) else 0 := by
    intro x y hne hnadj
    have hmap : Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y) = s(Sum.inl x, Sum.inl y) := rfl
    have hFnadj : ¬ (extF H S T).Adj (Sum.inl x) (Sum.inl y) := by
      rw [extF_adj_inl_inl]; exact hnadj
    rw [hmap, cwt_of_not_adj H hnadj, cwt_of_not_adj (extF H S T) hFnadj, mem_ZPairs_iff]
    by_cases hcod : H.commonNeighbors x y = ∅
    · by_cases hST : (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)
      · have hAnonH : s(x, y) ∉ Anon H := by
          rw [mem_Anon_iff]; rintro ⟨-, -, hne2⟩; rw [hcod] at hne2
          exact Set.not_nonempty_empty hne2
        have hAnonF : s(Sum.inl x, Sum.inl y) ∈ Anon (extF H S T) := by
          rw [mem_Anon_iff]
          refine ⟨fun h => hne (Sum.inl.inj h), hFnadj, ?_⟩
          rcases hST with ⟨hxS, hyS⟩ | ⟨hxT, hyT⟩
          · exact ⟨Sum.inr true, (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inr_true H S T x).mpr hxS, (extF_adj_inl_inr_true H S T y).mpr hyS⟩⟩
          · exact ⟨Sum.inr false, (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inr_false H S T x).mpr hxT,
                (extF_adj_inl_inr_false H S T y).mpr hyT⟩⟩
        rw [if_neg hAnonH, if_pos hAnonF, if_pos ⟨hne, hnadj, hcod, hST⟩]; ring
      · have hAnonH : s(x, y) ∉ Anon H := by
          rw [mem_Anon_iff]; rintro ⟨-, -, hne2⟩; rw [hcod] at hne2
          exact Set.not_nonempty_empty hne2
        have hAnonF : s(Sum.inl x, Sum.inl y) ∉ Anon (extF H S T) := by
          rw [mem_Anon_iff]; rintro ⟨-, -, hnc⟩
          rw [hcn_none x y hcod (fun h => hST (Or.inl h)) (fun h => hST (Or.inr h))] at hnc
          exact Set.not_nonempty_empty hnc
        rw [if_neg hAnonH, if_neg hAnonF, if_neg (fun h => hST h.2.2.2)]; ring
    · have hAnonH : s(x, y) ∈ Anon H :=
        (mem_Anon_iff H x y).mpr ⟨hne, hnadj, Set.nonempty_iff_ne_empty.mpr hcod⟩
      have hAnonF : s(Sum.inl x, Sum.inl y) ∈ Anon (extF H S T) :=
        (mem_Anon_iff _ _ _).mpr ⟨fun h => hne (Sum.inl.inj h), hFnadj,
          hcn_some x y (Set.nonempty_iff_ne_empty.mpr hcod)⟩
      rw [if_pos hAnonH, if_pos hAnonF, if_neg (fun h => hcod h.2.2.1)]; ring
  have hpt : ∀ P : Sym2 W,
      cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) P) - cwt H P =
        (if P ∈ WPairs H S T then (-1 : ℤ) else 0) +
        (if P ∈ ZPairs H S T then (-1 : ℤ) else 0) := by
    intro P
    induction P using Sym2.ind with
    | _ x y =>
      by_cases hxy : x = y
      · subst hxy
        have hmap : Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, x) = s(Sum.inl x, Sum.inl x) := rfl
        rw [hmap, cwt_diag, cwt_diag,
          if_neg (fun h => H.irrefl ((mem_WPairs_iff H S T x x).mp h).1),
          if_neg (fun h => ((mem_ZPairs_iff H S T x x).mp h).1 rfl)]
        ring
      · by_cases hadj : H.Adj x y
        · have hZfalse : s(x, y) ∉ ZPairs H S T :=
            fun h => ((mem_ZPairs_iff H S T x y).mp h).2.1 hadj
          rw [hpt_edge x y hadj, if_neg hZfalse, add_zero]
        · have hWfalse : s(x, y) ∉ WPairs H S T :=
            fun h => hadj ((mem_WPairs_iff H S T x y).mp h).1
          rw [hpt_nonedge x y hxy hadj, if_neg hWfalse, zero_add]
  have hsum_ncard : ∀ Qp : Sym2 W → Prop,
      (∑ P : Sym2 W, if Qp P then (1 : ℤ) else 0) = (({P | Qp P} : Set (Sym2 W)).ncard : ℤ) := by
    intro Qp
    -- explicit type ascription on `h` drives unification of `sum_ite_filter_eq_ncard`'s
    -- PLAIN-implicit decidability arguments (these are deliberately plain, not instance,
    -- implicits — so they need an expected type to unify against rather than a typeclass
    -- search).
    have h : (∑ a ∈ (Finset.univ : Finset (Sym2 W)).filter (fun _ : Sym2 W => True),
        if Qp a then (1 : ℤ) else 0) = (({a | Qp a} : Set (Sym2 W)).ncard : ℤ) :=
      sum_ite_filter_eq_ncard (fun a _ => trivial)
    rwa [Finset.filter_true] at h
  have hWsumPos : (∑ P : Sym2 W, if P ∈ WPairs H S T then (1 : ℤ) else 0) =
      (Wcount H S T : ℤ) := hsum_ncard (fun P => P ∈ WPairs H S T)
  have hZsumPos : (∑ P : Sym2 W, if P ∈ ZPairs H S T then (1 : ℤ) else 0) =
      (Zcount H S T : ℤ) := hsum_ncard (fun P => P ∈ ZPairs H S T)
  have hWsumNeg : (∑ P : Sym2 W, if P ∈ WPairs H S T then (-1 : ℤ) else 0) =
      -(Wcount H S T : ℤ) := by
    have step : (∑ P : Sym2 W, if P ∈ WPairs H S T then (-1 : ℤ) else 0) =
        ∑ P : Sym2 W, -(if P ∈ WPairs H S T then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl (fun P _ => by split <;> ring)
    rw [step, Finset.sum_neg_distrib, hWsumPos]
  have hZsumNeg : (∑ P : Sym2 W, if P ∈ ZPairs H S T then (-1 : ℤ) else 0) =
      -(Zcount H S T : ℤ) := by
    have step : (∑ P : Sym2 W, if P ∈ ZPairs H S T then (-1 : ℤ) else 0) =
        ∑ P : Sym2 W, -(if P ∈ ZPairs H S T then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl (fun P _ => by split <;> ring)
    rw [step, Finset.sum_neg_distrib, hZsumPos]
  calc ∑ P : Sym2 W, (cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) P) - cwt H P)
      = ∑ P : Sym2 W, ((if P ∈ WPairs H S T then (-1 : ℤ) else 0) +
          (if P ∈ ZPairs H S T then (-1 : ℤ) else 0)) := Finset.sum_congr rfl (fun P _ => hpt P)
    _ = (∑ P : Sym2 W, if P ∈ WPairs H S T then (-1 : ℤ) else 0) +
        (∑ P : Sym2 W, if P ∈ ZPairs H S T then (-1 : ℤ) else 0) := Finset.sum_add_distrib
    _ = -(Wcount H S T : ℤ) + -(Zcount H S T : ℤ) := by rw [hWsumNeg, hZsumNeg]
    _ = -((Wcount H S T : ℤ) + (Zcount H S T : ℤ)) := by ring

/-! ### The swallow lemma: fully-absorbed components -/

/-- No `p` witnesses `{x,y}` at `x` in `F`, given `x`'s whole `H`-reachability class lies in
`S`. Core of the swallow lemma's direct proof: a witness candidate
`p = Sum.inl q` is forced (by `y` itself lying in the singleton `commonNeighbors`) to have
`H.Adj q y`, hence `q` is reachable from `x` too, hence `q ∈ S` — but then `u` is ALSO a
common neighbour of `x` and `q`, breaking the required singleton. `p = u` is excluded directly
(`x ∈ S` makes it adjacent). `p = v` is excluded the same way as `p = Sum.inl q ∈ S`, using
`u` as the second common neighbour. -/
theorem no_witAt_of_swallow_S (H : SimpleGraph W) (S T : Set W) {x y : W} (hxy : H.Adj x y)
    (hS : ∀ z, H.Reachable x z → z ∈ S) :
    WitAt (extF H S T) (Sum.inl x) (Sum.inl y) = ∅ := by
  have hxS : x ∈ S := hS x (SimpleGraph.Reachable.refl x)
  ext p
  simp only [Set.mem_empty_iff_false, iff_false, WitAt, Set.mem_setOf_eq, IsWitAt]
  rintro ⟨-, hpnadj, hpcn⟩
  have hymem : Sum.inl y ∈ (extF H S T).commonNeighbors (Sum.inl x) p := by
    rw [hpcn]; exact Set.mem_singleton _
  rw [SimpleGraph.mem_commonNeighbors] at hymem
  obtain ⟨-, hyp⟩ := hymem
  rcases p with q | b
  · rw [extF_adj_inl_inl] at hyp
    have hqS : q ∈ S := hS q (hxy.reachable.trans hyp.symm.reachable)
    have humem : Sum.inr true ∈ (extF H S T).commonNeighbors (Sum.inl x) (Sum.inl q) := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨(extF_adj_inl_inr_true H S T x).mpr hxS, (extF_adj_inl_inr_true H S T q).mpr hqS⟩
    rw [hpcn] at humem
    exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
  · cases b
    · have humem : Sum.inr true ∈ (extF H S T).commonNeighbors (Sum.inl x) (Sum.inr false) := by
        rw [SimpleGraph.mem_commonNeighbors]
        exact ⟨(extF_adj_inl_inr_true H S T x).mpr hxS, (extF_adj_uv H S T).symm⟩
      rw [hpcn] at humem
      exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
    · exact hpnadj ((extF_adj_inl_inr_true H S T x).mpr hxS)

/-- The `T`-mirror of `no_witAt_of_swallow_S`. -/
theorem no_witAt_of_swallow_T (H : SimpleGraph W) (S T : Set W) {x y : W} (hxy : H.Adj x y)
    (hT : ∀ z, H.Reachable x z → z ∈ T) :
    WitAt (extF H S T) (Sum.inl x) (Sum.inl y) = ∅ := by
  have hxT : x ∈ T := hT x (SimpleGraph.Reachable.refl x)
  ext p
  simp only [Set.mem_empty_iff_false, iff_false, WitAt, Set.mem_setOf_eq, IsWitAt]
  rintro ⟨-, hpnadj, hpcn⟩
  have hymem : Sum.inl y ∈ (extF H S T).commonNeighbors (Sum.inl x) p := by
    rw [hpcn]; exact Set.mem_singleton _
  rw [SimpleGraph.mem_commonNeighbors] at hymem
  obtain ⟨-, hyp⟩ := hymem
  rcases p with q | b
  · rw [extF_adj_inl_inl] at hyp
    have hqT : q ∈ T := hT q (hxy.reachable.trans hyp.symm.reachable)
    have hvmem : Sum.inr false ∈ (extF H S T).commonNeighbors (Sum.inl x) (Sum.inl q) := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨(extF_adj_inl_inr_false H S T x).mpr hxT, (extF_adj_inl_inr_false H S T q).mpr hqT⟩
    rw [hpcn] at hvmem
    exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)
  · cases b
    · exact hpnadj ((extF_adj_inl_inr_false H S T x).mpr hxT)
    · have hvmem : Sum.inr false ∈ (extF H S T).commonNeighbors (Sum.inl x) (Sum.inr true) := by
        rw [SimpleGraph.mem_commonNeighbors]
        exact ⟨(extF_adj_inl_inr_false H S T x).mpr hxT, extF_adj_uv H S T⟩
      rw [hpcn] at hvmem
      exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)

/-- **The swallow lemma, first half**: if `x`'s whole `H`-reachability
class lies in `S` or in `T`, the `H`-edge `{x,y}` is unclassified in `F` — not in `E0(F)`
(codegree `≥ 1`, since `x, y` share the common neighbour `u` or `v`) and not in `Ew(F)`
(no witness at either endpoint, `no_witAt_of_swallow_S`/`_T` applied at `x` and, by symmetry
of `Reachable`, at `y`). -/
theorem lemma_swallow_edge (H : SimpleGraph W) (S T : Set W) {x y : W} (hxy : H.Adj x y)
    (hclosed : (∀ z, H.Reachable x z → z ∈ S) ∨ (∀ z, H.Reachable x z → z ∈ T)) :
    Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y) ∉ E0 (extF H S T) ∪ Ew (extF H S T) := by
  have hmap : Sym2.map (Sum.inl : W → W ⊕ Bool) s(x, y) = s(Sum.inl x, Sum.inl y) := rfl
  rw [hmap, Set.mem_union, mem_E0_iff, mem_Ew_iff, not_or]
  have hclosedY : (∀ z, H.Reachable y z → z ∈ S) ∨ (∀ z, H.Reachable y z → z ∈ T) := by
    rcases hclosed with hS | hT
    · exact Or.inl (fun z hz => hS z (hxy.reachable.trans hz))
    · exact Or.inr (fun z hz => hT z (hxy.reachable.trans hz))
  have hcodeg : ((extF H S T).commonNeighbors (Sum.inl x) (Sum.inl y)).Nonempty := by
    rcases hclosed with hS | hT
    · have hxS : x ∈ S := hS x (SimpleGraph.Reachable.refl x)
      have hyS : y ∈ S := hS y hxy.reachable
      exact ⟨Sum.inr true, (extF H S T).mem_commonNeighbors.mpr
        ⟨(extF_adj_inl_inr_true H S T x).mpr hxS, (extF_adj_inl_inr_true H S T y).mpr hyS⟩⟩
    · have hxT : x ∈ T := hT x (SimpleGraph.Reachable.refl x)
      have hyT : y ∈ T := hT y hxy.reachable
      exact ⟨Sum.inr false, (extF H S T).mem_commonNeighbors.mpr
        ⟨(extF_adj_inl_inr_false H S T x).mpr hxT, (extF_adj_inl_inr_false H S T y).mpr hyT⟩⟩
  have hWit : Wit (extF H S T) (Sum.inl x) (Sum.inl y) = ∅ := by
    rw [Wit]
    have h1 : WitAt (extF H S T) (Sum.inl x) (Sum.inl y) = ∅ := by
      rcases hclosed with hS | hT
      · exact no_witAt_of_swallow_S H S T hxy hS
      · exact no_witAt_of_swallow_T H S T hxy hT
    have h2 : WitAt (extF H S T) (Sum.inl y) (Sum.inl x) = ∅ := by
      rcases hclosedY with hS | hT
      · exact no_witAt_of_swallow_S H S T hxy.symm hS
      · exact no_witAt_of_swallow_T H S T hxy.symm hT
    rw [h1, h2, Set.union_empty]
  constructor
  · rintro ⟨-, hce⟩
    exact absurd hce (Set.nonempty_iff_ne_empty.mp hcodeg)
  · rintro ⟨-, -, hwne⟩
    exact absurd hWit (Set.nonempty_iff_ne_empty.mp hwne)

/-! ### The swallow lemma, second half -/

/-- **The swallow lemma, second half.**  `W = 0` forces every fully-swallowed component of an
`H ∈ 𝓑` to be `K_1`.  Connects `lemma_swallow_edge` (the first half) to `W`
via `IsBalCBUnion`'s own structure: a `same`-class of size `≥ 2` is forced, by BALANCE, to
contain vertices of both `part` values (if one side were empty the balance clause would cap
the whole class at size `1`), hence an internal `H`-edge — which the first half shows is
counted by `W` once the whole class lies in `S` or `T`.  Takes `(same, part)` as bare
witnesses, matching `same_of_reachable`'s established pattern in this file rather than the
packaged `IsBalCBUnion`. -/
theorem lemma_swallow_component (H : SimpleGraph W) (S T : Set W) {same : W → W → Prop}
    {part : W → Bool} (hequiv : Equivalence same)
    (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (hW0 : Wcount H S T = 0) {x : W}
    (hclosed : (∀ z, same x z → z ∈ S) ∨ (∀ z, same x z → z ∈ T)) :
    ∀ y, same x y → y = x := by
  classical
  intro y hxy
  by_contra hne
  have hne' : x ≠ y := fun h => hne h.symm
  have key : ∀ a b : W, same x a → same x b → part a ≠ part b → H.Adj a b :=
    fun a b ha hb hab => (hbip a b).mpr ⟨hequiv.trans (hequiv.symm ha) hb, hab⟩
  obtain ⟨p, q, hxp, hxq, hpq⟩ : ∃ p q, same x p ∧ same x q ∧ H.Adj p q := by
    by_cases hpxy : part x = part y
    · have h2le : 2 ≤ {b : W | same x b ∧ part b = part x}.ncard := by
        have hsub : ({x, y} : Set W) ⊆ {b : W | same x b ∧ part b = part x} := by
          intro z hz
          rcases hz with rfl | rfl
          · exact ⟨hequiv.refl _, rfl⟩
          · exact ⟨hxy, hpxy.symm⟩
        calc (2 : ℕ) = ({x, y} : Set W).ncard := (Set.ncard_pair hne').symm
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hopp_pos : 0 < {b : W | same x b ∧ part b ≠ part x}.ncard := by
        -- ⚠ `by_cases` on the PROP `part x = true` (not `cases hpx : part x`, which
        -- SUBSTITUTES `part x` throughout the goal and breaks the `rw [heqN]` steps
        -- below).
        by_cases hpx : part x = true
        · have heq1 : {b : W | same x b ∧ part b = part x} =
              {b : W | same x b ∧ part b = true} := by rw [hpx]
          have heq2 : {b : W | same x b ∧ part b ≠ part x} =
              {b : W | same x b ∧ part b = false} := by
            rw [hpx]; ext z; simp
          rw [heq1] at h2le; rw [heq2]; have := hbal1 x; omega
        · have hpxf : part x = false := Bool.eq_false_iff.mpr hpx
          have heq1 : {b : W | same x b ∧ part b = part x} =
              {b : W | same x b ∧ part b = false} := by rw [hpxf]
          have heq2 : {b : W | same x b ∧ part b ≠ part x} =
              {b : W | same x b ∧ part b = true} := by
            rw [hpxf]; ext z; simp
          rw [heq1] at h2le; rw [heq2]; have := hbal2 x; omega
      obtain ⟨r, hr⟩ := Set.nonempty_of_ncard_ne_zero
        (show {b : W | same x b ∧ part b ≠ part x}.ncard ≠ 0 by omega)
      exact ⟨x, r, hequiv.refl x, hr.1, key x r (hequiv.refl x) hr.1 (fun h => hr.2 h.symm)⟩
    · exact ⟨x, y, hequiv.refl x, hxy, key x y (hequiv.refl x) hxy hpxy⟩
  have hclosed_p : (∀ z, H.Reachable p z → z ∈ S) ∨ (∀ z, H.Reachable p z → z ∈ T) := by
    rcases hclosed with hS | hT
    · exact Or.inl (fun z hz => hS z (hequiv.trans hxp (same_of_reachable hbip hequiv hz)))
    · exact Or.inr (fun z hz => hT z (hequiv.trans hxp (same_of_reachable hbip hequiv hz)))
  have hunc := lemma_swallow_edge H S T hpq hclosed_p
  have hmemW : (p ∈ S ∧ q ∈ S) ∨ (p ∈ T ∧ q ∈ T) := by
    rcases hclosed with hS | hT
    · exact Or.inl ⟨hS p hxp, hS q hxq⟩
    · exact Or.inr ⟨hT p hxp, hT q hxq⟩
  have hmemSet : s(p, q) ∈ WPairs H S T := ⟨p, q, rfl, hpq, hmemW, hunc⟩
  have hWpos : 0 < Wcount H S T :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(p, q), hmemSet⟩
  omega

/-! ### The witness criteria: K-u, K3, PST-W
Which edges at `u`, at `v`, and `{u,v}` itself are classified.  Standing context throughout:
`H ∈ 𝓑` on `W`, `F = extF H S T`, `u := Sum.inr true`, `v := Sum.inr false`. -/

/-- **The witness criterion at `u` (LEMMA K-u)**.
For `w ∈ S`, `{u,w}` is not unclassified in `F = extF H S T` iff at least one of
four clauses: (a) codegree `0`; (b) witness at `u`; (c) witness at `w` via `v`; (d) witness at
`w` via a different-`same`-class `S`-vertex (the family-reduced form).  Unlike `lemma_K3`,
clause (d) genuinely consumes `H ∈ 𝓑`'s structure (complete-bipartite-per-class AND balance —
the `claim` sub-lemma below needs balance to rule out a same-part class of size `≥ 2` with an
empty opposite part).  The symmetric statement for `w ∈ T` is `S ↔ T`, `u ↔ v`. -/
theorem lemma_Ku (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W) {w : W} (hwS : w ∈ S) :
    s(Sum.inr true, Sum.inl w) ∈ E0 (extF H S T) ∪ Ew (extF H S T) ↔
      (H.neighborSet w ∩ S = ∅ ∧ w ∉ T) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {w}) ∨
      (w ∉ T ∧ H.neighborSet w ∩ T = ∅) ∨
      (∃ q : W, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ (w ∉ T ∨ q ∉ T)) := by
  classical
  have huw : (extF H S T).Adj (Sum.inr true) (Sum.inl w) :=
    (extF_adj_inr_true_inl H S T w).mpr hwS
  have claim : ∀ q : W, q ≠ w → ¬ H.Adj q w → H.commonNeighbors w q = ∅ → ¬ same w q := by
    intro q hqw hnadj hcn hsame
    have hpq : part q = part w := by
      by_contra hne
      exact hnadj ((hbip q w).mpr ⟨hequiv.symm hsame, hne⟩)
    have h2le : 2 ≤ {b : W | same w b ∧ part b = part w}.ncard := by
      have hsub : ({w, q} : Set W) ⊆ {b : W | same w b ∧ part b = part w} := by
        intro z hz
        rcases hz with rfl | rfl
        · exact ⟨hequiv.refl _, rfl⟩
        · exact ⟨hsame, hpq⟩
      calc (2 : ℕ) = ({w, q} : Set W).ncard := (Set.ncard_pair hqw.symm).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hopp_pos : 0 < {b : W | same w b ∧ part b ≠ part w}.ncard := by
      by_cases hpx : part w = true
      · have heq1 : {b : W | same w b ∧ part b = part w} =
            {b : W | same w b ∧ part b = true} := by rw [hpx]
        have heq2 : {b : W | same w b ∧ part b ≠ part w} =
            {b : W | same w b ∧ part b = false} := by rw [hpx]; ext z; simp
        rw [heq1] at h2le; rw [heq2]; have := hbal1 w; omega
      · have hpxf : part w = false := Bool.eq_false_iff.mpr hpx
        have heq1 : {b : W | same w b ∧ part b = part w} =
            {b : W | same w b ∧ part b = false} := by rw [hpxf]
        have heq2 : {b : W | same w b ∧ part b ≠ part w} =
            {b : W | same w b ∧ part b = true} := by rw [hpxf]; ext z; simp
        rw [heq1] at h2le; rw [heq2]; have := hbal2 w; omega
    obtain ⟨r, hr⟩ := Set.nonempty_of_ncard_ne_zero
      (show {b : W | same w b ∧ part b ≠ part w}.ncard ≠ 0 by omega)
    have hrw : H.Adj w r := (hbip w r).mpr ⟨hr.1, hr.2.symm⟩
    have hrq : H.Adj q r := (hbip q r).mpr
      ⟨hequiv.trans (hequiv.symm hsame) hr.1, by rw [hpq]; exact hr.2.symm⟩
    have hrmem : r ∈ H.commonNeighbors w q := H.mem_commonNeighbors.mpr ⟨hrw, hrq⟩
    rw [hcn] at hrmem
    exact hrmem
  rw [Set.mem_union, mem_E0_iff, mem_Ew_iff]
  constructor
  · rintro (⟨-, hcn0⟩ | ⟨-, -, hwit⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have hxmem : Sum.inl x ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl w) :=
          (extF H S T).mem_commonNeighbors.mpr
            ⟨(extF_adj_inr_true_inl H S T x).mpr hx.2, (extF_adj_inl_inl H S T w x).mpr hx.1⟩
        rw [hcn0] at hxmem; exact hxmem
      · intro hT
        have hvmem : Sum.inr false ∈
            (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl w) := by
          rw [SimpleGraph.mem_commonNeighbors]
          exact ⟨extF_adj_uv H S T, (extF_adj_inl_inr_false H S T w).mpr hT⟩
        rw [hcn0] at hvmem; exact hvmem
    · obtain ⟨p, hp | hp⟩ := hwit
      · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
        have hpnev : p ≠ Sum.inr false := by rintro rfl; exact hpnadj (extF_adj_uv H S T)
        obtain ⟨x, rfl⟩ : ∃ x, p = Sum.inl x := by
          rcases p with x | b
          · exact ⟨x, rfl⟩
          · cases b
            · exact absurd rfl hpnev
            · exact absurd rfl hpne
        have hxS : x ∉ S := fun h => hpnadj ((extF_adj_inr_true_inl H S T x).mpr h)
        have hwmem : Sum.inl w ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) := by
          rw [hpcn]; exact Set.mem_singleton _
        rw [SimpleGraph.mem_commonNeighbors] at hwmem
        have hxwH : H.Adj x w := (extF_adj_inl_inl H S T x w).mp hwmem.2
        have hxT : x ∉ T := by
          intro hT
          have hvmem : Sum.inr false ∈
              (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) := by
            rw [SimpleGraph.mem_commonNeighbors]
            exact ⟨extF_adj_uv H S T, (extF_adj_inl_inr_false H S T x).mpr hT⟩
          rw [hpcn] at hvmem
          exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)
        refine Or.inr (Or.inl ⟨x, hxS, hxT, ?_⟩)
        ext z
        rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hzx, hzS⟩
          have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) :=
            (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inr_true_inl H S T z).mpr hzS, (extF_adj_inl_inl H S T x z).mpr hzx⟩
          rw [hpcn] at hzmem
          exact Sum.inl.inj (Set.mem_singleton_iff.mp hzmem)
        · rintro rfl
          exact ⟨hxwH, hwS⟩
      · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
        have hune : Sum.inr true ∈ (extF H S T).commonNeighbors (Sum.inl w) p := by
          rw [hpcn]; exact Set.mem_singleton _
        rw [SimpleGraph.mem_commonNeighbors] at hune
        obtain ⟨-, hpu⟩ := hune
        rcases p with x | b
        · have hxS : x ∈ S := (extF_adj_inl_inr_true H S T x).mp hpu
          have hxwne : x ≠ w := fun h => hpne (congrArg Sum.inl h)
          have hqnadjWw : ¬ H.Adj x w := fun h =>
            hpnadj ((extF_adj_inl_inl H S T w x).mpr h.symm)
          have hcn0' : H.commonNeighbors w x = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro z hz
            rw [SimpleGraph.mem_commonNeighbors] at hz
            have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inl w) (Sum.inl x) :=
              (extF H S T).mem_commonNeighbors.mpr
                ⟨(extF_adj_inl_inl H S T w z).mpr hz.1, (extF_adj_inl_inl H S T x z).mpr hz.2⟩
            rw [hpcn] at hzmem
            exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
          have hnsame : ¬ same w x := claim x hxwne hqnadjWw hcn0'
          have hwT_or : w ∉ T ∨ x ∉ T := by
            by_contra hcon
            push_neg at hcon
            obtain ⟨hwT, hxT⟩ := hcon
            have hvmem : Sum.inr false ∈
                (extF H S T).commonNeighbors (Sum.inl w) (Sum.inl x) := by
              rw [SimpleGraph.mem_commonNeighbors]
              exact ⟨(extF_adj_inl_inr_false H S T w).mpr hwT,
                (extF_adj_inl_inr_false H S T x).mpr hxT⟩
            rw [hpcn] at hvmem
            exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)
          exact Or.inr (Or.inr (Or.inr ⟨x, hxS, hxwne, hnsame, hwT_or⟩))
        · cases b
          · have hwT : w ∉ T := fun hT => hpnadj ((extF_adj_inl_inr_false H S T w).mpr hT)
            refine Or.inr (Or.inr (Or.inl ⟨hwT, ?_⟩))
            rw [Set.eq_empty_iff_forall_notMem]
            intro z hz
            rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hz
            have hzmem : Sum.inl z ∈
                (extF H S T).commonNeighbors (Sum.inl w) (Sum.inr false) :=
              (extF H S T).mem_commonNeighbors.mpr
                ⟨(extF_adj_inl_inl H S T w z).mpr hz.1, (extF_adj_inr_false_inl H S T z).mpr hz.2⟩
            rw [hpcn] at hzmem
            exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
          · exact absurd hpu (extF H S T).irrefl
  · intro hdisj
    by_cases hcn0 : (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl w) = ∅
    · exact Or.inl ⟨huw, hcn0⟩
    · right
      refine ⟨huw, Set.nonempty_iff_ne_empty.mpr hcn0, ?_⟩
      rcases hdisj with ⟨hempty, hnT⟩ | ⟨p, hpS, hpT, hpsingle⟩ | ⟨hnTw, hTempty⟩ |
        ⟨q, hqS, hqw, hnsame, hTor⟩
      · exfalso; apply hcn0
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        rw [SimpleGraph.mem_commonNeighbors] at hz
        rcases z with x | b
        · obtain ⟨hz1, hz2⟩ := hz
          rw [extF_adj_inr_true_inl] at hz1
          rw [extF_adj_inl_inl] at hz2
          exact (Set.eq_empty_iff_forall_notMem.mp hempty) x ⟨hz2, hz1⟩
        · cases b
          · exact hnT ((extF_adj_inl_inr_false H S T w).mp hz.2)
          · exact (extF H S T).irrefl hz.1
      · refine ⟨Sum.inl p,
          Or.inl ⟨by simp, fun h => hpS ((extF_adj_inr_true_inl H S T p).mp h), ?_⟩⟩
        ext z
        rw [SimpleGraph.mem_commonNeighbors, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hz1, hz2⟩
          rcases z with y | b
          · rw [extF_adj_inr_true_inl] at hz1
            rw [extF_adj_inl_inl] at hz2
            have hy : y ∈ H.neighborSet p ∩ S := ⟨hz2, hz1⟩
            rw [hpsingle] at hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
          · cases b
            · exact absurd ((extF_adj_inl_inr_false H S T p).mp hz2) hpT
            · exact absurd hz1 (extF H S T).irrefl
        · rintro hzeq
          rw [hzeq]
          have hwmem : w ∈ H.neighborSet p ∩ S := by rw [hpsingle]; exact Set.mem_singleton w
          exact ⟨huw, (extF_adj_inl_inl H S T p w).mpr hwmem.1⟩
      · refine ⟨Sum.inr false, Or.inr
          ⟨by simp, fun h => hnTw ((extF_adj_inl_inr_false H S T w).mp h), ?_⟩⟩
        ext z
        rw [SimpleGraph.mem_commonNeighbors, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hz1, hz2⟩
          rcases z with y | b
          · rw [extF_adj_inl_inl] at hz1
            rw [extF_adj_inr_false_inl] at hz2
            have hy : y ∈ H.neighborSet w ∩ T := ⟨hz1, hz2⟩
            rw [hTempty] at hy
            exact ((Set.mem_empty_iff_false y).mp hy).elim
          · cases b with
            | false => exact absurd ((extF_adj_inl_inr_false H S T w).mp hz1) hnTw
            | true => rfl
        · rintro hzeq
          rw [hzeq]
          exact ⟨(extF_adj_inl_inr_true H S T w).mpr hwS, (extF_adj_uv H S T).symm⟩
      · have hcn_empty : H.commonNeighbors w q = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [SimpleGraph.mem_commonNeighbors] at hz
          have hsz : same w z := ((hbip w z).mp hz.1).1
          have hsqz : same q z := ((hbip q z).mp hz.2).1
          exact hnsame (hequiv.trans hsz (hequiv.symm hsqz))
        refine ⟨Sum.inl q, Or.inr ⟨fun h => hqw (Sum.inl.inj h), ?_, ?_⟩⟩
        · intro hadjwq
          rw [extF_adj_inl_inl] at hadjwq
          exact hnsame ((hbip w q).mp hadjwq).1
        · ext z
          rw [SimpleGraph.mem_commonNeighbors, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hz1, hz2⟩
            rcases z with y | b
            · exfalso
              rw [extF_adj_inl_inl] at hz1 hz2
              have hy : y ∈ H.commonNeighbors w q := H.mem_commonNeighbors.mpr ⟨hz1, hz2⟩
              rw [hcn_empty] at hy
              exact hy
            · cases b
              · exfalso
                rw [extF_adj_inl_inr_false] at hz1 hz2
                rcases hTor with hwT' | hqT'
                · exact hwT' hz1
                · exact hqT' hz2
              · rfl
          · rintro hzeq
            rw [hzeq]
            exact ⟨(extF_adj_inl_inr_true H S T w).mpr hwS,
              (extF_adj_inl_inr_true H S T q).mpr hqS⟩

/-- **The witness criterion for the edge `{u,v}` itself (LEMMA K3)**: it is not
unclassified in `F = extF H S T` iff `S ∩ T = ∅`, or a witness-at-`u` condition
(`∃p∈T∖S, N_H(p)∩S=∅`), or a witness-at-`v` condition (`∃p∈S∖T, N_H(p)∩T=∅`).  Direct
computation, independent of `H ∈ 𝓑` — no `IsBalCBUnion` hypothesis needed. -/
theorem lemma_K3 (H : SimpleGraph W) (S T : Set W) :
    s(Sum.inr true, Sum.inr false) ∈ E0 (extF H S T) ∪ Ew (extF H S T) ↔
      S ∩ T = ∅ ∨
      (∃ p : W, p ∈ T ∧ p ∉ S ∧ H.neighborSet p ∩ S = ∅) ∨
      (∃ p : W, p ∈ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = ∅) := by
  classical
  have huv : (extF H S T).Adj (Sum.inr true) (Sum.inr false) := extF_adj_uv H S T
  rw [Set.mem_union, mem_E0_iff, mem_Ew_iff]
  constructor
  · rintro (⟨-, hcn0⟩ | ⟨-, -, hwit⟩)
    · refine Or.inl (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
      have hxmem : Sum.inl x ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inr false) :=
        (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inr_true_inl H S T x).mpr hx.1, (extF_adj_inr_false_inl H S T x).mpr hx.2⟩
      rw [hcn0] at hxmem; exact hxmem
    · obtain ⟨p, hp | hp⟩ := hwit
      · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
        have hpnev : p ≠ Sum.inr false := by rintro rfl; exact hpnadj huv
        obtain ⟨x, rfl⟩ : ∃ x, p = Sum.inl x := by
          rcases p with x | b
          · exact ⟨x, rfl⟩
          · cases b
            · exact absurd rfl hpnev
            · exact absurd rfl hpne
        have hxS : x ∉ S := fun h => hpnadj ((extF_adj_inr_true_inl H S T x).mpr h)
        refine Or.inr (Or.inl ⟨x, ?_, hxS, ?_⟩)
        · have hv : Sum.inr false ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) := by
            rw [hpcn]; exact Set.mem_singleton _
          rw [SimpleGraph.mem_commonNeighbors] at hv
          exact (extF_adj_inl_inr_false H S T x).mp hv.2
        · rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hz
          have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) :=
            (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inr_true_inl H S T z).mpr hz.2,
                (extF_adj_inl_inl H S T x z).mpr hz.1⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
      · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
        have hpneu : p ≠ Sum.inr true := by rintro rfl; exact hpnadj huv.symm
        obtain ⟨x, rfl⟩ : ∃ x, p = Sum.inl x := by
          rcases p with x | b
          · exact ⟨x, rfl⟩
          · cases b
            · exact absurd rfl hpne
            · exact absurd rfl hpneu
        have hxT : x ∉ T := fun h => hpnadj ((extF_adj_inr_false_inl H S T x).mpr h)
        refine Or.inr (Or.inr ⟨x, ?_, hxT, ?_⟩)
        · have hu : Sum.inr true ∈ (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) := by
            rw [hpcn]; exact Set.mem_singleton _
          rw [SimpleGraph.mem_commonNeighbors] at hu
          exact (extF_adj_inl_inr_true H S T x).mp hu.2
        · rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hz
          have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) :=
            (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inr_false_inl H S T z).mpr hz.2,
                (extF_adj_inl_inl H S T x z).mpr hz.1⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
  · rintro (hST | ⟨p, hpT, hpS, hpN⟩ | ⟨p, hpS, hpT, hpN⟩)
    · left
      refine ⟨huv, Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
      rw [SimpleGraph.mem_commonNeighbors] at hz
      rcases z with x | b
      · exact (Set.eq_empty_iff_forall_notMem.mp hST) x
          ⟨(extF_adj_inr_true_inl H S T x).mp hz.1, (extF_adj_inr_false_inl H S T x).mp hz.2⟩
      · cases b
        · exact (extF H S T).irrefl hz.2
        · exact (extF H S T).irrefl hz.1
    · by_cases hSTe : S ∩ T = ∅
      · left
        refine ⟨huv, Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
        rw [SimpleGraph.mem_commonNeighbors] at hz
        rcases z with x | b
        · exact (Set.eq_empty_iff_forall_notMem.mp hSTe) x
            ⟨(extF_adj_inr_true_inl H S T x).mp hz.1, (extF_adj_inr_false_inl H S T x).mp hz.2⟩
        · cases b
          · exact (extF H S T).irrefl hz.2
          · exact (extF H S T).irrefl hz.1
      · right
        obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hSTe
        refine ⟨huv, ⟨Sum.inl z, (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inr_true_inl H S T z).mpr hz.1, (extF_adj_inr_false_inl H S T z).mpr hz.2⟩⟩,
          Sum.inl p, Or.inl ⟨?_, ?_, ?_⟩⟩
        · simp
        · exact fun h => hpS ((extF_adj_inr_true_inl H S T p).mp h)
        · ext w
          rw [SimpleGraph.mem_commonNeighbors]
          constructor
          · rintro ⟨h1, h2⟩
            rcases w with y | b
            · exfalso
              have hyS : y ∈ S := (extF_adj_inr_true_inl H S T y).mp h1
              have hyN : y ∈ H.neighborSet p := (extF_adj_inl_inl H S T p y).mp h2
              exact (Set.eq_empty_iff_forall_notMem.mp hpN) y ⟨hyN, hyS⟩
            · cases b
              · rfl
              · exact absurd h1 (extF H S T).irrefl
          · rintro rfl
            exact ⟨huv, (extF_adj_inl_inr_false H S T p).mpr hpT⟩
    · by_cases hSTe : S ∩ T = ∅
      · left
        refine ⟨huv, Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
        rw [SimpleGraph.mem_commonNeighbors] at hz
        rcases z with x | b
        · exact (Set.eq_empty_iff_forall_notMem.mp hSTe) x
            ⟨(extF_adj_inr_true_inl H S T x).mp hz.1, (extF_adj_inr_false_inl H S T x).mp hz.2⟩
        · cases b
          · exact (extF H S T).irrefl hz.2
          · exact (extF H S T).irrefl hz.1
      · right
        obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hSTe
        refine ⟨huv, ⟨Sum.inl z, (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inr_true_inl H S T z).mpr hz.1, (extF_adj_inr_false_inl H S T z).mpr hz.2⟩⟩,
          Sum.inl p, Or.inr ⟨?_, ?_, ?_⟩⟩
        · simp
        · exact fun h => hpT ((extF_adj_inr_false_inl H S T p).mp h)
        · ext w
          rw [SimpleGraph.mem_commonNeighbors]
          constructor
          · rintro ⟨h1, h2⟩
            rcases w with y | b
            · exfalso
              have hyT : y ∈ T := (extF_adj_inr_false_inl H S T y).mp h1
              have hyN : y ∈ H.neighborSet p := (extF_adj_inl_inl H S T p y).mp h2
              exact (Set.eq_empty_iff_forall_notMem.mp hpN) y ⟨hyN, hyT⟩
            · cases b
              · exact absurd h1 (extF H S T).irrefl
              · rfl
          · rintro rfl
            exact ⟨huv.symm, (extF_adj_inl_inr_true H S T p).mpr hpS⟩

/-! ### The counting inequality `K ≤ Z + R_c` (LEMMA PST-L2)

Its proof cites only `lemma_Ku`, never PST-W (which follows later).
PST-L2 needs the `w ∈ S∩T` specialization
of `lemma_Ku` on the `u`-side directly, and a symmetric (but NOT identical — clauses (a)/(c) are
vacuous on both sides for a different reason each time) derivation on the `v`-side, built here
without a full `lemma_Kv` mirror (deliberately smaller). -/

/-- Shared component-disjointness fact, extracted top-level so both `lemma_Ku`'s clause (d)
(which keeps its own local copy) and the `v`-side
derivation can use it: inside a `same`-class, `q ≠ w`, `¬H.Adj q w`,
`H.commonNeighbors w q = ∅` forces `¬ same w q`.  Needs BALANCE — a class can only have an
empty opposite part when balance caps it at a single vertex, so two distinct same-class
vertices always have a common neighbour or an edge between them. -/
theorem not_same_of_disjoint_commonNeighbors {H : SimpleGraph W} {same : W → W → Prop}
    {part : W → Bool} (hequiv : Equivalence same)
    (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {w q : W} (hqw : q ≠ w) (hnadj : ¬ H.Adj q w) (hcn : H.commonNeighbors w q = ∅) :
    ¬ same w q := by
  classical
  intro hsame
  have hpq : part q = part w := by
    by_contra hne
    exact hnadj ((hbip q w).mpr ⟨hequiv.symm hsame, hne⟩)
  have h2le : 2 ≤ {b : W | same w b ∧ part b = part w}.ncard := by
    have hsub : ({w, q} : Set W) ⊆ {b : W | same w b ∧ part b = part w} := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨hequiv.refl _, rfl⟩
      · exact ⟨hsame, hpq⟩
    calc (2 : ℕ) = ({w, q} : Set W).ncard := (Set.ncard_pair hqw.symm).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hopp_pos : 0 < {b : W | same w b ∧ part b ≠ part w}.ncard := by
    by_cases hpx : part w = true
    · have heq1 : {b : W | same w b ∧ part b = part w} =
          {b : W | same w b ∧ part b = true} := by rw [hpx]
      have heq2 : {b : W | same w b ∧ part b ≠ part w} =
          {b : W | same w b ∧ part b = false} := by rw [hpx]; ext z; simp
      rw [heq1] at h2le; rw [heq2]; have := hbal1 w; omega
    · have hpxf : part w = false := Bool.eq_false_iff.mpr hpx
      have heq1 : {b : W | same w b ∧ part b = part w} =
          {b : W | same w b ∧ part b = false} := by rw [hpxf]
      have heq2 : {b : W | same w b ∧ part b ≠ part w} =
          {b : W | same w b ∧ part b = true} := by rw [hpxf]; ext z; simp
      rw [heq1] at h2le; rw [heq2]; have := hbal2 w; omega
  obtain ⟨r, hr⟩ := Set.nonempty_of_ncard_ne_zero
    (show {b : W | same w b ∧ part b ≠ part w}.ncard ≠ 0 by omega)
  have hrw : H.Adj w r := (hbip w r).mpr ⟨hr.1, hr.2.symm⟩
  have hrq : H.Adj q r := (hbip q r).mpr
    ⟨hequiv.trans (hequiv.symm hsame) hr.1, by rw [hpq]; exact hr.2.symm⟩
  have hrmem : r ∈ H.commonNeighbors w q := H.mem_commonNeighbors.mpr ⟨hrw, hrq⟩
  rw [hcn] at hrmem
  exact hrmem

/-- **The counting inequality (LEMMA PST-L2)**:
`K(u,v) ≤ Z(u,v) + R_c(u,v)`.  Two injections: for `w ∈ S∩T` with `{u,w}` (resp. `{v,w}`)
witnessed, the `q`-route gives a different-`same`-class vertex `q_w`, and `{w,q_w}` injects
into `ZPairs`; the `p`-route gives an outside vertex `p_w` with `N_H(p_w)∩S = {w}`
(resp. `∩T`), injecting `w ↦ p_w` into the `u`-side (resp. `v`-side) summand of `R_c(u,v)`
(`Rc_eq_sum_ncard`) SEPARATELY — no cross-side collision bookkeeping needed there, since the
two summands are already counted disjointly by that identity. -/
theorem lemma_PST_L2 (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W) :
    Kc (extF H S T) (Sum.inr true) (Sum.inr false) ≤
      Zcount H S T + Rc (extF H S T) (Sum.inr true) (Sum.inr false) := by
  classical
  set F := extF H S T with hFdef
  have hne : (Sum.inr true : W ⊕ Bool) ≠ Sum.inr false := by simp
  have hWuv_eq : ∀ w : W ⊕ Bool, w ∈ Wuv F (Sum.inr true) (Sum.inr false) ↔
      ∃ x, w = Sum.inl x ∧ x ∈ S ∧ x ∈ T := by
    intro w
    rw [Wuv, SimpleGraph.mem_commonNeighbors]
    constructor
    · rintro ⟨h1, h2⟩
      rcases w with x | b
      · exact ⟨x, rfl, (extF_adj_inr_true_inl H S T x).mp h1,
          (extF_adj_inr_false_inl H S T x).mp h2⟩
      · cases b with
        | true => exact absurd h1 F.irrefl
        | false => exact absurd h2 F.irrefl
    · rintro ⟨x, rfl, hxS, hxT⟩
      exact ⟨(extF_adj_inr_true_inl H S T x).mpr hxS, (extF_adj_inr_false_inl H S T x).mpr hxT⟩
  have hKc0 : Kc F (Sum.inr true) (Sum.inr false) =
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr true, w) ∈ Ew F}.ncard +
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr false, w) ∈ Ew F}.ncard :=
    Kc_eq_sum_ncard F hne
  -- One proof for both the `u`-side (`r = true`) and `v`-side (`r = false`) index sets.
  have hIdxEq : ∀ r : Bool,
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr r, w) ∈ Ew F}
      = Sum.inl '' {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr r, Sum.inl x) ∈ Ew F} := by
    intro r
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hw, hEw⟩
      obtain ⟨x, rfl, hxS, hxT⟩ := (hWuv_eq w).mp hw
      exact ⟨x, ⟨hxS, hxT, hEw⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, hxT, hEw⟩, rfl⟩
      exact ⟨(hWuv_eq (Sum.inl x)).mpr ⟨x, rfl, hxS, hxT⟩, hEw⟩
  set AuIdx : Set W := {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr true, Sum.inl x) ∈ Ew F} with hAuIdxDef
  set AvIdx : Set W := {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr false, Sum.inl x) ∈ Ew F} with hAvIdxDef
  have hAuCard : {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr true, w) ∈ Ew F}.ncard = AuIdx.ncard := by
    rw [hIdxEq true, ← hAuIdxDef]; exact Set.ncard_image_of_injective _ Sum.inl_injective
  have hAvCard : {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr false, w) ∈ Ew F}.ncard = AvIdx.ncard := by
    rw [hIdxEq false, ← hAvIdxDef]; exact Set.ncard_image_of_injective _ Sum.inl_injective
  have hKc : Kc F (Sum.inr true) (Sum.inr false) = AuIdx.ncard + AvIdx.ncard := by
    rw [hKc0, hAuCard, hAvCard]
  -- The `q`/`p`-route dichotomy, `u`-side (directly from `lemma_Ku`, `w ∈ S∩T` = K1).
  have hAu_qp : ∀ x ∈ AuIdx,
      (∃ q : W, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {x}) := by
    rintro x ⟨hxS, hxT, hxEw⟩
    have h4 := (lemma_Ku H hequiv hbip hbal1 hbal2 S T hxS).mp (Or.inr hxEw)
    rcases h4 with ⟨-, hxTfalse⟩ | hb | ⟨hxTfalse, -⟩ | ⟨q, hqS, hqx, hnsame, hTor⟩
    · exact absurd hxT hxTfalse
    · exact Or.inr hb
    · exact absurd hxT hxTfalse
    · refine Or.inl ⟨q, hqS, hqx, hnsame, ?_⟩
      rcases hTor with hf | hf
      · exact absurd hxT hf
      · exact hf
  -- The `q`/`p`-route dichotomy, `v`-side (direct derivation, mirroring `lemma_Ku`'s Ew-branch
  -- with `u↔v, S↔T` — clauses (a)/(c) are auto-vacuous here too, via `x ∈ S` this time).
  have hAv_qp : ∀ x ∈ AvIdx,
      (∃ q : W, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = {x}) := by
    rintro x ⟨hxS, hxT, hxEw⟩
    obtain ⟨p, hp | hp⟩ := ((mem_Ew_iff F (Sum.inr false) (Sum.inl x)).mp hxEw).2.2
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hpneu : p ≠ Sum.inr true := by rintro rfl; exact hpnadj (extF_adj_uv H S T).symm
      obtain ⟨y, rfl⟩ : ∃ y, p = Sum.inl y := by
        rcases p with y | b
        · exact ⟨y, rfl⟩
        · cases b with
          | true => exact absurd rfl hpneu
          | false => exact absurd rfl hpne
      have hyT : y ∉ T := fun h => hpnadj ((extF_adj_inr_false_inl H S T y).mpr h)
      have hxmem : Sum.inl x ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hxmem
      have hyxH : H.Adj y x := (extF_adj_inl_inl H S T y x).mp hxmem.2
      have hyS : y ∉ S := by
        intro hS
        have humem : Sum.inr true ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) := by
          rw [SimpleGraph.mem_commonNeighbors]
          exact ⟨(extF_adj_uv H S T).symm, ((extF_adj_inr_true_inl H S T y).mpr hS).symm⟩
        rw [hpcn] at humem
        exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
      refine Or.inr ⟨y, hyS, hyT, ?_⟩
      ext z
      rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzy, hzT⟩
        have hzmem : Sum.inl z ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) :=
          F.mem_commonNeighbors.mpr
            ⟨(extF_adj_inr_false_inl H S T z).mpr hzT, (extF_adj_inl_inl H S T y z).mpr hzy⟩
        rw [hpcn] at hzmem
        exact Sum.inl.inj (Set.mem_singleton_iff.mp hzmem)
      · rintro rfl
        exact ⟨hyxH, hxT⟩
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hvne : Sum.inr false ∈ F.commonNeighbors (Sum.inl x) p := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hvne
      obtain ⟨-, hpv⟩ := hvne
      rcases p with y | b
      · have hyT : y ∈ T := (extF_adj_inl_inr_false H S T y).mp hpv
        have hyxne : y ≠ x := fun h => hpne (congrArg Sum.inl h)
        have hqnadjXx : ¬ H.Adj y x := fun h =>
          hpnadj ((extF_adj_inl_inl H S T x y).mpr h.symm)
        have hcn0' : H.commonNeighbors x y = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [SimpleGraph.mem_commonNeighbors] at hz
          have hzmem : Sum.inl z ∈ F.commonNeighbors (Sum.inl x) (Sum.inl y) :=
            F.mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inl H S T x z).mpr hz.1, (extF_adj_inl_inl H S T y z).mpr hz.2⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
        have hnsame : ¬ same x y :=
          not_same_of_disjoint_commonNeighbors hequiv hbip hbal1 hbal2 hyxne hqnadjXx hcn0'
        have hxS_or : x ∉ S ∨ y ∉ S := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨hxS', hyS'⟩ := hcon
          have humem : Sum.inr true ∈ F.commonNeighbors (Sum.inl x) (Sum.inl y) := by
            rw [SimpleGraph.mem_commonNeighbors]
            exact ⟨(extF_adj_inl_inr_true H S T x).mpr hxS',
              (extF_adj_inl_inr_true H S T y).mpr hyS'⟩
          rw [hpcn] at humem
          exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
        refine Or.inl ⟨y, hyT, hyxne, hnsame, ?_⟩
        rcases hxS_or with h | h
        · exact absurd hxS h
        · exact h
      · cases b with
        | true =>
          have hxSfalse : x ∉ S := fun hS => hpnadj ((extF_adj_inl_inr_true H S T x).mpr hS)
          exact absurd hxS hxSfalse
        | false => exact absurd hpv F.irrefl
  -- Split each side into its `q`-available and `p`-only parts.
  set QAu : Set W := {x | x ∈ AuIdx ∧ ∃ q, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T} with hQAudef
  set QAv : Set W := {x | x ∈ AvIdx ∧ ∃ q, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S} with hQAvdef
  set PAu : Set W := AuIdx \ QAu with hPAudef
  set PAv : Set W := AvIdx \ QAv with hPAvdef
  have hQAu_sub : QAu ⊆ AuIdx := fun x hx => hx.1
  have hQAv_sub : QAv ⊆ AvIdx := fun x hx => hx.1
  -- ★ `choose` on `∀ x ∈ s, ∃ y, P x y` yields a function taking the MEMBERSHIP PROOF as a
  -- second argument (`f : ∀ x, x∈s → W`), not a plain `W → W` — incompatible with using
  -- `f x` inside a bare lambda (e.g. an image map) with no proof in scope. Fix: move the
  -- membership hypothesis INSIDE the existential body as an implication, supplying a junk
  -- witness (`x` itself) when it fails, so `choose` produces a TOTAL `W → W` function.
  have hPAu_p : ∀ x : W, ∃ p : W, x ∈ PAu → (p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {x}) := by
    intro x
    by_cases hxP : x ∈ PAu
    · obtain ⟨hxA, hxnQ⟩ := hxP
      have hnq : ¬ (∃ q, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) := fun hex => hxnQ ⟨hxA, hex⟩
      obtain ⟨p, hp⟩ := (hAu_qp x hxA).resolve_left hnq
      exact ⟨p, fun _ => hp⟩
    · exact ⟨x, fun h => absurd h hxP⟩
  have hPAv_p : ∀ x : W, ∃ p : W, x ∈ PAv → (p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = {x}) := by
    intro x
    by_cases hxP : x ∈ PAv
    · obtain ⟨hxA, hxnQ⟩ := hxP
      have hnq : ¬ (∃ q, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) := fun hex => hxnQ ⟨hxA, hex⟩
      obtain ⟨p, hp⟩ := (hAv_qp x hxA).resolve_left hnq
      exact ⟨p, fun _ => hp⟩
    · exact ⟨x, fun h => absurd h hxP⟩
  choose pu hpu using hPAu_p
  choose pv hpv using hPAv_p
  have hQAu_q : ∀ x : W, ∃ q : W, x ∈ QAu → (q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) := by
    intro x
    by_cases hxQ : x ∈ QAu
    · exact ⟨(hxQ.2).choose, fun _ => (hxQ.2).choose_spec⟩
    · exact ⟨x, fun h => absurd h hxQ⟩
  have hQAv_q : ∀ x : W, ∃ q : W, x ∈ QAv → (q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) := by
    intro x
    by_cases hxQ : x ∈ QAv
    · exact ⟨(hxQ.2).choose, fun _ => (hxQ.2).choose_spec⟩
    · exact ⟨x, fun h => absurd h hxQ⟩
  choose qu hqu using hQAu_q
  choose qv hqv using hQAv_q
  -- `q`-route: combined injection into `ZPairs`.
  set imgQu : Set (Sym2 W) := (fun x => s(x, qu x)) '' QAu with himgQudef
  set imgQv : Set (Sym2 W) := (fun x => s(x, qv x)) '' QAv with himgQvdef
  have hinjQu : Set.InjOn (fun x => s(x, qu x)) QAu := by
    intro x1 hx1 x2 hx2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hxx, -⟩ | ⟨hxq, -⟩
    · exact hxx
    · exfalso
      have h2 := hqu x2 hx2
      have hx1T : x1 ∈ T := (hQAu_sub hx1).2.1
      rw [hxq] at hx1T
      exact h2.2.2.2 hx1T
  have hinjQv : Set.InjOn (fun x => s(x, qv x)) QAv := by
    intro x1 hx1 x2 hx2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hxx, -⟩ | ⟨hxq, -⟩
    · exact hxx
    · exfalso
      have h2 := hqv x2 hx2
      have hx1S : x1 ∈ S := (hQAv_sub hx1).1
      rw [hxq] at hx1S
      exact h2.2.2.2 hx1S
  have hdisjQ : Disjoint imgQu imgQv := by
    rw [Set.disjoint_left]
    rintro P ⟨x1, hx1, rfl⟩ ⟨x2, hx2, heq⟩
    rw [Sym2.eq_iff] at heq
    have h1 := hqu x1 hx1
    have h2 := hqv x2 hx2
    rcases heq with ⟨hx12, hq12⟩ | ⟨hxq, hqx⟩
    · have hquS : qu x1 ∈ S := h1.1
      have hqvnS : qv x2 ∉ S := h2.2.2.2
      rw [← hq12] at hquS
      exact hqvnS hquS
    · have hx2AT : x2 ∈ T := (hQAv_sub hx2).2.1
      have hqunT : qu x1 ∉ T := h1.2.2.2
      rw [hxq] at hx2AT
      exact hqunT hx2AT
  have himgQu_sub : imgQu ⊆ ZPairs H S T := by
    rintro P ⟨x, hx, rfl⟩
    have h := hqu x hx
    have hxS : x ∈ S := (hQAu_sub hx).1
    rw [mem_ZPairs_iff]
    refine ⟨h.2.1.symm, ?_, ?_, Or.inl ⟨hxS, h.1⟩⟩
    · exact fun hadj => h.2.2.1 ((hbip x (qu x)).mp hadj).1
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [SimpleGraph.mem_commonNeighbors] at hz
      have hsz : same x z := ((hbip x z).mp hz.1).1
      have hsqz : same (qu x) z := ((hbip (qu x) z).mp hz.2).1
      exact h.2.2.1 (hequiv.trans hsz (hequiv.symm hsqz))
  have himgQv_sub : imgQv ⊆ ZPairs H S T := by
    rintro P ⟨x, hx, rfl⟩
    have h := hqv x hx
    have hxT : x ∈ T := (hQAv_sub hx).2.1
    rw [mem_ZPairs_iff]
    refine ⟨h.2.1.symm, ?_, ?_, Or.inr ⟨hxT, h.1⟩⟩
    · exact fun hadj => h.2.2.1 ((hbip x (qv x)).mp hadj).1
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [SimpleGraph.mem_commonNeighbors] at hz
      have hsz : same x z := ((hbip x z).mp hz.1).1
      have hsqz : same (qv x) z := ((hbip (qv x) z).mp hz.2).1
      exact h.2.2.1 (hequiv.trans hsz (hequiv.symm hsqz))
  have hQubound : QAu.ncard + QAv.ncard ≤ Zcount H S T := by
    have e1 : imgQu.ncard = QAu.ncard := Set.ncard_image_of_injOn hinjQu
    have e2 : imgQv.ncard = QAv.ncard := Set.ncard_image_of_injOn hinjQv
    have hunion : (imgQu ∪ imgQv).ncard = imgQu.ncard + imgQv.ncard :=
      Set.ncard_union_eq hdisjQ (Set.toFinite _) (Set.toFinite _)
    have hsub : imgQu ∪ imgQv ⊆ ZPairs H S T := Set.union_subset himgQu_sub himgQv_sub
    have hle : (imgQu ∪ imgQv).ncard ≤ (ZPairs H S T).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    show QAu.ncard + QAv.ncard ≤ (ZPairs H S T).ncard
    omega
  -- `p`-route: separate injections into the two `R_c` summands.
  have hinjPu : Set.InjOn (fun x => Sum.inl (pu x) : W → W ⊕ Bool) PAu := by
    intro x1 hx1 x2 hx2 heq
    have h1 := hpu x1 hx1
    have h2 := hpu x2 hx2
    have heq' : pu x1 = pu x2 := Sum.inl.inj heq
    have hset : ({x1} : Set W) = {x2} := by rw [← h1.2.2, ← h2.2.2, heq']
    exact Set.singleton_eq_singleton_iff.mp hset
  have hinjPv : Set.InjOn (fun x => Sum.inl (pv x) : W → W ⊕ Bool) PAv := by
    intro x1 hx1 x2 hx2 heq
    have h1 := hpv x1 hx1
    have h2 := hpv x2 hx2
    have heq' : pv x1 = pv x2 := Sum.inl.inj heq
    have hset : ({x1} : Set W) = {x2} := by rw [← h1.2.2, ← h2.2.2, heq']
    exact Set.singleton_eq_singleton_iff.mp hset
  have himgPu_sub : (fun x => Sum.inl (pu x) : W → W ⊕ Bool) '' PAu ⊆
      {w | w ∈ catC F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr true, w) ∈ Anon F} := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpu x hx
    have hxS : x ∈ S := (hx.1 : x ∈ AuIdx).1
    have hcatC : Sum.inl (pu x) ∈ catC F (Sum.inr true) (Sum.inr false) :=
      ⟨by simp, by simp, fun hadj => h.1 ((extF_adj_inr_true_inl H S T (pu x)).mp hadj),
        fun hadj => h.2.1 ((extF_adj_inr_false_inl H S T (pu x)).mp hadj)⟩
    refine ⟨hcatC, ?_⟩
    rw [mem_Anon_iff]
    refine ⟨by simp, fun hadj => h.1 ((extF_adj_inr_true_inl H S T (pu x)).mp hadj), ?_⟩
    have hwmem : x ∈ H.neighborSet (pu x) ∩ S := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨Sum.inl x, F.mem_commonNeighbors.mpr
      ⟨(extF_adj_inr_true_inl H S T x).mpr hxS, (extF_adj_inl_inl H S T (pu x) x).mpr hwmem.1⟩⟩
  have himgPv_sub : (fun x => Sum.inl (pv x) : W → W ⊕ Bool) '' PAv ⊆
      {w | w ∈ catC F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr false, w) ∈ Anon F} := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpv x hx
    have hxT : x ∈ T := (hx.1 : x ∈ AvIdx).2.1
    have hcatC : Sum.inl (pv x) ∈ catC F (Sum.inr true) (Sum.inr false) :=
      ⟨by simp, by simp, fun hadj => h.1 ((extF_adj_inr_true_inl H S T (pv x)).mp hadj),
        fun hadj => h.2.1 ((extF_adj_inr_false_inl H S T (pv x)).mp hadj)⟩
    refine ⟨hcatC, ?_⟩
    rw [mem_Anon_iff]
    refine ⟨by simp, fun hadj => h.2.1 ((extF_adj_inr_false_inl H S T (pv x)).mp hadj), ?_⟩
    have hwmem : x ∈ H.neighborSet (pv x) ∩ T := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨Sum.inl x, F.mem_commonNeighbors.mpr
      ⟨(extF_adj_inr_false_inl H S T x).mpr hxT, (extF_adj_inl_inl H S T (pv x) x).mpr hwmem.1⟩⟩
  have hPubound : PAu.ncard ≤ {w | w ∈ catC F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr true, w) ∈ Anon F}.ncard := by
    rw [← Set.ncard_image_of_injOn hinjPu]
    exact Set.ncard_le_ncard himgPu_sub (Set.toFinite _)
  have hPvbound : PAv.ncard ≤ {w | w ∈ catC F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr false, w) ∈ Anon F}.ncard := by
    rw [← Set.ncard_image_of_injOn hinjPv]
    exact Set.ncard_le_ncard himgPv_sub (Set.toFinite _)
  have hRcEq := Rc_eq_sum_ncard F hne
  -- Assemble.
  have hAu_split : AuIdx.ncard = QAu.ncard + PAu.ncard := by
    have hu : QAu ∪ PAu = AuIdx := by rw [hPAudef, Set.union_sdiff_cancel hQAu_sub]
    have hdisjP : Disjoint QAu PAu :=
      Set.disjoint_left.mpr (fun x hxQ hxP => hxP.2 hxQ)
    rw [← hu, Set.ncard_union_eq hdisjP (Set.toFinite _) (Set.toFinite _)]
  have hAv_split : AvIdx.ncard = QAv.ncard + PAv.ncard := by
    have hv : QAv ∪ PAv = AvIdx := by rw [hPAvdef, Set.union_sdiff_cancel hQAv_sub]
    have hdisjP : Disjoint QAv PAv :=
      Set.disjoint_left.mpr (fun x hxQ hxP => hxP.2 hxQ)
    rw [← hv, Set.ncard_union_eq hdisjP (Set.toFinite _) (Set.toFinite _)]
  rw [hAu_split, hAv_split] at hKc
  omega

/-! ### The identity assembly

The task: assemble `row04_deletion_decomposition`
(`Erdos742.lean`) with `row07iii_S_identity` (`Erdos742.lean`) and
`lemma_rem` (this file) into a single closed-form identity for `D_inc(u,v)`.
The obstacle is a TYPE MISMATCH: `row04`'s remote sum ranges over `Sym2 {w : W ⊕ Bool //
w ≠ u ∧ w ≠ v}` (the `delPair`-subtype `Erdos742.lean`'s transport layer always uses), while
`lemma_rem`'s sum ranges over `Sym2 W` directly (`H`'s own vertex type).  Since `Bool` has
exactly two constructors, `{w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}` consists
of nothing but `Sum.inl`-images of `W`, so the two types are canonically equivalent — but
mathlib does not know this, and every `cwt`/`Wit`/`commonNeighbors` fact needs transporting
across the equivalence before the two sums can be identified. -/

/-- The canonical bijection `{w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false} ≃ W`:
every element of the subtype is (necessarily) `Sum.inl x` for a unique `x`, since `Bool` has
only the two excluded values. -/
def unwrapDel {W : Type*} :
    ∀ w : W ⊕ Bool, w ≠ Sum.inr true → w ≠ Sum.inr false → W
  | Sum.inl x, _, _ => x
  | Sum.inr true, h, _ => absurd rfl h
  | Sum.inr false, _, h => absurd rfl h

/-- The bijection itself, `delBoolEquiv : {w : W ⊕ Bool // w ≠ u ∧ w ≠ v} ≃ W` for
`u := Sum.inr true`, `v := Sum.inr false` — exactly the type `delPair (extF H S T) u v`'s
vertex type. -/
def delBoolEquiv :
    {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false} ≃ W where
  toFun p := unwrapDel p.1 p.2.1 p.2.2
  invFun x := ⟨Sum.inl x, by simp, by simp⟩
  left_inv := by
    rintro ⟨w, h1, h2⟩
    rcases w with x | b
    · rfl
    · cases b with
      | true => exact absurd rfl h1
      | false => exact absurd rfl h2
  right_inv _ := rfl

/-- Every subtype element's underlying `W ⊕ Bool` value is `Sum.inl` of its `delBoolEquiv`
image. -/
theorem val_eq_inl_delBoolEquiv
    (a : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    (a : W ⊕ Bool) = Sum.inl (delBoolEquiv a) := by
  obtain ⟨w, h1, h2⟩ := a
  rcases w with x | b
  · rfl
  · cases b with
    | true => exact absurd rfl h1
    | false => exact absurd rfl h2

/-- `delBoolEquiv` is a graph isomorphism from `delPair (extF H S T) u v` to `H`: this is the
whole point of the construction — `delPair` (delete `u,v`) undoes exactly what `extF` (add
`u,v`) did. -/
theorem delPair_extF_adj (H : SimpleGraph W) (S T : Set W)
    (a b : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    (delPair (extF H S T) (Sum.inr true) (Sum.inr false)).Adj a b ↔
      H.Adj (delBoolEquiv a) (delBoolEquiv b) := by
  rw [delPair_adj, val_eq_inl_delBoolEquiv a, val_eq_inl_delBoolEquiv b, extF_adj_inl_inl]

/-- `commonNeighbors` transports along `delBoolEquiv` as a SET IMAGE — the one fact
everything else (`E0`/`Ew`/`Anon`/`Wit` transport) is built from. -/
theorem delPair_extF_commonNeighbors_image (H : SimpleGraph W) (S T : Set W)
    (a b : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    delBoolEquiv '' ((delPair (extF H S T) (Sum.inr true) (Sum.inr false)).commonNeighbors a b) =
      H.commonNeighbors (delBoolEquiv a) (delBoolEquiv b) := by
  ext z
  simp only [Set.mem_image, SimpleGraph.mem_commonNeighbors]
  constructor
  · rintro ⟨c, ⟨hac, hbc⟩, rfl⟩
    exact ⟨(delPair_extF_adj H S T a c).mp hac, (delPair_extF_adj H S T b c).mp hbc⟩
  · rintro ⟨haz, hbz⟩
    refine ⟨delBoolEquiv.symm z, ⟨?_, ?_⟩, Equiv.apply_symm_apply _ _⟩
    · rw [delPair_extF_adj, Equiv.apply_symm_apply]; exact haz
    · rw [delPair_extF_adj, Equiv.apply_symm_apply]; exact hbz

theorem delPair_extF_commonNeighbors_eq_empty_iff (H : SimpleGraph W) (S T : Set W)
    (a b : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    (delPair (extF H S T) (Sum.inr true) (Sum.inr false)).commonNeighbors a b = ∅ ↔
      H.commonNeighbors (delBoolEquiv a) (delBoolEquiv b) = ∅ := by
  constructor
  · intro h
    have himg := delPair_extF_commonNeighbors_image H S T a b
    rw [h, Set.image_empty] at himg
    exact himg.symm
  · intro h
    have himg := delPair_extF_commonNeighbors_image H S T a b
    rw [h] at himg
    exact Set.image_eq_empty.mp himg

theorem delPair_extF_commonNeighbors_nonempty_iff (H : SimpleGraph W) (S T : Set W)
    (a b : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    ((delPair (extF H S T) (Sum.inr true) (Sum.inr false)).commonNeighbors a b).Nonempty ↔
      (H.commonNeighbors (delBoolEquiv a) (delBoolEquiv b)).Nonempty := by
  rw [← delPair_extF_commonNeighbors_image H S T a b, Set.image_nonempty]

theorem delPair_extF_commonNeighbors_eq_singleton_iff (H : SimpleGraph W) (S T : Set W)
    (a b c : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    (delPair (extF H S T) (Sum.inr true) (Sum.inr false)).commonNeighbors a b = {c} ↔
      H.commonNeighbors (delBoolEquiv a) (delBoolEquiv b) = {delBoolEquiv c} := by
  constructor
  · intro h
    have himg := delPair_extF_commonNeighbors_image H S T a b
    rw [h, Set.image_singleton] at himg
    exact himg.symm
  · intro h
    have himg := delPair_extF_commonNeighbors_image H S T a b
    rw [h, ← Set.image_singleton] at himg
    exact (Equiv.image_eq_iff_eq delBoolEquiv _ _).mp himg

theorem delPair_extF_ne_iff (a b : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    a ≠ b ↔ delBoolEquiv a ≠ delBoolEquiv b := by
  constructor
  · exact fun hne heq => hne (delBoolEquiv.injective heq)
  · exact fun hne heq => hne (congrArg delBoolEquiv heq)

theorem delPair_extF_isWitAt_iff (H : SimpleGraph W) (S T : Set W)
    (x z y : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    IsWitAt (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) x z y ↔
      IsWitAt H (delBoolEquiv x) (delBoolEquiv z) (delBoolEquiv y) := by
  unfold IsWitAt
  rw [delPair_extF_ne_iff, delPair_extF_adj, delPair_extF_commonNeighbors_eq_singleton_iff]

theorem delPair_extF_wit_nonempty_iff (H : SimpleGraph W) (S T : Set W)
    (x y : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    (Wit (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) x y).Nonempty ↔
      (Wit H (delBoolEquiv x) (delBoolEquiv y)).Nonempty := by
  unfold Wit
  constructor
  · rintro ⟨p, hp | hp⟩
    · exact ⟨delBoolEquiv p, Or.inl ((delPair_extF_isWitAt_iff H S T x y p).mp hp)⟩
    · exact ⟨delBoolEquiv p, Or.inr ((delPair_extF_isWitAt_iff H S T y x p).mp hp)⟩
  · rintro ⟨q, hq | hq⟩
    · refine ⟨delBoolEquiv.symm q, Or.inl ((delPair_extF_isWitAt_iff H S T x y
        (delBoolEquiv.symm q)).mpr ?_)⟩
      rw [Equiv.apply_symm_apply]; exact hq
    · refine ⟨delBoolEquiv.symm q, Or.inr ((delPair_extF_isWitAt_iff H S T y x
        (delBoolEquiv.symm q)).mpr ?_)⟩
      rw [Equiv.apply_symm_apply]; exact hq

theorem delPair_extF_mem_E0_iff (H : SimpleGraph W) (S T : Set W)
    (x y : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    s(x, y) ∈ E0 (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) ↔
      s(delBoolEquiv x, delBoolEquiv y) ∈ E0 H := by
  rw [mem_E0_iff, mem_E0_iff, delPair_extF_adj, delPair_extF_commonNeighbors_eq_empty_iff]

theorem delPair_extF_mem_Ew_iff (H : SimpleGraph W) (S T : Set W)
    (x y : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    s(x, y) ∈ Ew (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) ↔
      s(delBoolEquiv x, delBoolEquiv y) ∈ Ew H := by
  rw [mem_Ew_iff, mem_Ew_iff, delPair_extF_adj, delPair_extF_commonNeighbors_nonempty_iff,
    delPair_extF_wit_nonempty_iff]

theorem delPair_extF_mem_Anon_iff (H : SimpleGraph W) (S T : Set W)
    (x y : {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    s(x, y) ∈ Anon (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) ↔
      s(delBoolEquiv x, delBoolEquiv y) ∈ Anon H := by
  rw [mem_Anon_iff, mem_Anon_iff, delPair_extF_ne_iff, delPair_extF_adj,
    delPair_extF_commonNeighbors_nonempty_iff]

/-- `cwt` transports along `delBoolEquiv`: `cwt` on `delPair (extF H S T) u v` equals `cwt`
on `H`, at the corresponding pair. This is what lets `row04`'s remote sum (over the
`delPair`-subtype) be reindexed into `lemma_rem`'s sum (over `Sym2 W` directly). -/
theorem delPair_extF_cwt (H : SimpleGraph W) (S T : Set W)
    (e : Sym2 {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    cwt (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) e = cwt H (Sym2.map delBoolEquiv e) := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk]
    by_cases hxy : x = y
    · subst hxy; simp
    · by_cases hadj : (delPair (extF H S T) (Sum.inr true) (Sum.inr false)).Adj x y
      · have hadjH : H.Adj (delBoolEquiv x) (delBoolEquiv y) := (delPair_extF_adj H S T x y).mp hadj
        rw [cwt_of_adj _ hadj, cwt_of_adj _ hadjH]
        congr 1
        simp only [Set.mem_union, delPair_extF_mem_E0_iff, delPair_extF_mem_Ew_iff]
      · have hnadjH : ¬ H.Adj (delBoolEquiv x) (delBoolEquiv y) :=
          fun h => hadj ((delPair_extF_adj H S T x y).mpr h)
        rw [cwt_of_not_adj _ hadj, cwt_of_not_adj _ hnadjH]
        congr 1
        simp only [delPair_extF_mem_Anon_iff]

/-- `Sym2.map Subtype.val` and `Sym2.map Sum.inl ∘ Sym2.map delBoolEquiv` agree on the
`delPair`-subtype: the identity assembly's other reindexing fact. -/
theorem map_val_eq_map_inl_comp_delBoolEquiv
    (e : Sym2 {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false}) :
    Sym2.map (Subtype.val) e =
      Sym2.map (Sum.inl : W → W ⊕ Bool) (Sym2.map delBoolEquiv e) := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk, Sym2.map_mk, Sym2.map_mk, val_eq_inl_delBoolEquiv x, val_eq_inl_delBoolEquiv y]

/-- `Sym2.map delBoolEquiv` is a bijection `Sym2 (delPair-subtype) → Sym2 W` — used to
reindex `row04`'s remote sum onto `lemma_rem`'s. -/
theorem sym2_map_delBoolEquiv_bijective :
    Function.Bijective
      (Sym2.map (delBoolEquiv (W := W)) :
        Sym2 {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false} → Sym2 W) := by
  refine ⟨Sym2.map.injective (delBoolEquiv (W := W)).injective, ?_⟩
  intro Q
  induction Q using Sym2.ind with
  | _ a b =>
    exact ⟨s(delBoolEquiv.symm a, delBoolEquiv.symm b), by
      rw [Sym2.map_mk]; simp⟩

open scoped Classical in
/-- `χ(u,v)`: `[{u,v}$ is unclassified in $F]`, for `F = extF H S T`.
`c({u,v},F) = 1 − χ` (`cwt_of_adj`); the identity below states `D_inc` directly in terms of
`χ`. -/
noncomputable def Chi (H : SimpleGraph W) (S T : Set W) : ℤ :=
  if s((Sum.inr true : W ⊕ Bool), (Sum.inr false : W ⊕ Bool)) ∈
      E0 (extF H S T) ∪ Ew (extF H S T) then 0 else 1

/-- ★★★ **THE IDENTITY**:
`D_inc(u,v) = 1 − χ − W(u,v) − Z(u,v) − R_c(u,v) − U_a(u,v) − U_a(v,u) + K(u,v)`.

Derivation: substitute `row07iii_S_identity`
into `row04_deletion_decomposition`, using
`c({u,v},F) = 1 − χ` (`cwt_of_adj`); this leaves exactly the remote sum, evaluated by
`lemma_rem` (this file) after reindexing `row04`'s `delPair`-subtype sum onto `Sym2 W`
via `delBoolEquiv` (`delPair_extF_cwt`, `map_val_eq_map_inl_comp_delBoolEquiv`,
`sym2_map_delBoolEquiv_bijective`). -/
theorem identity_assembly (H : SimpleGraph W) (hH : IsBalCBUnion H) (S T : Set W) :
    Dinc (extF H S T) (Sum.inr true) (Sum.inr false) =
      1 - Chi H S T - (Wcount H S T : ℤ) - (Zcount H S T : ℤ)
        - (Rc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ)
        - (Ua (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ)
        - (Ua (extF H S T) (Sum.inr false) (Sum.inr true) : ℤ)
        + (Kc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) := by
  have huv := extF_adj_uv H S T
  have h4 := row04_deletion_decomposition (extF H S T) huv
  have h7 := row07iii_S_identity (extF H S T) huv
  have hreindex :
      (∑ e : Sym2 {w : W ⊕ Bool // w ≠ Sum.inr true ∧ w ≠ Sum.inr false},
        (cwt (extF H S T) (Sym2.map Subtype.val e) -
          cwt (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) e)) =
      ∑ P : Sym2 W, (cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) P) - cwt H P) :=
    Fintype.sum_bijective (Sym2.map (delBoolEquiv (W := W)))
      sym2_map_delBoolEquiv_bijective
      (fun e => cwt (extF H S T) (Sym2.map Subtype.val e) -
        cwt (delPair (extF H S T) (Sum.inr true) (Sum.inr false)) e)
      (fun P => cwt (extF H S T) (Sym2.map (Sum.inl : W → W ⊕ Bool) P) - cwt H P)
      (fun e => by rw [← map_val_eq_map_inl_comp_delBoolEquiv e, delPair_extF_cwt H S T e])
  have hrem := lemma_rem H hH S T
  have hchi : cwt (extF H S T) s((Sum.inr true : W ⊕ Bool), Sum.inr false) = 1 - Chi H S T := by
    rw [cwt_of_adj (extF H S T) huv]
    unfold Chi
    by_cases hc : s((Sum.inr true : W ⊕ Bool), Sum.inr false) ∈
        E0 (extF H S T) ∪ Ew (extF H S T)
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [h4, hreindex, hrem, hchi, h7]
  ring

/-! ### The saturation lemma -/

/-- **The saturation lemma (LEMMA SAT), stated as an EQUIVALENCE with `D_inc(u,v) = 1`**,
not a one-directional implication.
`⟹`: given the identity (`identity_assembly`) and `K ≤ Z + R_c` (`lemma_PST_L2`), `D_inc = 1`
forces `χ + W + U_a(u,v) + U_a(v,u) + (Z + R_c − K)` — a sum of five non-negative terms — to be
`0`, hence each term `0`. `⟸`: direct substitution into the identity. -/
theorem lemma_SAT (H : SimpleGraph W) (hH : IsBalCBUnion H) (S T : Set W) :
    Dinc (extF H S T) (Sum.inr true) (Sum.inr false) = 1 ↔
      Chi H S T = 0 ∧ Wcount H S T = 0 ∧
        Ua (extF H S T) (Sum.inr true) (Sum.inr false) = 0 ∧
        Ua (extF H S T) (Sum.inr false) (Sum.inr true) = 0 ∧
        Kc (extF H S T) (Sum.inr true) (Sum.inr false) =
          Zcount H S T + Rc (extF H S T) (Sum.inr true) (Sum.inr false) := by
  have hid := identity_assembly H hH S T
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, -⟩ := hH
  have hpst := lemma_PST_L2 H hequiv hbip hbal1 hbal2 S T
  have hChi_nonneg : 0 ≤ Chi H S T := by unfold Chi; split_ifs <;> norm_num
  constructor
  · intro hdinc
    rw [hdinc] at hid
    have hKZR : (Kc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) ≤
        (Zcount H S T : ℤ) + (Rc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) := by
      exact_mod_cast hpst
    have hW0 : (0 : ℤ) ≤ (Wcount H S T : ℤ) := Nat.cast_nonneg _
    have hZ0 : (0 : ℤ) ≤ (Zcount H S T : ℤ) := Nat.cast_nonneg _
    have hR0 : (0 : ℤ) ≤ (Rc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) := Nat.cast_nonneg _
    have hU0 : (0 : ℤ) ≤ (Ua (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) := Nat.cast_nonneg _
    have hU'0 : (0 : ℤ) ≤ (Ua (extF H S T) (Sum.inr false) (Sum.inr true) : ℤ) := Nat.cast_nonneg _
    have hall0 : Chi H S T = 0 ∧ (Wcount H S T : ℤ) = 0 ∧
        (Ua (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) = 0 ∧
        (Ua (extF H S T) (Sum.inr false) (Sum.inr true) : ℤ) = 0 ∧
        (Kc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) =
          (Zcount H S T : ℤ) + (Rc (extF H S T) (Sum.inr true) (Sum.inr false) : ℤ) := by omega
    exact ⟨hall0.1, by exact_mod_cast hall0.2.1, by exact_mod_cast hall0.2.2.1,
      by exact_mod_cast hall0.2.2.2.1, by exact_mod_cast hall0.2.2.2.2⟩
  · rintro ⟨hchi, hW, hUa1, hUa2, hK⟩
    rw [hid, hchi, hW, hUa1, hUa2, hK]
    push_cast
    ring

/-! ### The witnessing criterion for `H`-edges (LEMMA PST-W) — groundwork -/

/-- The codegree dichotomy the witnessing criterion's proof needs
first: for an `H`-edge `{x,y}` with `codeg_F(x,y) ≥ 1`, since `H` itself is triangle-free
per component (`codeg_H(x,y) = 0` for any `H`-edge `{x,y}`, by the Bool-pigeonhole argument
`delPair_extF_mem_E0_iff`'s neighbours already use), the extra common `F`-neighbour can only be
`u` or `v` — forcing `x,y` BOTH into `S`, or BOTH into `T`. -/
theorem extF_codeg_dichotomy (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b) (S T : Set W) {x y : W}
    (hxy : H.Adj x y)
    (hcodeg : ((extF H S T).commonNeighbors (Sum.inl x) (Sum.inl y)).Nonempty) :
    (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T) := by
  obtain ⟨w, hw⟩ := hcodeg
  rw [SimpleGraph.mem_commonNeighbors] at hw
  obtain ⟨hwx, hwy⟩ := hw
  rcases w with c | b
  · exfalso
    have hxc : H.Adj x c := (extF_adj_inl_inl H S T x c).mp hwx
    have hyc : H.Adj y c := (extF_adj_inl_inl H S T y c).mp hwy
    have h1 := ((hbip x c).mp hxc).2
    have h2 := ((hbip y c).mp hyc).2
    have h3 := ((hbip x y).mp hxy).2
    revert h1 h2 h3
    cases part x <;> cases part y <;> cases part c <;> decide
  · cases b with
    | true => exact Or.inl ⟨(extF_adj_inl_inr_true H S T x).mp hwx,
        (extF_adj_inl_inr_true H S T y).mp hwy⟩
    | false => exact Or.inr ⟨(extF_adj_inl_inr_false H S T x).mp hwx,
        (extF_adj_inl_inr_false H S T y).mp hwy⟩

/-- **LEMMA PST-W, one-sided core**: the "witness at
`a`" half, stated for a general `H`-edge `{a,b}` so it can be applied twice — once at `(a,b) =
(x,y)` for the "witness at `x`" clause, once at `(a,b) = (y,x)` for the "witness at `y`" clause
— rather than proved twice. `X_a := {c | same a c ∧ part c = part a}` (`a`'s own part class),
`Y_a := {c | same a c ∧ part c = part b}` (the OTHER part class, containing `b`). -/
theorem lemma_PST_W_core (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (S T : Set W) {a b : W} (hab : H.Adj a b)
    (hdich : (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T)) :
    (WitAt (extF H S T) (Sum.inl a) (Sum.inl b)).Nonempty ↔
      {c | same a c ∧ part c = part b}.ncard = 1 ∧
      ∃ p ∈ {c | same a c ∧ part c = part a} \ {a}, (p ∉ S ∨ a ∉ S) ∧ (p ∉ T ∨ a ∉ T) := by
  classical
  set F := extF H S T with hFdef
  obtain ⟨hsab, hpab⟩ := (hbip a b).mp hab
  have hbZb : b ∈ {c | same a c ∧ part c = part b} := ⟨hsab, rfl⟩
  constructor
  · rintro ⟨w, hwne, hwadj, hwcn⟩
    have hwb : F.Adj w (Sum.inl b) :=
      (F.mem_commonNeighbors.mp (hwcn ▸ Set.mem_singleton (Sum.inl b))).2
    rcases w with p | c
    · -- w = inl p : the genuine witness case.
      have hap : H.Adj p b := (extF_adj_inl_inl H S T p b).mp hwb
      obtain ⟨hspb, hppb⟩ := (hbip p b).mp hap
      have hsap : same a p := hequiv.trans hsab (hequiv.symm hspb)
      have hpa : p ≠ a := fun h => hwne (by rw [h])
      have hnadj_ap : ¬ H.Adj a p := fun h => hwadj ((extF_adj_inl_inl H S T a p).mpr h)
      have hppa : part p = part a := by
        by_contra hne
        exact hnadj_ap ((hbip a p).mpr ⟨hsap, Ne.symm hne⟩)
      have hwcn' : F.commonNeighbors (Sum.inl a) (Sum.inl p) = {Sum.inl b} := hwcn
      have hZa_eq : {c | same a c ∧ part c = part b} = {b} := by
        apply Set.Subset.antisymm
        · intro c hc
          have hac : H.Adj a c := (hbip a c).mpr ⟨hc.1, by rw [hc.2]; exact hpab⟩
          have hpc : H.Adj p c := (hbip p c).mpr
            ⟨hequiv.trans (hequiv.symm hsap) hc.1, by rw [hppa, hc.2]; exact hpab⟩
          have hmem : (Sum.inl c : W ⊕ Bool) ∈ F.commonNeighbors (Sum.inl a) (Sum.inl p) :=
            F.mem_commonNeighbors.mpr ⟨(extF_adj_inl_inl H S T a c).mpr hac,
              (extF_adj_inl_inl H S T p c).mpr hpc⟩
          rw [hwcn'] at hmem
          exact Sum.inl.inj (Set.mem_singleton_iff.mp hmem)
        · intro c hc
          rw [Set.mem_singleton_iff] at hc
          rw [hc]; exact hbZb
      have hcount : {c | same a c ∧ part c = part b}.ncard = 1 := by
        rw [hZa_eq]; exact Set.ncard_singleton b
      have hSavoid : p ∉ S ∨ a ∉ S := by
        by_contra hcon
        push_neg at hcon
        have hmem : (Sum.inr true : W ⊕ Bool) ∈ F.commonNeighbors (Sum.inl a) (Sum.inl p) :=
          F.mem_commonNeighbors.mpr ⟨(extF_adj_inl_inr_true H S T a).mpr hcon.2,
            (extF_adj_inl_inr_true H S T p).mpr hcon.1⟩
        rw [hwcn'] at hmem
        exact absurd (Set.mem_singleton_iff.mp hmem) (by simp)
      have hTavoid : p ∉ T ∨ a ∉ T := by
        by_contra hcon
        push_neg at hcon
        have hmem : (Sum.inr false : W ⊕ Bool) ∈ F.commonNeighbors (Sum.inl a) (Sum.inl p) :=
          F.mem_commonNeighbors.mpr ⟨(extF_adj_inl_inr_false H S T a).mpr hcon.2,
            (extF_adj_inl_inr_false H S T p).mpr hcon.1⟩
        rw [hwcn'] at hmem
        exact absurd (Set.mem_singleton_iff.mp hmem) (by simp)
      exact ⟨hcount, p, ⟨⟨hsap, hppa⟩, hpa⟩, hSavoid, hTavoid⟩
    · -- w = inr c : `u`/`v` cannot witness, using the codegree dichotomy.
      exfalso
      have hwcn' : F.commonNeighbors (Sum.inl a) (Sum.inr c) = {Sum.inl b} := hwcn
      cases c with
      | true =>
        have hbS : b ∈ S := (extF_adj_inr_true_inl H S T b).mp hwb
        have hnaS : a ∉ S := fun haS => hwadj ((extF_adj_inl_inr_true H S T a).mpr haS)
        rcases hdich with ⟨haS, -⟩ | ⟨haT, -⟩
        · exact hnaS haS
        · have hav : F.Adj (Sum.inl a) (Sum.inr false) := (extF_adj_inl_inr_false H S T a).mpr haT
          have huv : F.Adj (Sum.inr true) (Sum.inr false) := extF_adj_uv H S T
          have hmem : (Sum.inr false : W ⊕ Bool) ∈ F.commonNeighbors (Sum.inl a) (Sum.inr true) :=
            F.mem_commonNeighbors.mpr ⟨hav, huv⟩
          rw [hwcn'] at hmem
          exact absurd (Set.mem_singleton_iff.mp hmem) (by simp)
      | false =>
        have hbT : b ∈ T := (extF_adj_inr_false_inl H S T b).mp hwb
        have hnaT : a ∉ T := fun haT => hwadj ((extF_adj_inl_inr_false H S T a).mpr haT)
        rcases hdich with ⟨haS, -⟩ | ⟨haT, -⟩
        · have hau : F.Adj (Sum.inl a) (Sum.inr true) := (extF_adj_inl_inr_true H S T a).mpr haS
          have huv : F.Adj (Sum.inr true) (Sum.inr false) := extF_adj_uv H S T
          have hmem : (Sum.inr true : W ⊕ Bool) ∈ F.commonNeighbors (Sum.inl a) (Sum.inr false) :=
            F.mem_commonNeighbors.mpr ⟨hau, huv.symm⟩
          rw [hwcn'] at hmem
          exact absurd (Set.mem_singleton_iff.mp hmem) (by simp)
        · exact hnaT haT
  · rintro ⟨hcount, p, ⟨⟨hsap, hppa⟩, hpne⟩, hSavoid, hTavoid⟩
    have hZa_eq : {c | same a c ∧ part c = part b} = {b} := by
      obtain ⟨a0, ha0⟩ := Set.ncard_eq_one.mp hcount
      rw [ha0] at hbZb ⊢
      rw [Set.mem_singleton_iff] at hbZb
      rw [hbZb]
    refine ⟨Sum.inl p, fun h => hpne (Sum.inl.inj h),
      fun h => ((hbip a p).mp ((extF_adj_inl_inl H S T a p).mp h)).2 hppa.symm, ?_⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    have hpb : H.Adj p b := (hbip p b).mpr
      ⟨hequiv.trans (hequiv.symm hsap) hsab, by rw [hppa]; exact hpab⟩
    refine ⟨F.mem_commonNeighbors.mpr ⟨(extF_adj_inl_inl H S T a b).mpr hab,
      (extF_adj_inl_inl H S T p b).mpr hpb⟩, ?_⟩
    rintro z hz
    rw [SimpleGraph.mem_commonNeighbors] at hz
    obtain ⟨hzA, hzP⟩ := hz
    rcases z with c | d
    · have hac : H.Adj a c := (extF_adj_inl_inl H S T a c).mp hzA
      have hpc : H.Adj p c := (extF_adj_inl_inl H S T p c).mp hzP
      have hsac := ((hbip a c).mp hac).1
      have hcZa : c ∈ {c | same a c ∧ part c = part b} := by
        refine ⟨hsac, ?_⟩
        have h1 := ((hbip a c).mp hac).2
        have h2 := ((hbip p c).mp hpc).2
        rw [hppa] at h2
        revert h1 h2 hpab
        cases part a <;> cases part b <;> cases part c <;> decide
      rw [hZa_eq] at hcZa
      rw [Set.mem_singleton_iff] at hcZa
      rw [hcZa]
    · cases d with
      | true =>
        have haS : a ∈ S := (extF_adj_inl_inr_true H S T a).mp hzA
        have hpS : p ∈ S := (extF_adj_inl_inr_true H S T p).mp hzP
        rcases hSavoid with h | h
        · exact absurd hpS h
        · exact absurd haS h
      | false =>
        have haT : a ∈ T := (extF_adj_inl_inr_false H S T a).mp hzA
        have hpT : p ∈ T := (extF_adj_inl_inr_false H S T p).mp hzP
        rcases hTavoid with h | h
        · exact absurd hpT h
        · exact absurd haT h

/-- ★★★ **LEMMA PST-W, the witnessing criterion for `H`-edges**: an `H`-edge
`{x,y}` with `codeg_F(x,y) ≥ 1` is witnessed in `F` iff EITHER (witness at `x`: `Y_i := {c |
same x c ∧ part c = part y}` has `b_i = 1`, plus an avoiding `X_i`-partner) OR (witness at `y`:
`X_i := {c | same x c ∧ part c = part x}` has `a_i = 1`, plus an avoiding `Y_i`-partner).
Assembled from `lemma_PST_W_core` applied at `(a,b) = (x,y)` and `(a,b) = (y,x)`, bridged by
`same x c ↔ same y c` (`H.Adj x y` puts `x,y` in the same class, so the two applications' own
`same y ·`/`same x ·` phrasings coincide). -/
theorem lemma_PST_W (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (S T : Set W) {x y : W} (hxy : H.Adj x y)
    (hcodeg : ((extF H S T).commonNeighbors (Sum.inl x) (Sum.inl y)).Nonempty) :
    (Wit (extF H S T) (Sum.inl x) (Sum.inl y)).Nonempty ↔
      ({c | same x c ∧ part c = part y}.ncard = 1 ∧
        ∃ p ∈ {c | same x c ∧ part c = part x} \ {x}, (p ∉ S ∨ x ∉ S) ∧ (p ∉ T ∨ x ∉ T)) ∨
      ({c | same x c ∧ part c = part x}.ncard = 1 ∧
        ∃ q ∈ {c | same x c ∧ part c = part y} \ {y}, (q ∉ S ∨ y ∉ S) ∧ (q ∉ T ∨ y ∉ T)) := by
  have hsxy := ((hbip x y).mp hxy).1
  have hyx_iff : ∀ c, same y c ↔ same x c :=
    fun c => ⟨fun h => hequiv.trans hsxy h, fun h => hequiv.trans (hequiv.symm hsxy) h⟩
  have hset1 : {c | same y c ∧ part c = part x} = {c | same x c ∧ part c = part x} := by
    ext c; simp only [Set.mem_setOf_eq]; rw [hyx_iff c]
  have hset2 : {c | same y c ∧ part c = part y} = {c | same x c ∧ part c = part y} := by
    ext c; simp only [Set.mem_setOf_eq]; rw [hyx_iff c]
  have hdich := extF_codeg_dichotomy H hbip S T hxy hcodeg
  have hdich' : (y ∈ S ∧ x ∈ S) ∨ (y ∈ T ∧ x ∈ T) :=
    hdich.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  have hcoreX := lemma_PST_W_core H hequiv hbip S T hxy hdich
  have hcoreY := lemma_PST_W_core H hequiv hbip S T hxy.symm hdich'
  rw [hset1, hset2] at hcoreY
  unfold Wit
  rw [Set.union_nonempty, hcoreX, hcoreY]

/-! ### THEOREM PST-A: the `S ∩ T = ∅` classification

First, the `K_c = 0` fact and the resulting "five vanishings". -/

/-- `u,v`'s common `H`-neighbours inside `F = extF H S T` are exactly the image of `S ∩ T`
under `Sum.inl` (the SET-level form of the computation `codeg_F(u,v) = |S∩T|`,
which is what `Kc`'s vanishing below needs — a cardinality alone is not enough to invoke
`Kc_eq_sum_ncard`). -/
theorem extF_Wuv_eq_image (H : SimpleGraph W) (S T : Set W) :
    Wuv (extF H S T) (Sum.inr true) (Sum.inr false) =
      (Sum.inl : W → W ⊕ Bool) '' (S ∩ T) := by
  ext p
  simp only [Wuv, SimpleGraph.mem_commonNeighbors, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases p with x | b
    · exact ⟨x, ⟨(extF_adj_inr_true_inl H S T x).mp h1,
        (extF_adj_inr_false_inl H S T x).mp h2⟩, rfl⟩
    · cases b with
      | true => exact absurd h1 (extF H S T).irrefl
      | false => exact absurd h2 (extF H S T).irrefl
  · rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
    exact ⟨(extF_adj_inr_true_inl H S T x).mpr hxS, (extF_adj_inr_false_inl H S T x).mpr hxT⟩

/-- **`K_c(u,v) = 0` when `S ∩ T = ∅`**: with `S` and `T` disjoint, `u` and `v` have no
common neighbour in `F`, so no edge at `u` or `v` can be `K`-counted. -/
theorem Kc_eq_zero_of_disjoint (H : SimpleGraph W) {S T : Set W} (hST : S ∩ T = ∅) :
    Kc (extF H S T) (Sum.inr true) (Sum.inr false) = 0 := by
  have hne : (Sum.inr true : W ⊕ Bool) ≠ Sum.inr false := by simp
  have hWuv : Wuv (extF H S T) (Sum.inr true) (Sum.inr false) = ∅ := by
    rw [extF_Wuv_eq_image, hST, Set.image_empty]
  rw [Kc_eq_sum_ncard (extF H S T) hne]
  have h1 : {w : W ⊕ Bool | w ∈ Wuv (extF H S T) (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr true, w) ∈ Ew (extF H S T)} = ∅ := by
    rw [hWuv]; ext w; simp
  have h2 : {w : W ⊕ Bool | w ∈ Wuv (extF H S T) (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr false, w) ∈ Ew (extF H S T)} = ∅ := by
    rw [hWuv]; ext w; simp
  rw [h1, h2, Set.ncard_empty]

/-- ★★ **The five vanishings**: when `H ∈ 𝓑`, `S ∩ T = ∅` and
`D_inc(u,v) = 1`, every one of `χ, W(u,v), Z(u,v), R_c(u,v), U_a(u,v), U_a(v,u)` is `0`. -/
theorem pst_a_vanish (H : SimpleGraph W) (hH : IsBalCBUnion H) {S T : Set W}
    (hST : S ∩ T = ∅) (hDinc : Dinc (extF H S T) (Sum.inr true) (Sum.inr false) = 1) :
    Chi H S T = 0 ∧ Wcount H S T = 0 ∧ Zcount H S T = 0 ∧
      Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0 ∧
      Ua (extF H S T) (Sum.inr true) (Sum.inr false) = 0 ∧
      Ua (extF H S T) (Sum.inr false) (Sum.inr true) = 0 := by
  obtain ⟨hchi, hW, hUa1, hUa2, hK⟩ := (lemma_SAT H hH S T).mp hDinc
  have hK0 := Kc_eq_zero_of_disjoint H hST
  rw [hK0] at hK
  refine ⟨hchi, hW, ?_, ?_, hUa1, hUa2⟩ <;> omega

/-! #### Clause (i): `S = T = ∅`

The simplest case: `u,v` form their own
new `K_2` component, every `H`-class passes through unchanged.  Exercises the
witness-construction shape clause (ii) will need, at the cheapest possible instance. -/

/-- **THEOREM PST-A, clause (i)**: `S = T = ∅` gives
`extF H ∅ ∅ ∈ 𝓑`. -/
theorem pst_a_case_empty (H : SimpleGraph W) (hH : IsBalCBUnion H) :
    IsBalCBUnion (extF H (∅ : Set W) (∅ : Set W)) := by
  classical
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  set same' : W ⊕ Bool → W ⊕ Bool → Prop := fun a b =>
    match a, b with
    | Sum.inl x, Sum.inl y => same x y
    | Sum.inr _, Sum.inr _ => True
    | _, _ => False with hsame'_def
  set part' : W ⊕ Bool → Bool := fun a =>
    match a with
    | Sum.inl x => part x
    | Sum.inr true => true
    | Sum.inr false => false with hpart'_def
  have hsame'_ll : ∀ x y : W, same' (Sum.inl x) (Sum.inl y) = same x y := fun _ _ => rfl
  have hsame'_rr : ∀ b c : Bool, same' (Sum.inr b) (Sum.inr c) = True := fun _ _ => rfl
  have hsame'_lr : ∀ (x : W) (b : Bool), same' (Sum.inl x) (Sum.inr b) = False := fun _ _ => rfl
  have hsame'_rl : ∀ (b : Bool) (x : W), same' (Sum.inr b) (Sum.inl x) = False := fun _ _ => rfl
  have hpart'_l : ∀ x : W, part' (Sum.inl x) = part x := fun _ => rfl
  have hpart'_u : part' (Sum.inr true) = true := rfl
  have hpart'_v : part' (Sum.inr false) = false := rfl
  refine ⟨same', part', ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- refl
    intro a
    rcases a with x | b
    · rw [hsame'_ll x x]; exact hequiv.refl x
    · rw [hsame'_rr b b]; trivial
  · -- symm
    intro a b hab
    rcases a with x | bx <;> rcases b with y | by'
    · rw [hsame'_ll x y] at hab; rw [hsame'_ll y x]; exact hequiv.symm hab
    · rw [hsame'_lr x by'] at hab; exact hab.elim
    · rw [hsame'_rl bx y] at hab; exact hab.elim
    · rw [hsame'_rr by' bx]; trivial
  · -- trans
    intro a b c hab hbc
    rcases a with x | bx <;> rcases b with y | by' <;> rcases c with z | bz
    · rw [hsame'_ll x y] at hab; rw [hsame'_ll y z] at hbc; rw [hsame'_ll x z]
      exact hequiv.trans hab hbc
    · rw [hsame'_lr y bz] at hbc; exact hbc.elim
    · rw [hsame'_lr x by'] at hab; exact hab.elim
    · rw [hsame'_lr x by'] at hab; exact hab.elim
    · rw [hsame'_rl bx y] at hab; exact hab.elim
    · rw [hsame'_rl bx y] at hab; exact hab.elim
    · rw [hsame'_rl by' z] at hbc; exact hbc.elim
    · rw [hsame'_rr bx bz]; trivial
  · -- adjacency iff
    intro a b
    rcases a with x | bx <;> rcases b with y | by'
    · rw [extF_adj_inl_inl, hsame'_ll x y, hpart'_l x, hpart'_l y]; exact hbip x y
    · cases by' with
      | true => rw [extF_adj_inl_inr_true, hsame'_lr x true]; simp
      | false => rw [extF_adj_inl_inr_false, hsame'_lr x false]; simp
    · cases bx with
      | true => rw [extF_adj_inr_true_inl, hsame'_rl true y]; simp
      | false => rw [extF_adj_inr_false_inl, hsame'_rl false y]; simp
    · rw [hsame'_rr bx by', true_and]
      cases bx <;> cases by'
      · rw [hpart'_v]
        exact ⟨fun h => absurd h (extF H ∅ ∅).irrefl, fun h => absurd h (by simp)⟩
      · rw [hpart'_v, hpart'_u]
        exact ⟨fun _ => by simp, fun _ => (extF_adj_uv H ∅ ∅).symm⟩
      · rw [hpart'_u, hpart'_v]
        exact ⟨fun _ => by simp, fun _ => extF_adj_uv H ∅ ∅⟩
      · rw [hpart'_u]
        exact ⟨fun h => absurd h (extF H ∅ ∅).irrefl, fun h => absurd h (by simp)⟩
  · -- bal1
    intro a
    rcases a with x | bx
    · have himgT : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
          (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_ll x y, hpart'_l y]
        · simp [hsame'_lr x by']
      have himgF : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
          (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_ll x y, hpart'_l y]
        · simp [hsame'_lr x by']
      rw [himgT, himgF, Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inl_injective]
      exact hbal1 x
    · have hT : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = true} = {Sum.inr true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      have hF : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = false} = {Sum.inr false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      rw [hT, hF, Set.ncard_singleton, Set.ncard_singleton]; omega
  · -- bal2
    intro a
    rcases a with x | bx
    · have himgT : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
          (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_ll x y, hpart'_l y]
        · simp [hsame'_lr x by']
      have himgF : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
          (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_ll x y, hpart'_l y]
        · simp [hsame'_lr x by']
      rw [himgT, himgF, Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inl_injective]
      exact hbal2 x
    · have hT : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = true} = {Sum.inr true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      have hF : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = false} = {Sum.inr false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      rw [hT, hF, Set.ncard_singleton, Set.ncard_singleton]; omega
  · -- odd
    intro a b ha hb
    rcases a with x | bx
    · rcases b with y | by'
      · have hcardx : {c : W ⊕ Bool | same' (Sum.inl x) c}.ncard = {c : W | same x c}.ncard := by
          have heq : {c : W ⊕ Bool | same' (Sum.inl x) c} =
              (Sum.inl : W → W ⊕ Bool) '' {c : W | same x c} := by
            ext c
            rcases c with z | bz
            · simp [hsame'_ll x z]
            · simp [hsame'_lr x bz]
          rw [heq, Set.ncard_image_of_injective _ Sum.inl_injective]
        have hcardy : {c : W ⊕ Bool | same' (Sum.inl y) c}.ncard = {c : W | same y c}.ncard := by
          have heq : {c : W ⊕ Bool | same' (Sum.inl y) c} =
              (Sum.inl : W → W ⊕ Bool) '' {c : W | same y c} := by
            ext c
            rcases c with z | bz
            · simp [hsame'_ll y z]
            · simp [hsame'_lr y bz]
          rw [heq, Set.ncard_image_of_injective _ Sum.inl_injective]
        rw [hcardx] at ha
        rw [hcardy] at hb
        rw [hsame'_ll x y]
        exact hodd x y ha hb
      · exfalso
        have hcardb : {c : W ⊕ Bool | same' (Sum.inr by') c}.ncard = 2 := by
          have heq : {c : W ⊕ Bool | same' (Sum.inr by') c} =
              ({Sum.inr true, Sum.inr false} : Set (W ⊕ Bool)) := by
            ext c
            rcases c with z | bz
            · simp [hsame'_rl by' z]
            · simp [hsame'_rr by' bz]
          rw [heq]
          exact Set.ncard_pair (by simp)
        rw [hcardb] at hb
        exact (by decide : ¬ Odd 2) hb
    · exfalso
      have hcarda : {c : W ⊕ Bool | same' (Sum.inr bx) c}.ncard = 2 := by
        have heq : {c : W ⊕ Bool | same' (Sum.inr bx) c} =
            ({Sum.inr true, Sum.inr false} : Set (W ⊕ Bool)) := by
          ext c
          rcases c with z | bz
          · simp [hsame'_rl bx z]
          · simp [hsame'_rr bx bz]
        rw [heq]
        exact Set.ncard_pair (by simp)
      rw [hcarda] at ha
      exact (by decide : ¬ Odd 2) ha

/-! #### The closure lemma

A nonempty subset of one `same`-class, closed under `H`-adjacency, is the WHOLE class. Needed
for Case 1 (`S ≠ ∅, T = ∅`: `Z = 0` gives "`S` inside one class", `R_c = 0` gives "`S` closed
under `H.Adj`") and for Case 3 (the same-component sub-claim). `same_of_reachable` goes the
WRONG direction (reachable ⟹ same, not "closed ⟹ everything reachable/absorbed") — this is
genuinely new content, not a repackaging. -/

/-- ★★ **THEOREM (closure)**: if `A` contains `a₀` and is closed under `H.Adj`
(`∀ p ∈ A, ∀ q, H.Adj p q → q ∈ A`), then every element of `a₀`'s `same`-class lies in `A`.
Two-step argument: if `a₀`'s class has an element of the OPPOSITE `part` value, it is absorbed
directly (adjacent to `a₀`), and every other class member is then absorbed via ONE more
adjacency step through that absorbed opposite-part witness (same-part members are adjacent to
it, opposite-part members are adjacent to `a₀` itself). If the opposite part is EMPTY, BALANCE
forces `a₀`'s own class to be the singleton `{a₀}` (the `b_i = 0` degenerate case), so there is
nothing else to absorb. -/
theorem same_class_of_closed (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {A : Set W} {a0 : W} (ha0 : a0 ∈ A) (hclosed : ∀ p ∈ A, ∀ q, H.Adj p q → q ∈ A) :
    ∀ c, same a0 c → c ∈ A := by
  classical
  by_cases hopp : {c : W | same a0 c ∧ part c ≠ part a0}.Nonempty
  · obtain ⟨r0, hr0⟩ := hopp
    have hAr0 : r0 ∈ A := hclosed a0 ha0 r0 ((hbip a0 r0).mpr ⟨hr0.1, hr0.2.symm⟩)
    intro c hc
    by_cases hpc : part c = part a0
    · by_cases hca0 : c = a0
      · rw [hca0]; exact ha0
      · have hadj : H.Adj c r0 := (hbip c r0).mpr
          ⟨hequiv.trans (hequiv.symm hc) hr0.1, by rw [hpc]; exact hr0.2.symm⟩
        exact hclosed r0 hAr0 c hadj.symm
    · exact hclosed a0 ha0 c ((hbip a0 c).mpr ⟨hc, fun h => hpc h.symm⟩)
  · intro c hc
    by_contra hcA
    have hcne : c ≠ a0 := fun h => hcA (h ▸ ha0)
    have hcpart : part c = part a0 := by
      by_contra hne
      exact hopp ⟨c, hc, hne⟩
    have h2le : 2 ≤ {b : W | same a0 b ∧ part b = part a0}.ncard := by
      have hsub : ({a0, c} : Set W) ⊆ {b : W | same a0 b ∧ part b = part a0} := by
        intro z hz
        rcases hz with rfl | rfl
        · exact ⟨hequiv.refl _, rfl⟩
        · exact ⟨hc, hcpart⟩
      calc (2 : ℕ) = ({a0, c} : Set W).ncard := (Set.ncard_pair hcne.symm).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hoppEmpty : {b : W | same a0 b ∧ part b ≠ part a0}.ncard = 0 := by
      rw [Set.not_nonempty_iff_eq_empty] at hopp
      rw [hopp]; exact Set.ncard_empty _
    by_cases hpa : part a0 = true
    · have heq1 : {b : W | same a0 b ∧ part b = part a0} =
          {b : W | same a0 b ∧ part b = true} := by rw [hpa]
      have heq2 : {b : W | same a0 b ∧ part b ≠ part a0} =
          {b : W | same a0 b ∧ part b = false} := by rw [hpa]; ext z; simp
      rw [heq1] at h2le; rw [heq2] at hoppEmpty
      have := hbal1 a0; omega
    · have hpaf : part a0 = false := Bool.eq_false_iff.mpr hpa
      have heq1 : {b : W | same a0 b ∧ part b = part a0} =
          {b : W | same a0 b ∧ part b = false} := by rw [hpaf]
      have heq2 : {b : W | same a0 b ∧ part b ≠ part a0} =
          {b : W | same a0 b ∧ part b = true} := by rw [hpaf]; ext z; simp
      rw [heq1] at h2le; rw [heq2] at hoppEmpty
      have := hbal2 a0; omega

/-! #### Case 1 assembly — bridge lemmas (a)/(b)

The two small bridges standing between `pst_a_vanish`'s `Zcount = 0`/
`Rc = 0` outputs and `same_class_of_closed`'s `hAsub`-shaped input. Both stated at general
`S, T` (not specialised to `T = ∅`) since Case 3's sub-claim will also want them. -/

/-- ★ **Bridge (a)**: `Z(u,v) = 0` forces any two `S`-elements (or any two `T`-elements) into
the SAME `same`-class. `mem_ZPairs_iff`'s contrapositive: if `x, y` (both in `S`, or both in
`T`) were in different classes, `H ∈ 𝓑`'s structure (`hbip` + `hequiv`-transitivity through any
common neighbour) forces `x ≠ y`, `¬H.Adj x y`, `H.commonNeighbors x y = ∅` — exactly a
`ZPairs` witness, contradicting `Z = 0`. -/
theorem z0_same_of_mem (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    {S T : Set W} (hZ0 : Zcount H S T = 0) {x y : W}
    (hmem : (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) : same x y := by
  classical
  by_contra hns
  have hne : x ≠ y := fun h => hns (h ▸ hequiv.refl x)
  have hnadj : ¬ H.Adj x y := fun h => hns ((hbip x y).mp h).1
  have hcn : H.commonNeighbors x y = ∅ := by
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxz, hyz⟩
    exact hns (hequiv.trans ((hbip x z).mp hxz).1 (hequiv.symm ((hbip y z).mp hyz).1))
  have hmemZ : s(x, y) ∈ ZPairs H S T := (mem_ZPairs_iff H S T x y).mpr ⟨hne, hnadj, hcn, hmem⟩
  have hZpos : 0 < Zcount H S T := (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(x, y), hmemZ⟩
  omega

/-- ★ **Bridge (b)**: `R_c(u,v) = 0` forces `S ∪ T` closed under `H.Adj` — any `H`-edge with
one end in `S ∪ T` has its other end in `S ∪ T` too. Read off `catC`/`Anon`'s definitions
directly: an outside neighbour `q` of an `S ∪ T`-vertex `p` would put `q ∈ catC (extF H S T) u
v` (neither adjacent to `u` nor `v` in `F`, since `q ∉ S`, `q ∉ T`) with `s(u,q) ∈ Anon F` (or
`s(v,q)`, depending which of `S`/`T` holds `p`) witnessed by `p` as the common neighbour — an
`R_c`-counted pair, contradicting `R_c = 0`. Needs no `H ∈ 𝓑` hypothesis at all — purely `extF`
structural. -/
theorem rc0_closed_union (H : SimpleGraph W) (S T : Set W)
    (hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0) :
    ∀ p q : W, H.Adj p q → p ∈ S ∪ T → q ∈ S ∪ T := by
  classical
  intro p q hpq hpST
  by_contra hqST
  rw [Set.mem_union, not_or] at hqST
  obtain ⟨hqS, hqT⟩ := hqST
  have hRcEmpty : {r : (W ⊕ Bool) × (W ⊕ Bool) | (r.1 = Sum.inr true ∨ r.1 = Sum.inr false) ∧
      r.2 ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) ∧
      s(r.1, r.2) ∈ Anon (extF H S T)} = ∅ :=
    (Set.ncard_eq_zero (Set.toFinite _)).mp hRc0
  have hqcatC : Sum.inl q ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) :=
    ⟨Sum.inl_ne_inr, Sum.inl_ne_inr, by rw [extF_adj_inr_true_inl]; exact hqS,
      by rw [extF_adj_inr_false_inl]; exact hqT⟩
  rcases hpST with hpS | hpT
  · have hadjUp : (extF H S T).Adj (Sum.inr true) (Sum.inl p) :=
      (extF_adj_inr_true_inl H S T p).mpr hpS
    have hadjPq : (extF H S T).Adj (Sum.inl p) (Sum.inl q) := (extF_adj_inl_inl H S T p q).mpr hpq
    have hcn : ((extF H S T).commonNeighbors (Sum.inr true) (Sum.inl q)).Nonempty :=
      ⟨Sum.inl p, (extF H S T).mem_commonNeighbors.mpr ⟨hadjUp, hadjPq.symm⟩⟩
    have hAnon : s(Sum.inr true, Sum.inl q) ∈ Anon (extF H S T) :=
      (mem_Anon_iff (extF H S T) (Sum.inr true) (Sum.inl q)).mpr
        ⟨Sum.inr_ne_inl, by rw [extF_adj_inr_true_inl]; exact hqS, hcn⟩
    have hmemRc : (Sum.inr true, Sum.inl q) ∈
        {r : (W ⊕ Bool) × (W ⊕ Bool) | (r.1 = Sum.inr true ∨ r.1 = Sum.inr false) ∧
          r.2 ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) ∧
          s(r.1, r.2) ∈ Anon (extF H S T)} := ⟨Or.inl rfl, hqcatC, hAnon⟩
    rw [hRcEmpty] at hmemRc
    exact hmemRc
  · have hadjVp : (extF H S T).Adj (Sum.inr false) (Sum.inl p) :=
      (extF_adj_inr_false_inl H S T p).mpr hpT
    have hadjPq : (extF H S T).Adj (Sum.inl p) (Sum.inl q) := (extF_adj_inl_inl H S T p q).mpr hpq
    have hcn : ((extF H S T).commonNeighbors (Sum.inr false) (Sum.inl q)).Nonempty :=
      ⟨Sum.inl p, (extF H S T).mem_commonNeighbors.mpr ⟨hadjVp, hadjPq.symm⟩⟩
    have hAnon : s(Sum.inr false, Sum.inl q) ∈ Anon (extF H S T) :=
      (mem_Anon_iff (extF H S T) (Sum.inr false) (Sum.inl q)).mpr
        ⟨Sum.inr_ne_inl, by rw [extF_adj_inr_false_inl]; exact hqT, hcn⟩
    have hmemRc : (Sum.inr false, Sum.inl q) ∈
        {r : (W ⊕ Bool) × (W ⊕ Bool) | (r.1 = Sum.inr true ∨ r.1 = Sum.inr false) ∧
          r.2 ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) ∧
          s(r.1, r.2) ∈ Anon (extF H S T)} := ⟨Or.inr rfl, hqcatC, hAnon⟩
    rw [hRcEmpty] at hmemRc
    exact hmemRc

/-! #### Case 1 closure: `S ≠ ∅, T = ∅` (and symmetric `T ≠ ∅, S = ∅`)

Closed via bridges (a)/(b) + `same_class_of_closed` +
`lemma_swallow_component`. Both bridges were built at the
GENERAL `S,T` form specifically so this closure — and its symmetric twin — reuse the same two
lemmas rather than needing a `T=∅`-specialised restatement of each. -/

/-- ★★ **Case 1, `S ≠ ∅, T = ∅` branch**: under the five vanishings (`W=Z=R_c=0`), `S` is
exactly one `H`-class, singleton. This IS clause (ii)'s `b_i = 0` degenerate instance
(`{S,T} = {X_i,∅}` with `X_i = S = {x0}`, `C_i = K_1`). Bridge (a) gives `S ⊆ class(x0)`
(any `S`-element is `same` any other, since `Z=0`); bridge (b) + `same_class_of_closed` give
`class(x0) ⊆ S` (`x0`'s class is closed under `H.Adj` inside `S ∪ ∅ = S`, since `R_c=0`);
`lemma_swallow_component` collapses `class(x0)` itself to the singleton `{x0}` (`W=0`). -/
theorem pst_a_case1_singleton_S (H : SimpleGraph W) (hH : IsBalCBUnion H) {S : Set W}
    (hSne : S.Nonempty) (hW0 : Wcount H S ∅ = 0) (hZ0 : Zcount H S ∅ = 0)
    (hRc0 : Rc (extF H S ∅) (Sum.inr true) (Sum.inr false) = 0) :
    ∃ x0, S = {x0} := by
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  obtain ⟨x0, hx0⟩ := hSne
  refine ⟨x0, ?_⟩
  have hsub : ∀ c, same x0 c → c ∈ S := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hx0
    intro p hp q hpq
    rcases rc0_closed_union H S ∅ hRc0 p q hpq (Or.inl hp) with h | h
    · exact h
    · exact h.elim
  have hsup : ∀ s ∈ S, same x0 s :=
    fun s hs => z0_same_of_mem H hequiv hbip hZ0 (Or.inl ⟨hx0, hs⟩)
  have hsingleton : ∀ y, same x0 y → y = x0 :=
    lemma_swallow_component H S ∅ hequiv hbip hbal1 hbal2 hW0 (Or.inl hsub)
  ext s
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hsS => hsingleton s (hsup s hsS), fun hseq => by rw [hseq]; exact hx0⟩

/-- ★★ **Case 1, symmetric `T ≠ ∅, S = ∅` branch** (`u ↔ v` swap of `pst_a_case1_singleton_S`).
Identical proof shape, `Or.inr` throughout instead of `Or.inl`, exploiting that bridges (a)/(b)
and `lemma_swallow_component` were all built at the general `S,T` form. -/
theorem pst_a_case1_singleton_T (H : SimpleGraph W) (hH : IsBalCBUnion H) {T : Set W}
    (hTne : T.Nonempty) (hW0 : Wcount H ∅ T = 0) (hZ0 : Zcount H ∅ T = 0)
    (hRc0 : Rc (extF H ∅ T) (Sum.inr true) (Sum.inr false) = 0) :
    ∃ x0, T = {x0} := by
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  obtain ⟨x0, hx0⟩ := hTne
  refine ⟨x0, ?_⟩
  have hsub : ∀ c, same x0 c → c ∈ T := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hx0
    intro p hp q hpq
    rcases rc0_closed_union H ∅ T hRc0 p q hpq (Or.inr hp) with h | h
    · exact h.elim
    · exact h
  have hsup : ∀ t ∈ T, same x0 t :=
    fun t ht => z0_same_of_mem H hequiv hbip hZ0 (Or.inr ⟨hx0, ht⟩)
  have hsingleton : ∀ y, same x0 y → y = x0 :=
    lemma_swallow_component H ∅ T hequiv hbip hbal1 hbal2 hW0 (Or.inr hsub)
  ext s
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hsT => hsingleton s (hsup s hsT), fun hseq => by rw [hseq]; exact hx0⟩

/-! #### Clause (ii), general witness construction

Given `{S,T} = {X_i,Y_i}` for one component `C_i = K_{X_i,Y_i}` of `H`, represented by `x0 ∈
X_i` (`S = X_i` = the `true`-part of `x0`'s class, `T = Y_i` = the `false`-part): construct
`(same',part')` for `F = extF H S T` merging `u,v` into `x0`'s class (`v` joins the `true`
side with `S`, `u` joins the `false` side with `T`) -- exactly `K_{X_i∪\{v\},Y_i∪\{u\}}`. The
mirrored `S=Y_i,T=X_i` orientation is the `u↔v` swap, reached by transport across
`extF_swap_isBalCBUnion` below (no second construction is built). -/

/-- ★★★ **Clause (ii), general witness construction**, one orientation. Parity falls out
free: the merged class's `ncard` is the old class's `ncard + 2` (an even shift), so `Odd` is
unaffected — no standalone parity lemma is needed. Every other
`H`-class passes through `same'`/`part'` UNCHANGED (`same'(inl x)(inl y) := same x y`, no
merging of two distinct original classes -- only `x0`'s own class is extended). -/
theorem pst_a_case_component (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (hodd : ∀ a b, Odd {c | same a c}.ncard → Odd {c | same b c}.ncard → same a b)
    {S T : Set W} {x0 : W}
    (hS : S = {c : W | same x0 c ∧ part c = true})
    (hT : T = {c : W | same x0 c ∧ part c = false}) :
    IsBalCBUnion (extF H S T) := by
  classical
  have hbne : ∀ b : Bool, b ≠ false ↔ b = true := by intro b; cases b <;> simp
  have hbne' : ∀ b : Bool, b ≠ true ↔ b = false := by intro b; cases b <;> simp
  set same' : W ⊕ Bool → W ⊕ Bool → Prop := fun a b =>
    match a, b with
    | Sum.inl x, Sum.inl y => same x y
    | Sum.inl x, Sum.inr _ => same x0 x
    | Sum.inr _, Sum.inl y => same x0 y
    | Sum.inr _, Sum.inr _ => True with hsame'_def
  set part' : W ⊕ Bool → Bool := fun a =>
    match a with
    | Sum.inl x => part x
    | Sum.inr true => false
    | Sum.inr false => true with hpart'_def
  have hsame'_ll : ∀ x y : W, same' (Sum.inl x) (Sum.inl y) = same x y := fun _ _ => rfl
  have hsame'_lr : ∀ (x : W) (b : Bool), same' (Sum.inl x) (Sum.inr b) = same x0 x := fun _ _ => rfl
  have hsame'_rl : ∀ (b : Bool) (x : W), same' (Sum.inr b) (Sum.inl x) = same x0 x := fun _ _ => rfl
  have hsame'_rr : ∀ b c : Bool, same' (Sum.inr b) (Sum.inr c) = True := fun _ _ => rfl
  have hpart'_l : ∀ x : W, part' (Sum.inl x) = part x := fun _ => rfl
  have hpart'_u : part' (Sum.inr true) = false := rfl
  have hpart'_v : part' (Sum.inr false) = true := rfl
  refine ⟨same', part', ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- refl
    intro a
    rcases a with x | b
    · rw [hsame'_ll x x]; exact hequiv.refl x
    · rw [hsame'_rr b b]; trivial
  · -- symm
    intro a b hab
    rcases a with x | bx <;> rcases b with y | by'
    · rw [hsame'_ll x y] at hab; rw [hsame'_ll y x]; exact hequiv.symm hab
    · rw [hsame'_lr x by'] at hab; rw [hsame'_rl by' x]; exact hab
    · rw [hsame'_rl bx y] at hab; rw [hsame'_lr y bx]; exact hab
    · rw [hsame'_rr bx by']; trivial
  · -- trans
    intro a b c hab hbc
    rcases a with x | bx <;> rcases b with y | by' <;> rcases c with z | bz
    · rw [hsame'_ll x y] at hab; rw [hsame'_ll y z] at hbc; rw [hsame'_ll x z]
      exact hequiv.trans hab hbc
    · rw [hsame'_ll x y] at hab; rw [hsame'_lr y bz] at hbc; rw [hsame'_lr x bz]
      exact hequiv.trans hbc (hequiv.symm hab)
    · rw [hsame'_lr x by'] at hab; rw [hsame'_rl by' z] at hbc; rw [hsame'_ll x z]
      exact hequiv.trans (hequiv.symm hab) hbc
    · rw [hsame'_lr x by'] at hab; rw [hsame'_lr x bz]; exact hab
    · rw [hsame'_rl bx y] at hab; rw [hsame'_ll y z] at hbc; rw [hsame'_rl bx z]
      exact hequiv.trans hab hbc
    · rw [hsame'_rr bx bz]; trivial
    · rw [hsame'_rl by' z] at hbc; rw [hsame'_rl bx z]; exact hbc
    · rw [hsame'_rr bx bz]; trivial
  · -- adjacency iff
    intro a b
    rcases a with x | bx <;> rcases b with y | by'
    · rw [extF_adj_inl_inl, hsame'_ll x y, hpart'_l x, hpart'_l y]; exact hbip x y
    · cases by' with
      | true =>
        rw [extF_adj_inl_inr_true, hsame'_lr x true, hpart'_l x, hpart'_u, hS, hbne (part x)]
        simp only [Set.mem_setOf_eq]
      | false =>
        rw [extF_adj_inl_inr_false, hsame'_lr x false, hpart'_l x, hpart'_v, hT, hbne' (part x)]
        simp only [Set.mem_setOf_eq]
    · cases bx with
      | true =>
        rw [extF_adj_inr_true_inl, hsame'_rl true y, hpart'_u, hpart'_l y, hS, ne_comm,
          hbne (part y)]
        simp only [Set.mem_setOf_eq]
      | false =>
        rw [extF_adj_inr_false_inl, hsame'_rl false y, hpart'_v, hpart'_l y, hT, ne_comm,
          hbne' (part y)]
        simp only [Set.mem_setOf_eq]
    · cases bx with
      | true =>
        cases by' with
        | true => simp [extF.eq_1]
        | false =>
          rw [hsame'_rr true false, hpart'_u, hpart'_v]
          exact ⟨fun _ => ⟨trivial, by simp⟩, fun _ => extF_adj_uv H S T⟩
      | false =>
        cases by' with
        | true =>
          rw [hsame'_rr false true, hpart'_v, hpart'_u]
          exact ⟨fun _ => ⟨trivial, by simp⟩, fun _ => (extF_adj_uv H S T).symm⟩
        | false => simp [extF.eq_1]
  · -- bal1
    intro a
    rcases a with x | bx
    · by_cases hx : same x0 x
      · have hSx : {y : W | same x y ∧ part y = true} = S := by
          rw [hS]; ext y
          exact ⟨fun ⟨hxy, hp⟩ => ⟨hequiv.trans hx hxy, hp⟩,
            fun ⟨hxy, hp⟩ => ⟨hequiv.trans (hequiv.symm hx) hxy, hp⟩⟩
        have hTx : {y : W | same x y ∧ part y = false} = T := by
          rw [hT]; ext y
          exact ⟨fun ⟨hxy, hp⟩ => ⟨hequiv.trans hx hxy, hp⟩,
            fun ⟨hxy, hp⟩ => ⟨hequiv.trans (hequiv.symm hx) hxy, hp⟩⟩
        have him_true : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} ∪ {Sum.inr false} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · cases by' with
            | true => simp [hsame'_lr x true, hpart'_u]
            | false => simp [hsame'_lr x false, hpart'_v, hx]
        have him_false : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} ∪ {Sum.inr true} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · cases by' with
            | true => simp [hsame'_lr x true, hpart'_u, hx]
            | false => simp [hsame'_lr x false, hpart'_v]
        rw [him_true, him_false, hSx, hTx,
          Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
            (Set.toFinite _),
          Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
            (Set.toFinite _),
          Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_singleton, Set.ncard_singleton]
        have hb0 := hbal1 x0
        rw [← hS, ← hT] at hb0
        omega
      · have heq1 : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · simp [hsame'_lr x by', hx]
        have heq2 : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · simp [hsame'_lr x by', hx]
        rw [heq1, heq2, Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inl_injective]
        exact hbal1 x
    · have him_true : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = true} =
          (Sum.inl : W → W ⊕ Bool) '' S ∪ {Sum.inr false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y, hpart'_l y, hS]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      have him_false : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = false} =
          (Sum.inl : W → W ⊕ Bool) '' T ∪ {Sum.inr true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y, hpart'_l y, hT]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      rw [him_true, him_false,
        Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
          (Set.toFinite _),
        Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
          (Set.toFinite _),
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_singleton, Set.ncard_singleton]
      have hb0 := hbal1 x0
      rw [← hS, ← hT] at hb0
      omega
  · -- bal2
    intro a
    rcases a with x | bx
    · by_cases hx : same x0 x
      · have hSx : {y : W | same x y ∧ part y = true} = S := by
          rw [hS]; ext y
          exact ⟨fun ⟨hxy, hp⟩ => ⟨hequiv.trans hx hxy, hp⟩,
            fun ⟨hxy, hp⟩ => ⟨hequiv.trans (hequiv.symm hx) hxy, hp⟩⟩
        have hTx : {y : W | same x y ∧ part y = false} = T := by
          rw [hT]; ext y
          exact ⟨fun ⟨hxy, hp⟩ => ⟨hequiv.trans hx hxy, hp⟩,
            fun ⟨hxy, hp⟩ => ⟨hequiv.trans (hequiv.symm hx) hxy, hp⟩⟩
        have him_true : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} ∪ {Sum.inr false} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · cases by' with
            | true => simp [hsame'_lr x true, hpart'_u]
            | false => simp [hsame'_lr x false, hpart'_v, hx]
        have him_false : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} ∪ {Sum.inr true} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · cases by' with
            | true => simp [hsame'_lr x true, hpart'_u, hx]
            | false => simp [hsame'_lr x false, hpart'_v]
        rw [him_true, him_false, hSx, hTx,
          Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
            (Set.toFinite _),
          Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
            (Set.toFinite _),
          Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_singleton, Set.ncard_singleton]
        have hb0 := hbal2 x0
        rw [← hS, ← hT] at hb0
        omega
      · have heq1 : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = true} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = true} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · simp [hsame'_lr x by', hx]
        have heq2 : {b : W ⊕ Bool | same' (Sum.inl x) b ∧ part' b = false} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x y ∧ part y = false} := by
          ext b
          rcases b with y | by'
          · simp [hsame'_ll x y, hpart'_l y]
          · simp [hsame'_lr x by', hx]
        rw [heq1, heq2, Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inl_injective]
        exact hbal2 x
    · have him_true : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = true} =
          (Sum.inl : W → W ⊕ Bool) '' S ∪ {Sum.inr false} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y, hpart'_l y, hS]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      have him_false : {b : W ⊕ Bool | same' (Sum.inr bx) b ∧ part' b = false} =
          (Sum.inl : W → W ⊕ Bool) '' T ∪ {Sum.inr true} := by
        ext b
        rcases b with y | by'
        · simp [hsame'_rl bx y, hpart'_l y, hT]
        · cases by' with
          | true => simp [hsame'_rr bx true, hpart'_u]
          | false => simp [hsame'_rr bx false, hpart'_v]
      rw [him_true, him_false,
        Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
          (Set.toFinite _),
        Set.ncard_union_eq (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2))
          (Set.toFinite _),
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_singleton, Set.ncard_singleton]
      have hb0 := hbal2 x0
      rw [← hS, ← hT] at hb0
      omega
  · -- odd
    intro a b ha hb
    have hparity_shift : ∀ n : ℕ, Odd (n + 2) → Odd n := by
      rintro n ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have hcard_touched : ∀ z : W ⊕ Bool,
        (match z with | Sum.inl w => same x0 w | Sum.inr _ => True) →
        {c : W ⊕ Bool | same' z c}.ncard = {y : W | same x0 y}.ncard + 2 := by
      rintro (w | bz) hw
      · have hw' : same x0 w := hw
        have heq : {c : W ⊕ Bool | same' (Sum.inl w) c} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x0 y} ∪ {Sum.inr true, Sum.inr false} := by
          ext c
          rcases c with y | by'
          · simp only [Set.mem_union, Set.mem_image, Set.mem_insert_iff,
              Set.mem_singleton_iff, reduceCtorEq, or_false, Sum.inl.injEq]
            constructor
            · intro hwy; exact ⟨y, hequiv.trans hw' hwy, rfl⟩
            · rintro ⟨y', hy', rfl⟩; exact hequiv.trans (hequiv.symm hw') hy'
          · simp [hsame'_lr w by', hw']
        rw [heq, Set.ncard_union_eq
          (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2)) (Set.toFinite _),
          Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_pair (by simp)]
      · have heq : {c : W ⊕ Bool | same' (Sum.inr bz) c} =
            (Sum.inl : W → W ⊕ Bool) '' {y : W | same x0 y} ∪ {Sum.inr true, Sum.inr false} := by
          ext c
          rcases c with y | by'
          · simp only [Set.mem_union, Set.mem_image, Set.mem_insert_iff,
              Set.mem_singleton_iff, reduceCtorEq, or_false, Sum.inl.injEq]
            constructor
            · intro hy; exact ⟨y, hy, rfl⟩
            · rintro ⟨y', hy', rfl⟩; exact hy'
          · simp [hsame'_rr bz by']
        rw [heq, Set.ncard_union_eq
          (Set.disjoint_left.mpr (by rintro z ⟨y, -, rfl⟩ hz2; simp at hz2)) (Set.toFinite _),
          Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_pair (by simp)]
    have hcard_untouched : ∀ w : W, ¬ same x0 w →
        {c : W ⊕ Bool | same' (Sum.inl w) c}.ncard = {y : W | same w y}.ncard := by
      intro w hw
      have heq : {c : W ⊕ Bool | same' (Sum.inl w) c} =
          (Sum.inl : W → W ⊕ Bool) '' {y : W | same w y} := by
        ext c
        rcases c with y | by'
        · simp [hsame'_ll w y]
        · simp [hsame'_lr w by', hw]
      rw [heq, Set.ncard_image_of_injective _ Sum.inl_injective]
    rcases a with x | bx
    · by_cases hx : same x0 x
      · rcases b with y | by'
        · by_cases hy : same x0 y
          · rw [hsame'_ll x y]; exact hequiv.trans (hequiv.symm hx) hy
          · exfalso
            rw [hcard_untouched y hy] at hb
            rw [hcard_touched (Sum.inl x) hx] at ha
            exact hy (hequiv.symm (hodd y x0 hb (hparity_shift _ ha)))
        · rw [hsame'_lr x by']; exact hx
      · rcases b with y | by'
        · by_cases hy : same x0 y
          · exfalso
            rw [hcard_untouched x hx] at ha
            rw [hcard_touched (Sum.inl y) hy] at hb
            exact hx (hequiv.symm (hodd x x0 ha (hparity_shift _ hb)))
          · rw [hcard_untouched x hx] at ha
            rw [hcard_untouched y hy] at hb
            rw [hsame'_ll x y]; exact hodd x y ha hb
        · exfalso
          rw [hcard_untouched x hx] at ha
          rw [hcard_touched (Sum.inr by') trivial] at hb
          exact hx (hequiv.symm (hodd x x0 ha (hparity_shift _ hb)))
    · rcases b with y | by'
      · by_cases hy : same x0 y
        · rw [hsame'_rl bx y]; exact hy
        · exfalso
          rw [hcard_touched (Sum.inr bx) trivial] at ha
          rw [hcard_untouched y hy] at hb
          exact hy (hequiv.symm (hodd y x0 hb (hparity_shift _ ha)))
      · rw [hsame'_rr bx by']; trivial

/-! #### Case 2 exclusion

`S ≠ ∅, T ≠ ∅`, in DIFFERENT components of `H`: Case 1's argument, applied separately
to `S` (inside its own component) and `T` (inside its own) forces both edgeless (`K_1`),
contradicting `H`'s standing `≤1`-odd-component hypothesis (two odd `K_1`s). Built directly
against the general bridges rather than by literally re-invoking
`pst_a_case1_singleton_S`/`_T` (whose own statements fix the OTHER side to `∅`, not merely
disjoint from the class in question) -- the closure argument is the same shape, adapted to rule
out the `T`-branch of `rc0_closed_union`'s disjunction via the "different classes" hypothesis
instead of `T = ∅` outright. -/

/-- ★★ **Case 2 exclusion**: if `S`'s representative `x0` and `T`'s representative `y0` are in
DIFFERENT `same`-classes, the five vanishings are contradictory -- `S` collapses to `{x0}`,
`T` to `{y0}` (exactly as in Case 1, but for two DIFFERENT singleton classes now), giving `H`
two distinct odd (`K_1`, order `1`) components, contradicting `hodd`. -/
theorem pst_a_case2_excluded (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (hodd : ∀ a b, Odd {c | same a c}.ncard → Odd {c | same b c}.ncard → same a b)
    {S T : Set W} (hW0 : Wcount H S T = 0) (hZ0 : Zcount H S T = 0)
    (hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    {x0 y0 : W} (hx0 : x0 ∈ S) (hy0 : y0 ∈ T) (hdiff : ¬ same x0 y0) : False := by
  have hsub : ∀ c, same x0 c → c ∈ S := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hx0
    intro p hp q hpq
    have hxp : same x0 p := z0_same_of_mem H hequiv hbip hZ0 (Or.inl ⟨hx0, hp⟩)
    have hpq' : same p q := ((hbip p q).mp hpq).1
    have hxq : same x0 q := hequiv.trans hxp hpq'
    rcases rc0_closed_union H S T hRc0 p q hpq (Or.inl hp) with hqS | hqT
    · exact hqS
    · exact absurd (hequiv.trans hxq
        (hequiv.symm (z0_same_of_mem H hequiv hbip hZ0 (Or.inr ⟨hy0, hqT⟩)))) hdiff
  have hsub' : ∀ c, same y0 c → c ∈ T := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hy0
    intro p hp q hpq
    have hyp : same y0 p := z0_same_of_mem H hequiv hbip hZ0 (Or.inr ⟨hy0, hp⟩)
    have hpq' : same p q := ((hbip p q).mp hpq).1
    have hyq : same y0 q := hequiv.trans hyp hpq'
    rcases rc0_closed_union H S T hRc0 p q hpq (Or.inr hp) with hqS | hqT
    · exact absurd (hequiv.trans (z0_same_of_mem H hequiv hbip hZ0 (Or.inl ⟨hx0, hqS⟩))
        (hequiv.symm hyq)) hdiff
    · exact hqT
  have hsingletonS : ∀ y, same x0 y → y = x0 :=
    lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inl hsub)
  have hsingletonT : ∀ y, same y0 y → y = y0 :=
    lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inr hsub')
  have hcardS : {c : W | same x0 c}.ncard = 1 := by
    have hset : {c : W | same x0 c} = {x0} := by
      ext c
      exact ⟨hsingletonS c, fun h => by rw [h]; exact hequiv.refl x0⟩
    rw [hset]; exact Set.ncard_singleton x0
  have hcardT : {c : W | same y0 c}.ncard = 1 := by
    have hset : {c : W | same y0 c} = {y0} := by
      ext c
      exact ⟨hsingletonT c, fun h => by rw [h]; exact hequiv.refl y0⟩
    rw [hset]; exact Set.ncard_singleton y0
  have hoddS : Odd ({c : W | same x0 c}.ncard) := by rw [hcardS]; exact ⟨0, by omega⟩
  have hoddT : Odd ({c : W | same y0 c}.ncard) := by rw [hcardT]; exact ⟨0, by omega⟩
  exact hdiff (hodd x0 y0 hoddS hoddT)

/-! #### Case 3 setup — bridges, the closure shortcut, and the route-elimination core

Case 3 (`S, T` both nonempty, SAME `same`-component) needs (1) the
`S ∪ T = class(x0)` closure fact (cheaper than Case 1/2's -- feed `rc0_closed_union`'s output
straight into `same_class_of_closed` with `A := S ∪ T`, no branch-stripping needed since we
never need to separate `S` from `T` at this stage), (2) a bridge from `Ua = 0` to "not
unclassified" (mirroring `Kc_eq_zero_of_disjoint`'s contrapositive shape), and (3)
`lemma_Ku`'s four-clause disjunction wired against the closure fact to exclude three of the
four routes, leaving only the codegree-`0`-via-the-other-side route. The route-elimination
step is IDENTICAL in shape for `S` (via `u`, `lemma_Ku`) and `T` (via `v`, built as
`lemma_Kv_mp` below) -- factored into one generic lemma, applied to both. -/

/-- ★ **Bridge, `S`-side**: `U_a(u,v) = 0` forces every `w ∈ S` to be not-unclassified at `u`
(mirrors `Kc_eq_zero_of_disjoint`'s contrapositive shape: unfold `Ua`'s `Set.ncard`-based
definition via `Set.ncard_pos`, contradict `Ua = 0`). -/
theorem mem_E0_Ew_of_Ua_eq_zero_S (H : SimpleGraph W) {S T : Set W} (hST : S ∩ T = ∅)
    (hUa0 : Ua (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    {w : W} (hwS : w ∈ S) :
    s(Sum.inr true, Sum.inl w) ∈ E0 (extF H S T) ∪ Ew (extF H S T) := by
  classical
  have hwT : w ∉ T := by
    intro h
    have hmem : w ∈ S ∩ T := Set.mem_inter hwS h
    rw [hST] at hmem
    exact hmem
  have hadj : (extF H S T).Adj (Sum.inr true) (Sum.inl w) :=
    (extF_adj_inr_true_inl H S T w).mpr hwS
  by_cases hcn : (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl w) = ∅
  · exact Set.mem_union_left _ ((mem_E0_iff _ _ _).mpr ⟨hadj, hcn⟩)
  · have hcn' := Set.nonempty_iff_ne_empty.mpr hcn
    have hcatA : Sum.inl w ∈ catA (extF H S T) (Sum.inr true) (Sum.inr false) :=
      ⟨hadj, by simp, fun h => hwT ((extF_adj_inr_false_inl H S T w).mp h)⟩
    by_cases hwit : Wit (extF H S T) (Sum.inr true) (Sum.inl w) = ∅
    · exfalso
      have hmem : Sum.inl w ∈ {x : W ⊕ Bool | x ∈
          catA (extF H S T) (Sum.inr true) (Sum.inr false) ∧
          ((extF H S T).commonNeighbors (Sum.inr true) x).Nonempty ∧
          Wit (extF H S T) (Sum.inr true) x = ∅} := ⟨hcatA, hcn', hwit⟩
      have hpos : 0 < Ua (extF H S T) (Sum.inr true) (Sum.inr false) :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩
      omega
    · have hwit' := Set.nonempty_iff_ne_empty.mpr hwit
      exact Set.mem_union_right _ ((mem_Ew_iff _ _ _).mpr ⟨hadj, hcn', hwit'⟩)

/-- ★ **Bridge, `T`-side mirror** (`v = inr false`, `U_a(v,u) = 0`). -/
theorem mem_E0_Ew_of_Ua_eq_zero_T (H : SimpleGraph W) {S T : Set W} (hST : S ∩ T = ∅)
    (hUa0 : Ua (extF H S T) (Sum.inr false) (Sum.inr true) = 0)
    {w : W} (hwT : w ∈ T) :
    s(Sum.inr false, Sum.inl w) ∈ E0 (extF H S T) ∪ Ew (extF H S T) := by
  classical
  have hwS : w ∉ S := by
    intro h
    have hmem : w ∈ S ∩ T := Set.mem_inter h hwT
    rw [hST] at hmem
    exact hmem
  have hadj : (extF H S T).Adj (Sum.inr false) (Sum.inl w) :=
    (extF_adj_inr_false_inl H S T w).mpr hwT
  by_cases hcn : (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl w) = ∅
  · exact Set.mem_union_left _ ((mem_E0_iff _ _ _).mpr ⟨hadj, hcn⟩)
  · have hcn' := Set.nonempty_iff_ne_empty.mpr hcn
    have hcatA : Sum.inl w ∈ catA (extF H S T) (Sum.inr false) (Sum.inr true) :=
      ⟨hadj, by simp, fun h => hwS ((extF_adj_inr_true_inl H S T w).mp h)⟩
    by_cases hwit : Wit (extF H S T) (Sum.inr false) (Sum.inl w) = ∅
    · exfalso
      have hmem : Sum.inl w ∈ {x : W ⊕ Bool | x ∈
          catA (extF H S T) (Sum.inr false) (Sum.inr true) ∧
          ((extF H S T).commonNeighbors (Sum.inr false) x).Nonempty ∧
          Wit (extF H S T) (Sum.inr false) x = ∅} := ⟨hcatA, hcn', hwit⟩
      have hpos : 0 < Ua (extF H S T) (Sum.inr false) (Sum.inr true) :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩
      omega
    · have hwit' := Set.nonempty_iff_ne_empty.mpr hwit
      exact Set.mem_union_right _ ((mem_Ew_iff _ _ _).mpr ⟨hadj, hcn', hwit'⟩)

/-- ★★ **The `S ∪ T = class(x0)` shortcut**: Case 3's own
closure step is EASIER than Case 1/2's — feed `rc0_closed_union`'s `S ∪ T` disjunction
straight into `same_class_of_closed` with `A := S ∪ T` (no branch-stripping needed), and the
reverse inclusion is bridge (a) applied twice (through the standing same-component witness
`same x0 y0`). -/
theorem pst_a_case3_union_eq_class (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {S T : Set W} (hZ0 : Zcount H S T = 0)
    (hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    {x0 y0 : W} (hx0 : x0 ∈ S) (hy0 : y0 ∈ T) (hsame0 : same x0 y0) :
    S ∪ T = {c : W | same x0 c} := by
  apply Set.Subset.antisymm
  · intro c hc
    rcases hc with hcS | hcT
    · exact z0_same_of_mem H hequiv hbip hZ0 (Or.inl ⟨hx0, hcS⟩)
    · exact hequiv.trans hsame0 (z0_same_of_mem H hequiv hbip hZ0 (Or.inr ⟨hy0, hcT⟩))
  · exact same_class_of_closed H hequiv hbip hbal1 hbal2 (Set.mem_union_left T hx0)
      (fun p hp q hpq => rc0_closed_union H S T hRc0 p q hpq hp)

/-- ★ **Route-elimination core**, shared by the `S`-side and `T`-side (this rank's `q ↔ q'`,
`u ↔ v` symmetry): given `w`'s four-clause "not unclassified" disjunction (`lemma_Ku`'s exact
shape, reused with `S, T` in EITHER order) plus `w`'s own class containment and a witness that
`N_H(w) ∩ S ≠ ∅`, routes (a)/(b)/(d) all fail, leaving only route (c). -/
theorem pst_a_case3_route_elim (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    {S T : Set W} {x0 w : W} (hw0 : same x0 w) (hC : {c : W | same x0 c} = S ∪ T)
    (hSsub : S ⊆ {c : W | same x0 c})
    (hdisj : (H.neighborSet w ∩ S = ∅ ∧ w ∉ T) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {w}) ∨
      (w ∉ T ∧ H.neighborSet w ∩ T = ∅) ∨
      (∃ q : W, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ (w ∉ T ∨ q ∉ T)))
    (hNSne : (H.neighborSet w ∩ S).Nonempty) :
    w ∉ T ∧ H.neighborSet w ∩ T = ∅ := by
  have hNsub : H.neighborSet w ⊆ S ∪ T := by
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    have hsy : same w y := ((hbip w y).mp hy).1
    rw [← hC]
    exact hequiv.trans hw0 hsy
  rcases hdisj with ⟨hempty, -⟩ | ⟨p, hpS, hpT, hpeq⟩ | hc | ⟨q, hqS, -, hnsame, -⟩
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hNSne)
  · exfalso
    have hwmem : w ∈ H.neighborSet p ∩ S := by rw [hpeq]; exact Set.mem_singleton w
    have hAdjpw : H.Adj p w := (SimpleGraph.mem_neighborSet H p w).mp hwmem.1
    have hpw : p ∈ H.neighborSet w := (SimpleGraph.mem_neighborSet H w p).mpr hAdjpw.symm
    rcases hNsub hpw with h | h
    · exact hpS h
    · exact hpT h
  · exact hc
  · exact absurd (hequiv.trans (hequiv.symm hw0) (hSsub hqS)) hnsame

/-- ★ Inside `x0`'s `same`-class, `H`-adjacency is exactly "same class, opposite `part`" --
`N_H(w) = {c | same x0 c ∧ part c ≠ part w}` for any `w` with `same x0 w`. -/
theorem neighborSet_eq_of_mem_class (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    {x0 w : W} (hw0 : same x0 w) :
    H.neighborSet w = {c : W | same x0 c ∧ part c ≠ part w} := by
  ext y
  rw [SimpleGraph.mem_neighborSet, hbip]
  constructor
  · rintro ⟨hwy, hpy⟩
    exact ⟨hequiv.trans hw0 hwy, hpy.symm⟩
  · rintro ⟨hxy, hpy⟩
    exact ⟨hequiv.trans (hequiv.symm hw0) hxy, hpy.symm⟩

/-- ★★ **LEMMA Kv (forward direction only)** — the `T`-side, `v = inr false` mirror of
`lemma_Ku`'s `w ∈ S`, `u`-side criteria, for
`w ∈ T`. Built as a ONE-DIRECTION mirror (`→` only, not the full `↔`) since Case 3's `T`-side
sub-claim only ever DESTRUCTS "`{v,w}` not unclassified" into the four routes, never
constructs it from a route — this roughly halves the mirror's cost relative to a full
`lemma_Kv`. Mechanically adapted from `lemma_Ku`'s `mp` direction (`S ↔ T`, `u ↔ v`,
`true ↔ false` throughout); the shared "claim" sub-lemma is `not_same_of_disjoint_commonNeighbors`
(already top-level, no local copy needed). -/
theorem lemma_Kv_mp (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W) {w : W} (hwT : w ∈ T)
    (hmem : s(Sum.inr false, Sum.inl w) ∈ E0 (extF H S T) ∪ Ew (extF H S T)) :
    (H.neighborSet w ∩ T = ∅ ∧ w ∉ S) ∨
      (∃ p : W, p ∉ T ∧ p ∉ S ∧ H.neighborSet p ∩ T = {w}) ∨
      (w ∉ S ∧ H.neighborSet w ∩ S = ∅) ∨
      (∃ q : W, q ∈ T ∧ q ≠ w ∧ ¬ same w q ∧ (w ∉ S ∨ q ∉ S)) := by
  classical
  rw [Set.mem_union, mem_E0_iff, mem_Ew_iff] at hmem
  rcases hmem with (⟨-, hcn0⟩ | ⟨-, -, hwit⟩)
  · refine Or.inl ⟨?_, ?_⟩
    · rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxmem : Sum.inl x ∈ (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl w) :=
        (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inr_false_inl H S T x).mpr hx.2, (extF_adj_inl_inl H S T w x).mpr hx.1⟩
      rw [hcn0] at hxmem; exact hxmem
    · intro hS
      have hvmem : Sum.inr true ∈
          (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl w) := by
        rw [SimpleGraph.mem_commonNeighbors]
        exact ⟨(extF_adj_uv H S T).symm, (extF_adj_inl_inr_true H S T w).mpr hS⟩
      rw [hcn0] at hvmem; exact hvmem
  · obtain ⟨p, hp | hp⟩ := hwit
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hpnev : p ≠ Sum.inr true := by rintro rfl; exact hpnadj (extF_adj_uv H S T).symm
      obtain ⟨x, rfl⟩ : ∃ x, p = Sum.inl x := by
        rcases p with x | b
        · exact ⟨x, rfl⟩
        · cases b with
          | false => exact absurd rfl hpne
          | true => exact absurd rfl hpnev
      have hxT : x ∉ T := fun h => hpnadj ((extF_adj_inr_false_inl H S T x).mpr h)
      have hwmem : Sum.inl w ∈ (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hwmem
      have hxwH : H.Adj x w := (extF_adj_inl_inl H S T x w).mp hwmem.2
      have hxS : x ∉ S := by
        intro hS
        have hvmem : Sum.inr true ∈
            (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) := by
          rw [SimpleGraph.mem_commonNeighbors]
          exact ⟨(extF_adj_uv H S T).symm, (extF_adj_inl_inr_true H S T x).mpr hS⟩
        rw [hpcn] at hvmem
        exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)
      refine Or.inr (Or.inl ⟨x, hxT, hxS, ?_⟩)
      ext z
      rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzx, hzT⟩
        have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) :=
          (extF H S T).mem_commonNeighbors.mpr
            ⟨(extF_adj_inr_false_inl H S T z).mpr hzT, (extF_adj_inl_inl H S T x z).mpr hzx⟩
        rw [hpcn] at hzmem
        exact Sum.inl.inj (Set.mem_singleton_iff.mp hzmem)
      · rintro rfl
        exact ⟨hxwH, hwT⟩
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hune : Sum.inr false ∈ (extF H S T).commonNeighbors (Sum.inl w) p := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hune
      obtain ⟨-, hpu⟩ := hune
      rcases p with x | b
      · have hxT : x ∈ T := (extF_adj_inl_inr_false H S T x).mp hpu
        have hxwne : x ≠ w := fun h => hpne (congrArg Sum.inl h)
        have hqnadjWw : ¬ H.Adj x w := fun h =>
          hpnadj ((extF_adj_inl_inl H S T w x).mpr h.symm)
        have hcn0' : H.commonNeighbors w x = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [SimpleGraph.mem_commonNeighbors] at hz
          have hzmem : Sum.inl z ∈ (extF H S T).commonNeighbors (Sum.inl w) (Sum.inl x) :=
            (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inl H S T w z).mpr hz.1, (extF_adj_inl_inl H S T x z).mpr hz.2⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
        have hnsame : ¬ same w x :=
          not_same_of_disjoint_commonNeighbors hequiv hbip hbal1 hbal2 hxwne hqnadjWw hcn0'
        have hwS_or : w ∉ S ∨ x ∉ S := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨hwS, hxS⟩ := hcon
          have hvmem : Sum.inr true ∈
              (extF H S T).commonNeighbors (Sum.inl w) (Sum.inl x) := by
            rw [SimpleGraph.mem_commonNeighbors]
            exact ⟨(extF_adj_inl_inr_true H S T w).mpr hwS,
              (extF_adj_inl_inr_true H S T x).mpr hxS⟩
          rw [hpcn] at hvmem
          exact absurd (Set.mem_singleton_iff.mp hvmem) (by simp)
        exact Or.inr (Or.inr (Or.inr ⟨x, hxT, hxwne, hnsame, hwS_or⟩))
      · cases b with
        | true =>
          have hwS : w ∉ S := fun hS => hpnadj ((extF_adj_inl_inr_true H S T w).mpr hS)
          refine Or.inr (Or.inr (Or.inl ⟨hwS, ?_⟩))
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hz
          have hzmem : Sum.inl z ∈
              (extF H S T).commonNeighbors (Sum.inl w) (Sum.inr true) :=
            (extF H S T).mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inl H S T w z).mpr hz.1, (extF_adj_inr_true_inl H S T z).mpr hz.2⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
        | false => exact absurd hpu (extF H S T).irrefl

/-- ★★★ **Case 3 sub-claim, `S`-side** (`S ⊆ X` or
`S ⊆ Y`): a straddling pair `x1 ∈ S ∩ X`, `y1 ∈ S ∩ Y` (`X, Y` the two `part`-classes of
`x0`'s class) forces, via `lemma_Ku` + `pst_a_case3_route_elim` applied once from each side,
`Y ⊆ S` and `X ⊆ S`, hence `T ⊆ S` (since `S ∪ T = X ∪ Y`), contradicting `S ∩ T = ∅` and
`T` nonempty. -/
theorem pst_a_case3_subclaim_S (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {S T : Set W} (hST : S ∩ T = ∅)
    (hUa0 : Ua (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    {x0 : W} (hC : {c : W | same x0 c} = S ∪ T) (hSsub : S ⊆ {c : W | same x0 c})
    (hTne : T.Nonempty) :
    S ⊆ {c : W | same x0 c ∧ part c = true} ∨ S ⊆ {c : W | same x0 c ∧ part c = false} := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hSX, hSY⟩ := hcon
  rw [Set.not_subset] at hSX hSY
  obtain ⟨y1, hy1S, hy1X⟩ := hSX
  obtain ⟨x1, hx1S, hx1Y⟩ := hSY
  have hw01 : same x0 x1 := hSsub hx1S
  have hw02 : same x0 y1 := hSsub hy1S
  have hy1part : part y1 = false := by
    cases hb : part y1 with
    | false => rfl
    | true => exact absurd ⟨hw02, hb⟩ hy1X
  have hx1part : part x1 = true := by
    cases hb : part x1 with
    | true => rfl
    | false => exact absurd ⟨hw01, hb⟩ hx1Y
  have hadj : H.Adj x1 y1 := (hbip x1 y1).mpr
    ⟨hequiv.trans (hequiv.symm hw01) hw02, by rw [hx1part, hy1part]; decide⟩
  have hNSne1 : (H.neighborSet x1 ∩ S).Nonempty :=
    ⟨y1, (SimpleGraph.mem_neighborSet H x1 y1).mpr hadj, hy1S⟩
  have hdisj1 := (lemma_Ku H hequiv hbip hbal1 hbal2 S T hx1S).mp
    (mem_E0_Ew_of_Ua_eq_zero_S H hST hUa0 hx1S)
  have hroute1 := pst_a_case3_route_elim H hequiv hbip hw01 hC hSsub hdisj1 hNSne1
  have hNx1 : H.neighborSet x1 = {c : W | same x0 c ∧ part c = false} := by
    rw [neighborSet_eq_of_mem_class H hequiv hbip hw01, hx1part]
    ext c
    constructor
    · rintro ⟨hsc, hpc⟩
      refine ⟨hsc, ?_⟩
      cases hb : part c with
      | false => rfl
      | true => exact absurd hb hpc
    · rintro ⟨hsc, hpc⟩
      exact ⟨hsc, by rw [hpc]; decide⟩
  have hYsub : {c : W | same x0 c ∧ part c = false} ⊆ S := by
    intro c hc
    have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
    rcases hcST with h | h
    · exact h
    · exfalso
      have hcmem : c ∈ H.neighborSet x1 ∩ T := by rw [hNx1]; exact ⟨hc, h⟩
      rw [hroute1.2] at hcmem
      exact hcmem
  have hadj' : H.Adj y1 x1 := hadj.symm
  have hNSne2 : (H.neighborSet y1 ∩ S).Nonempty :=
    ⟨x1, (SimpleGraph.mem_neighborSet H y1 x1).mpr hadj', hx1S⟩
  have hdisj2 := (lemma_Ku H hequiv hbip hbal1 hbal2 S T hy1S).mp
    (mem_E0_Ew_of_Ua_eq_zero_S H hST hUa0 hy1S)
  have hroute2 := pst_a_case3_route_elim H hequiv hbip hw02 hC hSsub hdisj2 hNSne2
  have hNy1 : H.neighborSet y1 = {c : W | same x0 c ∧ part c = true} := by
    rw [neighborSet_eq_of_mem_class H hequiv hbip hw02, hy1part]
    ext c
    constructor
    · rintro ⟨hsc, hpc⟩
      refine ⟨hsc, ?_⟩
      cases hb : part c with
      | true => rfl
      | false => exact absurd hb hpc
    · rintro ⟨hsc, hpc⟩
      exact ⟨hsc, by rw [hpc]; decide⟩
  have hXsub : {c : W | same x0 c ∧ part c = true} ⊆ S := by
    intro c hc
    have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
    rcases hcST with h | h
    · exact h
    · exfalso
      have hcmem : c ∈ H.neighborSet y1 ∩ T := by rw [hNy1]; exact ⟨hc, h⟩
      rw [hroute2.2] at hcmem
      exact hcmem
  obtain ⟨t0, ht0⟩ := hTne
  have ht0ST : t0 ∈ S ∪ T := Set.mem_union_right S ht0
  have ht0C : same x0 t0 := by rw [← hC] at ht0ST; exact ht0ST
  have ht0S : t0 ∈ S := by
    cases hb : part t0 with
    | false => exact hYsub ⟨ht0C, hb⟩
    | true => exact hXsub ⟨ht0C, hb⟩
  have hcontra : t0 ∈ S ∩ T := ⟨ht0S, ht0⟩
  rw [hST] at hcontra
  exact hcontra

/-- ★★★ **Case 3 sub-claim, `T`-side mirror**: `T ⊆ X` or `T ⊆ Y`, via `lemma_Kv_mp` and
`pst_a_case3_route_elim` re-applied with `S, T` SWAPPED as arguments (the generic lemma is
already symmetric in its own `S, T` slots, so no separate route-elimination core is needed). -/
theorem pst_a_case3_subclaim_T (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {S T : Set W} (hST : S ∩ T = ∅)
    (hUa0' : Ua (extF H S T) (Sum.inr false) (Sum.inr true) = 0)
    {x0 : W} (hC : {c : W | same x0 c} = S ∪ T) (hTsub : T ⊆ {c : W | same x0 c})
    (hSne : S.Nonempty) :
    T ⊆ {c : W | same x0 c ∧ part c = true} ∨ T ⊆ {c : W | same x0 c ∧ part c = false} := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hTX, hTY⟩ := hcon
  rw [Set.not_subset] at hTX hTY
  obtain ⟨y1, hy1T, hy1X⟩ := hTX
  obtain ⟨x1, hx1T, hx1Y⟩ := hTY
  have hw01 : same x0 x1 := hTsub hx1T
  have hw02 : same x0 y1 := hTsub hy1T
  have hy1part : part y1 = false := by
    cases hb : part y1 with
    | false => rfl
    | true => exact absurd ⟨hw02, hb⟩ hy1X
  have hx1part : part x1 = true := by
    cases hb : part x1 with
    | true => rfl
    | false => exact absurd ⟨hw01, hb⟩ hx1Y
  have hadj : H.Adj x1 y1 := (hbip x1 y1).mpr
    ⟨hequiv.trans (hequiv.symm hw01) hw02, by rw [hx1part, hy1part]; decide⟩
  have hCTS : {c : W | same x0 c} = T ∪ S := by rw [hC, Set.union_comm]
  have hNTne1 : (H.neighborSet x1 ∩ T).Nonempty :=
    ⟨y1, (SimpleGraph.mem_neighborSet H x1 y1).mpr hadj, hy1T⟩
  have hdisj1 := lemma_Kv_mp H hequiv hbip hbal1 hbal2 S T hx1T
    (mem_E0_Ew_of_Ua_eq_zero_T H hST hUa0' hx1T)
  have hroute1 := pst_a_case3_route_elim H hequiv hbip hw01 hCTS hTsub hdisj1 hNTne1
  have hNx1 : H.neighborSet x1 = {c : W | same x0 c ∧ part c = false} := by
    rw [neighborSet_eq_of_mem_class H hequiv hbip hw01, hx1part]
    ext c
    constructor
    · rintro ⟨hsc, hpc⟩
      refine ⟨hsc, ?_⟩
      cases hb : part c with
      | false => rfl
      | true => exact absurd hb hpc
    · rintro ⟨hsc, hpc⟩
      exact ⟨hsc, by rw [hpc]; decide⟩
  have hYsub : {c : W | same x0 c ∧ part c = false} ⊆ T := by
    intro c hc
    have hcST : c ∈ T ∪ S := by rw [← hCTS]; exact hc.1
    rcases hcST with h | h
    · exact h
    · exfalso
      have hcmem : c ∈ H.neighborSet x1 ∩ S := by rw [hNx1]; exact ⟨hc, h⟩
      rw [hroute1.2] at hcmem
      exact hcmem
  have hadj' : H.Adj y1 x1 := hadj.symm
  have hNTne2 : (H.neighborSet y1 ∩ T).Nonempty :=
    ⟨x1, (SimpleGraph.mem_neighborSet H y1 x1).mpr hadj', hx1T⟩
  have hdisj2 := lemma_Kv_mp H hequiv hbip hbal1 hbal2 S T hy1T
    (mem_E0_Ew_of_Ua_eq_zero_T H hST hUa0' hy1T)
  have hroute2 := pst_a_case3_route_elim H hequiv hbip hw02 hCTS hTsub hdisj2 hNTne2
  have hNy1 : H.neighborSet y1 = {c : W | same x0 c ∧ part c = true} := by
    rw [neighborSet_eq_of_mem_class H hequiv hbip hw02, hy1part]
    ext c
    constructor
    · rintro ⟨hsc, hpc⟩
      refine ⟨hsc, ?_⟩
      cases hb : part c with
      | true => rfl
      | false => exact absurd hb hpc
    · rintro ⟨hsc, hpc⟩
      exact ⟨hsc, by rw [hpc]; decide⟩
  have hXsub : {c : W | same x0 c ∧ part c = true} ⊆ T := by
    intro c hc
    have hcST : c ∈ T ∪ S := by rw [← hCTS]; exact hc.1
    rcases hcST with h | h
    · exact h
    · exfalso
      have hcmem : c ∈ H.neighborSet y1 ∩ S := by rw [hNy1]; exact ⟨hc, h⟩
      rw [hroute2.2] at hcmem
      exact hcmem
  obtain ⟨s0, hs0⟩ := hSne
  have hs0TS : s0 ∈ T ∪ S := Set.mem_union_right T hs0
  have hs0C : same x0 s0 := by rw [← hCTS] at hs0TS; exact hs0TS
  have hs0T : s0 ∈ T := by
    cases hb : part s0 with
    | false => exact hYsub ⟨hs0C, hb⟩
    | true => exact hXsub ⟨hs0C, hb⟩
  have hcontra : s0 ∈ S ∩ T := ⟨hs0, hs0T⟩
  rw [hST] at hcontra
  exact hcontra

/-- ★★★ **THEOREM PST-A, Case 3** (`S, T` both nonempty, SAME
`same`-component): combining the two sub-claims with balance (ruling out "both `S, T` inside
the same part", which would force the OTHER part empty and hence, by `hbal1`/`hbal2`, that
part's own class size `≤ 1` — too small to hold both disjoint nonempty `S` and `T`) gives
`{S, T} = {X, Y}` exactly — clause (ii)'s general
non-degenerate case. The `u ↔ v` orientation question (whether this needs a mirrored twin, or
whether the final PST-A theorem's own "up to swapping `u, v`" phrasing absorbs the single
built orientation) is left to the assembly stage. -/
theorem pst_a_case3_component (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {S T : Set W} (hST : S ∩ T = ∅)
    (hZ0 : Zcount H S T = 0) (hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    (hUa0 : Ua (extF H S T) (Sum.inr true) (Sum.inr false) = 0)
    (hUa0' : Ua (extF H S T) (Sum.inr false) (Sum.inr true) = 0)
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    {x0 y0 : W} (hx0 : x0 ∈ S) (hy0 : y0 ∈ T) (hsame0 : same x0 y0) :
    (S = {c : W | same x0 c ∧ part c = true} ∧ T = {c : W | same x0 c ∧ part c = false}) ∨
    (S = {c : W | same x0 c ∧ part c = false} ∧ T = {c : W | same x0 c ∧ part c = true}) := by
  classical
  have hC : {c : W | same x0 c} = S ∪ T :=
    (pst_a_case3_union_eq_class H hequiv hbip hbal1 hbal2 hZ0 hRc0 hx0 hy0 hsame0).symm
  have hSsub : S ⊆ {c : W | same x0 c} := by rw [hC]; exact Set.subset_union_left
  have hTsub : T ⊆ {c : W | same x0 c} := by rw [hC]; exact Set.subset_union_right
  have hScl := pst_a_case3_subclaim_S H hequiv hbip hbal1 hbal2 hST hUa0 hC hSsub hTne
  have hTcl := pst_a_case3_subclaim_T H hequiv hbip hbal1 hbal2 hST hUa0' hC hTsub hSne
  have hdisjST : Disjoint S T := Set.disjoint_left.mpr (fun a ha hb => by
    have h : a ∈ S ∩ T := ⟨ha, hb⟩
    rw [hST] at h
    exact h)
  have key : ∀ b : Bool, S ⊆ {c : W | same x0 c ∧ part c = b} →
      T ⊆ {c : W | same x0 c ∧ part c = b} → False := by
    intro b hSb hTb
    have hSTb : S ∪ T ⊆ {c : W | same x0 c ∧ part c = b} := Set.union_subset hSb hTb
    have hfull : {c : W | same x0 c} ⊆ {c : W | same x0 c ∧ part c = b} := by
      rw [hC]; exact hSTb
    have hopp_empty : {c : W | same x0 c ∧ part c = !b} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hsc, hpc⟩
      have hcb := (hfull hsc).2
      rw [hcb] at hpc
      cases b <;> simp at hpc
    have hcard0 : ({c : W | same x0 c ∧ part c = !b} : Set W).ncard = 0 := by
      rw [hopp_empty]; exact Set.ncard_empty _
    have hScard : (S ∪ T).ncard = S.ncard + T.ncard :=
      Set.ncard_union_eq hdisjST (Set.toFinite _)
    have hSTcard_le : (S ∪ T).ncard ≤ ({c : W | same x0 c ∧ part c = b} : Set W).ncard :=
      Set.ncard_le_ncard hSTb (Set.toFinite _)
    have hSpos : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr hSne
    have hTpos : 0 < T.ncard := (Set.ncard_pos (Set.toFinite _)).mpr hTne
    cases b with
    | true =>
      have hb1 := hbal1 x0
      simp only [Bool.not_true] at hcard0
      omega
    | false =>
      have hb2 := hbal2 x0
      simp only [Bool.not_false] at hcard0
      omega
  rcases hScl with hSX | hSY
  · rcases hTcl with hTX | hTY
    · exact absurd (key true hSX hTX) id
    · left
      refine ⟨Set.Subset.antisymm hSX ?_, Set.Subset.antisymm hTY ?_⟩
      · intro c hc
        have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
        rcases hcST with h | h
        · exact h
        · exfalso
          have hcf : part c = false := (hTY h).2
          have hct : part c = true := hc.2
          rw [hcf] at hct
          exact absurd hct (by decide)
      · intro c hc
        have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
        rcases hcST with h | h
        · exfalso
          have hcf : part c = true := (hSX h).2
          have hct : part c = false := hc.2
          rw [hcf] at hct
          exact absurd hct (by decide)
        · exact h
  · rcases hTcl with hTX | hTY
    · right
      refine ⟨Set.Subset.antisymm hSY ?_, Set.Subset.antisymm hTX ?_⟩
      · intro c hc
        have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
        rcases hcST with h | h
        · exact h
        · exfalso
          have hcf : part c = true := (hTX h).2
          have hct : part c = false := hc.2
          rw [hcf] at hct
          exact absurd hct (by decide)
      · intro c hc
        have hcST : c ∈ S ∪ T := by rw [← hC]; exact hc.1
        rcases hcST with h | h
        · exfalso
          have hcf : part c = false := (hSY h).2
          have hct : part c = true := hc.2
          rw [hcf] at hct
          exact absurd hct (by decide)
        · exact h
    · exact absurd (key false hSY hTY) id

/-! #### PST-A final assembly — the orientation fix

`pst_a_case_component` and `pst_a_case3_component` only ever hand
back ONE fixed `(S,T)` orientation (`S` = the `true`-part of `x0`'s class), while Case 1's
singleton output and Case 3's `(S=Y∧T=X)` disjunct can land on the OTHER orientation depending
on `part x0`. Resolved via a route cheaper than either a
full mirrored twin or a case-split baked into the construction itself: `extF H S T` and
`extF H T S` are related by an actual graph ISOMORPHISM (the "swap which of `S`/`T` attaches to
`u`/`v`" relabelling — `Sum.inl` fixed, `Sum.inr true ↔ Sum.inr false`), so `IsBalCBUnion`
transports between the two orientations for FREE via the already-built `IsBalCBUnion.map_iso` —
no mirrored construction, no per-site case-split inside `pst_a_case_component` itself. -/

/-- The "swap `S`/`T`" relabelling of `W ⊕ Bool`: identity on `Sum.inl`, `true ↔ false` on
`Sum.inr`. -/
def extFSwapEquiv : W ⊕ Bool ≃ W ⊕ Bool where
  toFun := fun x => match x with
    | Sum.inl a => Sum.inl a
    | Sum.inr true => Sum.inr false
    | Sum.inr false => Sum.inr true
  invFun := fun x => match x with
    | Sum.inl a => Sum.inl a
    | Sum.inr true => Sum.inr false
    | Sum.inr false => Sum.inr true
  left_inv := by
    rintro (a | b)
    · rfl
    · cases b <;> rfl
  right_inv := by
    rintro (a | b)
    · rfl
    · cases b <;> rfl

theorem extFSwapEquiv_inl (a : W) : extFSwapEquiv (Sum.inl a : W ⊕ Bool) = Sum.inl a := rfl
theorem extFSwapEquiv_true : extFSwapEquiv (Sum.inr true : W ⊕ Bool) = Sum.inr false := rfl
theorem extFSwapEquiv_false : extFSwapEquiv (Sum.inr false : W ⊕ Bool) = Sum.inr true := rfl

/-- `extF H S T` and `extF H T S` are isomorphic, via `extFSwapEquiv`. -/
def extF_swap_iso (H : SimpleGraph W) (S T : Set W) :
    extF H S T ≃g extF H T S := by
  refine ⟨extFSwapEquiv, ?_⟩
  intro x y
  rcases x with a | bx <;> rcases y with b | by'
  · simp [extFSwapEquiv_inl, extF_adj_inl_inl]
  · cases by' with
    | true => simp [extFSwapEquiv_inl, extFSwapEquiv_true, extF_adj_inl_inr_false,
        extF_adj_inl_inr_true]
    | false => simp [extFSwapEquiv_inl, extFSwapEquiv_false, extF_adj_inl_inr_true,
        extF_adj_inl_inr_false]
  · cases bx with
    | true => simp [extFSwapEquiv_inl, extFSwapEquiv_true, extF_adj_inr_false_inl,
        extF_adj_inr_true_inl]
    | false => simp [extFSwapEquiv_inl, extFSwapEquiv_false, extF_adj_inr_true_inl,
        extF_adj_inr_false_inl]
  · cases bx with
    | true =>
      cases by' with
      | true => simp [extFSwapEquiv_true, extF.eq_1]
      | false =>
        simp only [extFSwapEquiv_true, extFSwapEquiv_false]
        exact ⟨fun _ => extF_adj_uv H S T, fun _ => (extF_adj_uv H T S).symm⟩
    | false =>
      cases by' with
      | true =>
        simp only [extFSwapEquiv_false, extFSwapEquiv_true]
        exact ⟨fun _ => (extF_adj_uv H S T).symm, fun _ => extF_adj_uv H T S⟩
      | false => simp [extFSwapEquiv_false, extF.eq_1]

/-- **The orientation fix, packaged.** `IsBalCBUnion (extF H S T)` is INVARIANT under swapping
`S`/`T` (equivalently, swapping which of `u`/`v` each attaches to) — this is exactly what lets
`pst_a_case_component`'s single fixed orientation cover both orientations of the "up to
swapping `u` and `v`" conclusion. -/
theorem extF_swap_isBalCBUnion (H : SimpleGraph W) (S T : Set W) :
    IsBalCBUnion (extF H S T) ↔ IsBalCBUnion (extF H T S) :=
  ⟨fun h => IsBalCBUnion.map_iso (extF_swap_iso H T S) h,
   fun h => IsBalCBUnion.map_iso (extF_swap_iso H S T) h⟩

/-! #### Case 1, class form (strengthens `pst_a_case1_singleton_S`/`_T` for the assembly) -/

/-- **Case 1, `S ≠ ∅, T = ∅` branch, CLASS form.** Strengthens `pst_a_case1_singleton_S`'s
`S = {x0}` output with the underlying "`x0`'s WHOLE `same`-class collapses to `{x0}`" fact
(`lemma_swallow_component`'s own conclusion, not otherwise exposed by that theorem) — exactly
what the final PST-A assembly needs to compute `trueClass x0`/`falseClass x0` and decide the
orientation via `part x0`. Same proof shape as `pst_a_case1_singleton_S`, one extra output. -/
theorem pst_a_case1_class_S (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {S : Set W} (hSne : S.Nonempty) (hW0 : Wcount H S ∅ = 0) (hZ0 : Zcount H S ∅ = 0)
    (hRc0 : Rc (extF H S ∅) (Sum.inr true) (Sum.inr false) = 0) :
    ∃ x0, S = {x0} ∧ ∀ y, same x0 y → y = x0 := by
  obtain ⟨x0, hx0⟩ := hSne
  have hsub : ∀ c, same x0 c → c ∈ S := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hx0
    intro p hp q hpq
    rcases rc0_closed_union H S ∅ hRc0 p q hpq (Or.inl hp) with h | h
    · exact h
    · exact h.elim
  have hsup : ∀ s ∈ S, same x0 s :=
    fun s hs => z0_same_of_mem H hequiv hbip hZ0 (Or.inl ⟨hx0, hs⟩)
  have hsingleton : ∀ y, same x0 y → y = x0 :=
    lemma_swallow_component H S ∅ hequiv hbip hbal1 hbal2 hW0 (Or.inl hsub)
  refine ⟨x0, ?_, hsingleton⟩
  ext s
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hsS => hsingleton s (hsup s hsS), fun hseq => by rw [hseq]; exact hx0⟩

/-- **Case 1, symmetric `T ≠ ∅, S = ∅` branch, CLASS form** (`u ↔ v` swap of
`pst_a_case1_class_S`). -/
theorem pst_a_case1_class_T (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    {T : Set W} (hTne : T.Nonempty) (hW0 : Wcount H ∅ T = 0) (hZ0 : Zcount H ∅ T = 0)
    (hRc0 : Rc (extF H ∅ T) (Sum.inr true) (Sum.inr false) = 0) :
    ∃ x0, T = {x0} ∧ ∀ y, same x0 y → y = x0 := by
  obtain ⟨x0, hx0⟩ := hTne
  have hsub : ∀ c, same x0 c → c ∈ T := by
    apply same_class_of_closed H hequiv hbip hbal1 hbal2 hx0
    intro p hp q hpq
    rcases rc0_closed_union H ∅ T hRc0 p q hpq (Or.inr hp) with h | h
    · exact h.elim
    · exact h
  have hsup : ∀ t ∈ T, same x0 t :=
    fun t ht => z0_same_of_mem H hequiv hbip hZ0 (Or.inr ⟨hx0, ht⟩)
  have hsingleton : ∀ y, same x0 y → y = x0 :=
    lemma_swallow_component H ∅ T hequiv hbip hbal1 hbal2 hW0 (Or.inr hsub)
  refine ⟨x0, ?_, hsingleton⟩
  ext s
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hsT => hsingleton s (hsup s hsT), fun hseq => by rw [hseq]; exact hx0⟩

/-! #### THEOREM PST-A — final assembly (the `S ∩ T = ∅` case) -/

/-- ★★★ **THEOREM PST-A.** Given `H ∈ 𝓑`, `S ∩ T = ∅`,
and `D_inc(u,v) = 1`, `F = extF H S T ∈ 𝓑`. The
five vanishings (`pst_a_vanish`) force one of two clauses — (i) `S = T = ∅` (new
component `K_2`, `pst_a_case_empty`) or (ii) `{S,T} = {X_i,Y_i}` for a component `C_i` of `H`
(new component the balanced merge, `pst_a_case_component`), reached either directly from Case 1
(`pst_a_case1_class_S`/`_T`, the `b_i=0` degenerate instance) or from Case 3
(`pst_a_case3_component`, the general instance) — with Case 2 (`S,T` nonempty, different
components) excluded outright (`pst_a_case2_excluded`: forces two `K_1`s, contradicting the
standing `≤1`-odd hypothesis). The orientation question is resolved
uniformly: whichever of `pst_a_case_component`'s two possible orientations a given branch lands
on (decided by `part x0`, or read directly off `pst_a_case3_component`'s own disjunction), the
other is reached by transport across `extF_swap_isBalCBUnion`, never a second construction. -/
theorem pst_a (H : SimpleGraph W) (hH : IsBalCBUnion H) {S T : Set W} (hST : S ∩ T = ∅)
    (hDinc : Dinc (extF H S T) (Sum.inr true) (Sum.inr false) = 1) :
    IsBalCBUnion (extF H S T) := by
  obtain ⟨hchi, hW, hZ, hRc, hUa1, hUa2⟩ := pst_a_vanish H hH hST hDinc
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  rcases Set.eq_empty_or_nonempty S with hSe | hSne
  · rcases Set.eq_empty_or_nonempty T with hTe | hTne
    · subst hSe; subst hTe
      exact pst_a_case_empty H ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩
    · subst hSe
      obtain ⟨x0, hTeq, hsing⟩ := pst_a_case1_class_T H hequiv hbip hbal1 hbal2 hTne hW hZ hRc
      by_cases hpx0 : part x0 = true
      · -- SWAP needed: T = trueClass x0, ∅ = falseClass x0
        have hT' : T = {c : W | same x0 c ∧ part c = true} := by
          rw [hTeq]; ext c
          simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro heq; rw [heq]; exact ⟨hequiv.refl x0, hpx0⟩
          · rintro ⟨hc, -⟩; exact hsing c hc
        have hS' : (∅ : Set W) = {c : W | same x0 c ∧ part c = false} := by
          ext c
          simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff]
          rintro ⟨hc, hcf⟩
          have hcx0 := hsing c hc
          rw [hcx0] at hcf
          rw [hpx0] at hcf
          exact absurd hcf (by decide)
        have hBig : IsBalCBUnion (extF H T (∅ : Set W)) :=
          pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hT' hS'
        exact (extF_swap_isBalCBUnion H (∅ : Set W) T).mpr hBig
      · -- DIRECT: part x0 = false, ∅ = trueClass x0, T = falseClass x0
        have hpx0f : part x0 = false := Bool.eq_false_iff.mpr hpx0
        have hS' : (∅ : Set W) = {c : W | same x0 c ∧ part c = true} := by
          ext c
          simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff]
          rintro ⟨hc, hct⟩
          have hcx0 := hsing c hc
          rw [hcx0] at hct
          rw [hpx0f] at hct
          exact absurd hct (by decide)
        have hT' : T = {c : W | same x0 c ∧ part c = false} := by
          rw [hTeq]; ext c
          simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro heq; rw [heq]; exact ⟨hequiv.refl x0, hpx0f⟩
          · rintro ⟨hc, -⟩; exact hsing c hc
        exact pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hS' hT'
  · rcases Set.eq_empty_or_nonempty T with hTe | hTne
    · subst hTe
      obtain ⟨x0, hSeq, hsing⟩ := pst_a_case1_class_S H hequiv hbip hbal1 hbal2 hSne hW hZ hRc
      by_cases hpx0 : part x0 = true
      · -- DIRECT: S = trueClass x0, ∅ = falseClass x0
        have hS' : S = {c : W | same x0 c ∧ part c = true} := by
          rw [hSeq]; ext c
          simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro heq; rw [heq]; exact ⟨hequiv.refl x0, hpx0⟩
          · rintro ⟨hc, -⟩; exact hsing c hc
        have hT' : (∅ : Set W) = {c : W | same x0 c ∧ part c = false} := by
          ext c
          simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff]
          rintro ⟨hc, hcf⟩
          have hcx0 := hsing c hc
          rw [hcx0] at hcf
          rw [hpx0] at hcf
          exact absurd hcf (by decide)
        exact pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hS' hT'
      · -- SWAP needed: part x0 = false
        have hpx0f : part x0 = false := Bool.eq_false_iff.mpr hpx0
        have hT' : (∅ : Set W) = {c : W | same x0 c ∧ part c = true} := by
          ext c
          simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff]
          rintro ⟨hc, hct⟩
          have hcx0 := hsing c hc
          rw [hcx0] at hct
          rw [hpx0f] at hct
          exact absurd hct (by decide)
        have hS' : S = {c : W | same x0 c ∧ part c = false} := by
          rw [hSeq]; ext c
          simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro heq; rw [heq]; exact ⟨hequiv.refl x0, hpx0f⟩
          · rintro ⟨hc, -⟩; exact hsing c hc
        have hBig : IsBalCBUnion (extF H (∅ : Set W) S) :=
          pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hT' hS'
        exact (extF_swap_isBalCBUnion H S (∅ : Set W)).mpr hBig
    · -- both S,T nonempty
      obtain ⟨x0, hx0⟩ := id hSne
      obtain ⟨y0, hy0⟩ := id hTne
      by_cases hsame0 : same x0 y0
      · -- Case 3: S,T nonempty, same component
        rcases pst_a_case3_component H hequiv hbip hbal1 hbal2 hST hZ hRc hUa1 hUa2 hSne hTne
            hx0 hy0 hsame0 with ⟨hSeq, hTeq⟩ | ⟨hSeq, hTeq⟩
        · exact pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hSeq hTeq
        · have hBig : IsBalCBUnion (extF H T S) :=
            pst_a_case_component H hequiv hbip hbal1 hbal2 hodd hTeq hSeq
          exact (extF_swap_isBalCBUnion H S T).mpr hBig
      · -- Case 2: S,T nonempty, different components -- excluded
        exact (pst_a_case2_excluded H hequiv hbip hbal1 hbal2 hodd hW hZ hRc hx0 hy0 hsame0).elim

/-! ### THEOREM PST-B: the `S ∩ T ≠ ∅` case is impossible

**Statement:** if `S ∩ T ≠ ∅` then
`D_inc(u,v) = 1` is impossible for `F = extF H S T`, `H ∈ 𝓑`.

Internal structure below: the SAT-bundle, then the
`q`-maximising assignment (`pst_b_tight`, which packages the tightness facts labelled
`(E-a)/(E-b)/(E-c)` in the docstrings that use them), then the case analysis
`(1,1)/(2,1)/(1,2)/(2,2)` on how `S` and `T` sit relative to the `same`-class of a fixed
element of `S ∩ T`.  Intermediate structural facts are minted as declarations only where a
case actually consumes them. -/

/-- If `S ∩ T ≠ ∅` and `D_inc(u,v) = 1`, then `S ≠ T`.
Cheap warm-up, no choice function needed: `χ = 0` (SAT) plus LEMMA K3's surviving disjunct
(the first disjunct, `S ∩ T = ∅`, is excluded by hypothesis) produces a witness in `T ∖ S` or
`S ∖ T`. -/
theorem pst_b_S_ne_T (H : SimpleGraph W) (hH : IsBalCBUnion H) {S T : Set W}
    (hR : (S ∩ T).Nonempty)
    (hDinc : Dinc (extF H S T) (Sum.inr true) (Sum.inr false) = 1) :
    S ≠ T := by
  obtain ⟨hchi, -, -, -, -⟩ := (lemma_SAT H hH S T).mp hDinc
  have hmem : s(Sum.inr true, Sum.inr false) ∈ E0 (extF H S T) ∪ Ew (extF H S T) := by
    by_contra hc
    unfold Chi at hchi
    rw [if_neg hc] at hchi
    exact absurd hchi one_ne_zero
  rcases (lemma_K3 H S T).mp hmem with hSTe | ⟨p, hpT, hpS, -⟩ | ⟨p, hpS, hpT, -⟩
  · exact absurd hSTe (Set.nonempty_iff_ne_empty.mp hR)
  · intro heq; apply hpS; rw [heq]; exact hpT
  · intro heq; apply hpT; rw [← heq]; exact hpS

/-! #### The `q`-maximising assignment

`RcUSet`/`RcVSet` below are the `u`-side/`v`-side `R_c(u,v)`-summand index sets, restated
directly as subsets of `V(H)` (rather than `catC F u v ⊆ V(F)`): `p ∉ S∪T`
with `N_H(p)∩S≠∅` (resp. `∩T≠∅`). -/

/-- `RcUSet H S T`: vertices of `H` outside `S ∪ T` with an `H`-neighbour in `S`. -/
def RcUSet (H : SimpleGraph W) (S T : Set W) : Set W :=
  {x | x ∉ S ∧ x ∉ T ∧ (H.neighborSet x ∩ S).Nonempty}

/-- `RcVSet H S T`: the `T`-side mirror of `RcUSet`. -/
def RcVSet (H : SimpleGraph W) (S T : Set W) : Set W :=
  {x | x ∉ S ∧ x ∉ T ∧ (H.neighborSet x ∩ T).Nonempty}

theorem extF_commonNeighbors_inr_true_inl_of_notMem (H : SimpleGraph W) (S T : Set W)
    {x : W} (hxS : x ∉ S) (hxT : x ∉ T) :
    (extF H S T).commonNeighbors (Sum.inr true) (Sum.inl x) =
      Sum.inl '' (H.neighborSet x ∩ S) := by
  ext z
  rw [SimpleGraph.mem_commonNeighbors, Set.mem_image]
  rcases z with y | b
  · rw [extF_adj_inr_true_inl, extF_adj_inl_inl]
    constructor
    · rintro ⟨hyS, hxy⟩
      exact ⟨y, ⟨hxy, hyS⟩, rfl⟩
    · rintro ⟨y', ⟨hxy', hy'S⟩, hyeq⟩
      rw [← Sum.inl.inj hyeq]
      exact ⟨hy'S, hxy'⟩
  · cases b with
    | true =>
      constructor
      · rintro ⟨h1, -⟩; exact absurd h1 (extF H S T).irrefl
      · rintro ⟨y', -, hy'⟩; exact absurd hy' (by simp)
    | false =>
      constructor
      · rintro ⟨-, h2⟩
        rw [extF_adj_inl_inr_false] at h2
        exact absurd h2 hxT
      · rintro ⟨y', -, hy'⟩; exact absurd hy' (by simp)

theorem extF_commonNeighbors_inr_false_inl_of_notMem (H : SimpleGraph W) (S T : Set W)
    {x : W} (hxS : x ∉ S) (hxT : x ∉ T) :
    (extF H S T).commonNeighbors (Sum.inr false) (Sum.inl x) =
      Sum.inl '' (H.neighborSet x ∩ T) := by
  ext z
  rw [SimpleGraph.mem_commonNeighbors, Set.mem_image]
  rcases z with y | b
  · rw [extF_adj_inr_false_inl, extF_adj_inl_inl]
    constructor
    · rintro ⟨hyT, hxy⟩
      exact ⟨y, ⟨hxy, hyT⟩, rfl⟩
    · rintro ⟨y', ⟨hxy', hy'T⟩, hyeq⟩
      rw [← Sum.inl.inj hyeq]
      exact ⟨hy'T, hxy'⟩
  · cases b with
    | false =>
      constructor
      · rintro ⟨h1, -⟩; exact absurd h1 (extF H S T).irrefl
      · rintro ⟨y', -, hy'⟩; exact absurd hy' (by simp)
    | true =>
      constructor
      · rintro ⟨-, h2⟩
        rw [extF_adj_inl_inr_true] at h2
        exact absurd h2 hxS
      · rintro ⟨y', -, hy'⟩; exact absurd hy' (by simp)

/-- `R_c(u,v) = |RcUSet| + |RcVSet|`: `Rc_eq_sum_ncard`'s `catC`/`Anon` description,
specialised to `F = extF H S T` and reindexed onto `V(H)` via `Sum.inl` (`catC F u v` consists
entirely of `Sum.inl`-images, since `u, v` are excluded by `catC`'s own `w ≠ u ∧ w ≠ v`
clause). -/
theorem catC_Anon_true_eq_image_RcUSet (H : SimpleGraph W) (S T : Set W) :
    {w : W ⊕ Bool | w ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr true, w) ∈ Anon (extF H S T)} = Sum.inl '' RcUSet H S T := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨hwu, hwv, hnu, hnv⟩, hanon⟩
    rcases w with x | b
    · have hxS : x ∉ S := fun h => hnu ((extF_adj_inr_true_inl H S T x).mpr h)
      have hxT : x ∉ T := fun h => hnv ((extF_adj_inr_false_inl H S T x).mpr h)
      refine ⟨x, ⟨hxS, hxT, ?_⟩, rfl⟩
      obtain ⟨-, -, hne'⟩ :=
        (mem_Anon_iff (extF H S T) (Sum.inr true) (Sum.inl x)).mp hanon
      rw [extF_commonNeighbors_inr_true_inl_of_notMem H S T hxS hxT] at hne'
      exact Set.image_nonempty.mp hne'
    · cases b with
      | true => exact absurd rfl hwu
      | false => exact absurd rfl hwv
  · rintro ⟨x, ⟨hxS, hxT, hne'⟩, rfl⟩
    refine ⟨⟨by simp, by simp,
      fun h => hxS ((extF_adj_inr_true_inl H S T x).mp h),
      fun h => hxT ((extF_adj_inr_false_inl H S T x).mp h)⟩, ?_⟩
    rw [mem_Anon_iff]
    refine ⟨by simp, fun h => hxS ((extF_adj_inr_true_inl H S T x).mp h), ?_⟩
    rw [extF_commonNeighbors_inr_true_inl_of_notMem H S T hxS hxT]
    exact Set.image_nonempty.mpr hne'

theorem catC_Anon_false_eq_image_RcVSet (H : SimpleGraph W) (S T : Set W) :
    {w : W ⊕ Bool | w ∈ catC (extF H S T) (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr false, w) ∈ Anon (extF H S T)} = Sum.inl '' RcVSet H S T := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨hwu, hwv, hnu, hnv⟩, hanon⟩
    rcases w with x | b
    · have hxS : x ∉ S := fun h => hnu ((extF_adj_inr_true_inl H S T x).mpr h)
      have hxT : x ∉ T := fun h => hnv ((extF_adj_inr_false_inl H S T x).mpr h)
      refine ⟨x, ⟨hxS, hxT, ?_⟩, rfl⟩
      obtain ⟨-, -, hne'⟩ :=
        (mem_Anon_iff (extF H S T) (Sum.inr false) (Sum.inl x)).mp hanon
      rw [extF_commonNeighbors_inr_false_inl_of_notMem H S T hxS hxT] at hne'
      exact Set.image_nonempty.mp hne'
    · cases b with
      | true => exact absurd rfl hwu
      | false => exact absurd rfl hwv
  · rintro ⟨x, ⟨hxS, hxT, hne'⟩, rfl⟩
    refine ⟨⟨by simp, by simp,
      fun h => hxS ((extF_adj_inr_true_inl H S T x).mp h),
      fun h => hxT ((extF_adj_inr_false_inl H S T x).mp h)⟩, ?_⟩
    rw [mem_Anon_iff]
    refine ⟨by simp, fun h => hxT ((extF_adj_inr_false_inl H S T x).mp h), ?_⟩
    rw [extF_commonNeighbors_inr_false_inl_of_notMem H S T hxS hxT]
    exact Set.image_nonempty.mpr hne'

/-- `R_c(u,v) = |RcUSet| + |RcVSet|`: `Rc_eq_sum_ncard`'s `catC`/`Anon` description,
specialised to `F = extF H S T` and reindexed onto `V(H)` via `Sum.inl` (`catC F u v` consists
entirely of `Sum.inl`-images, since `u, v` are excluded by `catC`'s own `w ≠ u ∧ w ≠ v`
clause). -/
theorem Rc_eq_RcUSet_add_RcVSet (H : SimpleGraph W) (S T : Set W) :
    Rc (extF H S T) (Sum.inr true) (Sum.inr false) =
      (RcUSet H S T).ncard + (RcVSet H S T).ncard := by
  classical
  have hne : (Sum.inr true : W ⊕ Bool) ≠ Sum.inr false := by simp
  rw [Rc_eq_sum_ncard (extF H S T) hne, catC_Anon_true_eq_image_RcUSet H S T,
    catC_Anon_false_eq_image_RcVSet H S T, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inl_injective]

/-- ★★★ **The `q`-maximising assignment, fixed once and for all**:
the tightness upgrade of `lemma_PST_L2`'s inequality
(`K_c ≤ Z + R_c`) to the SAT-forced equality, packaged as exactly the downstream facts
the impossibility cases need (labelled `(E-a)/(E-b)/(E-c)` below).

The construction (`AuIdx`/`AvIdx`/`QAu`/`QAv`/`PAu`/`PAv`, the choice functions `pu,pv,qu,qv`)
is `lemma_PST_L2`'s own local machinery, rebuilt here (not touching that
proof) because `hKeq` — SAT's `K_c = Z + R_c` EQUALITY rather than PST-L2's `≤` — forces every
inequality inside it to be tight, which is new content `lemma_PST_L2` itself never needed.

Output:
1. `RcUSet = RcVSet` (the two `R_c`-summand index sets coincide — every `u`-side witness `p`
   is automatically a `v`-side witness too, since the `w ∈ R` it serves lies in `T` as well as
   `S`, and conversely; this is `(E-a)`'s content, `P_u = P_v`, stated directly via the common
   set rather than via the two images).
2. `R_c(u,v) = 2·|RcUSet|` (`(E-b)`).
3. `R := S ∩ T` lies in a single `same`-class (needs `(E-c)`'s exhaustiveness: any two
   distinct, non-`same`-related elements of `R` would themselves be an unassigned `Z`-pair).
4. If every `w ∈ R` has an available `u`-side `q`-route, `RcUSet = ∅` (feeds the `(2,1)`/`(2,2)`
   closure: `S` meeting a second component supplies such a route for every `w ∈ R`).
5. The `v`-side mirror of 4 (feeds the `(1,2)` mirror case).
6. `(E-b)`'s SINGLETON content: every `y ∈ RcUSet` is one of the accounted `P`-vertices, so
   `N_H(y) ∩ S` and `N_H(y) ∩ T` are each a singleton (`P`'s own defining property,
   `N_H(p_w) ∩ S = {w}`). Feeds Case `(1,1)`'s closure.
7. ★ `(E-c)`'s EXHAUSTIVENESS, packaged with the chosen-pair partner functions: every
   `Z`-pair is a chosen pair, i.e. has one end `w` in `R = S ∩ T` and the other end equal to
   `w`'s own chosen partner — `f w` (the `u`-side partner, outside `T`) or `g w` (the `v`-side
   partner, outside `S`). Three consequences are read off at the use sites: every `Z`-pair has
   an end in `R`; a `Z`-pair inside `S` has its non-`R` end in `S ∖ T`; and each `w ∈ R` lies
   in AT MOST ONE `Z`-pair inside `S` (its partner is the single value `f w`) — the
   at-most-one-partner fact, which is what pins `|S ∩ C_2| = 1` in Case `(2,2)`. -/
theorem pst_b_tight (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W)
    (hKeq : Kc (extF H S T) (Sum.inr true) (Sum.inr false) =
      Zcount H S T + Rc (extF H S T) (Sum.inr true) (Sum.inr false)) :
    RcUSet H S T = RcVSet H S T ∧
    Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 2 * (RcUSet H S T).ncard ∧
    (∀ w w' : W, w ∈ S → w ∈ T → w' ∈ S → w' ∈ T → w ≠ w' → same w w') ∧
    ((∀ w ∈ S ∩ T, ∃ q, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ T) → RcUSet H S T = ∅) ∧
    ((∀ w ∈ S ∩ T, ∃ q, q ∈ T ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ S) → RcUSet H S T = ∅) ∧
    (∀ y ∈ RcUSet H S T,
      (∃ x, H.neighborSet y ∩ S = {x}) ∧ (∃ x, H.neighborSet y ∩ T = {x})) ∧
    (∃ f g : W → W, ∀ a b : W, s(a, b) ∈ ZPairs H S T →
      (a ∈ S ∩ T ∧ ((b = f a ∧ b ∉ T) ∨ (b = g a ∧ b ∉ S))) ∨
      (b ∈ S ∩ T ∧ ((a = f b ∧ a ∉ T) ∨ (a = g b ∧ a ∉ S)))) := by
  classical
  set F := extF H S T with hFdef
  have hne : (Sum.inr true : W ⊕ Bool) ≠ Sum.inr false := by simp
  have hZcount_def : Zcount H S T = (ZPairs H S T).ncard := rfl
  -- The `AuIdx`/`AvIdx` index sets (`lemma_PST_L2`'s own construction, reproduced).
  have hWuv_eq : ∀ w : W ⊕ Bool, w ∈ Wuv F (Sum.inr true) (Sum.inr false) ↔
      ∃ x, w = Sum.inl x ∧ x ∈ S ∧ x ∈ T := by
    intro w
    rw [Wuv, SimpleGraph.mem_commonNeighbors]
    constructor
    · rintro ⟨h1, h2⟩
      rcases w with x | b
      · exact ⟨x, rfl, (extF_adj_inr_true_inl H S T x).mp h1,
          (extF_adj_inr_false_inl H S T x).mp h2⟩
      · cases b with
        | true => exact absurd h1 F.irrefl
        | false => exact absurd h2 F.irrefl
    · rintro ⟨x, rfl, hxS, hxT⟩
      exact ⟨(extF_adj_inr_true_inl H S T x).mpr hxS, (extF_adj_inr_false_inl H S T x).mpr hxT⟩
  have hKc0 : Kc F (Sum.inr true) (Sum.inr false) =
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr true, w) ∈ Ew F}.ncard +
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr false, w) ∈ Ew F}.ncard :=
    Kc_eq_sum_ncard F hne
  -- One proof for both the `u`-side (`r = true`) and `v`-side (`r = false`) index sets.
  have hIdxEq : ∀ r : Bool,
      {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧ s(Sum.inr r, w) ∈ Ew F}
      = Sum.inl '' {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr r, Sum.inl x) ∈ Ew F} := by
    intro r
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hw, hEw⟩
      obtain ⟨x, rfl, hxS, hxT⟩ := (hWuv_eq w).mp hw
      exact ⟨x, ⟨hxS, hxT, hEw⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, hxT, hEw⟩, rfl⟩
      exact ⟨(hWuv_eq (Sum.inl x)).mpr ⟨x, rfl, hxS, hxT⟩, hEw⟩
  set AuIdx : Set W := {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr true, Sum.inl x) ∈ Ew F} with hAuIdxDef
  set AvIdx : Set W := {x | x ∈ S ∧ x ∈ T ∧ s(Sum.inr false, Sum.inl x) ∈ Ew F} with hAvIdxDef
  have hAuCard : {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr true, w) ∈ Ew F}.ncard = AuIdx.ncard := by
    rw [hIdxEq true, ← hAuIdxDef]; exact Set.ncard_image_of_injective _ Sum.inl_injective
  have hAvCard : {w | w ∈ Wuv F (Sum.inr true) (Sum.inr false) ∧
      s(Sum.inr false, w) ∈ Ew F}.ncard = AvIdx.ncard := by
    rw [hIdxEq false, ← hAvIdxDef]; exact Set.ncard_image_of_injective _ Sum.inl_injective
  have hKc : Kc F (Sum.inr true) (Sum.inr false) = AuIdx.ncard + AvIdx.ncard := by
    rw [hKc0, hAuCard, hAvCard]
  have hAu_qp : ∀ x ∈ AuIdx,
      (∃ q : W, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {x}) := by
    rintro x ⟨hxS, hxT, hxEw⟩
    have h4 := (lemma_Ku H hequiv hbip hbal1 hbal2 S T hxS).mp (Or.inr hxEw)
    rcases h4 with ⟨-, hxTfalse⟩ | hb | ⟨hxTfalse, -⟩ | ⟨q, hqS, hqx, hnsame, hTor⟩
    · exact absurd hxT hxTfalse
    · exact Or.inr hb
    · exact absurd hxT hxTfalse
    · refine Or.inl ⟨q, hqS, hqx, hnsame, ?_⟩
      rcases hTor with hf | hf
      · exact absurd hxT hf
      · exact hf
  have hAv_qp : ∀ x ∈ AvIdx,
      (∃ q : W, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) ∨
      (∃ p : W, p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = {x}) := by
    rintro x ⟨hxS, hxT, hxEw⟩
    obtain ⟨p, hp | hp⟩ := ((mem_Ew_iff F (Sum.inr false) (Sum.inl x)).mp hxEw).2.2
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hpneu : p ≠ Sum.inr true := by rintro rfl; exact hpnadj (extF_adj_uv H S T).symm
      obtain ⟨y, rfl⟩ : ∃ y, p = Sum.inl y := by
        rcases p with y | b
        · exact ⟨y, rfl⟩
        · cases b with
          | true => exact absurd rfl hpneu
          | false => exact absurd rfl hpne
      have hyT : y ∉ T := fun h => hpnadj ((extF_adj_inr_false_inl H S T y).mpr h)
      have hxmem : Sum.inl x ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hxmem
      have hyxH : H.Adj y x := (extF_adj_inl_inl H S T y x).mp hxmem.2
      have hyS : y ∉ S := by
        intro hS
        have humem : Sum.inr true ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) := by
          rw [SimpleGraph.mem_commonNeighbors]
          exact ⟨(extF_adj_uv H S T).symm, ((extF_adj_inr_true_inl H S T y).mpr hS).symm⟩
        rw [hpcn] at humem
        exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
      refine Or.inr ⟨y, hyS, hyT, ?_⟩
      ext z
      rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzy, hzT⟩
        have hzmem : Sum.inl z ∈ F.commonNeighbors (Sum.inr false) (Sum.inl y) :=
          F.mem_commonNeighbors.mpr
            ⟨(extF_adj_inr_false_inl H S T z).mpr hzT, (extF_adj_inl_inl H S T y z).mpr hzy⟩
        rw [hpcn] at hzmem
        exact Sum.inl.inj (Set.mem_singleton_iff.mp hzmem)
      · rintro rfl
        exact ⟨hyxH, hxT⟩
    · obtain ⟨hpne, hpnadj, hpcn⟩ := hp
      have hvne : Sum.inr false ∈ F.commonNeighbors (Sum.inl x) p := by
        rw [hpcn]; exact Set.mem_singleton _
      rw [SimpleGraph.mem_commonNeighbors] at hvne
      obtain ⟨-, hpv⟩ := hvne
      rcases p with y | b
      · have hyT : y ∈ T := (extF_adj_inl_inr_false H S T y).mp hpv
        have hyxne : y ≠ x := fun h => hpne (congrArg Sum.inl h)
        have hqnadjXx : ¬ H.Adj y x := fun h =>
          hpnadj ((extF_adj_inl_inl H S T x y).mpr h.symm)
        have hcn0' : H.commonNeighbors x y = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [SimpleGraph.mem_commonNeighbors] at hz
          have hzmem : Sum.inl z ∈ F.commonNeighbors (Sum.inl x) (Sum.inl y) :=
            F.mem_commonNeighbors.mpr
              ⟨(extF_adj_inl_inl H S T x z).mpr hz.1, (extF_adj_inl_inl H S T y z).mpr hz.2⟩
          rw [hpcn] at hzmem
          exact absurd (Set.mem_singleton_iff.mp hzmem) (by simp)
        have hnsame : ¬ same x y :=
          not_same_of_disjoint_commonNeighbors hequiv hbip hbal1 hbal2 hyxne hqnadjXx hcn0'
        have hxS_or : x ∉ S ∨ y ∉ S := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨hxS', hyS'⟩ := hcon
          have humem : Sum.inr true ∈ F.commonNeighbors (Sum.inl x) (Sum.inl y) := by
            rw [SimpleGraph.mem_commonNeighbors]
            exact ⟨(extF_adj_inl_inr_true H S T x).mpr hxS',
              (extF_adj_inl_inr_true H S T y).mpr hyS'⟩
          rw [hpcn] at humem
          exact absurd (Set.mem_singleton_iff.mp humem) (by simp)
        refine Or.inl ⟨y, hyT, hyxne, hnsame, ?_⟩
        rcases hxS_or with h | h
        · exact absurd hxS h
        · exact h
      · cases b with
        | true =>
          have hxSfalse : x ∉ S := fun hS => hpnadj ((extF_adj_inl_inr_true H S T x).mpr hS)
          exact absurd hxS hxSfalse
        | false => exact absurd hpv F.irrefl
  set QAu : Set W := {x | x ∈ AuIdx ∧ ∃ q, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T} with hQAudef
  set QAv : Set W := {x | x ∈ AvIdx ∧ ∃ q, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S} with hQAvdef
  set PAu : Set W := AuIdx \ QAu with hPAudef
  set PAv : Set W := AvIdx \ QAv with hPAvdef
  have hQAu_sub : QAu ⊆ AuIdx := fun x hx => hx.1
  have hQAv_sub : QAv ⊆ AvIdx := fun x hx => hx.1
  have hPAu_p : ∀ x : W, ∃ p : W, x ∈ PAu → (p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ S = {x}) := by
    intro x
    by_cases hxP : x ∈ PAu
    · obtain ⟨hxA, hxnQ⟩ := hxP
      have hnq : ¬ (∃ q, q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) := fun hex => hxnQ ⟨hxA, hex⟩
      obtain ⟨p, hp⟩ := (hAu_qp x hxA).resolve_left hnq
      exact ⟨p, fun _ => hp⟩
    · exact ⟨x, fun h => absurd h hxP⟩
  have hPAv_p : ∀ x : W, ∃ p : W, x ∈ PAv → (p ∉ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = {x}) := by
    intro x
    by_cases hxP : x ∈ PAv
    · obtain ⟨hxA, hxnQ⟩ := hxP
      have hnq : ¬ (∃ q, q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) := fun hex => hxnQ ⟨hxA, hex⟩
      obtain ⟨p, hp⟩ := (hAv_qp x hxA).resolve_left hnq
      exact ⟨p, fun _ => hp⟩
    · exact ⟨x, fun h => absurd h hxP⟩
  choose pu hpu using hPAu_p
  choose pv hpv using hPAv_p
  have hQAu_q : ∀ x : W, ∃ q : W, x ∈ QAu → (q ∈ S ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ T) := by
    intro x
    by_cases hxQ : x ∈ QAu
    · exact ⟨(hxQ.2).choose, fun _ => (hxQ.2).choose_spec⟩
    · exact ⟨x, fun h => absurd h hxQ⟩
  have hQAv_q : ∀ x : W, ∃ q : W, x ∈ QAv → (q ∈ T ∧ q ≠ x ∧ ¬ same x q ∧ q ∉ S) := by
    intro x
    by_cases hxQ : x ∈ QAv
    · exact ⟨(hxQ.2).choose, fun _ => (hxQ.2).choose_spec⟩
    · exact ⟨x, fun h => absurd h hxQ⟩
  choose qu hqu using hQAu_q
  choose qv hqv using hQAv_q
  set imgQu : Set (Sym2 W) := (fun x => s(x, qu x)) '' QAu with himgQudef
  set imgQv : Set (Sym2 W) := (fun x => s(x, qv x)) '' QAv with himgQvdef
  have hinjQu : Set.InjOn (fun x => s(x, qu x)) QAu := by
    intro x1 hx1 x2 hx2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hxx, -⟩ | ⟨hxq, -⟩
    · exact hxx
    · exfalso
      have h2 := hqu x2 hx2
      have hx1T : x1 ∈ T := (hQAu_sub hx1).2.1
      rw [hxq] at hx1T
      exact h2.2.2.2 hx1T
  have hinjQv : Set.InjOn (fun x => s(x, qv x)) QAv := by
    intro x1 hx1 x2 hx2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hxx, -⟩ | ⟨hxq, -⟩
    · exact hxx
    · exfalso
      have h2 := hqv x2 hx2
      have hx1S : x1 ∈ S := (hQAv_sub hx1).1
      rw [hxq] at hx1S
      exact h2.2.2.2 hx1S
  have hdisjQ : Disjoint imgQu imgQv := by
    rw [Set.disjoint_left]
    rintro P ⟨x1, hx1, rfl⟩ ⟨x2, hx2, heq⟩
    rw [Sym2.eq_iff] at heq
    have h1 := hqu x1 hx1
    have h2 := hqv x2 hx2
    rcases heq with ⟨hx12, hq12⟩ | ⟨hxq, hqx⟩
    · have hquS : qu x1 ∈ S := h1.1
      have hqvnS : qv x2 ∉ S := h2.2.2.2
      rw [← hq12] at hquS
      exact hqvnS hquS
    · have hx2AT : x2 ∈ T := (hQAv_sub hx2).2.1
      have hqunT : qu x1 ∉ T := h1.2.2.2
      rw [hxq] at hx2AT
      exact hqunT hx2AT
  have himgQu_sub : imgQu ⊆ ZPairs H S T := by
    rintro P ⟨x, hx, rfl⟩
    have h := hqu x hx
    have hxS : x ∈ S := (hQAu_sub hx).1
    rw [mem_ZPairs_iff]
    refine ⟨h.2.1.symm, ?_, ?_, Or.inl ⟨hxS, h.1⟩⟩
    · exact fun hadj => h.2.2.1 ((hbip x (qu x)).mp hadj).1
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [SimpleGraph.mem_commonNeighbors] at hz
      have hsz : same x z := ((hbip x z).mp hz.1).1
      have hsqz : same (qu x) z := ((hbip (qu x) z).mp hz.2).1
      exact h.2.2.1 (hequiv.trans hsz (hequiv.symm hsqz))
  have himgQv_sub : imgQv ⊆ ZPairs H S T := by
    rintro P ⟨x, hx, rfl⟩
    have h := hqv x hx
    have hxT : x ∈ T := (hQAv_sub hx).2.1
    rw [mem_ZPairs_iff]
    refine ⟨h.2.1.symm, ?_, ?_, Or.inr ⟨hxT, h.1⟩⟩
    · exact fun hadj => h.2.2.1 ((hbip x (qv x)).mp hadj).1
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [SimpleGraph.mem_commonNeighbors] at hz
      have hsz : same x z := ((hbip x z).mp hz.1).1
      have hsqz : same (qv x) z := ((hbip (qv x) z).mp hz.2).1
      exact h.2.2.1 (hequiv.trans hsz (hequiv.symm hsqz))
  have hQubound : QAu.ncard + QAv.ncard ≤ Zcount H S T := by
    have e1 : imgQu.ncard = QAu.ncard := Set.ncard_image_of_injOn hinjQu
    have e2 : imgQv.ncard = QAv.ncard := Set.ncard_image_of_injOn hinjQv
    have hunion : (imgQu ∪ imgQv).ncard = imgQu.ncard + imgQv.ncard :=
      Set.ncard_union_eq hdisjQ (Set.toFinite _) (Set.toFinite _)
    have hsub : imgQu ∪ imgQv ⊆ ZPairs H S T := Set.union_subset himgQu_sub himgQv_sub
    have hle : (imgQu ∪ imgQv).ncard ≤ (ZPairs H S T).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    show QAu.ncard + QAv.ncard ≤ (ZPairs H S T).ncard
    omega
  -- `p`-route: injections directly into `RcUSet`/`RcVSet` (simpler than `lemma_PST_L2`'s
  -- `catC`-shaped target, since we land in `V(H)` directly), PLUS the cross-containment
  -- `(E-a)` needs: a `u`-side witness `p` (serving `w ∈ R ⊆ T`) is automatically a `v`-side
  -- witness too, since `p ~ w` in `H` and `w ∈ T`.
  have hinjPu : Set.InjOn pu PAu := by
    intro x1 hx1 x2 hx2 heq
    have h1 := hpu x1 hx1
    have h2 := hpu x2 hx2
    have hset : ({x1} : Set W) = {x2} := by rw [← h1.2.2, ← h2.2.2, heq]
    exact Set.singleton_eq_singleton_iff.mp hset
  have hinjPv : Set.InjOn pv PAv := by
    intro x1 hx1 x2 hx2 heq
    have h1 := hpv x1 hx1
    have h2 := hpv x2 hx2
    have hset : ({x1} : Set W) = {x2} := by rw [← h1.2.2, ← h2.2.2, heq]
    exact Set.singleton_eq_singleton_iff.mp hset
  have himgPu_sub : pu '' PAu ⊆ RcUSet H S T := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpu x hx
    have hxS : x ∈ S := (hx.1 : x ∈ AuIdx).1
    have hxmem : x ∈ H.neighborSet (pu x) ∩ S := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨h.1, h.2.1, x, hxmem.1, hxS⟩
  have himgPv_sub : pv '' PAv ⊆ RcVSet H S T := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpv x hx
    have hxT : x ∈ T := (hx.1 : x ∈ AvIdx).2.1
    have hxmem : x ∈ H.neighborSet (pv x) ∩ T := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨h.1, h.2.1, x, hxmem.1, hxT⟩
  have himgPu_cross : pu '' PAu ⊆ RcVSet H S T := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpu x hx
    have hxT : x ∈ T := (hx.1 : x ∈ AuIdx).2.1
    have hxmem : x ∈ H.neighborSet (pu x) ∩ S := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨h.1, h.2.1, x, hxmem.1, hxT⟩
  have himgPv_cross : pv '' PAv ⊆ RcUSet H S T := by
    rintro w ⟨x, hx, rfl⟩
    have h := hpv x hx
    have hxS : x ∈ S := (hx.1 : x ∈ AvIdx).1
    have hxmem : x ∈ H.neighborSet (pv x) ∩ T := by rw [h.2.2]; exact Set.mem_singleton x
    exact ⟨h.1, h.2.1, x, hxmem.1, hxS⟩
  have hPubound2 : PAu.ncard ≤ (RcUSet H S T).ncard := by
    rw [← Set.ncard_image_of_injOn hinjPu]
    exact Set.ncard_le_ncard himgPu_sub (Set.toFinite _)
  have hPvbound2 : PAv.ncard ≤ (RcVSet H S T).ncard := by
    rw [← Set.ncard_image_of_injOn hinjPv]
    exact Set.ncard_le_ncard himgPv_sub (Set.toFinite _)
  have hRcEq2 : Rc F (Sum.inr true) (Sum.inr false) =
      (RcUSet H S T).ncard + (RcVSet H S T).ncard := Rc_eq_RcUSet_add_RcVSet H S T
  have hAu_split : AuIdx.ncard = QAu.ncard + PAu.ncard := by
    have hu : QAu ∪ PAu = AuIdx := by rw [hPAudef, Set.union_sdiff_cancel hQAu_sub]
    have hdisjP : Disjoint QAu PAu :=
      Set.disjoint_left.mpr (fun x hxQ hxP => hxP.2 hxQ)
    rw [← hu, Set.ncard_union_eq hdisjP (Set.toFinite _) (Set.toFinite _)]
  have hAv_split : AvIdx.ncard = QAv.ncard + PAv.ncard := by
    have hv : QAv ∪ PAv = AvIdx := by rw [hPAvdef, Set.union_sdiff_cancel hQAv_sub]
    have hdisjP : Disjoint QAv PAv :=
      Set.disjoint_left.mpr (fun x hxQ hxP => hxP.2 hxQ)
    rw [← hv, Set.ncard_union_eq hdisjP (Set.toFinite _) (Set.toFinite _)]
  -- Everything above holds unconditionally (matching `lemma_PST_L2`); NOW spend `hKeq`
  -- (SAT's equality, not just `≤`) to force every inequality above to be tight.
  have hCeq : PAu.ncard = (RcUSet H S T).ncard := by omega
  have hDeq : PAv.ncard = (RcVSet H S T).ncard := by omega
  have hABeq : QAu.ncard + QAv.ncard = Zcount H S T := by omega
  have hUimg_eq : pu '' PAu = RcUSet H S T := by
    apply Set.eq_of_subset_of_ncard_le himgPu_sub
    rw [Set.ncard_image_of_injOn hinjPu]
    exact le_of_eq hCeq.symm
  have hVimg_eq : pv '' PAv = RcVSet H S T := by
    apply Set.eq_of_subset_of_ncard_le himgPv_sub
    rw [Set.ncard_image_of_injOn hinjPv]
    exact le_of_eq hDeq.symm
  have hUVeq : RcUSet H S T = RcVSet H S T := by
    apply Set.Subset.antisymm
    · rw [← hUimg_eq]; exact himgPu_cross
    · rw [← hVimg_eq]; exact himgPv_cross
  have hRc2 : Rc F (Sum.inr true) (Sum.inr false) = 2 * (RcUSet H S T).ncard := by
    rw [hRcEq2, hUVeq]; ring
  have himgQ_card : (imgQu ∪ imgQv).ncard = Zcount H S T := by
    rw [Set.ncard_union_eq hdisjQ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injOn hinjQu, Set.ncard_image_of_injOn hinjQv]
    exact hABeq
  have himgQ_eq : imgQu ∪ imgQv = ZPairs H S T := by
    apply Set.eq_of_subset_of_ncard_le (Set.union_subset himgQu_sub himgQv_sub)
    rw [himgQ_card, ← hZcount_def]
  have hRone : ∀ w w' : W, w ∈ S → w ∈ T → w' ∈ S → w' ∈ T → w ≠ w' → same w w' := by
    intro w w' hwS hwT hw'S hw'T hne'
    by_contra hnsame
    have hzp : s(w, w') ∈ ZPairs H S T := by
      rw [mem_ZPairs_iff]
      refine ⟨hne', fun hadj => hnsame ((hbip w w').mp hadj).1, ?_, Or.inl ⟨hwS, hw'S⟩⟩
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [SimpleGraph.mem_commonNeighbors] at hz
      have hsz : same w z := ((hbip w z).mp hz.1).1
      have hsw'z : same w' z := ((hbip w' z).mp hz.2).1
      exact hnsame (hequiv.trans hsz (hequiv.symm hsw'z))
    rw [← himgQ_eq] at hzp
    rcases hzp with ⟨x, hxQ, hxeq⟩ | ⟨x, hxQ, hxeq⟩
    · have hq := hqu x hxQ
      rw [Sym2.eq_iff] at hxeq
      rcases hxeq with ⟨hxw, hqw'⟩ | ⟨hxw, hqw⟩
      · rw [hqw'] at hq; exact hq.2.2.2 hw'T
      · rw [hqw] at hq; exact hq.2.2.2 hwT
    · have hq := hqv x hxQ
      rw [Sym2.eq_iff] at hxeq
      rcases hxeq with ⟨hxw, hqw'⟩ | ⟨hxw, hqw⟩
      · rw [hqw'] at hq; exact hq.2.2.2 hw'S
      · rw [hqw] at hq; exact hq.2.2.2 hwS
  have hFullU : (∀ w ∈ S ∩ T, ∃ q, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ T) → RcUSet H S T = ∅ := by
    intro hfull
    have hPAuEmpty : PAu = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxA, hxnQ⟩ := hx
      have hxR : x ∈ S ∩ T := ⟨hxA.1, hxA.2.1⟩
      obtain ⟨q, hqS, hqx, hnsame, hqT⟩ := hfull x hxR
      exact hxnQ ⟨hxA, q, hqS, hqx, hnsame, hqT⟩
    have hRcU0 : (RcUSet H S T).ncard = 0 := by rw [← hCeq, hPAuEmpty]; exact Set.ncard_empty _
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp hRcU0
  have hFullT : (∀ w ∈ S ∩ T, ∃ q, q ∈ T ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ S) → RcUSet H S T = ∅ := by
    intro hfull
    have hPAvEmpty : PAv = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxA, hxnQ⟩ := hx
      have hxR : x ∈ S ∩ T := ⟨hxA.1, hxA.2.1⟩
      obtain ⟨q, hqT, hqx, hnsame, hqS⟩ := hfull x hxR
      exact hxnQ ⟨hxA, q, hqT, hqx, hnsame, hqS⟩
    have hRcV0 : (RcVSet H S T).ncard = 0 := by rw [← hDeq, hPAvEmpty]; exact Set.ncard_empty _
    have hV0 : RcVSet H S T = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hRcV0
    rw [hUVeq]; exact hV0
  -- `(E-b)`'s singleton content: `RcUSet` is EXACTLY `pu '' PAu` (`hUimg_eq`, tightness-forced),
  -- and `pu x`'s defining property is `N_H(pu x) ∩ S = {x}` — likewise on the `v` side via
  -- `hUVeq`/`hVimg_eq`.
  have hEbSingle : ∀ y ∈ RcUSet H S T,
      (∃ x, H.neighborSet y ∩ S = {x}) ∧ (∃ x, H.neighborSet y ∩ T = {x}) := by
    intro y hy
    constructor
    · rw [← hUimg_eq] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, (hpu x hx).2.2⟩
    · rw [hUVeq, ← hVimg_eq] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, (hpv x hx).2.2⟩
  -- `(E-c)`: `himgQ_eq` says the chosen pairs EXHAUST `ZPairs`, so reading a `Z`-pair back
  -- through that equality names both its ends — the index `x ∈ R` and its chosen partner
  -- `qu x ∉ T` (a `u`-side pair) or `qv x ∉ S` (a `v`-side pair).
  have hEc : ∃ f g : W → W, ∀ a b : W, s(a, b) ∈ ZPairs H S T →
      (a ∈ S ∩ T ∧ ((b = f a ∧ b ∉ T) ∨ (b = g a ∧ b ∉ S))) ∨
      (b ∈ S ∩ T ∧ ((a = f b ∧ a ∉ T) ∨ (a = g b ∧ a ∉ S))) := by
    refine ⟨qu, qv, ?_⟩
    intro a b hab
    rw [← himgQ_eq] at hab
    rcases hab with ⟨x, hxQ, hxeq⟩ | ⟨x, hxQ, hxeq⟩
    · have hq := hqu x hxQ
      have hxA := hQAu_sub hxQ
      have hxR : x ∈ S ∩ T := ⟨hxA.1, hxA.2.1⟩
      rw [Sym2.eq_iff] at hxeq
      rcases hxeq with ⟨hxa, hqb⟩ | ⟨hxb, hqa⟩
      · refine Or.inl ⟨by rw [← hxa]; exact hxR, Or.inl ⟨by rw [← hxa, ← hqb], ?_⟩⟩
        rw [← hqb]; exact hq.2.2.2
      · refine Or.inr ⟨by rw [← hxb]; exact hxR, Or.inl ⟨by rw [← hxb, ← hqa], ?_⟩⟩
        rw [← hqa]; exact hq.2.2.2
    · have hq := hqv x hxQ
      have hxA := hQAv_sub hxQ
      have hxR : x ∈ S ∩ T := ⟨hxA.1, hxA.2.1⟩
      rw [Sym2.eq_iff] at hxeq
      rcases hxeq with ⟨hxa, hqb⟩ | ⟨hxb, hqa⟩
      · refine Or.inl ⟨by rw [← hxa]; exact hxR, Or.inr ⟨by rw [← hxa, ← hqb], ?_⟩⟩
        rw [← hqb]; exact hq.2.2.2
      · refine Or.inr ⟨by rw [← hxb]; exact hxR, Or.inr ⟨by rw [← hxb, ← hqa], ?_⟩⟩
        rw [← hqa]; exact hq.2.2.2
  exact ⟨hUVeq, hRc2, hRone, hFullU, hFullT, hEbSingle, hEc⟩

/-! #### Case `(1,1)` — `S` and `T` both inside `c`'s class

A symmetry note: one might open "by the `u ↔ v` symmetry of the whole
configuration, assume WLOG `∃ p_0 ∈ S∖T` with `N_H(p_0) ∩ T = ∅`", handling the `T∖S`
alternative as a mirror. **No WLOG is taken here and no mirror case is written.** The two LEMMA
K3 disjuncts are consumed at the top of the proof into the single symmetric fact they both
supply — a `p_0 ∈ S ∪ T` with `p_0 ≠ c` and `¬H.Adj c p_0` — after which every remaining step
(`2 ≤ |X|`; PST-W's two routes; `Y ∩ (S ∪ T) = ∅`; the `(E-b)` singleton closure) is already
symmetric in `S`/`T`. In particular
`Y ∩ T = ∅` and `Y ∩ S = ∅` are proved by ONE argument
(`hYout`) covering both, since PST-W's route at `c` demands a partner avoiding **both** `S` and
`T` (`c ∈ S ∩ T`) in either branch. -/

/-- ★★ **Case `(1,1)`**: if `S` and `T` both lie inside a
single `same`-class — that of a fixed `c ∈ S ∩ T` — the configuration is impossible.

Proof: LEMMA K3's surviving disjuncts both hand back a vertex `p_0` of
`S ∪ T`, distinct from `c` and non-adjacent to it, hence in `c`'s OWN part `X` (non-adjacent
same-class vertices share a part) — so `2 ≤ |X|`. Any `y` in the opposite part `Y` that met
`S ∪ T` would make `{c,y}` an `H`-edge with both ends in `S` (or both in `T`), which `W = 0`
forces to be witnessed; PST-W's route at `y` needs `|X| = 1`, and its route at `c` needs
`|Y| = 1` — whence balance caps `|X| ≤ 2`, so `X = {c,p_0}` and the required partner avoiding
both `S` and `T` would have to be `p_0 ∈ S ∪ T`. So `Y ∩ (S ∪ T) = ∅` and `S ∪ T ⊆ X`. A
nonempty `Y` then has some `y` with `N_H(y) = X ⊇ S ∪ T`, so `y ∈ RcUSet`, and `(E-b)`'s
singleton clause forces `S = N_H(y) ∩ S` and `T = N_H(y) ∩ T` to be singletons — both equal to
`{c}`, i.e. `S = T`, excluded. Finally `Y = ∅` caps `|X| ≤ 1` by balance, contradicting
`2 ≤ |X|`. -/
theorem pst_b_case11 (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W) (hW0 : Wcount H S T = 0)
    (hEb : ∀ y ∈ RcUSet H S T,
      (∃ x, H.neighborSet y ∩ S = {x}) ∧ (∃ x, H.neighborSet y ∩ T = {x}))
    (hSTne : S ≠ T) {c : W} (hcS : c ∈ S) (hcT : c ∈ T)
    (hSin : ∀ q ∈ S, same c q) (hTin : ∀ q ∈ T, same c q)
    (hK3 : (∃ p : W, p ∈ T ∧ p ∉ S ∧ H.neighborSet p ∩ S = ∅) ∨
      (∃ p : W, p ∈ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = ∅)) :
    False := by
  classical
  -- Balance, restated relative to `part c` (the `X`/`Y` naming of the source text).
  have hbalXY : {z | same c z ∧ part z = part c}.ncard ≤
        {z | same c z ∧ part z ≠ part c}.ncard + 1 := by
    by_cases hpc : part c = true
    · have e1 : {z | same c z ∧ part z = part c} = {b | same c b ∧ part b = true} := by rw [hpc]
      have e2 : {z | same c z ∧ part z ≠ part c} = {b | same c b ∧ part b = false} := by
        rw [hpc]; ext z; simp
      rw [e1, e2]; exact hbal1 c
    · have hpcf : part c = false := Bool.eq_false_iff.mpr hpc
      have e1 : {z | same c z ∧ part z = part c} = {b | same c b ∧ part b = false} := by rw [hpcf]
      have e2 : {z | same c z ∧ part z ≠ part c} = {b | same c b ∧ part b = true} := by
        rw [hpcf]; ext z; simp
      rw [e1, e2]; exact hbal2 c
  -- Both LEMMA K3 disjuncts supply the SAME symmetric datum (see the section note above).
  obtain ⟨p0, hp0ST, hp0ne, hp0nadj⟩ :
      ∃ p0 : W, (p0 ∈ S ∨ p0 ∈ T) ∧ p0 ≠ c ∧ ¬ H.Adj c p0 := by
    rcases hK3 with ⟨p, hpT, hpS, hpN⟩ | ⟨p, hpS, hpT, hpN⟩
    · refine ⟨p, Or.inr hpT, fun h => hpS (by rw [h]; exact hcS), fun hadj => ?_⟩
      have hmem : c ∈ H.neighborSet p ∩ S := ⟨hadj.symm, hcS⟩
      rw [hpN] at hmem; exact hmem
    · refine ⟨p, Or.inl hpS, fun h => hpT (by rw [h]; exact hcT), fun hadj => ?_⟩
      have hmem : c ∈ H.neighborSet p ∩ T := ⟨hadj.symm, hcT⟩
      rw [hpN] at hmem; exact hmem
  have hsamecp0 : same c p0 := by
    rcases hp0ST with h | h
    · exact hSin p0 h
    · exact hTin p0 h
  have hpartp0 : part p0 = part c := by
    by_contra hne
    exact hp0nadj ((hbip c p0).mpr ⟨hsamecp0, fun h => hne h.symm⟩)
  have hsubcp0 : ({c, p0} : Set W) ⊆ {z | same c z ∧ part z = part c} := by
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨hequiv.refl _, rfl⟩
    · exact ⟨hsamecp0, hpartp0⟩
  have hX2 : 2 ≤ {z | same c z ∧ part z = part c}.ncard := by
    calc (2 : ℕ) = ({c, p0} : Set W).ncard := (Set.ncard_pair (fun h => hp0ne h.symm)).symm
      _ ≤ _ := Set.ncard_le_ncard hsubcp0 (Set.toFinite _)
  -- ★ The one PST-W argument, covering the source's `Y ∩ T = ∅` and its `Y ∩ S = ∅` claim.
  have hYout : ∀ y : W, same c y → part y ≠ part c → (y ∈ S ∨ y ∈ T) → False := by
    intro y hcy hpy hyST
    have hadj : H.Adj c y := (hbip c y).mpr ⟨hcy, fun h => hpy h.symm⟩
    have hboth : (c ∈ S ∧ y ∈ S) ∨ (c ∈ T ∧ y ∈ T) := by
      rcases hyST with h | h
      · exact Or.inl ⟨hcS, h⟩
      · exact Or.inr ⟨hcT, h⟩
    have hcodeg : ((extF H S T).commonNeighbors (Sum.inl c) (Sum.inl y)).Nonempty := by
      rcases hboth with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Sum.inr true, (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inl_inr_true H S T c).mpr h1, (extF_adj_inl_inr_true H S T y).mpr h2⟩⟩
      · exact ⟨Sum.inr false, (extF H S T).mem_commonNeighbors.mpr
          ⟨(extF_adj_inl_inr_false H S T c).mpr h1, (extF_adj_inl_inr_false H S T y).mpr h2⟩⟩
    -- `W = 0` classifies the edge; codegree `≥ 1` rules out `E0`, so it is witnessed.
    have hWPempty : WPairs H S T = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hW0
    have hcl : s(Sum.inl c, Sum.inl y) ∈ E0 (extF H S T) ∪ Ew (extF H S T) := by
      by_contra hc
      have hmem : s(c, y) ∈ WPairs H S T := (mem_WPairs_iff H S T c y).mpr ⟨hadj, hboth, hc⟩
      rw [hWPempty] at hmem; exact hmem
    have hwit : (Wit (extF H S T) (Sum.inl c) (Sum.inl y)).Nonempty := by
      rcases hcl with h | h
      · exact absurd ((mem_E0_iff _ _ _).mp h).2 (Set.nonempty_iff_ne_empty.mp hcodeg)
      · exact ((mem_Ew_iff _ _ _).mp h).2.2
    have hpz : ∀ z : W, (part z = part y) ↔ (part z ≠ part c) := by
      intro z
      revert hpy
      cases part z <;> cases part y <;> cases part c <;> decide
    have hYset : {z | same c z ∧ part z = part y} = {z | same c z ∧ part z ≠ part c} := by
      ext z; simp only [Set.mem_setOf_eq, hpz z]
    rcases (lemma_PST_W H hequiv hbip S T hadj hcodeg).mp hwit with
      ⟨hY1, p, hpmem, hpav⟩ | ⟨hX1, -⟩
    · -- Route at `c`: `|Y| = 1`, so balance caps `|X| ≤ 2`, i.e. `X = {c, p_0}`.
      rw [hYset] at hY1
      have hXeq : ({c, p0} : Set W) = {z | same c z ∧ part z = part c} := by
        apply Set.eq_of_subset_of_ncard_le hsubcp0
        rw [Set.ncard_pair (fun h => hp0ne h.symm)]
        omega
      obtain ⟨hpX, hpnc⟩ := hpmem
      rw [← hXeq] at hpX
      have hpp0 : p = p0 := by
        rcases hpX with h | h
        · exact absurd (Set.mem_singleton_iff.mpr h) hpnc
        · exact Set.mem_singleton_iff.mp h
      have hpnS : p ∉ S := hpav.1.resolve_right (fun h => h hcS)
      have hpnT : p ∉ T := hpav.2.resolve_right (fun h => h hcT)
      rw [hpp0] at hpnS hpnT
      rcases hp0ST with h | h
      · exact hpnS h
      · exact hpnT h
    · -- Route at `y`: `|X| = 1`, contradicting `2 ≤ |X|`.
      omega
  -- `S ∪ T ⊆ X`.
  have hSTX : ∀ z : W, (z ∈ S ∨ z ∈ T) → same c z ∧ part z = part c := by
    intro z hz
    have hcz : same c z := by
      rcases hz with h | h
      · exact hSin z h
      · exact hTin z h
    refine ⟨hcz, ?_⟩
    by_contra hne
    exact hYout z hcz hne hz
  -- `Y = ∅`: a `y ∈ Y` lies in `RcUSet`, and `(E-b)`'s singletons collapse `S` and `T` to `{c}`.
  have hYempty : {z | same c z ∧ part z ≠ part c} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hcy, hpy⟩
    have hynS : y ∉ S := fun h => hYout y hcy hpy (Or.inl h)
    have hynT : y ∉ T := fun h => hYout y hcy hpy (Or.inr h)
    have hadjyc : H.Adj y c := (hbip y c).mpr ⟨hequiv.symm hcy, hpy⟩
    have hyRc : y ∈ RcUSet H S T := ⟨hynS, hynT, c, hadjyc, hcS⟩
    obtain ⟨⟨xs, hxs⟩, ⟨xt, hxt⟩⟩ := hEb y hyRc
    have hnbr : ∀ z : W, (z ∈ S ∨ z ∈ T) → z ∈ H.neighborSet y := by
      intro z hz
      obtain ⟨hcz, hpz⟩ := hSTX z hz
      exact (hbip y z).mpr ⟨hequiv.trans (hequiv.symm hcy) hcz, by rw [hpz]; exact hpy⟩
    have hSsing : S = {xs} := by
      rw [← hxs]
      ext z
      exact ⟨fun hz => ⟨hnbr z (Or.inl hz), hz⟩, fun hz => hz.2⟩
    have hTsing : T = {xt} := by
      rw [← hxt]
      ext z
      exact ⟨fun hz => ⟨hnbr z (Or.inr hz), hz⟩, fun hz => hz.2⟩
    have h1 : c = xs := by
      have hc' : c ∈ ({xs} : Set W) := by rw [← hSsing]; exact hcS
      exact Set.mem_singleton_iff.mp hc'
    have h2 : c = xt := by
      have hc' : c ∈ ({xt} : Set W) := by rw [← hTsing]; exact hcT
      exact Set.mem_singleton_iff.mp hc'
    exact hSTne (by rw [hSsing, hTsing, ← h1, ← h2])
  -- `Y = ∅` caps `|X| ≤ 1` by balance, contradicting `2 ≤ |X|`.
  have hY0 : {z | same c z ∧ part z ≠ part c}.ncard = 0 := by
    rw [hYempty]; exact Set.ncard_empty _
  omega

/-! #### Cases `(2,1)`/`(1,2)`/`(2,2)` — `S` (or `T`) meets a second class

The delicate step is `pst_b_out_S`'s last conjunct below ("`c`'s class meets `S` only inside
`T`"), and `(E-c)` supplies it in
three lines: a hypothetical `x ∈ (S ∖ T)` inside `c`'s class forms the CROSS-class pair
`{x, q0}` INSIDE `S` — cross-class because `q0` is the out-of-class witness — hence a `Z`-pair,
hence by `(E-c)` a chosen pair with an end in `R = S ∩ T`; but `x ∉ T` and `q0 ∉ T`, so neither
end is. (Note that `ZPairs` is blind to same-class pairs — the pair `{c,x}` is invisible to
it; the load-bearing pair is `{x,q0}`, which is cross-class.) -/

/-- Build a `ZPairs` witness from a cross-class pair lying inside `S` (or inside `T`) — the
converse direction of `z0_same_of_mem`, and the shape `(E-c)` is consumed through at every use
site below. On `H ∈ 𝓑` the three `ZPairs` side conditions are all consequences of `¬ same a b`:
distinctness (reflexivity), non-adjacency (`hbip`), and codegree `0` (a common neighbour would
make `a`, `b` `same` by transitivity). -/
theorem pst_b_mem_zpairs (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (S T : Set W) {a b : W} (hns : ¬ same a b)
    (hmem : (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T)) :
    s(a, b) ∈ ZPairs H S T := by
  refine (mem_ZPairs_iff H S T a b).mpr ⟨fun h => hns (by rw [← h]; exact hequiv.refl a),
    fun h => hns ((hbip a b).mp h).1, ?_, hmem⟩
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rw [SimpleGraph.mem_commonNeighbors] at hz
  exact hns (hequiv.trans ((hbip a z).mp hz.1).1 (hequiv.symm ((hbip b z).mp hz.2).1))

/-- Two distinct `same`-classes that LEMMA SWALLOW has collapsed to singletons are two `K_1`
components — two components of ODD order, which `IsBalCBUnion`'s at-most-one-odd clause
forbids. This is the contradiction all of Cases `(2,1)`, `(1,2)` and `(2,2)`'s first sub-case
end on. -/
theorem pst_b_two_K1 (H : SimpleGraph W) {same : W → W → Prop} (hequiv : Equivalence same)
    (hodd : ∀ a b : W, Odd {z | same a z}.ncard → Odd {z | same b z}.ncard → same a b)
    {a b : W} (hab : ¬ same a b)
    (ha : ∀ z, same a z → z = a) (hb : ∀ z, same b z → z = b) : False := by
  have hA : {z | same a z} = {a} := by
    ext z
    exact ⟨fun hz => Set.mem_singleton_iff.mpr (ha z hz),
      fun hz => by rw [Set.mem_singleton_iff.mp hz]; exact hequiv.refl a⟩
  have hB : {z | same b z} = {b} := by
    ext z
    exact ⟨fun hz => Set.mem_singleton_iff.mpr (hb z hz),
      fun hz => by rw [Set.mem_singleton_iff.mp hz]; exact hequiv.refl b⟩
  refine hab (hodd a b ?_ ?_)
  · rw [hA, Set.ncard_singleton]; exact odd_one
  · rw [hB, Set.ncard_singleton]; exact odd_one

/-- ★★ **The `S`-side out-of-class machinery.** An
out-of-`c`-class witness `q0 ∈ S` gives every `w ∈ R = S ∩ T` a `u`-side `q`-route at once, so
`pst_b_tight`'s fact 4 empties `RcUSet`, `R_c(u,v) = 0`, and `S ∪ T` is a union of `H`-classes
(`rc0_closed_union` + `same_class_of_closed`). The third output is the `(E-c)` step described in
the section note: `c`'s class meets `S` only inside `T`. -/
theorem pst_b_out_S (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W)
    (hFullU : (∀ w ∈ S ∩ T, ∃ q, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ T) → RcUSet H S T = ∅)
    (hRc2 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 2 * (RcUSet H S T).ncard)
    (hEcW : ∀ a b : W, s(a, b) ∈ ZPairs H S T → a ∈ S ∩ T ∨ b ∈ S ∩ T)
    {c q0 : W} (hcS : c ∈ S) (hq0S : q0 ∈ S) (hnq0 : ¬ same c q0)
    (hRclass : ∀ z, z ∈ S → z ∈ T → same c z) :
    (∀ z, same c z → z ∈ S ∪ T) ∧ (∀ z, same q0 z → z ∈ S ∪ T) ∧
      (∀ z, same c z → z ∈ S → z ∈ T) := by
  classical
  have hq0T : q0 ∉ T := fun h => hnq0 (hRclass q0 hq0S h)
  have hfull : ∀ w ∈ S ∩ T, ∃ q, q ∈ S ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ T := by
    rintro w ⟨hwS, hwT⟩
    have hnwq0 : ¬ same w q0 := fun h => hnq0 (hequiv.trans (hRclass w hwS hwT) h)
    exact ⟨q0, hq0S, fun heq => hnwq0 (by rw [heq]; exact hequiv.refl w), hnwq0, hq0T⟩
  have hRcU0 : (RcUSet H S T).ncard = 0 := by rw [hFullU hfull]; exact Set.ncard_empty _
  have hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0 := by omega
  have hclosed := rc0_closed_union H S T hRc0
  refine ⟨same_class_of_closed H hequiv hbip hbal1 hbal2 (Set.mem_union_left T hcS)
      (fun p hp q hpq => hclosed p q hpq hp),
    same_class_of_closed H hequiv hbip hbal1 hbal2 (Set.mem_union_left T hq0S)
      (fun p hp q hpq => hclosed p q hpq hp), ?_⟩
  intro x hcx hxS
  by_contra hxT
  have hnxq0 : ¬ same x q0 := fun h => hnq0 (hequiv.trans hcx h)
  rcases hEcW x q0 (pst_b_mem_zpairs H hequiv hbip S T hnxq0 (Or.inl ⟨hxS, hq0S⟩)) with h | h
  · exact hxT h.2
  · exact hq0T h.2

/-- The `T`-side mirror of `pst_b_out_S` (`pst_b_tight`'s fact 5 in place of fact 4; both land
on the same `RcUSet = ∅`, which is exactly why fact 5 was packaged with that conclusion). -/
theorem pst_b_out_T (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (S T : Set W)
    (hFullT : (∀ w ∈ S ∩ T, ∃ q, q ∈ T ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ S) → RcUSet H S T = ∅)
    (hRc2 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 2 * (RcUSet H S T).ncard)
    (hEcW : ∀ a b : W, s(a, b) ∈ ZPairs H S T → a ∈ S ∩ T ∨ b ∈ S ∩ T)
    {c q1 : W} (hcT : c ∈ T) (hq1T : q1 ∈ T) (hnq1 : ¬ same c q1)
    (hRclass : ∀ z, z ∈ S → z ∈ T → same c z) :
    (∀ z, same c z → z ∈ S ∪ T) ∧ (∀ z, same q1 z → z ∈ S ∪ T) ∧
      (∀ z, same c z → z ∈ T → z ∈ S) := by
  classical
  have hq1S : q1 ∉ S := fun h => hnq1 (hRclass q1 h hq1T)
  have hfull : ∀ w ∈ S ∩ T, ∃ q, q ∈ T ∧ q ≠ w ∧ ¬ same w q ∧ q ∉ S := by
    rintro w ⟨hwS, hwT⟩
    have hnwq1 : ¬ same w q1 := fun h => hnq1 (hequiv.trans (hRclass w hwS hwT) h)
    exact ⟨q1, hq1T, fun heq => hnwq1 (by rw [heq]; exact hequiv.refl w), hnwq1, hq1S⟩
  have hRcU0 : (RcUSet H S T).ncard = 0 := by rw [hFullT hfull]; exact Set.ncard_empty _
  have hRc0 : Rc (extF H S T) (Sum.inr true) (Sum.inr false) = 0 := by omega
  have hclosed := rc0_closed_union H S T hRc0
  refine ⟨same_class_of_closed H hequiv hbip hbal1 hbal2 (Set.mem_union_right S hcT)
      (fun p hp q hpq => hclosed p q hpq hp),
    same_class_of_closed H hequiv hbip hbal1 hbal2 (Set.mem_union_right S hq1T)
      (fun p hp q hpq => hclosed p q hpq hp), ?_⟩
  intro x hcx hxT
  by_contra hxS
  have hnxq1 : ¬ same x q1 := fun h => hnq1 (hequiv.trans hcx h)
  rcases hEcW x q1 (pst_b_mem_zpairs H hequiv hbip S T hnxq1 (Or.inr ⟨hxT, hq1T⟩)) with h | h
  · exact hxS h.1
  · exact hq1S h.1

/-- ★★ **Case `(2,2)`**: `S` and `T` each meet a second
class. Both `pst_b_out_S` and `pst_b_out_T` apply, so `c`'s class is exactly `R = S ∩ T`.

*Sub-case `C_2 ≠ C_2'`* (`¬ same q0 q1`): `q0`'s class avoids `T` — a `T`-element `z` of it
would make `{z, q1}` a cross-class `Z`-pair inside `T` whose ends are neither in `R` (`z` is
outside `c`'s class, and `R` is inside it) nor `q1` (`q1 ∉ S`). So `q0`'s class lies in `S`,
`q1`'s in `T`, SWALLOW collapses both, and `pst_b_two_K1` closes.

*Sub-case `C_2 = C_2'`* (`same q0 q1`): `c`'s class is inside `S`, so SWALLOW gives `R = {c}`.
`(E-c)`'s "at most one chosen partner per `w ∈ R`" (`hEcOneS`/`hEcOneT`)
then pins `S = {c,q0}` and `T = {c,q1}`, so
`q0`'s class is exactly `{q0,q1}`; balance forces the two into different parts, i.e.
`H.Adj q0 q1`. Both surviving LEMMA K3 routes now fail (`N_H(q1) ∩ S ∋ q0`, `N_H(q0) ∩ T ∋ q1`),
forcing `chi = 1` against (SAT)'s `chi = 0`. -/
theorem pst_b_case22 (H : SimpleGraph W) {same : W → W → Prop} {part : W → Bool}
    (hequiv : Equivalence same) (hbip : ∀ a b : W, H.Adj a b ↔ same a b ∧ part a ≠ part b)
    (hbal1 : ∀ a, {b | same a b ∧ part b = true}.ncard ≤
      {b | same a b ∧ part b = false}.ncard + 1)
    (hbal2 : ∀ a, {b | same a b ∧ part b = false}.ncard ≤
      {b | same a b ∧ part b = true}.ncard + 1)
    (hodd : ∀ a b : W, Odd {z | same a z}.ncard → Odd {z | same b z}.ncard → same a b)
    (S T : Set W) (hW0 : Wcount H S T = 0)
    (hK3 : (∃ p : W, p ∈ T ∧ p ∉ S ∧ H.neighborSet p ∩ S = ∅) ∨
      (∃ p : W, p ∈ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = ∅))
    (hEcW : ∀ a b : W, s(a, b) ∈ ZPairs H S T → a ∈ S ∩ T ∨ b ∈ S ∩ T)
    (hEcOneS : ∀ w x x' : W, w ∈ S ∩ T → x ∈ S → x' ∈ S →
      s(w, x) ∈ ZPairs H S T → s(w, x') ∈ ZPairs H S T → x = x')
    (hEcOneT : ∀ w x x' : W, w ∈ S ∩ T → x ∈ T → x' ∈ T →
      s(w, x) ∈ ZPairs H S T → s(w, x') ∈ ZPairs H S T → x = x')
    {c q0 q1 : W} (hcS : c ∈ S) (hcT : c ∈ T)
    (hq0S : q0 ∈ S) (hnq0 : ¬ same c q0) (hq0T : q0 ∉ T)
    (hq1T : q1 ∈ T) (hnq1 : ¬ same c q1) (hq1S : q1 ∉ S)
    (hRclass : ∀ z, z ∈ S → z ∈ T → same c z)
    (hcCl : ∀ z, same c z → z ∈ S ∪ T)
    (hq0Cl : ∀ z, same q0 z → z ∈ S ∪ T)
    (hq1Cl : ∀ z, same q1 z → z ∈ S ∪ T)
    (hcSsubT : ∀ z, same c z → z ∈ S → z ∈ T)
    (hcTsubS : ∀ z, same c z → z ∈ T → z ∈ S) :
    False := by
  classical
  -- `c`'s class is exactly `R = S ∩ T`.
  have hcR : ∀ z, same c z → z ∈ S ∧ z ∈ T := by
    intro z hz
    rcases hcCl z hz with h | h
    · exact ⟨h, hcSsubT z hz h⟩
    · exact ⟨hcTsubS z hz h, h⟩
  by_cases hsame01 : same q0 q1
  · -- Sub-case `C_2 = C_2'`.
    have hcK1 : ∀ y, same c y → y = c :=
      lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0
        (Or.inl (fun z hz => (hcR z hz).1))
    have hSeq : S = {c, q0} := by
      ext z
      constructor
      · intro hzS
        by_cases hcz : same c z
        · exact Set.mem_insert_iff.mpr (Or.inl (hcK1 z hcz))
        · refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ?_))
          exact hEcOneS c z q0 ⟨hcS, hcT⟩ hzS hq0S
            (pst_b_mem_zpairs H hequiv hbip S T hcz (Or.inl ⟨hcS, hzS⟩))
            (pst_b_mem_zpairs H hequiv hbip S T hnq0 (Or.inl ⟨hcS, hq0S⟩))
      · intro hz
        rcases hz with h | h
        · rw [h]; exact hcS
        · rw [Set.mem_singleton_iff.mp h]; exact hq0S
    have hTeq : T = {c, q1} := by
      ext z
      constructor
      · intro hzT
        by_cases hcz : same c z
        · exact Set.mem_insert_iff.mpr (Or.inl (hcK1 z hcz))
        · refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ?_))
          exact hEcOneT c z q1 ⟨hcS, hcT⟩ hzT hq1T
            (pst_b_mem_zpairs H hequiv hbip S T hcz (Or.inr ⟨hcT, hzT⟩))
            (pst_b_mem_zpairs H hequiv hbip S T hnq1 (Or.inr ⟨hcT, hq1T⟩))
      · intro hz
        rcases hz with h | h
        · rw [h]; exact hcT
        · rw [Set.mem_singleton_iff.mp h]; exact hq1T
    -- `q0`'s class is exactly `{q0, q1}`, so balance puts `q0`, `q1` in different parts.
    have hq0ne1 : q0 ≠ q1 := fun h => hq0T (by rw [h]; exact hq1T)
    have hclassq0 : ∀ z, same q0 z → (z = q0 ∨ z = q1) := by
      intro z hz
      have hnzc : ¬ same c z := fun h => hnq0 (hequiv.trans h (hequiv.symm hz))
      rcases hq0Cl z hz with h | h
      · rw [hSeq] at h
        rcases h with h1 | h1
        · exact absurd (by rw [h1]; exact hequiv.refl c : same c z) hnzc
        · exact Or.inl (Set.mem_singleton_iff.mp h1)
      · rw [hTeq] at h
        rcases h with h1 | h1
        · exact absurd (by rw [h1]; exact hequiv.refl c : same c z) hnzc
        · exact Or.inr (Set.mem_singleton_iff.mp h1)
    have hpart01 : part q0 ≠ part q1 := by
      by_contra hpe
      have hoppE0 : {z | same q0 z ∧ part z ≠ part q0}.ncard = 0 := by
        have hE : {z | same q0 z ∧ part z ≠ part q0} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨hz, hpz⟩
          rcases hclassq0 z hz with h | h
          · exact hpz (by rw [h])
          · exact hpz (by rw [h, ← hpe])
        rw [hE]; exact Set.ncard_empty _
      have h2le : 2 ≤ {z | same q0 z ∧ part z = part q0}.ncard := by
        have hsub : ({q0, q1} : Set W) ⊆ {z | same q0 z ∧ part z = part q0} := by
          intro z hz
          rcases hz with rfl | rfl
          · exact ⟨hequiv.refl _, rfl⟩
          · exact ⟨hsame01, hpe.symm⟩
        calc (2 : ℕ) = ({q0, q1} : Set W).ncard := (Set.ncard_pair hq0ne1).symm
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      by_cases hp : part q0 = true
      · have e1 : {z | same q0 z ∧ part z = part q0} = {b | same q0 b ∧ part b = true} := by
          rw [hp]
        have e2 : {z | same q0 z ∧ part z ≠ part q0} = {b | same q0 b ∧ part b = false} := by
          rw [hp]; ext z; simp
        rw [e1] at h2le; rw [e2] at hoppE0
        have := hbal1 q0; omega
      · have hpf : part q0 = false := Bool.eq_false_iff.mpr hp
        have e1 : {z | same q0 z ∧ part z = part q0} = {b | same q0 b ∧ part b = false} := by
          rw [hpf]
        have e2 : {z | same q0 z ∧ part z ≠ part q0} = {b | same q0 b ∧ part b = true} := by
          rw [hpf]; ext z; simp
        rw [e1] at h2le; rw [e2] at hoppE0
        have := hbal2 q0; omega
    have hadj01 : H.Adj q0 q1 := (hbip q0 q1).mpr ⟨hsame01, hpart01⟩
    -- Both surviving LEMMA K3 routes fail, forcing `chi = 1` against (SAT).
    rcases hK3 with ⟨p, hpT, hpS, hpN⟩ | ⟨p, hpS, hpT, hpN⟩
    · have hmem : q0 ∈ H.neighborSet p ∩ S := by
        have hpq1 : p = q1 := by
          rw [hTeq] at hpT
          rcases hpT with h | h
          · exact absurd (by rw [h]; exact hcS : p ∈ S) hpS
          · exact Set.mem_singleton_iff.mp h
        rw [hpq1]; exact ⟨hadj01.symm, hq0S⟩
      rw [hpN] at hmem; exact hmem
    · have hmem : q1 ∈ H.neighborSet p ∩ T := by
        have hpq0 : p = q0 := by
          rw [hSeq] at hpS
          rcases hpS with h | h
          · exact absurd (by rw [h]; exact hcT : p ∈ T) hpT
          · exact Set.mem_singleton_iff.mp h
        rw [hpq0]; exact ⟨hadj01, hq1T⟩
      rw [hpN] at hmem; exact hmem
  · -- Sub-case `C_2 ≠ C_2'`: two distinct `K_1` classes.
    have hq0Ssub : ∀ z, same q0 z → z ∈ S := by
      intro z hz
      rcases hq0Cl z hz with h | h
      · exact h
      · exfalso
        have hnzq1 : ¬ same z q1 := fun h1 => hsame01 (hequiv.trans hz h1)
        rcases hEcW z q1 (pst_b_mem_zpairs H hequiv hbip S T hnzq1 (Or.inr ⟨h, hq1T⟩)) with
          h2 | h2
        · exact hnq0 (hequiv.trans (hRclass z h2.1 h2.2) (hequiv.symm hz))
        · exact hq1S h2.1
    have hq1Tsub : ∀ z, same q1 z → z ∈ T := by
      intro z hz
      rcases hq1Cl z hz with h | h
      · exfalso
        have hnzq0 : ¬ same z q0 := fun h1 => hsame01 (hequiv.symm (hequiv.trans hz h1))
        rcases hEcW z q0 (pst_b_mem_zpairs H hequiv hbip S T hnzq0 (Or.inl ⟨h, hq0S⟩)) with
          h2 | h2
        · exact hnq1 (hequiv.trans (hRclass z h2.1 h2.2) (hequiv.symm hz))
        · exact hq0T h2.2
      · exact h
    exact pst_b_two_K1 H hequiv hodd hsame01
      (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inl hq0Ssub))
      (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inr hq1Tsub))

/-! ### THEOREM PST-B — assembly -/

/-- ★★★ **THEOREM PST-B**: **no
configuration with `S ∩ T ≠ ∅` is tight** — the branch is vacuous.

The `(E-a)/(E-b)/(E-c)` equalities and the `(r_S,r_T)` classification are consumed INTERNALLY
as this proof's own case split rather than minted as intermediate
classification lemmas with no downstream consumer.

The case split is taken directly on `same`-class membership rather than on a component count,
so no "`S` meets at most two components" fact is ever stated: fix
`c ∈ R = S ∩ T` (all of `R` lies in its class, `pst_b_tight`'s fact 3) and split on whether `S`
— and whether `T` — has a member outside that class. Cases `(2,1)` and `(1,2)` need no lemma of
their own: `pst_b_out_S`/`pst_b_out_T` deliver `c`'s class `= T` (resp. `= S`) and the witness's
class `⊆ S` (resp. `⊆ T`), LEMMA SWALLOW collapses both, and `pst_b_two_K1` closes on the
at-most-one-odd hypothesis. -/
theorem pst_b (H : SimpleGraph W) (hH : IsBalCBUnion H) {S T : Set W}
    (hR : (S ∩ T).Nonempty)
    (hDinc : Dinc (extF H S T) (Sum.inr true) (Sum.inr false) = 1) :
    False := by
  classical
  obtain ⟨hchi, hW0, -, -, hKeq⟩ := (lemma_SAT H hH S T).mp hDinc
  have hSTne : S ≠ T := pst_b_S_ne_T H hH hR hDinc
  -- LEMMA K3's two surviving disjuncts (`chi = 0` from (SAT); `S ∩ T = ∅` is excluded).
  have hK3 : (∃ p : W, p ∈ T ∧ p ∉ S ∧ H.neighborSet p ∩ S = ∅) ∨
      (∃ p : W, p ∈ S ∧ p ∉ T ∧ H.neighborSet p ∩ T = ∅) := by
    have hmemE : s(Sum.inr true, Sum.inr false) ∈ E0 (extF H S T) ∪ Ew (extF H S T) := by
      by_contra hc
      unfold Chi at hchi
      rw [if_neg hc] at hchi
      exact absurd hchi one_ne_zero
    rcases (lemma_K3 H S T).mp hmemE with h | h | h
    · exact absurd h (Set.nonempty_iff_ne_empty.mp hR)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨c, hcS, hcT⟩ := id hR
  obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, hodd⟩ := hH
  obtain ⟨-, hRc2, hRone, hFullU, hFullT, hEb, f, g, hEc⟩ :=
    pst_b_tight H hequiv hbip hbal1 hbal2 S T hKeq
  -- All of `R` lies in `c`'s class (`pst_b_tight`'s fact 3).
  have hRclass : ∀ z, z ∈ S → z ∈ T → same c z := by
    intro z hzS hzT
    by_cases heq : c = z
    · rw [heq]; exact hequiv.refl z
    · exact hRone c z hcS hcT hzS hzT heq
  -- The three forms of `(E-c)` the cases consume.
  have hEcW : ∀ a b : W, s(a, b) ∈ ZPairs H S T → a ∈ S ∩ T ∨ b ∈ S ∩ T := by
    intro a b hab
    rcases hEc a b hab with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hEcOneS : ∀ w x x' : W, w ∈ S ∩ T → x ∈ S → x' ∈ S →
      s(w, x) ∈ ZPairs H S T → s(w, x') ∈ ZPairs H S T → x = x' := by
    intro w x x' hwR hxS hx'S hzp hzp'
    have key : ∀ y : W, y ∈ S → s(w, y) ∈ ZPairs H S T → y = f w := by
      intro y hyS hzy
      rcases hEc w y hzy with ⟨-, h | h⟩ | ⟨-, h | h⟩
      · exact h.1
      · exact absurd hyS h.2
      · exact absurd hwR.2 h.2
      · exact absurd hwR.1 h.2
    rw [key x hxS hzp, key x' hx'S hzp']
  have hEcOneT : ∀ w x x' : W, w ∈ S ∩ T → x ∈ T → x' ∈ T →
      s(w, x) ∈ ZPairs H S T → s(w, x') ∈ ZPairs H S T → x = x' := by
    intro w x x' hwR hxT hx'T hzp hzp'
    have key : ∀ y : W, y ∈ T → s(w, y) ∈ ZPairs H S T → y = g w := by
      intro y hyT hzy
      rcases hEc w y hzy with ⟨-, h | h⟩ | ⟨-, h | h⟩
      · exact absurd hyT h.2
      · exact h.1
      · exact absurd hwR.2 h.2
      · exact absurd hwR.1 h.2
    rw [key x hxT hzp, key x' hx'T hzp']
  by_cases hSout : ∃ q, q ∈ S ∧ ¬ same c q
  · obtain ⟨q0, hq0S, hnq0⟩ := hSout
    obtain ⟨hcCl, hq0Cl, hcSsubT⟩ :=
      pst_b_out_S H hequiv hbip hbal1 hbal2 S T hFullU hRc2 hEcW hcS hq0S hnq0 hRclass
    by_cases hTout : ∃ q, q ∈ T ∧ ¬ same c q
    · -- Case `(2,2)`.
      obtain ⟨q1, hq1T, hnq1⟩ := hTout
      obtain ⟨-, hq1Cl, hcTsubS⟩ :=
        pst_b_out_T H hequiv hbip hbal1 hbal2 S T hFullT hRc2 hEcW hcT hq1T hnq1 hRclass
      exact pst_b_case22 H hequiv hbip hbal1 hbal2 hodd S T hW0 hK3 hEcW hEcOneS hEcOneT
        hcS hcT hq0S hnq0 (fun h => hnq0 (hRclass q0 hq0S h)) hq1T hnq1
        (fun h => hnq1 (hRclass q1 h hq1T)) hRclass hcCl hq0Cl hq1Cl hcSsubT hcTsubS
    · -- Case `(2,1)`: `c`'s class is exactly `T`, `q0`'s class lies in `S`; both are `K_1`.
      push_neg at hTout
      have hcTsub : ∀ z, same c z → z ∈ T := by
        intro z hz
        rcases hcCl z hz with h | h
        · exact hcSsubT z hz h
        · exact h
      have hq0Ssub : ∀ z, same q0 z → z ∈ S := by
        intro z hz
        rcases hq0Cl z hz with h | h
        · exact h
        · exact absurd (hequiv.trans (hTout z h) (hequiv.symm hz)) hnq0
      exact pst_b_two_K1 H hequiv hodd hnq0
        (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inr hcTsub))
        (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inl hq0Ssub))
  · push_neg at hSout
    by_cases hTout : ∃ q, q ∈ T ∧ ¬ same c q
    · -- Case `(1,2)`, the exact mirror of `(2,1)`.
      obtain ⟨q1, hq1T, hnq1⟩ := hTout
      obtain ⟨hcCl, hq1Cl, hcTsubS⟩ :=
        pst_b_out_T H hequiv hbip hbal1 hbal2 S T hFullT hRc2 hEcW hcT hq1T hnq1 hRclass
      have hcSsub : ∀ z, same c z → z ∈ S := by
        intro z hz
        rcases hcCl z hz with h | h
        · exact h
        · exact hcTsubS z hz h
      have hq1Tsub : ∀ z, same q1 z → z ∈ T := by
        intro z hz
        rcases hq1Cl z hz with h | h
        · exact absurd (hequiv.trans (hSout z h) (hequiv.symm hz)) hnq1
        · exact h
      exact pst_b_two_K1 H hequiv hodd hnq1
        (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inl hcSsub))
        (lemma_swallow_component H S T hequiv hbip hbal1 hbal2 hW0 (Or.inr hq1Tsub))
    · -- Case `(1,1)`.
      push_neg at hTout
      exact pst_b_case11 H hequiv hbip hbal1 hbal2 S T hW0 hEb hSTne hcS hcT hSout hTout hK3

/-! ### The deletion↔extension bridge for `step_del`

`step_del` is stated about a graph `G` carrying a distinguished tight edge `\{u,v\}`; THEOREM
PST-A and THEOREM PST-B are stated about `extF H S T`. The bridge is the
equivalence-of-enumeration fact: any `G` with `\{u,v\} ∈ E(G)` **is** `H + u + v` for `H := G − \{u,v\}`,
`S := N_G(u) ∖ \{v\}`, `T := N_G(v) ∖ \{u\}`, and the two enumeration schemes enumerate the same
objects. Realised here as an honest graph isomorphism (`stepIso`), so the sentence is a proved
fact in the development rather than a remark.

Carrying `D_inc(u,v) = 1` across that isomorphism needs `D` to be an isomorphism invariant,
which is `iso_Dv` below. It is proved once, in the general form, and used twice: on `stepIso`
itself and on `delPairExtFIso` (the deletion side). `D` is a sum of `cwt` over `Sym2`
(`Dv_eq_sum_cwt`), so the work is per-pair `E0`/`Ew`/`Anon` transport — the same shape the
`delPair_extF_*` layer above already used for its own reindexing. -/

section IsoTransport

variable {V' : Type*} [Fintype V'] [DecidableEq V']

/-- Common neighbourhoods transport along an isomorphism as a set image — the single fact all
the `E0`/`Ew`/`Anon` transports below are built from. -/
theorem iso_commonNeighbors_image {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G')
    (a b : V) :
    G'.commonNeighbors (φ a) (φ b) = (fun x => φ x) '' (G.commonNeighbors a b) := by
  ext z
  simp only [Set.mem_image, SimpleGraph.mem_commonNeighbors]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨φ.symm z, ⟨?_, ?_⟩, by simp⟩
    · rw [← φ.map_rel_iff]; simpa using h1
    · rw [← φ.map_rel_iff]; simpa using h2
  · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
    exact ⟨φ.map_rel_iff.mpr h1, φ.map_rel_iff.mpr h2⟩

theorem iso_commonNeighbors_eq_singleton {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G')
    (x y z : V) :
    G'.commonNeighbors (φ x) (φ y) = {φ z} ↔ G.commonNeighbors x y = {z} := by
  rw [iso_commonNeighbors_image φ x y]
  constructor
  · intro h
    ext w
    rw [Set.mem_singleton_iff]
    constructor
    · intro hw
      have hm : φ w ∈ ({φ z} : Set V') := by rw [← h]; exact ⟨w, hw, rfl⟩
      exact φ.injective (Set.mem_singleton_iff.mp hm)
    · intro hw
      have hm : φ z ∈ (fun x => φ x) '' (G.commonNeighbors x y) := by
        rw [h]; exact Set.mem_singleton _
      obtain ⟨c, hc, hce⟩ := hm
      rw [hw, ← φ.injective hce]
      exact hc
  · intro h
    rw [h]
    ext w
    simp only [Set.mem_image, Set.mem_singleton_iff]
    exact ⟨fun ⟨c, hc, hce⟩ => by rw [← hce, hc], fun hw => ⟨z, rfl, hw.symm⟩⟩

theorem iso_isWitAt {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (x z y : V) :
    IsWitAt G' (φ x) (φ z) (φ y) ↔ IsWitAt G x z y := by
  unfold IsWitAt
  rw [φ.map_rel_iff, iso_commonNeighbors_eq_singleton φ x y z]
  exact and_congr_left (fun _ => ⟨fun h he => h (by rw [he]), fun h he => h (φ.injective he)⟩)

theorem iso_wit_nonempty {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (x y : V) :
    (Wit G' (φ x) (φ y)).Nonempty ↔ (Wit G x y).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨φ.symm p, ?_⟩
    have hps : φ (φ.symm p) = p := by simp
    rcases hp with h | h
    · refine Or.inl ((iso_isWitAt φ x y (φ.symm p)).mp ?_)
      rw [hps]; exact h
    · refine Or.inr ((iso_isWitAt φ y x (φ.symm p)).mp ?_)
      rw [hps]; exact h
  · rintro ⟨p, hp⟩
    refine ⟨φ p, ?_⟩
    rcases hp with h | h
    · exact Or.inl ((iso_isWitAt φ x y p).mpr h)
    · exact Or.inr ((iso_isWitAt φ y x p).mpr h)

theorem iso_mem_E0 {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (x y : V) :
    s(φ x, φ y) ∈ E0 G' ↔ s(x, y) ∈ E0 G := by
  rw [mem_E0_iff, mem_E0_iff, φ.map_rel_iff, iso_commonNeighbors_image φ x y,
    Set.image_eq_empty]

theorem iso_mem_Ew {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (x y : V) :
    s(φ x, φ y) ∈ Ew G' ↔ s(x, y) ∈ Ew G := by
  rw [mem_Ew_iff, mem_Ew_iff, φ.map_rel_iff, iso_commonNeighbors_image φ x y,
    Set.image_nonempty, iso_wit_nonempty φ x y]

theorem iso_mem_Anon {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (x y : V) :
    s(φ x, φ y) ∈ Anon G' ↔ s(x, y) ∈ Anon G := by
  rw [mem_Anon_iff, mem_Anon_iff, φ.map_rel_iff, iso_commonNeighbors_image φ x y,
    Set.image_nonempty]
  exact and_congr_left (fun _ => ⟨fun h he => h (by rw [he]), fun h he => h (φ.injective he)⟩)

theorem iso_cwt {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (P : Sym2 V) :
    cwt G' (Sym2.map (fun x => φ x) P) = cwt G P := by
  classical
  induction P using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk]
    by_cases hadj : G.Adj x y
    · rw [cwt_of_adj _ (φ.map_rel_iff.mpr hadj), cwt_of_adj _ hadj]
      congr 1
      simp only [Set.mem_union, iso_mem_E0 φ, iso_mem_Ew φ]
    · rw [cwt_of_not_adj _ (fun h => hadj (φ.map_rel_iff.mp h)), cwt_of_not_adj _ hadj]
      congr 1
      simp only [iso_mem_Anon φ]

/-- ★ **`D` is a graph-isomorphism invariant.** `Dv_eq_sum_cwt` turns it into a sum over
`Sym2`, which reindexes along the bijection `Sym2.map φ`. -/
theorem iso_Dv {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') : Dv G = Dv G' := by
  classical
  have hbij : Function.Bijective
      (Sym2.map (fun x => (φ x : V')) : Sym2 V → Sym2 V') := by
    refine ⟨Sym2.map.injective φ.injective, ?_⟩
    intro Q
    induction Q using Sym2.ind with
    | _ a b => exact ⟨s(φ.symm a, φ.symm b), by rw [Sym2.map_mk]; simp⟩
  rw [Dv_eq_sum_cwt, Dv_eq_sum_cwt]
  exact Fintype.sum_bijective _ hbij (cwt G) (cwt G') (fun P => (iso_cwt φ P).symm)

end IsoTransport

/-- `delBoolEquiv` packaged as an isomorphism: deleting `u,v` from `extF H S T` gives back `H`
(this is `delPair_extF_adj`, restated so `iso_Dv` can consume it). -/
def delPairExtFIso (H : SimpleGraph W) (S T : Set W) :
    delPair (extF H S T) (Sum.inr true) (Sum.inr false) ≃g H := by
  refine ⟨delBoolEquiv, ?_⟩
  intro a b
  exact (delPair_extF_adj H S T a b).symm

/-- The vertex bijection `(V ∖ \{u,v\}) ⊕ Bool ≃ V` underlying `stepIso`: `Sum.inl` is the
subtype inclusion, `Sum.inr true ↦ u`, `Sum.inr false ↦ v`. -/
def stepEquiv {u v : V} (huv : u ≠ v) : {w : V // w ≠ u ∧ w ≠ v} ⊕ Bool ≃ V where
  toFun := Sum.elim (fun w => (w : V)) (fun b => cond b u v)
  invFun x := if h1 : x = u then Sum.inr true else if h2 : x = v then Sum.inr false
    else Sum.inl ⟨x, h1, h2⟩
  left_inv := by
    rintro (⟨w, hwu, hwv⟩ | b)
    · show (if h1 : w = u then _ else if h2 : w = v then _ else _) = _
      rw [dif_neg hwu, dif_neg hwv]
      rfl
    · cases b with
      | true =>
        show (if h1 : u = u then _ else if h2 : u = v then _ else _) = _
        rw [dif_pos rfl]
      | false =>
        show (if h1 : v = u then _ else if h2 : v = v then _ else _) = _
        rw [dif_neg (Ne.symm huv), dif_pos rfl]
  right_inv := by
    intro x
    dsimp only
    split_ifs with h1 h2
    · exact h1.symm
    · exact h2.symm
    · rfl

/-- ★★ **The extension-form realisation of a graph with a distinguished edge** (the
equivalence-of-enumeration fact, made literal): for `\{u,v\} ∈ E(G)`,
`G ≅ extF (G − \{u,v\}) (N_G(u) ∖ \{v\}) (N_G(v) ∖ \{u\})`. -/
def stepIso (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    extF (delPair G u v) {w : {w : V // w ≠ u ∧ w ≠ v} | G.Adj u (w : V)}
      {w : {w : V // w ≠ u ∧ w ≠ v} | G.Adj v (w : V)} ≃g G := by
  refine ⟨stepEquiv huv.ne, ?_⟩
  intro x y
  rcases x with a | bx <;> rcases y with b | by'
  · show G.Adj (a : V) (b : V) ↔ _
    rw [extF_adj_inl_inl, delPair_adj]
  · cases by' with
    | true =>
      show G.Adj (a : V) u ↔ _
      rw [extF_adj_inl_inr_true, SimpleGraph.adj_comm]
      exact Iff.rfl
    | false =>
      show G.Adj (a : V) v ↔ _
      rw [extF_adj_inl_inr_false, SimpleGraph.adj_comm]
      exact Iff.rfl
  · cases bx with
    | true =>
      show G.Adj u (b : V) ↔ _
      rw [extF_adj_inr_true_inl]
      exact Iff.rfl
    | false =>
      show G.Adj v (b : V) ↔ _
      rw [extF_adj_inr_false_inl]
      exact Iff.rfl
  · cases bx with
    | true =>
      cases by' with
      | true =>
        show G.Adj u u ↔ _
        simp [extF.eq_1]
      | false =>
        show G.Adj u v ↔ _
        exact ⟨fun _ => extF_adj_uv _ _ _, fun _ => huv⟩
    | false =>
      cases by' with
      | true =>
        show G.Adj v u ↔ _
        exact ⟨fun _ => (extF_adj_uv _ _ _).symm, fun _ => huv.symm⟩
      | false =>
        show G.Adj v v ↔ _
        simp [extF.eq_1]

/-! ## TOP-LEVEL RESULTS

`step_del` and its four dependents appear here, after the `extF` machinery, so that
`step_del` can cite THEOREM
PST-A (`pst_a`) and THEOREM PST-B (`pst_b`). -/

/-! ### The deletion step and the induction -/

/-- ★★★ **The deletion step**: if a tight edge's deletion lands in `𝓑`, the graph itself
was in `𝓑`.

Proof: `stepIso` realises `G` as the extension configuration `extF H S T` for `H := G − {u,v}`,
`S := N_G(u) ∖ {v}`, `T := N_G(v) ∖ {u}` — the equivalence-of-enumeration
fact — and `iso_Dv` carries `D_inc(u,v) = 1` across (applied twice: to `stepIso` and to
`delPairExtFIso` on the deletion side). Then the two cases:
`S ∩ T = ∅` is THEOREM PST-A (`pst_a`), whose `IsBalCBUnion (extF H S T)` transports back to
`G` along `IsBalCBUnion.map_iso`; `S ∩ T ≠ ∅` is THEOREM PST-B (`pst_b`), which shows the
branch is vacuous. -/
theorem step_del (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (hBal : IsBalCBUnion (delPair G u v)) (hDinc : Dinc G u v = 1) :
    IsBalCBUnion G := by
  classical
  set S : Set {w : V // w ≠ u ∧ w ≠ v} := {w | G.Adj u (w : V)} with hSdef
  set T : Set {w : V // w ≠ u ∧ w ≠ v} := {w | G.Adj v (w : V)} with hTdef
  have hiso : extF (delPair G u v) S T ≃g G := stepIso G huv
  have hDinc' : Dinc (extF (delPair G u v) S T) (Sum.inr true) (Sum.inr false) = 1 := by
    have h1 : Dv (extF (delPair G u v) S T) = Dv G := iso_Dv hiso
    have h2 : Dv (delPair (extF (delPair G u v) S T) (Sum.inr true) (Sum.inr false))
        = Dv (delPair G u v) := iso_Dv (delPairExtFIso (delPair G u v) S T)
    show Dv _ - Dv _ = 1
    rw [h1, h2]
    exact hDinc
  by_cases hST : S ∩ T = ∅
  · exact IsBalCBUnion.map_iso hiso.symm (pst_a (delPair G u v) hBal hST hDinc')
  · exact (pst_b (delPair G u v) hBal (Set.nonempty_iff_ne_empty.mpr hST) hDinc').elim

/-- ★ **The induction**: every graph with `D(G) = ⌊n/2⌋` is in `𝓑` — the forward
direction of the tightness characterization, by strong induction
(`lemma_supply → lemma_tight_del → IH → step_del`), a clone of `row19_strong_induction`
(`Erdos742.lean:3489`) carrying `IsBalCBUnion` through `delPair` instead of
just the inequality.  Base case `n ≤ 1` (both `n = 0` and `n = 1` at once) is
`isBalCBUnion_of_subsingleton`.  The converse (every member of `𝓑` has
`D(G) = ⌊n/2⌋`, in full multi-component generality) is not stated in
this file; the single-class instance the top-level results
actually consume, `dv_of_isBalCBUnion_connected`, is proved above, so
nothing downstream of this theorem rests on an open item. -/
theorem stmt5_forward : ∀ (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W), Fintype.card W = n →
    Dv G = ((n / 2 : ℕ) : ℤ) → IsBalCBUnion G := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W _ _ G hcard hD
    rw [← hcard] at hD
    by_cases hn1 : Fintype.card W ≤ 1
    · haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp hn1
      exact isBalCBUnion_of_subsingleton G
    · have hn2 : 2 ≤ Fintype.card W := by omega
      obtain ⟨u, v, huv, hle⟩ := lemma_supply G hn2 hD
      obtain ⟨hDinc1, hDdel⟩ := lemma_tight_del G hn2 hD huv hle
      have hcard2 : Fintype.card {w : W // w ≠ u ∧ w ≠ v} = Fintype.card W - 2 :=
        card_delPair_type huv.ne
      have hIHapp : IsBalCBUnion (delPair G u v) :=
        ih (Fintype.card W - 2) (by omega) (delPair G u v) hcard2 hDdel
      exact step_del G huv hIHapp hDinc1

/-- ★★★ **The equality characterization**, `n ≥ 3`, in the
INTRINSIC form: `G ≅ K_{⌈n/2⌉,⌊n/2⌋}` phrased as "`G` is connected and a
member of `𝓑`" rather than as an isomorphism to a constructed
`completeBipartiteGraph` — a connected member of `𝓑` has exactly one class
(`same_of_reachable`), which IS `K_{⌈n/2⌉,⌊n/2⌋}` (its two part-sizes differ
by ≤ 1 and sum to `n`), so this is mathematically the same content.
This intrinsic form is the internal
workhorse; the public statement is the literal isomorphism form,
`stmt6_ms_eq_iso` below, derived from this theorem as a corollary. -/
theorem stmt6_ms_eq (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeSet.ncard = (Fintype.card V) ^ 2 / 4 ↔
      (IsBalCBUnion G ∧ G.Preconnected) := by
  rw [← pta_l4_arith G hG]
  constructor
  · intro hD
    exact ⟨stmt5_forward (Fintype.card V) G rfl hD, isDiameter2Critical_preconnected hG⟩
  · rintro ⟨hBal, hconn⟩
    exact dv_of_isBalCBUnion_connected hBal hconn

/-- ★★★ **`stmt6_ms_eq_iso`** — the equality characterization as a literal
isomorphism.  Existential canonical-label form: `∃ a b,
a+b=n ∧ (a=b ∨ a=b+1 ∨ b=a+1) ∧ G ≅ K_{a,b}`, sidestepping which of `a,b` is `⌈n/2⌉` vs
`⌊n/2⌋` — mathematically the same content as the labelled form (the two are equal up to
`Sum.swap`), and this form needs no extra `completeBipartiteGraph`-symmetry lemma. -/
theorem stmt6_ms_eq_iso (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeSet.ncard = (Fintype.card V) ^ 2 / 4 ↔
      ∃ a b : ℕ, a + b = Fintype.card V ∧ (a = b ∨ a = b + 1 ∨ b = a + 1) ∧
        Nonempty (G ≃g completeBipartiteGraph (Fin a) (Fin b)) := by
  rw [stmt6_ms_eq G hn hG]
  constructor
  · rintro ⟨hBal, hconn⟩
    classical
    haveI : DecidableRel G.Adj := Classical.decRel _
    obtain ⟨same, part, hequiv, hbip, hbal1, hbal2, -⟩ := hBal
    have hsame : ∀ x y : V, same x y := fun x y => same_of_reachable hbip hequiv (hconn x y)
    have hbip' : ∀ x y : V, G.Adj x y ↔ part x ≠ part y := by
      intro x y; rw [hbip x y]; simp [hsame x y]
    set X : Finset V := Finset.univ.filter (fun a => part a = true) with hXdef
    set Y : Finset V := Finset.univ.filter (fun a => part a = false) with hYdef
    have hmemX : ∀ a, a ∈ X ↔ part a = true := by intro a; simp [hXdef]
    have hmemY : ∀ a, a ∈ Y ↔ part a = false := by intro a; simp [hYdef]
    have hXY : X.card + Y.card = Fintype.card V := by
      rw [hXdef]
      have hYeq : Y = Finset.univ.filter (fun a : V => ¬ part a = true) := by
        ext a; rw [hmemY]
        constructor
        · intro h; simp [h]
        · intro h; simpa using h
      rw [hYeq]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (p := fun a => part a = true)
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a₀⟩ := (inferInstance : Nonempty V)
    have hbalX : X.card ≤ Y.card + 1 := by
      have h := hbal1 a₀
      have heqX : {b : V | same a₀ b ∧ part b = true} = (X : Set V) := by
        ext b; simp [hmemX, hsame a₀ b]
      have heqY : {b : V | same a₀ b ∧ part b = false} = (Y : Set V) := by
        ext b; simp [hmemY, hsame a₀ b]
      rw [heqX, heqY, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
      exact h
    have hbalY : Y.card ≤ X.card + 1 := by
      have h := hbal2 a₀
      have heqX : {b : V | same a₀ b ∧ part b = true} = (X : Set V) := by
        ext b; simp [hmemX, hsame a₀ b]
      have heqY : {b : V | same a₀ b ∧ part b = false} = (Y : Set V) := by
        ext b; simp [hmemY, hsame a₀ b]
      rw [heqX, heqY, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
      exact h
    have hXYc : ∀ v : V, v ∉ X ↔ v ∈ Y := by
      intro v; rw [hmemX, hmemY]; cases part v <;> simp
    set e1 : V ≃ X ⊕ Y :=
      (Equiv.sumCompl (fun v => v ∈ X)).symm.trans
        (Equiv.sumCongr (Equiv.refl X) (Equiv.subtypeEquivRight hXYc)) with he1def
    have he1_left : ∀ (v : V) (hv : v ∈ X), e1 v = Sum.inl ⟨v, hv⟩ := by
      intro v hv
      rw [he1def]
      simp [Equiv.sumCompl_symm_apply_of_pos hv]
    have he1_right : ∀ (v : V) (hv : v ∉ X), e1 v = Sum.inr ⟨v, (hXYc v).mp hv⟩ := by
      intro v hv
      rw [he1def]
      simp [Equiv.sumCompl_symm_apply_of_neg hv, Equiv.subtypeEquivRight_apply]
    have hiso : G ≃g completeBipartiteGraph X Y := by
      refine ⟨e1, ?_⟩
      intro a b
      rw [hbip' a b]
      by_cases ha : a ∈ X <;> by_cases hb : b ∈ X
      · rw [he1_left a ha, he1_left b hb]
        have hpa : part a = true := (hmemX a).mp ha
        have hpb : part b = true := (hmemX b).mp hb
        simp [completeBipartiteGraph_adj, hpa, hpb]
      · rw [he1_left a ha, he1_right b hb]
        have hpa : part a = true := (hmemX a).mp ha
        have hpb : part b = false := (hmemY b).mp ((hXYc b).mp hb)
        simp [completeBipartiteGraph_adj, hpa, hpb]
      · rw [he1_right a ha, he1_left b hb]
        have hpa : part a = false := (hmemY a).mp ((hXYc a).mp ha)
        have hpb : part b = true := (hmemX b).mp hb
        simp [completeBipartiteGraph_adj, hpa, hpb]
      · rw [he1_right a ha, he1_right b hb]
        have hpa : part a = false := (hmemY a).mp ((hXYc a).mp ha)
        have hpb : part b = false := (hmemY b).mp ((hXYc b).mp hb)
        simp [completeBipartiteGraph_adj, hpa, hpb]
    refine ⟨Fintype.card X, Fintype.card Y, ?_, ?_,
      ⟨hiso.trans (SimpleGraph.completeBipartiteGraphCongr
        (Fintype.equivFin X) (Fintype.equivFin Y))⟩⟩
    · rw [Fintype.card_coe, Fintype.card_coe]; exact hXY
    · rw [Fintype.card_coe, Fintype.card_coe]; omega
  · rintro ⟨a, b, hab, htri, ⟨φ⟩⟩
    have ha1 : 1 ≤ a := by rcases htri with h | h | h <;> omega
    have hb1 : 1 ≤ b := by rcases htri with h | h | h <;> omega
    have hL : {c : Fin a ⊕ Fin b | True ∧ c.isLeft = true}.ncard = a := by
      have hset : {c : Fin a ⊕ Fin b | True ∧ c.isLeft = true} =
          Set.range (Sum.inl : Fin a → Fin a ⊕ Fin b) := by
        ext c; rcases c with c | c <;> simp
      rw [hset, Set.ncard_range_of_injective Sum.inl_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hR : {c : Fin a ⊕ Fin b | True ∧ c.isLeft = false}.ncard = b := by
      have hset : {c : Fin a ⊕ Fin b | True ∧ c.isLeft = false} =
          Set.range (Sum.inr : Fin b → Fin a ⊕ Fin b) := by
        ext c; rcases c with c | c <;> simp
      rw [hset, Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hCB : IsBalCBUnion (completeBipartiteGraph (Fin a) (Fin b)) := by
      classical
      refine ⟨fun _ _ => True, fun x => x.isLeft,
        ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩, ?_, ?_, ?_, ?_⟩
      · intro x y
        rcases x with x | x <;> rcases y with y | y <;> simp [completeBipartiteGraph_adj]
      · intro x
        show {c : Fin a ⊕ Fin b | True ∧ c.isLeft = true}.ncard ≤
          {c : Fin a ⊕ Fin b | True ∧ c.isLeft = false}.ncard + 1
        rw [hL, hR]; omega
      · intro x
        show {c : Fin a ⊕ Fin b | True ∧ c.isLeft = false}.ncard ≤
          {c : Fin a ⊕ Fin b | True ∧ c.isLeft = true}.ncard + 1
        rw [hL, hR]; omega
      · intro x y _ _; trivial
    have hKconn : (completeBipartiteGraph (Fin a) (Fin b)).Preconnected := by
      intro x y
      rcases x with x | x <;> rcases y with y | y
      · obtain ⟨r⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (Fin b) by
          rw [Fintype.card_fin]; omega)
        have h1 : (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inl x) (Sum.inr r) := by
          simp [completeBipartiteGraph_adj]
        have h2 : (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inl y) (Sum.inr r) := by
          simp [completeBipartiteGraph_adj]
        exact h1.reachable.trans h2.symm.reachable
      · exact (show (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inl x) (Sum.inr y) by
          simp [completeBipartiteGraph_adj]).reachable
      · exact (show (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inr x) (Sum.inl y) by
          simp [completeBipartiteGraph_adj]).reachable
      · obtain ⟨l⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (Fin a) by
          rw [Fintype.card_fin]; omega)
        have h1 : (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inr x) (Sum.inl l) := by
          simp [completeBipartiteGraph_adj]
        have h2 : (completeBipartiteGraph (Fin a) (Fin b)).Adj (Sum.inr y) (Sum.inl l) := by
          simp [completeBipartiteGraph_adj]
        exact h1.reachable.trans h2.symm.reachable
    exact ⟨hCB.map_iso φ, (SimpleGraph.Iso.preconnected_iff φ).mpr hKconn⟩

/-- ★★★ **`stmt6_ms_eq_iso_labelled`** — the equality characterization, fully labelled:
`e(G) = ⌊n²/4⌋ ↔ G ≅ K_{⌈n/2⌉,⌊n/2⌋}`, `⌈n/2⌉ := (n+1)/2`, `⌊n/2⌋ := n/2` (both Nat division).
Derived from `stmt6_ms_eq_iso`'s existential form by the WLOG arithmetic described above. -/
theorem stmt6_ms_eq_iso_labelled (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeSet.ncard = (Fintype.card V) ^ 2 / 4 ↔
      Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
        (Fin (Fintype.card V / 2))) := by
  rw [stmt6_ms_eq_iso G hn hG]
  set n := Fintype.card V with hndef
  constructor
  · rintro ⟨a, b, hab, htri, ⟨φ⟩⟩
    rcases htri with h | h | h
    · have hac : a = (n + 1) / 2 := by omega
      have hbc : b = n / 2 := by omega
      subst hac; subst hbc; exact ⟨φ⟩
    · have hac : a = (n + 1) / 2 := by omega
      have hbc : b = n / 2 := by omega
      subst hac; subst hbc; exact ⟨φ⟩
    · have hbc : a = n / 2 := by omega
      have hac : b = (n + 1) / 2 := by omega
      subst hbc; subst hac
      exact ⟨φ.trans (completeBipartiteGraph_swap (Fin (n / 2)) (Fin ((n + 1) / 2)))⟩
  · rintro ⟨φ⟩
    exact ⟨(n + 1) / 2, n / 2, by omega, by omega, ⟨φ⟩⟩

end Equality

end Campaign
end Erdos742
