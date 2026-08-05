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
