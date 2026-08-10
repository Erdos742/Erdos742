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
