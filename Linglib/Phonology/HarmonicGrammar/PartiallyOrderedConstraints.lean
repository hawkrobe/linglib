import Linglib.Phonology.HarmonicGrammar.Cumulativity
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.OptimalityTheory.Antimatroid
import Linglib.Phonology.OptimalityTheory.Grammar
import Linglib.Core.Optimization.PermSubsetCombinatorics
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Preorder.Finite

/-!
# Partially Ordered Constraints (POC)

A POC grammar is a partial order on the constraint set ([anttila-1997];
[kiparsky-1993b]). Each evaluation samples a total order consistent with the
partial order — a linear extension — and the OT optimum under that ranking is
the output, so a single grammar induces a distribution over outputs, uniform
over consistent linear extensions. The load-bearing identities are
division-free cardinality equations (`sum_card_filter_picksAt` here, the
head-fiber counting in `Core.Optimization.PermSubsetCombinatorics`);
`pocPredict` and its rate theorems are a ℚ veneer over them.

## Main definitions

- `PartialOrderConstraints n`: a decidable partial order on `Fin n` constraint
  indices, with constructors `discrete` (no rankings), `fromPermutation` (a
  total order), and `stratified` (mutually-ranked strata refined by an inner
  order — [tesar-smolensky-1995]'s Stratified Domination Hierarchies).
- `IsConsistent p σ` / `consistentTotalOrders p`: the linear extensions of
  `p`, a nonempty (Szpilrajn) decidable `Finset`.
- `pocPredict cands vp p i o`: the probability that sampling under `p` selects
  output `o` for input `i` — a genuine distribution (`pocPredict_nonneg`,
  `pocPredict_le_one`, `sum_pocPredict_eq_one`).
- `active vp i o o'` / `favoring vp i o o'`: the constraints distinguishing a
  candidate pair, and those preferring `o`.

## Main statements

- `consistentTotalOrders_eq_linearExtensions`: POC's linear extensions are the
  ERC ones — the simple-ERC (Hasse-edge) encoding `toERCSet` identifies
  `consistentTotalOrders` with `ERCSet.linearExtensions`
  ([merchant-riggle-2016]; [prince-2002]). `toGrammar` routes POC through the
  `Grammar` hub, and `pocAntimatroid` realizes the Birkhoff correspondence
  with order-ideal antimatroids ([dilworth-1940]).
- `stratified_rel_iff_lex`: the stratified order is mathlib's lexicographic
  sigma order (`Sigma.Lex`, underlying `Sigma.Lex.partialOrder`) transported
  along the fiber partition of the stratum map — strata as an ordinal sum,
  not a re-stipulation.
- `isOTRealizable_iff_isPOCRealizable`: categorically, POC adds nothing over
  OT. Its advantage is probabilistic — `pocPredict` produces intermediate
  frequencies (e.g. [coetzee-pater-2011]'s 8/24 vs 12/24 t/d-deletion rates)
  that no single ranking reproduces.
- `pocPredict_discrete_binary_rate` / `pocPredict_stratified_binary_rate`:
  closed-form win rates for binary competitions. A ranking is decided by its
  earliest active constraint (`picksAt_binary_iff_head_mem_favoring`), so
  `chosen` wins at rate `|favoring ∩ active| / |active|` — restricted to the
  deciding stratum in the stratified case — with no enumeration of rankings.
-/

namespace HarmonicGrammar

open Core.Optimization OptimalityTheory Finset

/-! ### PartialOrderConstraints -/

/-- A partial order on `Fin n` constraint indices. The OT case is a total
    order; the POC case allows incomparable pairs (multiple consistent
    linear extensions). -/
structure PartialOrderConstraints (n : ℕ) where
  /-- The partial-order relation: `rel a b` reads "a is ranked at-most-as-low-as
      b", i.e., a takes priority over b (or they're equal). -/
  rel : Fin n → Fin n → Prop
  /-- Decidability of the relation (required for `consistentTotalOrders` to
      be a computable `Finset`). -/
  [decidableRel : DecidableRel rel]
  /-- `rel` is a partial order — reflexive, transitive, antisymmetric — bundled
      as mathlib's `IsPartialOrder` instance instead of three loose proof
      fields, so the order-relation API (`antisymm_of`, …) applies to it. -/
  [isPartialOrder : IsPartialOrder (Fin n) rel]

attribute [instance] PartialOrderConstraints.decidableRel
  PartialOrderConstraints.isPartialOrder

namespace PartialOrderConstraints

variable {n : ℕ}

/-- The discrete partial order on `Fin n`, relating `a` to `b` iff `a = b`.
    Every permutation is a consistent linear extension — [anttila-1997]'s
    "no ranking imposed" baseline. -/
def discrete (n : ℕ) : PartialOrderConstraints n where
  rel := Eq
  isPartialOrder :=
    { refl := fun _ => rfl
      trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
      antisymm := fun _ _ h _ => h }

/-- The total order induced by a permutation `σ`: `rel a b` iff
    `σ.symm a ≤ σ.symm b` (i.e., a appears at least as early as b in σ's
    enumeration). This is a total order; its unique consistent linear
    extension is σ itself (`fromPermutation_consistent_unique` below). -/
def fromPermutation (σ : Ranking n) : PartialOrderConstraints n where
  rel := fun a b => σ.symm a ≤ σ.symm b
  isPartialOrder :=
    { refl := fun _ => le_refl _
      trans := fun _ _ _ h₁ h₂ => le_trans h₁ h₂
      antisymm := fun _ _ h₁ h₂ => σ.symm.injective (le_antisymm h₁ h₂) }

/-- A permutation σ is **consistent** with the partial order p if whenever
    `rel a b` holds, σ ranks a at least as early as b
    (`σ.symm a ≤ σ.symm b`) — that is, σ is a linear extension of p. -/
def IsConsistent (p : PartialOrderConstraints n) (σ : Ranking n) :
    Prop :=
  ∀ a b, p.rel a b → σ.symm a ≤ σ.symm b

instance (p : PartialOrderConstraints n) (σ : Ranking n) :
    Decidable (p.IsConsistent σ) := by
  unfold IsConsistent; infer_instance

/-- The (decidable, finite) set of linear extensions of `p`. -/
def consistentTotalOrders (p : PartialOrderConstraints n) :
    Finset (Ranking n) :=
  Finset.univ.filter p.IsConsistent

@[simp]
theorem mem_consistentTotalOrders {p : PartialOrderConstraints n}
    {σ : Ranking n} :
    σ ∈ p.consistentTotalOrders ↔ p.IsConsistent σ := by
  simp [consistentTotalOrders]

/-! ### Grounding in the ERC lex API

A partial order is a set of dominance requirements — each strict related pair
is a simple ERC `a ≫ b` ([merchant-riggle-2016]), and under this encoding the
consistent total orders are exactly `ERCSet.linearExtensions` ([prince-2002]). -/

/-- The simple-ERC encoding of a partial order, with one ERC `a ≫ b`
(`simpleERC a b`) for each strict related pair. Transitively-implied pairs are
entailed by the covering pairs, so the encoding has the same linear extensions
as the Hasse-edge one. -/
def toERCSet (p : PartialOrderConstraints n) : ERCSet n :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).filterMap fun b =>
      if a ≠ b ∧ p.rel a b then some (simpleERC a b) else none

theorem mem_toERCSet {p : PartialOrderConstraints n} {α : ERC n} :
    α ∈ p.toERCSet ↔ ∃ a b, a ≠ b ∧ p.rel a b ∧ simpleERC a b = α := by
  simp only [toERCSet, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, b, hif⟩
    split_ifs at hif with hc
    exact ⟨a, b, hc.1, hc.2, Option.some.inj hif⟩
  · rintro ⟨a, b, hab, hrel, rfl⟩
    exact ⟨a, b, by rw [if_pos ⟨hab, hrel⟩]⟩

/-- A ranking satisfies `p.toERCSet` exactly when it is a linear extension of `p`:
the `a ≫ b` ERCs are the strict dominance requirements, and reflexive pairs impose
nothing. -/
theorem satisfiedBy_toERCSet {p : PartialOrderConstraints n} {σ : Ranking n} :
    ERCSet.SatisfiedBy σ p.toERCSet ↔ p.IsConsistent σ := by
  constructor
  · intro h a b hrel
    rcases eq_or_ne a b with rfl | hab
    · exact le_refl _
    · exact le_of_lt ((simpleERC_satisfiedBy_iff hab σ).mp
        (h _ (mem_toERCSet.mpr ⟨a, b, hab, hrel, rfl⟩)))
  · intro hcons α hα
    obtain ⟨a, b, hab, hrel, rfl⟩ := mem_toERCSet.mp hα
    exact (simpleERC_satisfiedBy_iff hab σ).mpr
      (lt_of_le_of_ne (hcons a b hrel) (fun heq => hab (σ.symm.injective heq)))

/-- The consistent total orders of a partial order are exactly the linear
extensions of its simple-ERC encoding ([merchant-riggle-2016];
[prince-2002]). -/
theorem consistentTotalOrders_eq_linearExtensions (p : PartialOrderConstraints n) :
    p.consistentTotalOrders = p.toERCSet.linearExtensions := by
  ext σ
  rw [mem_consistentTotalOrders, ERCSet.mem_linearExtensions, satisfiedBy_toERCSet]

/-- For the discrete partial order, every permutation is a linear extension. -/
theorem consistentTotalOrders_discrete (n : ℕ) :
    (discrete n).consistentTotalOrders = Finset.univ := by
  ext σ
  simp [consistentTotalOrders, IsConsistent, discrete]

/-- σ is consistent with the partial order it induces. -/
theorem isConsistent_fromPermutation (σ : Ranking n) :
    (fromPermutation σ).IsConsistent σ := by
  intro a b h
  exact h

/-- The σ-induced total order has σ as a consistent linear extension. -/
theorem mem_consistentTotalOrders_fromPermutation (σ : Ranking n) :
    σ ∈ (fromPermutation σ).consistentTotalOrders :=
  mem_consistentTotalOrders.mpr (isConsistent_fromPermutation σ)

/-- The σ-induced total order has σ as its *unique* consistent linear
    extension. -/
theorem fromPermutation_consistent_unique {σ τ : Ranking n}
    (hτ : (fromPermutation σ).IsConsistent τ) : τ = σ := by
  have hmono : Monotone (⇑τ.symm ∘ ⇑σ) := by
    intro a b hab
    have hrel : (fromPermutation σ).rel (σ a) (σ b) := by
      show σ.symm (σ a) ≤ σ.symm (σ b)
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hab
    exact hτ (σ a) (σ b) hrel
  have hcomp : ⇑τ.symm ∘ ⇑σ = id :=
    (hmono.strictMono_of_injective (τ.symm.injective.comp σ.injective)).eq_id
  apply Equiv.ext
  intro k
  have hk : τ.symm (σ k) = k := congr_fun hcomp k
  calc τ k = τ (τ.symm (σ k)) := by rw [hk]
    _ = σ k := τ.apply_symm_apply (σ k)

@[simp]
theorem consistentTotalOrders_fromPermutation (σ : Ranking n) :
    (fromPermutation σ).consistentTotalOrders = {σ} := by
  ext τ
  rw [mem_consistentTotalOrders, Finset.mem_singleton]
  refine ⟨fromPermutation_consistent_unique, fun hτ => ?_⟩
  rw [hτ]
  exact isConsistent_fromPermutation σ

/-! ### Stratified partial orders

Earlier strata dominate later ones wholesale, and within a stratum an inner
order applies. With the discrete inner order this is the freely-ranked stratum
grammar of [anttila-1997] eq. (50) — the Stratified Domination Hierarchy of
[tesar-smolensky-1995] that constraint-demotion learning produces. -/

variable {s : ℕ}

/-- The stratified partial order induced by `stratumOf` and an inner order
`inner`: `rel a b` iff a's stratum strictly precedes b's, or they share a
stratum and `inner.rel a b`. Cross-stratum `inner` edges are ignored. -/
def stratified (stratumOf : Fin n → Fin s) (inner : PartialOrderConstraints n) :
    PartialOrderConstraints n where
  rel a b := stratumOf a < stratumOf b ∨ (stratumOf a = stratumOf b ∧ inner.rel a b)
  isPartialOrder :=
    { refl := fun a => Or.inr ⟨rfl, refl_of inner.rel a⟩
      trans := fun a b c hab hbc => by
        rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
        · exact Or.inl (hab.trans hbc)
        · exact Or.inl (lt_of_lt_of_eq hab hbc)
        · exact Or.inl (lt_of_eq_of_lt hab hbc)
        · exact Or.inr ⟨hab.trans hbc, trans_of inner.rel hab' hbc'⟩
      antisymm := fun a b hab hba => by
        rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hba with hba | ⟨hba, hba'⟩
        · exact absurd (hab.trans hba) (lt_irrefl _)
        · exact absurd (lt_of_lt_of_eq hab hba) (lt_irrefl _)
        · exact absurd (lt_of_lt_of_eq hba hab) (lt_irrefl _)
        · exact antisymm_of inner.rel hab' hba' }

private theorem sigmaMk_stratum_eq {stratumOf : Fin n → Fin s} {a : Fin n} {k : Fin s}
    (h : stratumOf a = k) :
    (⟨stratumOf a, a, rfl⟩ : Σ k, {c : Fin n // stratumOf c = k}) = ⟨k, a, h⟩ := by
  subst h; rfl

/-- `stratified` is the lexicographic sigma order — the relation underlying
    mathlib's `Sigma.Lex.partialOrder` — transported along the fiber partition
    `Equiv.sigmaFiberEquiv stratumOf`: constraints compare by stratum first
    and by the inner order within a stratum. -/
theorem stratified_rel_iff_lex {stratumOf : Fin n → Fin s}
    {inner : PartialOrderConstraints n} {a b : Fin n} :
    (stratified stratumOf inner).rel a b ↔
      Sigma.Lex (· < ·) (fun k (x y : {c : Fin n // stratumOf c = k}) => inner.rel x.1 y.1)
        ⟨stratumOf a, a, rfl⟩ ⟨stratumOf b, b, rfl⟩ := by
  constructor
  · rintro (hlt | ⟨heq, hrel⟩)
    · exact Sigma.Lex.left _ _ hlt
    · rw [sigmaMk_stratum_eq heq]
      exact Sigma.Lex.right _ _ hrel
  · intro hlex
    rcases Sigma.lex_iff.mp hlex with hlt | ⟨heq, -⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [sigmaMk_stratum_eq heq] at hlex
      cases hlex with
      | left _ _ h => exact absurd h (lt_irrefl _)
      | right _ _ hr => exact hr

/-- Under a stratified order, an earlier-stratum constraint occupies a strictly
    earlier position in every consistent ranking. -/
theorem IsConsistent.symm_lt_of_stratum_lt {stratumOf : Fin n → Fin s}
    {inner : PartialOrderConstraints n} {σ : Ranking n}
    (hσ : (stratified stratumOf inner).IsConsistent σ) {a b : Fin n}
    (h : stratumOf a < stratumOf b) : σ.symm a < σ.symm b :=
  lt_of_le_of_ne (hσ a b (Or.inl h))
    (fun heq => absurd (σ.symm.injective heq ▸ h) (lt_irrefl _))

/-- Consistent rankings of a stratified order are closed under swapping two
    constraints of a stratum on which the inner order is trivial. -/
theorem isConsistent_swap_mul {stratumOf : Fin n → Fin s}
    {inner : PartialOrderConstraints n} {k : Fin s}
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner.rel a b → a = b)
    {d d' : Fin n} (hd : stratumOf d = k) (hd' : stratumOf d' = k)
    {σ : Ranking n} (hσ : (stratified stratumOf inner).IsConsistent σ) :
    (stratified stratumOf inner).IsConsistent (Equiv.swap d d' * σ) := by
  have h_str : ∀ x, stratumOf (Equiv.swap d d' x) = stratumOf x := by
    intro x
    rcases eq_or_ne x d with rfl | hxd
    · rw [Equiv.swap_apply_left, hd', hd]
    rcases eq_or_ne x d' with rfl | hxd'
    · rw [Equiv.swap_apply_right, hd, hd']
    · rw [Equiv.swap_apply_of_ne_of_ne hxd hxd']
  intro a b hab
  have h_symm : ∀ x, (Equiv.swap d d' * σ).symm x = σ.symm (Equiv.swap d d' x) := by
    intro x
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [h_symm a, h_symm b]
  rcases hab with hlt | ⟨heq, hinner⟩
  · exact hσ _ _ (Or.inl (by rw [h_str a, h_str b]; exact hlt))
  · rcases eq_or_ne (stratumOf a) k with hk | hk
    · obtain rfl : a = b := h_triv a b hk (heq ▸ hk) hinner
      exact le_refl _
    · have ha : Equiv.swap d d' a = a :=
        Equiv.swap_apply_of_ne_of_ne (fun h => hk (by rw [h]; exact hd))
          (fun h => hk (by rw [h]; exact hd'))
      have hb : Equiv.swap d d' b = b :=
        Equiv.swap_apply_of_ne_of_ne (fun h => (heq ▸ hk) (by rw [h]; exact hd))
          (fun h => (heq ▸ hk) (by rw [h]; exact hd'))
      rw [ha, hb]
      exact hσ a b (Or.inr ⟨heq, hinner⟩)

/-- Opaque carrier for the extended linear order, so that the extension can be
    installed as a `LinearOrder` instance without clashing with `Fin n`'s
    standard order. -/
private structure LinExtCarrier (n : ℕ) where ofFin ::
  /-- The underlying index. -/
  toFin : Fin n

/-- Every partial order has a consistent linear extension (Szpilrajn, via
    mathlib's `extend_partialOrder`). -/
theorem consistentTotalOrders_nonempty (p : PartialOrderConstraints n) :
    p.consistentTotalOrders.Nonempty := by
  classical
  -- Szpilrajn: extend the partial order `p.rel` to a linear order `s`.
  obtain ⟨s, hs_lin, hsub⟩ := extend_partialOrder p.rel
  -- Equip the opaque carrier with `s`, then sort it against `Fin n`'s order.
  let wEquiv : LinExtCarrier n ≃ Fin n :=
    { toFun := LinExtCarrier.toFin, invFun := LinExtCarrier.ofFin,
      left_inv := fun ⟨_⟩ => rfl, right_inv := fun _ => rfl }
  let : Fintype (LinExtCarrier n) := Fintype.ofEquiv (Fin n) wEquiv.symm
  let : LinearOrder (LinExtCarrier n) :=
    { le := fun a b => s a.toFin b.toFin
      le_refl := fun a => hs_lin.refl a.toFin
      le_trans := fun a b c => hs_lin.trans a.toFin b.toFin c.toFin
      le_antisymm := fun a b h₁ h₂ => by
        have := hs_lin.antisymm a.toFin b.toFin h₁ h₂
        cases a; cases b; simpa using this
      le_total := fun a b => hs_lin.total a.toFin b.toFin
      toDecidableLE := Classical.decRel _ }
  have hcard : Fintype.card (LinExtCarrier n) = n := by
    rw [Fintype.card_congr wEquiv]; simp
  -- The order iso `Fin n ≃o LinExtCarrier n` enumerates the carrier in `s`-order;
  -- composing with `wEquiv` yields the consistent permutation.
  let e : Fin n ≃o LinExtCarrier n := Fintype.orderIsoFinOfCardEq (LinExtCarrier n) hcard
  refine ⟨e.toEquiv.trans wEquiv, mem_consistentTotalOrders.mpr ?_⟩
  intro a b hab
  show ((e.toEquiv.trans wEquiv).symm a : Fin n) ≤ (e.toEquiv.trans wEquiv).symm b
  have key : ∀ c : Fin n, (e.toEquiv.trans wEquiv).symm c = e.symm (LinExtCarrier.ofFin c) :=
    fun _ => rfl
  rw [key a, key b]
  exact e.symm.monotone (show s (LinExtCarrier.ofFin a).toFin (LinExtCarrier.ofFin b).toFin from
    hsub a b hab)

theorem consistentTotalOrders_card_pos (p : PartialOrderConstraints n) :
    0 < p.consistentTotalOrders.card :=
  p.consistentTotalOrders_nonempty.card_pos

/-! ### The order-ideal antimatroid of a POC

A partial order's Hasse-edge encoding is a consistent set of simple ERCs, so it
has a Birkhoff antimatroid whose feasible sets are exactly the order ideals of
`p` ([dilworth-1940]; [merchant-riggle-2016]). -/

/-- `p.toERCSet` consists of simple ERCs (each is a `simpleERC` of a strict pair). -/
theorem toERCSet_isSimpleSet (p : PartialOrderConstraints n) :
    ERCSet.IsSimpleSet p.toERCSet := by
  intro α hα
  obtain ⟨a, b, hab, _, rfl⟩ := mem_toERCSet.mp hα
  exact simpleERC_isSimple hab

/-- `p.toERCSet` is consistent: any linear extension of `p` satisfies it. -/
theorem toERCSet_consistent (p : PartialOrderConstraints n) :
    ERCSet.Consistent p.toERCSet := by
  obtain ⟨σ, hσ⟩ := p.consistentTotalOrders_nonempty
  exact ⟨σ, satisfiedBy_toERCSet.mpr (mem_consistentTotalOrders.mp hσ)⟩

/-- The **order-ideal antimatroid** of a partial order — the simple-ERC
Birkhoff antimatroid (`Antimat.ofSimple`) of its Hasse-edge encoding, whose
feasible sets are exactly the order ideals of `p`
(`pocAntimatroid_isFeasible_iff`). -/
def pocAntimatroid (p : PartialOrderConstraints n) : Antimatroid (Fin n) :=
  Antimat.ofSimple p.toERCSet p.toERCSet_consistent p.toERCSet_isSimpleSet

/-- Local feasibility against `p.toERCSet` is exactly the order-ideal
condition — whenever `b ∈ S` and `a` dominates `b`, also `a ∈ S`. -/
theorem feasible_toERCSet_iff {p : PartialOrderConstraints n} {S : Finset (Fin n)} :
    Feasible p.toERCSet S ↔ ∀ a b, p.rel a b → b ∈ S → a ∈ S := by
  constructor
  · intro h a b hrel hbS
    rcases eq_or_ne a b with rfl | hab
    · exact hbS
    · obtain ⟨w, hwW, hwS⟩ :=
        h (simpleERC a b) (mem_toERCSet.mpr ⟨a, b, hab, hrel, rfl⟩)
          ⟨b, simpleERC_apply_L hab, hbS⟩
      rwa [(simpleERC_eq_W_iff w).mp hwW] at hwS
  · intro h α hα
    obtain ⟨a, b, hab, hrel, rfl⟩ := mem_toERCSet.mp hα
    rintro ⟨l, hlL, hlS⟩
    rw [(simpleERC_eq_L_iff hab l).mp hlL] at hlS
    exact ⟨a, simpleERC_apply_W, h a b hrel hlS⟩

/-- The feasible sets of `pocAntimatroid` are the order ideals of `p` — the
Birkhoff correspondence, made concrete and decidable. -/
@[simp] theorem pocAntimatroid_isFeasible_iff {p : PartialOrderConstraints n}
    {S : Finset (Fin n)} :
    (p.pocAntimatroid).IsFeasible (↑S : Set (Fin n)) ↔
      ∀ a b, p.rel a b → b ∈ S → a ∈ S := by
  simp only [pocAntimatroid, ofSimple_isFeasible_coe, feasible_toERCSet_iff]

end PartialOrderConstraints

/-! ### POC Realizability of SystemicProblem -/

namespace SystemicProblem

variable {Input Output : Type*} {n : ℕ}

/-- A partial order p **POC-realizes** the target if every consistent
    extension realizes it. Since consistent extensions always exist
    (`consistentTotalOrders_nonempty`), this is never vacuous. -/
def realizedByPOC (P : SystemicProblem Input Output n)
    (p : PartialOrderConstraints n) : Prop :=
  ∀ σ ∈ p.consistentTotalOrders, P.realizedByRanking σ

/-- A `SystemicProblem` is **POC-realizable** if some partial order
    categorically realizes the target. -/
def IsPOCRealizable (P : SystemicProblem Input Output n) : Prop :=
  ∃ p : PartialOrderConstraints n, P.realizedByPOC p

end SystemicProblem

/-! ### Containments — OT ⊆ POC, POC ⊆ OT (categorical) -/

/-- Every POC-realized target is OT-realized, since any single consistent
    extension realizes it. -/
theorem poc_realizable_imp_ot_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsPOCRealizable → P.IsOTRealizable := by
  rintro ⟨p, hreal⟩
  obtain ⟨σ, hσ⟩ := p.consistentTotalOrders_nonempty
  exact ⟨σ, hreal σ hσ⟩

/-- Every OT-realized target is POC-realized — the witness is the σ-induced
    total order, whose unique consistent extension is σ itself. -/
theorem ot_realizable_imp_poc_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable → P.IsPOCRealizable := by
  rintro ⟨σ, hσ⟩
  refine ⟨PartialOrderConstraints.fromPermutation σ, ?_⟩
  simpa [SystemicProblem.realizedByPOC,
    PartialOrderConstraints.consistentTotalOrders_fromPermutation] using hσ

/-- Under categorical realizability, OT-realizable and POC-realizable
    coincide. POC's advantage over OT is probabilistic, captured by
    `pocPredict`. -/
theorem isOTRealizable_iff_isPOCRealizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable ↔ P.IsPOCRealizable :=
  ⟨ot_realizable_imp_poc_realizable P,
   poc_realizable_imp_ot_realizable P⟩

/-! ### Probabilistic POC — pocPredict -/

namespace PartialOrderConstraints

variable {Input Output : Type*} {n : ℕ}

/-- The constraints **active** on the candidate pair `o, o'` at input `i` —
    those assigning the two candidates different violation counts
    ([anttila-1997]'s decisive constraints). Inactive constraints cannot
    affect the competition. -/
def active (vp : Input → Output → Fin n → ℕ) (i : Input) (o o' : Output) :
    Finset (Fin n) :=
  Finset.univ.filter fun c => vp i o c ≠ vp i o' c

/-- The constraints **favoring** `o` over `o'` at input `i` — those assigning
    `o` strictly fewer violations. -/
def favoring (vp : Input → Output → Fin n → ℕ) (i : Input) (o o' : Output) :
    Finset (Fin n) :=
  Finset.univ.filter fun c => vp i o c < vp i o' c

@[simp] theorem mem_active {vp : Input → Output → Fin n → ℕ} {i : Input}
    {o o' : Output} {c : Fin n} :
    c ∈ active vp i o o' ↔ vp i o c ≠ vp i o' c := by
  simp [active]

@[simp] theorem mem_favoring {vp : Input → Output → Fin n → ℕ} {i : Input}
    {o o' : Output} {c : Fin n} :
    c ∈ favoring vp i o o' ↔ vp i o c < vp i o' c := by
  simp [favoring]

theorem favoring_subset_active (vp : Input → Output → Fin n → ℕ) (i : Input)
    (o o' : Output) : favoring vp i o o' ⊆ active vp i o o' :=
  fun _ hc => mem_active.mpr (Nat.ne_of_lt (mem_favoring.mp hc))

/-- σ **picks** output o for input i if o is the unique strict OT winner —
    every other in-set candidate is lex-strictly worse than o under σ. -/
def PicksAt (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Ranking n) (i : Input) (o : Output) : Prop :=
  o ∈ cands i ∧
  ∀ o' ∈ cands i, o' ≠ o →
    toLex (fun k : Fin n => vp i o (σ k)) <
    toLex (fun k : Fin n => vp i o' (σ k))

/-- A ranking picks at most one output, since strict lex domination is
    asymmetric. -/
theorem picksAt_unique {cands : Input → Finset Output}
    {vp : Input → Output → Fin n → ℕ} {σ : Ranking n} {i : Input} {o o' : Output}
    (h : PicksAt cands vp σ i o) (h' : PicksAt cands vp σ i o') : o = o' := by
  by_contra hne
  exact absurd (h'.2 o h.1 hne) (lt_asymm (h.2 o' h'.1 fun heq => hne heq.symm))

/-- With pairwise-distinct violation profiles, every ranking picks some
    output — the candidate with the lex-minimal permuted profile wins
    strictly. -/
theorem exists_picksAt (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) {i : Input}
    (h_ne : (cands i).Nonempty)
    (h_inj : ∀ o ∈ cands i, ∀ o' ∈ cands i, vp i o = vp i o' → o = o')
    (σ : Ranking n) : ∃ o ∈ cands i, PicksAt cands vp σ i o := by
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (cands i)
    (fun o => toLex (fun j : Fin n => vp i o (σ j))) h_ne
  refine ⟨m, hm, hm, fun o' ho' hne' => lt_of_le_of_ne (hmin o' ho') fun heq => hne' ?_⟩
  have h_fun : (fun j : Fin n => vp i m (σ j)) = fun j => vp i o' (σ j) := toLex_inj.mp heq
  refine h_inj o' ho' m hm (funext fun c => ?_)
  have := congrFun h_fun (σ.symm c)
  simpa using this.symm

variable [DecidableEq Output]

instance (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Ranking n) (i : Input) (o : Output) :
    Decidable (PicksAt cands vp σ i o) := by
  unfold PicksAt; infer_instance

/-- The probability that sampling under partial order p selects output o for
    input i — the fraction of consistent extensions picking o. The denominator
    is positive (`consistentTotalOrders_card_pos`), so this is a genuine
    probability. -/
def pocPredict (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (p : PartialOrderConstraints n) (i : Input) (o : Output) : ℚ :=
  ((p.consistentTotalOrders.filter
    (fun σ => PicksAt cands vp σ i o)).card : ℚ) /
  (p.consistentTotalOrders.card : ℚ)

/-- For the σ-induced total order, `pocPredict` collapses to a point mass —
    probability 1 if σ picks o and 0 otherwise. -/
theorem pocPredict_fromPermutation
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Ranking n) (i : Input) (o : Output) :
    pocPredict cands vp (fromPermutation σ) i o =
    if PicksAt cands vp σ i o then 1 else 0 := by
  simp only [pocPredict,
    consistentTotalOrders_fromPermutation,
    Finset.card_singleton, Nat.cast_one, div_one, Finset.filter_singleton]
  by_cases h : PicksAt cands vp σ i o
  · simp [if_pos h]
  · simp [if_neg h]

/-- Under the discrete order, `pocPredict` is the fraction of all `n!`
    rankings picking o. -/
theorem pocPredict_discrete
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (o : Output) :
    pocPredict cands vp (discrete n) i o =
    ((Finset.univ.filter
      (fun σ : Ranking n => PicksAt cands vp σ i o)).card : ℚ) /
    (Finset.univ : Finset (Ranking n)).card := by
  simp only [pocPredict, consistentTotalOrders_discrete]

/-! #### `pocPredict` is a probability distribution -/

theorem pocPredict_nonneg (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) (p : PartialOrderConstraints n)
    (i : Input) (o : Output) : 0 ≤ pocPredict cands vp p i o :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem pocPredict_le_one (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) (p : PartialOrderConstraints n)
    (i : Input) (o : Output) : pocPredict cands vp p i o ≤ 1 := by
  unfold pocPredict
  rw [div_le_one (by exact_mod_cast p.consistentTotalOrders_card_pos)]
  exact_mod_cast Finset.card_filter_le _ _

/-- With pairwise-distinct violation profiles the picks-fibers over the
    candidate set partition the consistent extensions — the division-free core
    of `sum_pocPredict_eq_one`. -/
theorem sum_card_filter_picksAt (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) (p : PartialOrderConstraints n) {i : Input}
    (h_ne : (cands i).Nonempty)
    (h_inj : ∀ o ∈ cands i, ∀ o' ∈ cands i, vp i o = vp i o' → o = o') :
    ∑ o ∈ cands i, (p.consistentTotalOrders.filter
      (fun σ => PicksAt cands vp σ i o)).card = p.consistentTotalOrders.card := by
  classical
  have h_disjoint : (↑(cands i) : Set Output).PairwiseDisjoint
      (fun o => p.consistentTotalOrders.filter (fun σ => PicksAt cands vp σ i o)) := by
    intro o _ o' _ hne'
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
    exact hne' (picksAt_unique h₁ h₂)
  have h_union : (cands i).biUnion (fun o => p.consistentTotalOrders.filter
      (fun σ => PicksAt cands vp σ i o)) = p.consistentTotalOrders := by
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨o, _, hσ, _⟩; exact hσ
    · intro hσ
      obtain ⟨o, ho, hpick⟩ := exists_picksAt cands vp h_ne h_inj σ
      exact ⟨o, ho, hσ, hpick⟩
  calc ∑ o ∈ cands i, (p.consistentTotalOrders.filter
        (fun σ => PicksAt cands vp σ i o)).card
      = ((cands i).biUnion (fun o => p.consistentTotalOrders.filter
          (fun σ => PicksAt cands vp σ i o))).card :=
        (Finset.card_biUnion h_disjoint).symm
    _ = p.consistentTotalOrders.card := by rw [h_union]

/-- Over a candidate set with pairwise-distinct violation profiles the win
    probabilities sum to 1, for any partial order — every consistent ranking
    picks exactly one winner. -/
theorem sum_pocPredict_eq_one (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) (p : PartialOrderConstraints n) {i : Input}
    (h_ne : (cands i).Nonempty)
    (h_inj : ∀ o ∈ cands i, ∀ o' ∈ cands i, vp i o = vp i o' → o = o') :
    ∑ o ∈ cands i, pocPredict cands vp p i o = 1 := by
  unfold pocPredict
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_card_filter_picksAt cands vp p h_ne h_inj]
  exact div_self (by exact_mod_cast p.consistentTotalOrders_card_pos.ne')

/-- Two distinct candidates with distinct violation profiles split the
    probability mass. -/
theorem pocPredict_binary_add_eq_one (cands : Input → Finset Output)
    (vp : Input → Output → Fin n → ℕ) (p : PartialOrderConstraints n) {i : Input}
    {o₁ o₂ : Output} (h_two : cands i = {o₁, o₂}) (h_ne : o₁ ≠ o₂)
    (h_vp : vp i o₁ ≠ vp i o₂) :
    pocPredict cands vp p i o₁ + pocPredict cands vp p i o₂ = 1 := by
  have h_inj : ∀ o ∈ cands i, ∀ o' ∈ cands i, vp i o = vp i o' → o = o' := by
    intro o ho o' ho' hvv
    rw [h_two, Finset.mem_insert, Finset.mem_singleton] at ho ho'
    rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl <;>
      first | rfl | exact absurd hvv h_vp | exact absurd hvv.symm h_vp
  have h := sum_pocPredict_eq_one cands vp p
    (by rw [h_two]; exact Finset.insert_nonempty _ _) h_inj
  rwa [h_two, Finset.sum_pair h_ne] at h

end PartialOrderConstraints

/-! ### Bridge — binary PicksAt is decided by the σ-earliest active constraint

For binary candidate sets `cands i = {chosen, other}`, `PicksAt σ i chosen`
reduces to lex domination of `chosen`'s permuted profile, which is decided at
the first position where the profiles differ — i.e., `chosen` wins iff the
σ-earliest constraint of `active vp i chosen other` lies in
`favoring vp i chosen other`. Combined with the head-fiber counting of
`Core.Optimization.PermSubsetCombinatorics`, this yields closed-form rates
for binary POC competitions without enumerating rankings. -/

namespace PartialOrderConstraints

open Core.Optimization.PermSubsetCombinatorics

variable {Input Output : Type*} [DecidableEq Output] {n : ℕ}

/-- For binary candidate sets, `PicksAt σ i chosen` holds exactly when the
    σ-earliest active constraint favors `chosen`. -/
theorem picksAt_binary_iff_head_mem_favoring
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other)
    (σ : Ranking n) :
    PicksAt cands vp σ i chosen ↔
    ∃ x ∈ favoring vp i chosen other,
      (permDList σ (active vp i chosen other)).head? = some x := by
  classical
  -- Binary candidates: `PicksAt` reduces to lex domination of `chosen` over `other`.
  have h_lex :
      PicksAt cands vp σ i chosen ↔
      ∃ k : Fin n, (∀ j, j < k → vp i chosen (σ j) = vp i other (σ j)) ∧
        vp i chosen (σ k) < vp i other (σ k) := by
    unfold PicksAt
    constructor
    · rintro ⟨_, h⟩
      exact h other
        (by rw [h_two]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
        (Ne.symm h_ne)
    · intro h
      refine ⟨by rw [h_two]; exact Finset.mem_insert_self _ _, ?_⟩
      intro o' h_o' h_o'_ne
      rw [h_two, Finset.mem_insert, Finset.mem_singleton] at h_o'
      rcases h_o' with h' | h'
      · exact absurd h' h_o'_ne
      · subst h'; exact h
  rw [h_lex]
  constructor
  · -- the first strict-difference position holds the σ-earliest active constraint
    rintro ⟨k, h_tie, h_lt⟩
    refine ⟨σ k, mem_favoring.mpr h_lt,
      (permDList_head?_eq_some_iff_min σ _ (σ k)).mpr
        ⟨mem_active.mpr (Nat.ne_of_lt h_lt), fun y hy => ?_⟩⟩
    rw [Equiv.symm_apply_apply]
    by_contra h
    exact mem_active.mp hy (by simpa using h_tie (σ.symm y) (lt_of_not_ge h))
  · -- the σ-earliest active constraint marks the first strict difference
    rintro ⟨x, hxF, hhead⟩
    obtain ⟨-, hmin⟩ := (permDList_head?_eq_some_iff_min σ _ x).mp hhead
    refine ⟨σ.symm x, fun j hj => ?_, by simpa using mem_favoring.mp hxF⟩
    by_contra h_ne'
    exact absurd (hmin (σ j) (mem_active.mpr h_ne')) (by simpa using not_le.mpr hj)

/-! ### Closed-form rate for binary candidates -/

/-- With binary candidates, the fraction of all `n!` rankings picking `chosen`
    is `|favoring ∩ active| / |active|` — each ranking is decided by its
    σ-earliest active constraint, and every active constraint is equally
    likely to come first. -/
theorem pocPredict_discrete_binary_rate
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other) :
    pocPredict cands vp (discrete n) i chosen =
      ((favoring vp i chosen other ∩ active vp i chosen other).card : ℚ) /
        ((active vp i chosen other).card : ℚ) := by
  rw [pocPredict_discrete, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Finset.filter_congr fun σ _ =>
      picksAt_binary_iff_head_mem_favoring cands vp i chosen other h_two h_ne σ]
  exact perm_filter_head_in_rate _ _

/-! ### Deciding-stratum rate for stratified grammars

A binary competition whose variants tie on every stratum before `k` is decided
within stratum `k`, with later strata — including any inner rankings among
them — provably irrelevant. This is [anttila-1997]'s tableau-count shortcut
stated against the full grammar rather than a per-stratum sub-grammar. -/

omit [DecidableEq Output] in
/-- On a consistent ranking of a stratified order, the σ-earliest active
    constraint lies in the deciding stratum: earlier strata are inactive
    (`h_tie`), and constraints of later strata come after all of stratum `k`. -/
private theorem permDList_head?_active_filter_stratum {s : ℕ}
    {stratumOf : Fin n → Fin s} {inner : PartialOrderConstraints n} {σ : Ranking n}
    (vp : Input → Output → Fin n → ℕ) {i : Input} {chosen other : Output} {k : Fin s}
    (hσ : (stratified stratumOf inner).IsConsistent σ)
    (h_tie : ∀ c, stratumOf c < k → vp i chosen c = vp i other c)
    (h_dec : ((active vp i chosen other).filter (stratumOf · = k)).Nonempty) :
    (permDList σ (active vp i chosen other)).head? =
      (permDList σ ((active vp i chosen other).filter (stratumOf · = k))).head? := by
  obtain ⟨x, hx_mem, hx⟩ := exists_permDList_head?_eq_some h_dec σ
  obtain ⟨hxD, hxk⟩ := Finset.mem_filter.mp hx_mem
  obtain ⟨-, hmin⟩ := (permDList_head?_eq_some_iff_min σ _ x).mp hx
  rw [hx]
  refine (permDList_head?_eq_some_iff_min σ _ x).mpr ⟨hxD, fun y hyD => ?_⟩
  rcases lt_trichotomy (stratumOf y) k with hlt | heq | hgt
  · exact absurd (h_tie y hlt) (mem_active.mp hyD)
  · exact hmin y (Finset.mem_filter.mpr ⟨hyD, heq⟩)
  · exact (hσ.symm_lt_of_stratum_lt (by rw [hxk]; exact hgt)).le

/-- Under a stratified grammar, a binary competition whose variants tie on
    every stratum before `k` — with `k` freely ranked internally (`h_triv`)
    and containing an active constraint (`h_dec`) — is won by `chosen` at rate
    `|favoring ∩ Dₖ| / |Dₖ|`, where `Dₖ` is the active set restricted to
    stratum `k`. Later strata cannot affect the outcome. -/
theorem pocPredict_stratified_binary_rate {s : ℕ}
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (stratumOf : Fin n → Fin s) (inner : PartialOrderConstraints n)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other) (k : Fin s)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner.rel a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → vp i chosen c = vp i other c)
    (h_dec : ((active vp i chosen other).filter (stratumOf · = k)).Nonempty) :
    pocPredict cands vp (stratified stratumOf inner) i chosen =
      ((favoring vp i chosen other ∩
          (active vp i chosen other).filter (stratumOf · = k)).card : ℚ) /
        (((active vp i chosen other).filter (stratumOf · = k)).card : ℚ) := by
  classical
  unfold pocPredict
  rw [Finset.filter_congr fun σ hσ =>
    (picksAt_binary_iff_head_mem_favoring cands vp i chosen other h_two h_ne σ).trans
      (by rw [permDList_head?_active_filter_stratum vp
        (mem_consistentTotalOrders.mp hσ) h_tie h_dec])]
  exact filter_head_in_rate_of_swaps _ _ _ (consistentTotalOrders_nonempty _)
    fun y₁ h₁ y₂ h₂ σ hσ => mem_consistentTotalOrders.mpr
      (isConsistent_swap_mul h_triv (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
        (mem_consistentTotalOrders.mp hσ))

/-! ### Bridge to the `Grammar` hub

A partial order on constraints is the simple-ERC fragment of an OT grammar —
its consistent total orders are exactly the legs of
`Grammar.ofERCSet p.toERCSet` ([merchant-riggle-2016]). -/

/-- The `Grammar` whose legs are `p`'s consistent total orders. -/
def toGrammar (p : PartialOrderConstraints n) : Grammar n :=
  Grammar.ofERCSet p.toERCSet p.toERCSet_consistent

@[simp] theorem toGrammar_legs (p : PartialOrderConstraints n) :
    p.toGrammar.legs = p.consistentTotalOrders := by
  show (Grammar.ofERCSet p.toERCSet p.toERCSet_consistent).legs = p.consistentTotalOrders
  rw [Grammar.legs_ofERCSet, consistentTotalOrders_eq_linearExtensions]

end PartialOrderConstraints

end HarmonicGrammar
