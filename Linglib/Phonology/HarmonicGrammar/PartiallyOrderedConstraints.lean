import Linglib.Phonology.HarmonicGrammar.Cumulativity
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.OptimalityTheory.Antimatroid
import Linglib.Core.Optimization.PermSubsetCombinatorics
import Mathlib.Order.Extension.Linear

/-!
# Partially Ordered Constraints (POC)
[anttila-1997] [kiparsky-1993b] [coetzee-pater-2011]

A POC grammar is a partial order on the constraint set. Each evaluation
samples a total order (i.e., a linear extension) consistent with the partial
order, and the OT optimum under that ranking is the output. The induced
distribution over outputs is uniform over consistent linear extensions.

This module provides the substrate counterpart to the per-paper POC
analyses: every linear extension is a `Ranking n`, and every
finite set of consistent extensions sits inside `Finset.univ` for that
permutation type. The probability of an output is then a ratio of `Finset`
cardinalities — a clean computation, no measure theory required.

## Architecture

POC sits in the substrate alongside `Cumulativity.SystemicProblem`, sharing
its multi-input optimization model and its `realizedByRanking` definition. The
new content here is:

- `PartialOrderConstraints n`: a partial order on `Fin n` (constraint indices).
- `IsConsistent p σ`: σ is a linear extension of p.
- `consistentTotalOrders p`: the (decidable, finite) set of linear extensions.
- `toERCSet p` / `consistentTotalOrders_eq_linearExtensions`: the simple-ERC
  (Hasse-edge) encoding of `p`, identifying its consistent total orders with the
  lex-grounded `ERCSet.linearExtensions` — so POC's "linear extension" is the ERC
  one, not a third re-stipulation ([merchant-riggle-2016]; [prince-2002]).
- `pocPredict P p i o`: the probability that POC sampling under p selects
  output o for input i, computed as a ratio of consistent extensions
  realizing o vs. all consistent extensions.
- `IsPOCRealizable P`: some non-trivial partial order has every consistent
  extension realizing the target. This is the categorical realizability
  notion; the probabilistic story is captured by `pocPredict`.

## Containments

- `poc_realizable_imp_ot_realizable` — trivial (pick any consistent extension).
- `ot_realizable_imp_poc_realizable` — non-trivial; the witness is the σ-induced
  total order, whose unique consistent extension is σ. The uniqueness step
  uses the standard fact that a strictly monotone bijection on a finite
  linear order is the identity (proof via `StrictMono.id_le` + dual).

The categorical containment `OT ⊆ POC` is somewhat misleading linguistically:
POC's expressive advantage over OT is *probabilistic*, not categorical. The
`pocPredict` API is the principled way to surface that — POC can produce
intermediate frequencies (e.g., 8/24, 12/24 in [coetzee-pater-2011]'s
t/d-deletion analysis) that no single OT ranking can reproduce.

## Where this is used

`Studies/CoetzeePater2011.lean` and `Studies/Zuraw2010.lean` consume this
substrate directly — `pocPredict`, `PicksAt`, and `pocPredict_discrete_binary_rate`
over the discrete partial order — rather than enumerating rankings by hand.
-/

namespace HarmonicGrammar

open Core.Optimization OptimalityTheory


open Finset

-- ============================================================================
-- § 1: Auxiliary — Strictly Monotone Bijection on Fin n is the Identity
-- ============================================================================

/-- A strictly monotone endo-function on `Fin n` is the identity. Both
    inequalities `id ≤ f` and `f ≤ id` follow from `StrictMono.id_le` (using
    `Fin n`'s `WellFoundedLT` instance) and its dual (using `WellFoundedGT`),
    which combine to `f = id` by antisymmetry. -/
private theorem fin_strictMono_eq_id {n : ℕ} (f : Fin n → Fin n)
    (hf : StrictMono f) : f = id := by
  funext k
  have h₁ : k ≤ f k := hf.id_le k
  have h₂ : f k ≤ k := hf.le_id k
  exact le_antisymm h₂ h₁

/-- A monotone bijection on `Fin n` is the identity. The bijection condition
    promotes monotone to strictly monotone (since equality of f-images forces
    equality of arguments), then `fin_strictMono_eq_id` finishes. -/
private theorem fin_monotone_bij_eq_id {n : ℕ}
    (f : Fin n → Fin n) (hbij : Function.Bijective f) (hmono : Monotone f) :
    f = id := by
  have hstrict : StrictMono f := by
    intro a b hab
    rcases lt_or_eq_of_le (hmono hab.le) with h | h
    · exact h
    · exact absurd (hbij.injective h) hab.ne
  exact fin_strictMono_eq_id f hstrict

-- ============================================================================
-- § 2: PartialOrderConstraints
-- ============================================================================

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

/-- The discrete partial order on `Fin n`: `rel a b` iff `a = b`. No
    constraint pair is comparable beyond reflexivity. Every permutation
    is a consistent linear extension — this matches [anttila-1997]'s
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

/-- A permutation σ is **consistent** with the partial order p if σ⁻¹
    respects rel: whenever `rel a b` holds, σ ranks a at least as early
    as b (`σ.symm a ≤ σ.symm b`). σ is a linear extension of p. -/
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

A partial order is a set of dominance requirements; each strict related pair
`a ≠ b` with `rel a b` is the Hasse-style ERC `a ≫ b` (`simpleERC a b`,
[merchant-riggle-2016]'s simple ERCs). Encoding `p` this way shows
`consistentTotalOrders p` *is* the ERC linear-extension set
`ERCSet.linearExtensions`, so the POC notion of "consistent total order" is not a
third re-stipulation of "linear extension" but the lex-grounded ERC one
([prince-2002]). -/

/-- The simple-ERC encoding of a partial order: one ERC `a ≫ b` (`simpleERC a b`)
for each strict related pair (`a ≠ b` with `rel a b`). Transitively-implied pairs
are included as well; they are entailed by the covering pairs, so this set has the
same linear extensions as the Hasse-edge encoding. Built by computable enumeration
over `List.finRange` so it carries no `noncomputable` marker. -/
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
    ERCSet.satisfiedBy σ p.toERCSet ↔ p.IsConsistent σ := by
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

/-- **POC consistency is ERC linear extension.** The consistent total orders of a
partial order are exactly the linear extensions of its simple-ERC encoding —
collapsing the POC `consistentTotalOrders` into the lex-grounded
`ERCSet.linearExtensions` ([merchant-riggle-2016]; [prince-2002]). -/
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

/-- **Uniqueness**: the σ-induced total order has σ as its *unique*
    consistent linear extension. Any consistent τ must agree with σ
    pointwise (since τ.symm ∘ σ is a monotone bijection on `Fin n`, hence
    the identity by `fin_monotone_bij_eq_id`). -/
theorem fromPermutation_consistent_unique {σ τ : Ranking n}
    (hτ : (fromPermutation σ).IsConsistent τ) : τ = σ := by
  have hcomp : ⇑τ.symm ∘ ⇑σ = id := by
    apply fin_monotone_bij_eq_id
    · exact τ.symm.bijective.comp σ.bijective
    · intro a b hab
      have hrel : (fromPermutation σ).rel (σ a) (σ b) := by
        show σ.symm (σ a) ≤ σ.symm (σ b)
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hab
      exact hτ (σ a) (σ b) hrel
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

/-- Opaque carrier for the extended linear order. Wrapping `Fin n` in a fresh
    structure lets us equip it with the linear-extension order `s` *without*
    clashing with `Fin n`'s standard order — the diamond that would otherwise
    make `≤` ambiguous in the goal. -/
private structure LinExtCarrier (n : ℕ) where ofFin ::
  /-- The underlying index. -/
  toFin : Fin n

/-- **Every POC has a consistent linear extension** (Szpilrajn): for *any*
    partial order `p`, `consistentTotalOrders p` is nonempty. This is what the
    `IsPartialOrder` instance buys — it is the hypothesis of mathlib's
    `extend_partialOrder`. Consequently `pocPredict`'s denominator
    (`consistentTotalOrders.card`) is provably positive for every POC, so
    `pocPredict` is a genuine distribution, not just on `discrete`/`fromPermutation`. -/
theorem consistentTotalOrders_nonempty (p : PartialOrderConstraints n) :
    p.consistentTotalOrders.Nonempty := by
  classical
  -- Szpilrajn: extend the partial order `p.rel` to a linear order `s`.
  obtain ⟨s, hs_lin, hsub⟩ := extend_partialOrder p.rel
  -- Equip the opaque carrier with `s`, then sort it against `Fin n`'s order.
  let wEquiv : LinExtCarrier n ≃ Fin n :=
    { toFun := LinExtCarrier.toFin, invFun := LinExtCarrier.ofFin,
      left_inv := fun ⟨_⟩ => rfl, right_inv := fun _ => rfl }
  letI : Fintype (LinExtCarrier n) := Fintype.ofEquiv (Fin n) wEquiv.symm
  letI : LinearOrder (LinExtCarrier n) :=
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

/-- `pocPredict`'s denominator `consistentTotalOrders.card` is strictly positive
    for **any** POC — the `0/0` guard in `pocPredict` is never exercised on a real
    partial order. Direct consequence of `consistentTotalOrders_nonempty`. -/
theorem consistentTotalOrders_card_pos (p : PartialOrderConstraints n) :
    0 < p.consistentTotalOrders.card :=
  p.consistentTotalOrders_nonempty.card_pos

/-! ### The order-ideal antimatroid of a POC

A POC partial order's Hasse-edge encoding is a consistent set of *simple* ERCs, so
it has a Birkhoff antimatroid (`Antimat.ofSimple`). Its feasible sets are exactly
the order ideals of `p`, giving the antimatroid theory its first grammar-level
consumer ([dilworth-1940]; [merchant-riggle-2016]). -/

/-- `p.toERCSet` consists of simple ERCs (each is a `simpleERC` of a strict pair). -/
theorem toERCSet_isSimpleSet (p : PartialOrderConstraints n) :
    ERCSet.isSimpleSet p.toERCSet := by
  intro α hα
  obtain ⟨a, b, hab, _, rfl⟩ := mem_toERCSet.mp hα
  exact simpleERC_isSimple hab

/-- `p.toERCSet` is consistent: any linear extension of `p` satisfies it. -/
theorem toERCSet_consistent (p : PartialOrderConstraints n) :
    ERCSet.consistent p.toERCSet := by
  obtain ⟨σ, hσ⟩ := p.consistentTotalOrders_nonempty
  exact ⟨σ, satisfiedBy_toERCSet.mpr (mem_consistentTotalOrders.mp hσ)⟩

/-- The **order-ideal antimatroid** of a POC partial order: the simple-ERC
Birkhoff antimatroid (`Antimat.ofSimple`) of its Hasse-edge encoding. Its feasible
sets are exactly the order ideals of `p` (`pocAntimatroid_isFeasible_iff`) — the
Birkhoff correspondence between a partial order and its antimatroid
([dilworth-1940]; [merchant-riggle-2016]). This is the first grammar-level
consumer of the antimatroid theory. -/
def pocAntimatroid (p : PartialOrderConstraints n) : Antimatroid (Fin n) :=
  Antimat.ofSimple p.toERCSet p.toERCSet_consistent p.toERCSet_isSimpleSet

/-- Local feasibility against `p.toERCSet` is exactly the order-ideal condition
(downward-closed under `rel`): if `b ∈ S` and `a` dominates `b` (`rel a b`), then
`a ∈ S`. -/
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

/-- **The feasible sets of `pocAntimatroid` are the order ideals of `p`** — the
Birkhoff correspondence, made concrete and decidable. -/
@[simp] theorem pocAntimatroid_isFeasible_iff {p : PartialOrderConstraints n}
    {S : Finset (Fin n)} :
    (p.pocAntimatroid).IsFeasible (↑S : Set (Fin n)) ↔
      ∀ a b, p.rel a b → b ∈ S → a ∈ S := by
  simp only [pocAntimatroid, ofSimple_isFeasible_coe, feasible_toERCSet_iff]

end PartialOrderConstraints

-- ============================================================================
-- § 3: POC Realizability of SystemicProblem
-- ============================================================================

namespace SystemicProblem

variable {Input Output : Type*} {n : ℕ}

/-- A partial order p **POC-realizes** the target if every consistent
    extension realizes it. There is always at least one consistent extension
    (`consistentTotalOrders_nonempty`), so this genuinely means target
    probability = 1 under POC sampling — not the vacuous empty case, which is
    why no explicit nonemptiness conjunct is needed. -/
def realizedByPOC (P : SystemicProblem Input Output n)
    (p : PartialOrderConstraints n) : Prop :=
  ∀ σ ∈ p.consistentTotalOrders, P.realizedByRanking σ

/-- A `SystemicProblem` is **POC-realizable** if some partial order
    categorically realizes the target. -/
def IsPOCRealizable (P : SystemicProblem Input Output n) : Prop :=
  ∃ p : PartialOrderConstraints n, P.realizedByPOC p

end SystemicProblem

-- ============================================================================
-- § 4: Containments — OT ⊆ POC, POC ⊆ OT (categorical)
-- ============================================================================

/-- **Trivial direction**: every POC-realized target is OT-realized
    (pick any single consistent extension). -/
theorem poc_realizable_imp_ot_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsPOCRealizable → P.IsOTRealizable := by
  rintro ⟨p, hreal⟩
  obtain ⟨σ, hσ⟩ := p.consistentTotalOrders_nonempty
  exact ⟨σ, hreal σ hσ⟩

/-- **Non-trivial direction**: every OT-realized target is POC-realized
    (the witness is the σ-induced total order, whose unique consistent
    extension is σ itself by `fromPermutation_consistent_unique`). -/
theorem ot_realizable_imp_poc_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable → P.IsPOCRealizable := by
  rintro ⟨σ, hσ⟩
  refine ⟨PartialOrderConstraints.fromPermutation σ, ?_⟩
  simpa [SystemicProblem.realizedByPOC,
    PartialOrderConstraints.consistentTotalOrders_fromPermutation] using hσ

/-- **Categorical equivalence**: under categorical realizability,
    OT-realizable and POC-realizable coincide. POC's *probabilistic*
    advantage over OT is captured separately by `pocPredict` (next section);
    no categorical theorem distinguishes them. -/
theorem isOTRealizable_iff_isPOCRealizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable ↔ P.IsPOCRealizable :=
  ⟨ot_realizable_imp_poc_realizable P,
   poc_realizable_imp_ot_realizable P⟩

-- ============================================================================
-- § 5: Probabilistic POC — pocPredict
-- ============================================================================

namespace PartialOrderConstraints

variable {Input Output : Type*} [DecidableEq Output] {n : ℕ}

/-- σ **picks** output o for input i if o is the unique strict OT winner
    (every other in-set candidate is lex-strictly worse than o under σ).

    Bare-args version: takes `cands` and `vp` directly rather than bundled
    in a `SystemicProblem`. POC analyses don't need a target — they're about
    distribution over outputs, not realization of a chosen one. -/
def PicksAt (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Ranking n) (i : Input) (o : Output) : Prop :=
  o ∈ cands i ∧
  ∀ o' ∈ cands i, o' ≠ o →
    toLex (fun k : Fin n => vp i o (σ k)) <
    toLex (fun k : Fin n => vp i o' (σ k))

instance (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Ranking n) (i : Input) (o : Output) :
    Decidable (PicksAt cands vp σ i o) := by
  unfold PicksAt; infer_instance

/-- The probability that POC sampling under partial order p selects output
    o for input i: ratio of consistent extensions picking o to total
    consistent extensions. The denominator is always positive
    (`consistentTotalOrders_card_pos`), so this is a genuine probability; ℚ's
    `0/0 = 0` convention is a harmless fallback never exercised on a real POC. -/
def pocPredict (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (p : PartialOrderConstraints n) (i : Input) (o : Output) : ℚ :=
  ((p.consistentTotalOrders.filter
    (fun σ => PicksAt cands vp σ i o)).card : ℚ) /
  (p.consistentTotalOrders.card : ℚ)

/-- For the σ-induced total order, `pocPredict` collapses to a δ at σ's
    OT-pick: probability 1 if σ picks o, probability 0 otherwise. -/
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

/-- Discrete-PO predict: uniform over all permutations (no ranking imposed).
    Counts the σ's that pick o, divides by `n!`. -/
theorem pocPredict_discrete
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (o : Output) :
    pocPredict cands vp (discrete n) i o =
    ((Finset.univ.filter
      (fun σ : Ranking n => PicksAt cands vp σ i o)).card : ℚ) /
    (Finset.univ : Finset (Ranking n)).card := by
  simp only [pocPredict, consistentTotalOrders_discrete]

end PartialOrderConstraints

-- ============================================================================
-- § 6: Bridge — PicksAt for binary candidates ↔ head-in-Y on permDList
-- ============================================================================

/-! For binary candidate sets `cands i = {chosen, other}`, `PicksAt σ i chosen`
reduces to lex domination of `vp i chosen ∘ σ` over `vp i other ∘ σ` (the
∀-quantifier collapses to a single check). And that lex predicate is exactly
"the highest-ranked constraint in the distinguishing set `D` favors `chosen`"
— i.e., `head of permDList σ D ∈ Y` where `D = {k : vp chosen k ≠ vp other k}`
and `Y = {k : vp chosen k < vp other k}`.

This bridges POC's lex-strict-better predicate to
`Core.Optimization.PermSubsetCombinatorics.perm_filter_head_in_card`'s closed
form, letting any binary-candidate POC study compute its `pocPredict` value
in closed form (`n! × |Y ∩ D| / |D|`) without enumerating `n!` rankings.

Used by `Studies/CoetzeePater2011.lean` (English t/d-deletion;
binary `{retain, delete}` outputs across 3 contexts). -/

namespace PartialOrderConstraints

open Core.Optimization.PermSubsetCombinatorics

variable {Input : Type*} {n : ℕ}

/-- For binary candidate sets, `PicksAt σ i chosen` is equivalent to
    "the head of `permDList σ D` lies in `Y`", where `D` is the set of
    constraints distinguishing `chosen` from `other` and `Y` is the
    favoring subset (`vp chosen < vp other`).

    The bridge uses `permDList_head_eq_some_iff` + `permToList_split_at` +
    `permToList_eq_append_cons_imp_apply` (substrate) to translate
    between the lex `∃k` form and the head-in-Y characterization. -/
theorem picksAt_binary_iff_permDList_head_lt {Output : Type*} [DecidableEq Output]
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other)
    (σ : Ranking n) :
    PicksAt cands vp σ i chosen ↔
    ∃ x ∈ Finset.univ.filter (fun k : Fin n => vp i chosen k < vp i other k),
      (permDList σ (Finset.univ.filter
        (fun k : Fin n => vp i chosen k ≠ vp i other k))).head? = some x := by
  classical
  -- Step 1: PicksAt with binary cands reduces to lex domination of chosen over other
  have h_picksAt_iff_lex :
      PicksAt cands vp σ i chosen ↔
      ∃ k : Fin n, (∀ j, j < k → vp i chosen (σ j) = vp i other (σ j)) ∧
        vp i chosen (σ k) < vp i other (σ k) := by
    unfold PicksAt
    constructor
    · rintro ⟨_, h_lex⟩
      exact h_lex other (by rw [h_two]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
        (Ne.symm h_ne)
    · intro h_lex
      refine ⟨by rw [h_two]; exact Finset.mem_insert_self _ _, ?_⟩
      intro o' h_o' h_o'_ne
      -- o' ∈ {chosen, other} ∧ o' ≠ chosen → o' = other
      rw [h_two, Finset.mem_insert, Finset.mem_singleton] at h_o'
      rcases h_o' with h | h
      · exact absurd h h_o'_ne
      · subst h; exact h_lex
  rw [h_picksAt_iff_lex]
  -- Step 2: lex domination ↔ head-in-Y characterization
  set D := Finset.univ.filter (fun k : Fin n => vp i chosen k ≠ vp i other k) with hD_def
  set Y := Finset.univ.filter (fun k : Fin n => vp i chosen k < vp i other k) with hY_def
  have h_D_iff : ∀ k, k ∈ D ↔ vp i chosen k ≠ vp i other k := by
    intro k; simp [hD_def]
  have h_Y_iff : ∀ k, k ∈ Y ↔ vp i chosen k < vp i other k := by
    intro k; simp [hY_def]
  constructor
  · -- lex domination → head-in-Y
    rintro ⟨k, h_below, h_lt⟩
    have h_σk_Y : σ k ∈ Y := (h_Y_iff (σ k)).mpr h_lt
    have h_σk_D : σ k ∈ D := (h_D_iff (σ k)).mpr (Nat.ne_of_lt h_lt)
    have h_below_notD : ∀ j < k, σ j ∉ D := fun j hj h =>
      ((h_D_iff (σ j)).mp h) (h_below j hj)
    refine ⟨σ k, h_σk_Y, ?_⟩
    rw [permDList_head_eq_some_iff]
    refine ⟨h_σk_D, ((List.finRange n).take k.val).map σ,
            ((List.finRange n).drop (k.val + 1)).map σ, permToList_split_at σ k, ?_⟩
    intro y hy
    obtain ⟨j, h_j_take, h_σj⟩ := List.mem_map.mp hy
    rw [List.mem_take_iff_getElem] at h_j_take
    obtain ⟨idx, h_idx_lt, h_idx_eq⟩ := h_j_take
    simp only [List.getElem_finRange] at h_idx_eq
    have h_idx_lt_k : idx < k.val := by
      simp only [List.length_finRange] at h_idx_lt
      omega
    have h_j_lt_k : j < k := by
      rw [Fin.lt_def, ← h_idx_eq]; exact h_idx_lt_k
    rw [← h_σj]
    exact h_below_notD j h_j_lt_k
  · -- head-in-Y → lex domination
    rintro ⟨x, hx_Y, h_head⟩
    rw [permDList_head_eq_some_iff] at h_head
    obtain ⟨h_x_D, pre, suf, h_split, h_pre⟩ := h_head
    have h_pre_len_lt : pre.length < n := by
      have h_perm_len : (permToList σ).length = n := permToList_length σ
      rw [h_split] at h_perm_len
      simp [List.length_append, List.length_cons] at h_perm_len
      omega
    have h_σk_x := permToList_eq_append_cons_imp_apply σ pre suf x h_split h_pre_len_lt
    refine ⟨⟨pre.length, h_pre_len_lt⟩, ?_, ?_⟩
    · -- ∀ j < ⟨pre.length, _⟩, vp chosen (σ j) = vp other (σ j)
      intro j h_j_lt
      rw [Fin.lt_def] at h_j_lt
      -- σ j is the j-th element of `((finRange n).take pre.length).map σ` (= pre)
      have h_split_pre := permToList_split_at σ ⟨pre.length, h_pre_len_lt⟩
      -- Combined: ((take pre.length).map σ) ++ σ ⟨...⟩ :: ((drop _).map σ) = pre ++ x :: suf
      have h_lhs_pre_len : (((List.finRange n).take pre.length).map σ).length = pre.length := by
        rw [List.length_map, List.length_take, List.length_finRange]; omega
      have h_combined : ((List.finRange n).take pre.length).map σ ++
          σ ⟨pre.length, h_pre_len_lt⟩ ::
          ((List.finRange n).drop (pre.length + 1)).map σ = pre ++ x :: suf := by
        rw [← h_split_pre]; exact h_split
      have h_pre_eq : ((List.finRange n).take pre.length).map σ = pre :=
        (List.append_inj h_combined h_lhs_pre_len).1
      -- σ j ∈ pre (j-th element of pre is σ j)
      have h_σj_in_pre : σ j ∈ pre := by
        rw [← h_pre_eq]
        refine List.mem_map.mpr ⟨j, ?_, rfl⟩
        rw [List.mem_take_iff_getElem]
        refine ⟨j.val, ?_, by simp [List.getElem_finRange]⟩
        simp only [List.length_finRange, lt_min_iff]
        exact ⟨h_j_lt, j.isLt⟩
      have h_eq : ¬ vp i chosen (σ j) ≠ vp i other (σ j) := fun h =>
        (h_pre _ h_σj_in_pre) ((h_D_iff (σ j)).mpr h)
      exact not_not.mp h_eq
    · show vp i chosen (σ ⟨pre.length, h_pre_len_lt⟩) <
          vp i other (σ ⟨pre.length, h_pre_len_lt⟩)
      rw [h_σk_x]
      exact (h_Y_iff x).mp hx_Y

-- ============================================================================
-- § 7: Closed-form rate for binary candidates
-- ============================================================================

variable {Input Output : Type*} [DecidableEq Output] {n : ℕ}

/-- **Closed-form rate for binary `pocPredict` under the discrete partial
    order**: when `cands i = {chosen, other}`, the fraction of all `n!`
    permutations that pick `chosen` for input `i` equals `|Y ∩ D| / |D|`,
    where `D` is the distinguishing set (constraints where `vp` differs)
    and `Y` is the favoring set (constraints where `chosen` has fewer
    violations).

    Combines `picksAt_binary_iff_permDList_head_lt` (the bridge from
    `PicksAt` to head-of-`permDList`) with
    `Core.Optimization.PermSubsetCombinatorics.perm_filter_head_in_rate`
    (the rate form of the closed-form combinatorics).

    Consumed by `Studies/CoetzeePater2011.lean`
    (binary `{retain, delete}` over Fin 4) and
    `Studies/Zuraw2010.lean` (binary `{yes, no}`
    over Fin 6). -/
theorem picksAt_rate_eq
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other)
    (D Y : Finset (Fin n))
    (h_D : ∀ k, k ∈ D ↔ vp i chosen k ≠ vp i other k)
    (h_Y : ∀ k, k ∈ Y ↔ vp i chosen k < vp i other k) :
    ((Finset.univ.filter (fun σ : Ranking n =>
      PicksAt cands vp σ i chosen)).card : ℚ) / (Nat.factorial n : ℚ) =
    ((Y ∩ D).card : ℚ) / (D.card : ℚ) := by
  have h_filter_eq :
      (Finset.univ.filter (fun σ : Ranking n =>
        PicksAt cands vp σ i chosen)) =
      (Finset.univ.filter (fun σ : Ranking n =>
        ∃ x ∈ Finset.univ.filter
          (fun k : Fin n => vp i chosen k < vp i other k),
        (Core.Optimization.PermSubsetCombinatorics.permDList σ
          (Finset.univ.filter
            (fun k : Fin n => vp i chosen k ≠ vp i other k))).head?
            = some x)) :=
    Finset.filter_congr (fun σ _ =>
      picksAt_binary_iff_permDList_head_lt cands vp i chosen other h_two h_ne σ)
  rw [h_filter_eq]
  have h_D_eq : D = Finset.univ.filter
      (fun k : Fin n => vp i chosen k ≠ vp i other k) :=
    Finset.ext (fun k => by simp [h_D k])
  have h_Y_eq : Y = Finset.univ.filter
      (fun k : Fin n => vp i chosen k < vp i other k) :=
    Finset.ext (fun k => by simp [h_Y k])
  rw [h_D_eq, h_Y_eq]
  exact Core.Optimization.PermSubsetCombinatorics.perm_filter_head_in_rate _ _

/-- **Closed-form rate for `pocPredict` under the discrete partial order**
    with binary candidate sets: `pocPredict cands vp (.discrete n) i chosen
    = |Y ∩ D| / |D|`. Composes `pocPredict_discrete` with `picksAt_rate_eq`,
    absorbing the `Fintype.card_perm`/`Fintype.card_fin` arithmetic bridge.

    This is the user-facing rate identity every binary-candidate POC study
    wants. Consumed by `Studies/CoetzeePater2011.lean` (3 contexts),
    `Studies/Anttila1997.lean` (2 grammar tiers), and
    `Studies/Zuraw2010.lean`. -/
theorem pocPredict_discrete_binary_rate
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other)
    (D Y : Finset (Fin n))
    (h_D : ∀ k, k ∈ D ↔ vp i chosen k ≠ vp i other k)
    (h_Y : ∀ k, k ∈ Y ↔ vp i chosen k < vp i other k) :
    pocPredict cands vp (discrete n) i chosen =
    ((Y ∩ D).card : ℚ) / (D.card : ℚ) := by
  rw [pocPredict_discrete, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  exact picksAt_rate_eq cands vp i chosen other h_two h_ne D Y h_D h_Y

end PartialOrderConstraints

end HarmonicGrammar
