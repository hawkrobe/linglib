/-
# Processing Model

Shared infrastructure for processing-based explanations across comparison modules.

## Design Rationale

Processing cost is modeled via **Pareto dominance** over ordinal dimensions rather
than weighted sums. This avoids magic numbers: if condition A is worse-or-equal on
every dimension and strictly worse on at least one, it is harder — period. When
dimensions conflict, the result is `incomparable`, which is honest about the
theory's predictions.

## Dimensions

| Dimension | Cognitive Correlate |
|-----------|-------------------|
| `locality` | Working memory decay (Gibson 2000, Lewis & Vasishth 2005) |
| `boundaries` | Clause/phrase boundaries increase retrieval interference |
| `referentialLoad` | Referential processing from intervening material |
| `ease` | Retrieval facilitation (filler complexity, predictability) |

## References

- Gibson, E. (2000). The dependency locality theory.
- Lewis, R.L. & Vasishth, S. (2005). An activation-based model.
- Hofmeister, P. & Sag, I.A. (2010). Cognitive constraints and island effects.
- Scontras, G. et al. (2017). Scope ambiguity processing.
-/

namespace ProcessingModel

-- ============================================================================
-- Processing Profile
-- ============================================================================

/-- A processing profile characterizing the difficulty of a linguistic dependency.

Each dimension is ordinal (higher = more of that factor). Comparison is via
Pareto dominance — no numeric aggregation. -/
structure ProcessingProfile where
  /-- Distance (words/nodes) between filler and integration site -/
  locality : Nat
  /-- Clause or phrase boundaries crossed -/
  boundaries : Nat
  /-- Referential processing load from intervening material
  (0 = none/pronominal, 1 = indefinite, 2 = definite/proper name) -/
  referentialLoad : Nat
  /-- Retrieval facilitation: richer fillers, higher predictability
  (higher = easier retrieval, so this dimension is inverted in comparison) -/
  ease : Nat
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Pareto Dominance
-- ============================================================================

/-- Result of comparing two processing profiles via Pareto dominance. -/
inductive CompareResult where
  | harder        -- Worse-or-equal on all dimensions, strictly worse on ≥1
  | easier        -- Better-or-equal on all dimensions, strictly better on ≥1
  | equal         -- Identical on all dimensions
  | incomparable  -- Some dimensions harder, some easier
  deriving Repr, DecidableEq, BEq

/-- Compare two processing profiles via Pareto dominance.

For cost dimensions (locality, boundaries, referentialLoad): higher = harder.
For the benefit dimension (ease): higher = easier, so we invert. -/
def ProcessingProfile.compare (a b : ProcessingProfile) : CompareResult :=
  -- Cost dimensions: a is "worse" if higher
  -- Ease dimension: a is "worse" if lower (less facilitation)
  let locCmp := Ord.compare a.locality b.locality
  let bndCmp := Ord.compare a.boundaries b.boundaries
  let refCmp := Ord.compare a.referentialLoad b.referentialLoad
  let easeCmp := Ord.compare b.ease a.ease  -- inverted: less ease = worse
  let dims := [locCmp, bndCmp, refCmp, easeCmp]
  let anyWorse := dims.any (· == .gt)
  let anyBetter := dims.any (· == .lt)
  match anyWorse, anyBetter with
  | false, false => .equal
  | true, false  => .harder
  | false, true  => .easier
  | true, true   => .incomparable

-- ============================================================================
-- HasProcessingProfile Typeclass
-- ============================================================================

/-- Typeclass for types that can be mapped to processing profiles.

Any module claiming processing-based predictions must provide an instance,
ensuring shared vocabulary across all comparison files. -/
class HasProcessingProfile (α : Type) where
  profile : α → ProcessingProfile

-- ============================================================================
-- Monotonicity Axioms
-- ============================================================================

/-! ### Monotonicity

These are the cognitive science claims underlying the processing model.
Each states that increasing a cost dimension (or decreasing ease) cannot
make processing easier. Stated as theorems with `sorry` per project convention.

These are provable from the Pareto dominance definition but not load-bearing —
nothing downstream depends on them. Proof deferred in favor of deeper results. -/

/-- More locality → not easier (working memory decay). -/
theorem locality_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with locality := p.locality + k + 1 } |>.compare p) ≠ .easier := by
  unfold ProcessingProfile.compare
  simp only [List.any]
  -- The locality dimension has a.locality > b.locality, so anyWorse = true,
  -- which prevents the result from being .easier
  have h : ¬(p.locality + k + 1 < p.locality) := by omega
  simp [Ord.compare, compareOfLessAndEq, h]
  split <;> simp_all

/-- More boundaries → not easier (interference at retrieval). -/
theorem boundaries_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with boundaries := p.boundaries + k + 1 } |>.compare p) ≠ .easier := by
  unfold ProcessingProfile.compare
  simp only [List.any]
  have h : ¬(p.boundaries + k + 1 < p.boundaries) := by omega
  simp [Ord.compare, compareOfLessAndEq, h]
  split <;> simp_all

/-- More referential load → not easier (similarity-based interference). -/
theorem referentialLoad_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with referentialLoad := p.referentialLoad + k + 1 } |>.compare p) ≠ .easier := by
  unfold ProcessingProfile.compare
  simp only [List.any]
  have h : ¬(p.referentialLoad + k + 1 < p.referentialLoad) := by omega
  simp [Ord.compare, compareOfLessAndEq, h]
  split <;> simp_all

/-- More ease → not harder (facilitation aids retrieval). -/
theorem ease_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with ease := p.ease + k + 1 } |>.compare p) ≠ .harder := by
  unfold ProcessingProfile.compare
  simp only [List.any]
  -- ease is inverted: compare b.ease a.ease, so more ease → .lt (better)
  have h1 : p.ease < p.ease + k + 1 := by omega
  have h2 : ¬(p.ease + k + 1 < p.ease) := by omega
  simp [Ord.compare, compareOfLessAndEq, h1, h2]

-- ============================================================================
-- Ordering Verification
-- ============================================================================

/-- An ordering prediction: condition A should be harder than condition B. -/
structure OrderingPrediction (α : Type) [HasProcessingProfile α] where
  harder : α
  easier : α
  description : String
  deriving Repr

/-- Verify that Pareto ordering matches the predicted direction. -/
def verifyOrdering {α : Type} [HasProcessingProfile α]
    (pred : OrderingPrediction α) : Bool :=
  (HasProcessingProfile.profile pred.harder |>.compare
    (HasProcessingProfile.profile pred.easier)) == .harder

end ProcessingModel
