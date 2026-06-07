import Linglib.Core.Order.PullbackPreorder
import Linglib.Core.Optimization.Profile
import Mathlib.Data.Finset.Filter

/-!
# Pareto preorders on `Cand → Profile β n` score functions

Two natural preorders on a candidate type carrying a score function
`Cand → Profile β n`, both instances of the `Core.Order.PullbackPreorder`
pattern:

| view                          | feature                      | feature-space order |
|-------------------------------|------------------------------|---------------------|
| `paretoPullbackPreorder`       | `score : Cand → Profile β n` | pointwise `≤`       |
| `supportPullbackPreorder`  | `support : Cand → Finset (Fin n)` | subset `⊆` |

Recognising both as `PullbackPreorder` instances means the implication
"pointwise dominance ⇒ subset-of-supports dominance" is a one-line
application of `PullbackPreorder.coarsen_via_monotone` with the support
extractor as the connecting monotone map.

When `0 ≤ b` for every `b : β` (so larger profile values are bigger),
pointwise dominance implies subset dominance of the nonzero-coordinate
set; the converse fails — see
`paretoPullbackPreorder_le_implies_supportPullbackPreorder_le`.

-/

namespace Core.Optimization

open Core.Order (PullbackPreorder)

variable {Cand : Type*} {β : Type*} {n : Nat}

-- ============================================================================
-- § 1: Quantitative view — pointwise Pareto on the score profile
-- ============================================================================

/-- **Pointwise Pareto preorder** as a `PullbackPreorder`: feature is the
    score vector `s.score : Cand → Profile β n`, feature-space order is
    `Pi.preorder` (pointwise `≤`). Read as "`c` is at-most-as-bad-as `c'` pointwise" under the
    "lower is better" convention. -/
def paretoPullbackPreorder [Preorder β]
    [∀ x y : β, Decidable (x ≤ y)]
    (score : Cand → Profile β n) :
    PullbackPreorder Cand (Profile β n) :=
  PullbackPreorder.ofProj score (fun a a' =>
    show Decidable (∀ i, score a i ≤ score a' i) from inferInstance)

-- ============================================================================
-- § 2: Qualitative view — subset of nonzero-coordinate indices
-- ============================================================================

/-- The set of indices at which the score is nonzero. -/
def nonzeroSet [DecidableEq β] [Zero β]
    (score : Cand → Profile β n) (c : Cand) : Finset (Fin n) :=
  Finset.univ.filter (fun i => score c i ≠ 0)

/-- **Qualitative coarsening** as a `PullbackPreorder`: feature is the
    nonzero-coordinate set, feature-space order is `Finset.⊆`.

    `c ≤ c'` iff the nonzero-index set of `c` is a subset of that of
    `c'` — every index at which `c' = 0`, also `c = 0`. This is the
    qualitative Pareto backbone underlying `Core.Order.SatisfactionOrdering`. -/
def supportPullbackPreorder [DecidableEq β] [Zero β]
    (score : Cand → Profile β n) :
    PullbackPreorder Cand (Finset (Fin n)) :=
  PullbackPreorder.ofProj (nonzeroSet score) (fun _ _ => inferInstance)

-- ============================================================================
-- § 3: The coarsening — pointwise dominance ⇒ qualitative dominance
-- ============================================================================

/-- The violated-set extractor `Profile β n → Finset (Fin n)`, as a function
    of the score profile alone (no `ConstraintSystem` needed). -/
def nonzeroSetOf [DecidableEq β] [Zero β] (p : Profile β n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≠ 0)

/-- The violated-set extractor is monotone in the pointwise order on
    profiles, *provided* `0` is the minimum element of `β`. With that
    hypothesis, `p ≤ p' ⇒ violated p ⊆ violated p'`: any index where `p` is nonzero (hence positive when `0` is the
    minimum), `p'` is also nonzero
    (`p' i ≥ p i > 0`). Without zero-as-min the implication can fail
    (e.g. `p i = -5, p' i = 0` over `ℝ`). -/
theorem nonzeroSetOf_monotone [PartialOrder β] [Zero β] [DecidableEq β]
    (h_zero_min : ∀ b : β, 0 ≤ b) :
    Monotone (nonzeroSetOf (β := β) (n := n)) := by
  intro p p' h i hi
  simp only [nonzeroSetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have h_pos : 0 < p i := lt_of_le_of_ne (h_zero_min _) (Ne.symm hi)
  exact ne_of_gt (lt_of_lt_of_le h_pos (h i))

/-- **Pointwise dominance implies qualitative dominance** (when zero is
    the minimum value of `β`). A one-line corollary of
    `PullbackPreorder.coarsen_via_monotone` applied to `nonzeroSetOf` as
    the connecting monotone map between the two feature spaces.

    The converse fails by design: equal nonzero values at a single index
    give qualitative equivalence but say nothing about further pointwise
    comparisons. -/
theorem paretoPullbackPreorder_le_implies_supportPullbackPreorder_le
    [PartialOrder β] [Zero β] [DecidableEq β]
    [∀ x y : β, Decidable (x ≤ y)]
    (score : Cand → Profile β n)
    (h_zero_min : ∀ b : β, 0 ≤ b)
    {c c' : Cand} (h : (paretoPullbackPreorder score).le c c') :
    (supportPullbackPreorder score).le c c' :=
  PullbackPreorder.coarsen_via_monotone
    (paretoPullbackPreorder score) (supportPullbackPreorder score)
    nonzeroSetOf (nonzeroSetOf_monotone h_zero_min)
    (fun _ => rfl) h

end Core.Optimization
