import Linglib.Core.Constraint.System
import Linglib.Core.Order.PullbackPreorder

/-!
# Pareto Bridge: Constraint Systems as Feature-Pullback Preorders

A `ConstraintSystem Cand (Profile β n)` carries a quantitative violation
profile per candidate plus a decoder. Forgetting the decoder, two natural
preorders on candidates emerge — both are instances of the
`Core.Order.PullbackPreorder` pattern:

| view                          | feature                      | feature-space order |
|-------------------------------|------------------------------|---------------------|
| `paretoPullbackPreorder`       | `score : Cand → Profile β n` | pointwise `≤`       |
| `qualitativePullbackPreorder`  | `violatedSet : Cand → Finset (Fin n)` | subset `⊆` |

Recognising both as `PullbackPreorder` instances means the implication
"pointwise dominance ⇒ qualitative dominance" is no longer a bespoke
proof — it is a one-line application of
`PullbackPreorder.coarsen_via_monotone` with the violated-set extractor as
the connecting monotone map.

## The gap (qualitative is strictly weaker)

The forward direction holds whenever zero is the minimum value of `β`
(e.g. `β = Nat`, raw violation counts). The converse fails — and worse,
a quantitative *winner* under OT or HG can be qualitatively dominated.
In OT with constraints `C₁ ≫ C₂`, a candidate `w` with profile `(0, 5)`
beats `c'` with profile `(1, 0)` lexicographically, yet `w` and `c'` are
qualitatively incomparable: each satisfies one constraint the other
violates. The qualitative coarsening forgets the magnitude trade-off
that lex-min and weighted-sum decoders use to choose a winner. This is
a feature, not a bug — it exposes when a numerical framework's winner
deviates from the Pareto frontier of satisfactions.
-/

namespace Core.Constraint

open Core.Order (PullbackPreorder)

namespace ConstraintSystem

variable {Cand : Type*} {β : Type*} {n : Nat}

-- ============================================================================
-- § 1: Quantitative view — pointwise Pareto on the score profile
-- ============================================================================

/-- **Pointwise Pareto preorder** as a `PullbackPreorder`: feature is the
    score vector `s.score : Cand → Profile β n`, feature-space order is
    `Pi.preorder` (pointwise `≤`). Read as "`c` is at-most-as-bad-as `c'`
    on every constraint" under the OT/HG "lower is better" convention. -/
def paretoPullbackPreorder [Preorder β]
    [∀ x y : β, Decidable (x ≤ y)]
    (s : ConstraintSystem Cand (Profile β n)) :
    PullbackPreorder Cand (Profile β n) :=
  PullbackPreorder.ofProj s.score (fun a a' =>
    show Decidable (∀ i, s.score a i ≤ s.score a' i) from inferInstance)

-- ============================================================================
-- § 2: Qualitative view — subset of violated constraints
-- ============================================================================

/-- The set of constraint indices that `c` violates (score ≠ 0). -/
def violatedSet [DecidableEq β] [Zero β]
    (s : ConstraintSystem Cand (Profile β n)) (c : Cand) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s.score c i ≠ 0)

/-- **Qualitative coarsening** as a `PullbackPreorder`: feature is the
    violated-constraint set, feature-space order is `Finset.⊆`.

    `c ≤ c'` iff `violatedSet c ⊆ violatedSet c'` — every constraint `c`
    violates, `c'` also violates — equivalently, every constraint `c'`
    satisfies (zero), `c` also satisfies. This is the qualitative Pareto
    backbone underlying `Core.Order.SatisfactionOrdering`. -/
def qualitativePullbackPreorder [DecidableEq β] [Zero β]
    (s : ConstraintSystem Cand (Profile β n)) :
    PullbackPreorder Cand (Finset (Fin n)) :=
  PullbackPreorder.ofProj (violatedSet s) (fun _ _ => inferInstance)

-- ============================================================================
-- § 3: The coarsening — pointwise dominance ⇒ qualitative dominance
-- ============================================================================

/-- The violated-set extractor `Profile β n → Finset (Fin n)`, as a function
    of the score profile alone (no `ConstraintSystem` needed). -/
def violatedSetOf [DecidableEq β] [Zero β] (p : Profile β n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≠ 0)

/-- The violated-set extractor is monotone in the pointwise order on
    profiles, *provided* `0` is the minimum element of `β`. With that
    hypothesis, `p ≤ p' ⇒ violated p ⊆ violated p'`: any constraint that
    `p` violates (`p i ≠ 0`, hence `0 < p i`), `p'` also violates
    (`p' i ≥ p i > 0`). Without zero-as-min the implication can fail
    (e.g. `p i = -5, p' i = 0` over `ℝ`). -/
theorem violatedSetOf_monotone [PartialOrder β] [Zero β] [DecidableEq β]
    (h_zero_min : ∀ b : β, 0 ≤ b) :
    Monotone (violatedSetOf (β := β) (n := n)) := by
  intro p p' h i hi
  simp only [violatedSetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have h_pos : 0 < p i := lt_of_le_of_ne (h_zero_min _) (Ne.symm hi)
  exact ne_of_gt (lt_of_lt_of_le h_pos (h i))

/-- **Pointwise dominance implies qualitative dominance** (when zero is
    the minimum value of `β`). A one-line corollary of
    `PullbackPreorder.coarsen_via_monotone` applied to `violatedSetOf` as
    the connecting monotone map between the two feature spaces.

    The converse fails by design: equal nonzero counts on a violated
    constraint give qualitative equivalence but say nothing about further
    pointwise comparisons. -/
theorem paretoPullbackPreorder_le_implies_qualitativePullbackPreorder_le
    [PartialOrder β] [Zero β] [DecidableEq β]
    [∀ x y : β, Decidable (x ≤ y)]
    (s : ConstraintSystem Cand (Profile β n))
    (h_zero_min : ∀ b : β, 0 ≤ b)
    {c c' : Cand} (h : (s.paretoPullbackPreorder).le c c') :
    (s.qualitativePullbackPreorder).le c c' :=
  PullbackPreorder.coarsen_via_monotone
    s.paretoPullbackPreorder s.qualitativePullbackPreorder
    violatedSetOf (violatedSetOf_monotone h_zero_min)
    (fun _ => rfl) h

end ConstraintSystem

end Core.Constraint
