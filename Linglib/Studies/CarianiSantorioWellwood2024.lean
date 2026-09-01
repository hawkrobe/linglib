import Linglib.Semantics.Attitudes.Confidence
import Linglib.Semantics.Attitudes.EpistemicThreshold
import Linglib.Studies.Wellwood2015

/-!
# Cariani, Santorio and Wellwood 2024: confidence reports

This file formalizes the argument of [cariani-santorio-wellwood-2024] that *confident* and
*confidence* are gradable predicates of confidence states rather than thresholds on credence. The
states-based semantics is `Confidence.ConfidenceOrdering`: one preorder per holder, ranking that
holder's states across themes, on which *confident*, *certain* and *doubts* differ only in a
contrast point. The positive form is membership in the region a contrast point cuts out, so no
covert positive morpheme is needed (§3.3), and the comparative sees only the ordering, so *more
confident* and *more certain* come out equivalent (72).

Because the ordering ranks states and not their contents, it is not required to respect
conjunction, and the paper takes the Tversky–Kahneman conjunction fallacy ([tversky-kahneman-1983];
*John is not confident that Linda is a bankteller* alongside *John is confident that Linda is a
feminist bankteller*, (52)) to be the datum that separates it from a threshold on probabilistic
credence, which validates conjunction elimination by monotonicity.

The logic the ordering does validate is proved of the ordering itself in
`Semantics/Attitudes/Confidence.lean`: transitivity (54) and antisymmetry (55) of the comparative,
upward monotonicity (53), the asymmetric entailment from *certain* to *confident* (65)–(66), and
its incompatibility with *doubts* (63). Connectedness (56) is not among them — the paper remains
agnostic about whether (58) is incoherent, which is why the ordering is a `Preorder` rather than a
linear order.

## Main results

* `exists_conjunction_fallacy_credence` — a credence ranking a consistent conjunction above one of
  its conjuncts
* `not_conjunction_fallacy_of_probabilistic` — no probabilistic credence does, at any threshold
* `confidence_comparative_reduces` — [wellwood-2015]'s cross-categorial comparative, specialized
  to confidence states, is comparison of their measures

## References

* [cariani-santorio-wellwood-2024]
* [wellwood-2015]
* [tversky-kahneman-1983]
-/

namespace CarianiSantorioWellwood2024

open Degree Confidence
open EpistemicThreshold (IsProbabilistic meetsThreshold)

/-! ### The conjunction fallacy -/

/-- A credence that ranks a consistent conjunction strictly above one of its conjuncts, as (52)
describes. A confidence ordering permits this because it ranks states, not contents. -/
theorem exists_conjunction_fallacy_credence :
    ∃ cr : Unit → Set Bool → ℚ,
      ¬ IsProbabilistic cr ∧ ∃ φ ψ : Set Bool, cr () φ < cr () (φ ∩ ψ) := by
  classical
  refine ⟨fun _ p => if false ∈ p then (0 : ℚ) else 1, ?_, Set.univ, {true}, ?_⟩
  · intro h
    have h1 := h () (Set.subset_univ ({true} : Set Bool))
    simp at h1
    exact absurd h1 (by norm_num)
  · simp

/-- No probabilistic credence ranks a conjunction above a conjunct, so a threshold on such a
credence cannot report the fallacy at any threshold. This is the prediction the states-based
account is designed to escape. -/
theorem not_conjunction_fallacy_of_probabilistic {E W : Type*} {cr : E → Set W → ℚ}
    (h : IsProbabilistic cr) (a : E) (φ ψ : Set W) : ¬ cr a φ < cr a (φ ∩ ψ) :=
  not_lt.2 (h a Set.inter_subset_left)

/-- The threshold account's verdict on (52) in report form: whenever the conjunctive report holds,
so does the report of the conjunct. -/
theorem meetsThreshold_of_meetsThreshold_inter {E W : Type*} {cr : E → Set W → ℚ}
    (h : IsProbabilistic cr) (θ : ℚ) (a : E) (φ ψ : Set W) :
    meetsThreshold cr θ a (φ ∩ ψ) → meetsThreshold cr θ a φ :=
  fun hθ => hθ.trans (h a Set.inter_subset_left)

/-! ### The comparative -/

/-- [wellwood-2015]'s cross-categorial comparative, instantiated for confidence states, is
comparison of the two states' measures whenever each holder has a unique state of the relevant
kind — the compositional half of the claim that nominal *confidence* and adjectival *confident*
are interchangeable in the comparative. -/
theorem confidence_comparative_reduces
    {E : Type*} {T : Type*} [LinearOrder T]
    {frame : ArgumentStructure.ThematicFrame E T}
    {P : Event T → Prop}
    {μ : Event T → ℚ}
    {a b : E} {sa sb : Event T}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    Wellwood2015.adjectivalComparative frame P μ a b ↔ μ sb < μ sa :=
  Degree.maxComparative_unique ha (fun s hs => ha_unique s hs.1 hs.2)
    hb (fun s hs => hb_unique s hs.1 hs.2)

end CarianiSantorioWellwood2024
