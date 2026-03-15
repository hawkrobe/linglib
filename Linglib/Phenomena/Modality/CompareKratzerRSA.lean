import Linglib.Core.Scales.Scale
import Linglib.Core.Scales.EpistemicScale
import Linglib.Theories.Semantics.Modality.Kratzer.Ordering
import Linglib.Theories.Semantics.Modality.ProbabilityOrdering
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Kratzer–Epistemic–RSA Bridge
@cite{holliday-icard-2013} @cite{kraft-pratt-seidenberg-1959} @cite{kratzer-1981} @cite{kratzer-2012}

This file traces the dependency chain from Kratzer's ordering source
semantics down to RSA's `worldPrior`, via @cite{holliday-icard-2013}
epistemic likelihood logics:

```
Kratzer ordering source A : List (BProp World)
    ↓ atLeastAsGoodAs (subset inclusion on satisfied propositions)
World preorder ge_w : World → World → Prop
    ↓ halpernLift (Lewis's l-lifting)
EpistemicSystemW
    ↓ + totality, transitivity, additivity
EpistemicSystemFA
    ↓ theorem8a (|World4| = 4 < 5, so FA = FP∞)
FinAddMeasure
    ↓ mu {w} → worldPrior
RSAConfig.worldPrior
```

An alternative, more direct path is provided by @cite{fagin-halpern-1994}'s
`KripkeKP` (see `Modality/KnowledgeProbability.lean`): a Kripke probability
structure packages both the accessibility relation and the probability
assignment. Under CONS, knowledge and probability-1 belief coincide
(`knows_implies_prob_one`), giving a single structure that serves both
the epistemic logic layer and the RSA prior.

§1 is definitions (no sorry). §3 constructs the pipeline via `theorem8a`.
§4 witnesses the round-trip with `P` itself.

-/

namespace Phenomena.Modality.CompareKratzerRSA

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional
open Core.Scale

-- World = World4 has 4 elements; needed by theorem8a
private instance : Fintype World :=
  ⟨{.w0, .w1, .w2, .w3}, fun x => by cases x <;> decide⟩

-- ══════════════════════════════════════════════════════════════════════
-- §1. Kratzer ordering → EpistemicSystemW (definition, no sorry)
-- ══════════════════════════════════════════════════════════════════════

/-- Convert Kratzer's Bool-valued `atLeastAsGoodAs` to a Prop-valued
    world preorder, suitable for `halpernLift`. -/
def kratzerWorldGe (A : List (BProp World)) (w z : World) : Prop :=
  atLeastAsGoodAs A w z = true

/-- Kratzer's ordering is reflexive (Prop version). -/
theorem kratzerWorldGe_refl (A : List (BProp World)) (w : World) :
    kratzerWorldGe A w w :=
  ordering_reflexive A w

/-- Applying Lewis's l-lifting to Kratzer's world ordering yields
    EpistemicSystemW. This connects Kratzer modal semantics to
    Holliday & Icard's weakest epistemic likelihood logic. -/
def kratzerToSystemW (A : List (BProp World)) : EpistemicSystemW World :=
  halpernSystemW (kratzerWorldGe A) (kratzerWorldGe_refl A)

-- ══════════════════════════════════════════════════════════════════════
-- §3. The Kratzer–RSA pipeline
-- ══════════════════════════════════════════════════════════════════════

/-- For `World` (= `World4`, 4 elements), if a Kratzer ordering source
    induces an l-lifted system that satisfies the FA axioms (totality,
    transitivity, qualitative additivity, non-triviality), then by
    Kraft–Pratt–Seidenberg (`theorem8a`, since |World4| = 4 < 5), the
    system is representable by a finitely additive measure, yielding
    an RSA world prior.

    The key gap is that not every Kratzer ordering source yields an
    l-lifted system satisfying FA — the hypotheses capture the
    additional conditions needed. -/
theorem kratzer_to_rsa_prior
    (A : List (BProp World))
    (hFA : ∀ (A' B' : Set World),
      (kratzerToSystemW A).ge A' B' ∨ (kratzerToSystemW A).ge B' A')
    (hTrans : ∀ (A' B' C' : Set World),
      (kratzerToSystemW A).ge A' B' → (kratzerToSystemW A).ge B' C' →
      (kratzerToSystemW A).ge A' C')
    (hAdd : EpistemicAxiom.A (kratzerToSystemW A).ge)
    (hBT : EpistemicAxiom.BT (kratzerToSystemW A).ge) :
    ∃ (prior : World → ℚ), ∀ w, 0 ≤ prior w := by
  -- Construct EpistemicSystemFA from the l-lifted system + FA hypotheses.
  -- Axiom F (bottom) is vacuously true: halpernLift _ Set.univ ∅ holds
  -- because ∅ has no elements to dominate.
  let sys : EpistemicSystemFA World := {
    ge := (kratzerToSystemW A).ge
    refl := (kratzerToSystemW A).refl
    mono := (kratzerToSystemW A).mono
    bottom := fun _ hb => hb.elim
    nonTrivial := hBT
    total := hFA
    trans := hTrans
    additive := hAdd
  }
  have hcard : Fintype.card World < 5 := by decide
  obtain ⟨m, _⟩ := theorem8a sys hcard
  exact ⟨m.toWorldPrior, m.toWorldPrior_nonneg⟩

-- ══════════════════════════════════════════════════════════════════════
-- §4. ProbabilityOrdering round-trip
-- ══════════════════════════════════════════════════════════════════════

open Semantics.Modality.ProbabilityOrdering in
/-- The probability-ordering round-trip is consistent: there exists a
    non-negative prior preserving the probability ordering.

    As stated, the existential is witnessed by `P` itself (positive →
    non-negative, and the ordering condition is trivial). The `hFA`
    hypothesis is unused because the statement doesn't require the
    prior to come from the `theorem8a` pipeline.

    TODO: Strengthen to require `prior` = `toWorldPrior` of the
    measure produced by `theorem8a` applied to the l-lifted system
    from `probToOrdering P`. -/
theorem prob_ordering_roundtrip
    (P : ProbAssignment)
    (_w₀ : World)
    (hPos : ∀ w, 0 < P w)
    (_hFA : ∀ (A B : Set World),
      (kratzerToSystemW ((probToOrdering P) _w₀)).ge A B ∨
      (kratzerToSystemW ((probToOrdering P) _w₀)).ge B A) :
    ∃ (prior : World → ℚ),
      (∀ w, 0 ≤ prior w) ∧
      (∀ w z : World, P w ≥ P z → prior w ≥ prior z) :=
  ⟨P, fun w => le_of_lt (hPos w), fun _ _ h => h⟩

end Phenomena.Modality.CompareKratzerRSA
