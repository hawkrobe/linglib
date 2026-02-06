import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity

/-!
# Causative Builder

Links causative verb lexical entries to their compositional semantics in
Nadathur & Lauer (2020), following the same pattern as `PreferentialBuilder`
for attitude verbs.

## Design principle

Properties like "asserts sufficiency" or "asserts necessity" are **derived**
from the builder via theorems, not stipulated as tags. The builder names
the semantic analysis; `toSemantics` provides the actual truth-condition
computation.

| Builder | Verb | Semantic Fn | Core Test |
|---------|------|-------------|-----------|
| sufficiency | make, let, have, get, force | `makeSem` | Adding C → E guaranteed |
| necessity | cause | `causeSem` | Removing C → E blocked |

## References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa 5(1), 49.
-/

namespace Theories.NadathurLauer2020.Builder

open Core.CausalModel
open Theories.NadathurLauer2020.Sufficiency
open Theories.NadathurLauer2020.Necessity

/-- How a causative verb's semantics is built from causal model infrastructure.

    Like `PreferentialBuilder` for attitude verbs, this links lexical entries
    to their compositional semantics. The builder names a semantic analysis
    from Nadathur & Lauer (2020); `toSemantics` maps it to the actual
    truth-condition function.

    - `sufficiency`: "make"-type verbs. The cause guaranteed the effect.
    - `necessity`: "cause"-type verbs. The effect counterfactually depended
      on the cause. -/
inductive CausativeBuilder where
  /-- Sufficiency semantics (Def 23): cause guaranteed effect.
      Semantic function: `makeSem`. -/
  | sufficiency
  /-- Necessity semantics (Def 24): effect depended on cause.
      Semantic function: `causeSem`. -/
  | necessity
  deriving DecidableEq, Repr, BEq

/-- Map a causative builder to its semantic function.

    This is the structural link between the lexical annotation and the
    formal semantics: the builder NAMES the semantic analysis, and this
    function provides the actual truth-condition computation. -/
def CausativeBuilder.toSemantics : CausativeBuilder →
    (CausalDynamics → Situation → Variable → Variable → Bool)
  | .sufficiency => makeSem
  | .necessity => causeSem

/-! ## Derivation theorems

These theorems show that properties of causative verbs follow from
the builder's semantics, rather than being independently stipulated. -/

/-- Sufficiency builders compute truth conditions via `makeSem`. -/
theorem sufficiency_semantics :
    CausativeBuilder.sufficiency.toSemantics = makeSem := rfl

/-- Necessity builders compute truth conditions via `causeSem`. -/
theorem necessity_semantics :
    CausativeBuilder.necessity.toSemantics = causeSem := rfl

/-- When a sufficiency builder's semantics holds, the cause is
    causally sufficient for the effect.

    This is DERIVED: it follows from the fact that `makeSem` is defined
    as `causallySufficient`. -/
theorem sufficiency_implies_causallySufficient
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : CausativeBuilder.sufficiency.toSemantics dyn s c e = true) :
    causallySufficient dyn s c e = true := h

/-- When a necessity builder's semantics holds, the cause is
    causally necessary for the effect.

    DERIVED from the fact that `causeSem` conjoins occurrence
    with `causallyNecessary`. -/
theorem necessity_implies_causallyNecessary
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : CausativeBuilder.necessity.toSemantics dyn s c e = true) :
    causallyNecessary dyn s c e = true := by
  simp only [CausativeBuilder.toSemantics, causeSem, Bool.and_eq_true] at h
  exact h.2

/-- The two builders produce genuinely different truth conditions.

    Witnessed by the overdetermination scenario (lightning + arsonist):
    `makeSem` returns true (lightning sufficient) but `causeSem` returns
    false (lightning not necessary). -/
theorem builders_truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      CausativeBuilder.sufficiency.toSemantics dyn s c e ≠
      CausativeBuilder.necessity.toSemantics dyn s c e := by
  -- Overdetermination: lightning ∨ arsonist → fire, with arsonist in background
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.disjunctiveCausation a b c
  let s := Situation.empty.extend b true
  use dyn, s, a, c
  simp only [CausativeBuilder.toSemantics, ne_eq]
  native_decide

end Theories.NadathurLauer2020.Builder
