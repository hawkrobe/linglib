/-!
# Causative and implicative verb features

This file defines two classifications carried by verb lexical entries:
`Causative`, the force-dynamic mechanism a causative verb lexicalizes, and
`Implicative`, the polarity of an implicative verb's complement entailment.

## References

* [Lauri Karttunen, *Implicative Verbs*][karttunen-1971]
* [Prerna Nadathur and Sven Lauer, *Causal Necessity, Causal Sufficiency, and
  the Implications of Causative Verbs*][nadathur-lauer-2020]
* [Leonard Talmy, *Force dynamics in language and cognition*][talmy-1988]
* [Phillip Wolff, *Direct causation in the linguistic coding and individuation
  of causal events*][wolff-2003]
-/

/-! ### Force-dynamic causatives -/

/-- Force-dynamic classification of causative verbs by the causal mechanism
the verb lexicalizes. `Causative.toSemantics` (in
`Semantics/Causation/Interpretation.lean`) maps each variant to its truth
conditions. -/
inductive Causative where
  /-- Counterfactual dependence: removing the cause blocks the effect (*cause*). -/
  | cause
  /-- Direct sufficient guarantee: adding the cause ensures the effect (*make*). -/
  | make
  /-- Coercive sufficiency: the causer overcomes the causee's resistance (*force*). -/
  | force
  /-- Permissive: the causer removes a barrier so the effect can occur (*let*). -/
  | enable
  /-- Blocking: the causer adds a barrier so the effect cannot occur (*prevent*). -/
  | prevent
  deriving DecidableEq, Repr

namespace Causative

/-- The variant asserts causal sufficiency: `make`, `force`, and `enable`
share sufficiency truth conditions (`AssertsSufficiency.toSemantics_eq`). -/
def AssertsSufficiency (b : Causative) : Prop :=
  b = make ∨ b = force ∨ b = enable

instance : DecidablePred AssertsSufficiency := fun b => by
  unfold AssertsSufficiency; infer_instance

end Causative

/-! ### Implicative polarity -/

/-- Polarity for implicative verbs: positive implicatives entail their
complement, negative implicatives entail its negation. -/
inductive Implicative where
  /-- The verb entails its complement (*manage*, *remember*). -/
  | positive
  /-- The verb entails the negation of its complement (*fail*, *forget*). -/
  | negative
  deriving DecidableEq, Repr
