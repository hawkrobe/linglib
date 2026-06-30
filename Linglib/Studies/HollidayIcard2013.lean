import Linglib.Core.Order.ComparativeProbability.Entailments
import Linglib.Core.Order.ComparativeProbability.Completeness

/-!
# Holliday & Icard (2013): Measure semantics for epistemic comparatives

[holliday-icard-2013] ask which semantics for the epistemic comparative
*at least as likely as* matches speakers' inference judgments. The benchmark
is measure semantics: *φ is at least as likely as ψ* is true iff μ(φ) ≥ μ(ψ)
for a probability measure μ over the worlds compatible with the relevant
evidence.

The paper's argument, formalized on the `Core/Scales/EpistemicScale` substrate:

1. **The disjunction problem** (Fact 1). Kratzer-style world-ordering
   semantics — the *l*-lifting of a world order to propositions, due to
   [lewis-1973] — validates the patterns I1–I3 that measure semantics
   refutes. I1 is the signature case: from *φ ≿ ψ* and *φ ≿ χ* it licenses
   *φ ≿ ψ ∨ χ*, predicting that a fair die's showing one is at least as
   likely as its showing an even number. (`disjunction_problem`,
   `measures_refute_I_patterns`)
2. **The m-lifting repair** (Fact 5). Requiring *distinct* dominating
   witnesses — an injection rather than a choice function — yields a lifting
   that agrees with measure semantics on every pattern in the paper's
   Figure 1. (`mLift_validates_V11_V12_V13`, `mLift_refutes_I_patterns`)
3. **Completeness for qualitative additivity** (Theorem 6; [van-der-hoek-1996]).
   The logic FA is sound and complete for qualitatively additive measures.
   (`fa_qualAdd_complete`)
4. **FA vs. finite additivity** (Theorem 8; [kraft-pratt-seidenberg-1959]).
   FA and the finitely-additive logic FP∞ coincide exactly below five worlds:
   the KPS ordering separates them at every |W| ≥ 5.
   (`fa_representable_iff_card_lt_five`)

See also [yalcin-2010] for the inference-pattern inventory V1–V13/I1–I3 and
[halpern-2003] for the l-lifting's completeness.
-/

namespace HollidayIcard2013

open ComparativeProbability ComparativeProbability

/-! ### Fact 1: the disjunction problem -/

/-- **Fact 1** (the disjunction problem): the l-lifting of any reflexive world
    order validates all three measure-invalid patterns I1–I3. -/
theorem disjunction_problem {W : Type*} (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    patternI1 (dominationLift ge_w) ∧ patternI2 (dominationLift ge_w) ∧
    patternI3 (dominationLift ge_w) :=
  ⟨dominationLift_I1 ge_w, dominationLift_I2 ge_w hRefl, dominationLift_I3 ge_w hRefl⟩

/-- Measure semantics refutes each of I1–I3 (uniform measure on three worlds). -/
theorem measures_refute_I_patterns :
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI1 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI2 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI3 m.inducedGe) :=
  ⟨measure_not_I1, measure_not_I2, measure_not_I3⟩

/-- The l-lifting also misses two valid patterns: V11 and V13 fail. -/
theorem lLift_refutes_V11_V13 :
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV11 (dominationLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV13 (dominationLift ge_w)) :=
  ⟨dominationLift_not_V11, dominationLift_not_V13⟩

/-! ### Fact 5: the m-lifting matches measure semantics -/

/-- **Fact 5**, validity half: on a finite preorder the m-lifting validates the
    distinctive patterns V11–V13 (V1–V7 hold for any world relation). -/
theorem mLift_validates_V11_V12_V13 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV11 (matchingLift ge_w) ∧ patternV12 (matchingLift ge_w) ∧
    patternV13 (matchingLift ge_w) :=
  ⟨matchingLift_V11 ge_w hRefl hTrans, matchingLift_V12 ge_w hRefl hTrans,
   matchingLift_V13 ge_w hRefl⟩

/-- **Fact 5**, invalidity half: the m-lifting refutes I1–I3, dissolving the
    disjunction problem. -/
theorem mLift_refutes_I_patterns :
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI1 (matchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI2 (matchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI3 (matchingLift ge_w)) :=
  ⟨matchingLift_not_I1, matchingLift_not_I2, matchingLift_not_I3⟩

/-! ### Theorem 6: completeness for qualitatively additive measures -/

/-- **Theorem 6** ([van-der-hoek-1996]): every FA system is represented by a
    qualitatively additive measure. -/
theorem fa_qualAdd_complete {W : Type*} [Fintype W] (sys : EpistemicSystemFA W) :
    ∃ m : QualAddMeasure ℚ W, ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  exists_qualAddMeasure_repr sys

/-! ### Theorem 8: FA = FP∞ exactly below five worlds -/

/-- **Theorem 8** ([kraft-pratt-seidenberg-1959]): every FA system on `Fin n`
    is representable by a finitely additive measure iff `n < 5`. -/
theorem fa_representable_iff_card_lt_five (n : ℕ) :
    (∀ sys : EpistemicSystemFA (Fin n), Representable sys) ↔ n < 5 :=
  ⟨fun h => by_contra fun hge =>
      let ⟨sys, hsys⟩ := exists_nonrepresentable_fin (n := n) (by omega); hsys (h sys),
    fun h sys => representable_of_card_lt_five sys (by simpa using h)⟩

end HollidayIcard2013
