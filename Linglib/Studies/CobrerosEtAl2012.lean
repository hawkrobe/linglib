import Linglib.Semantics.Supervaluation.TCS
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Cobreros, Egré, Ripley & van Rooij 2012: 4-Element Sorites Model

[cobreros-etal-2012]

The paper's worked 4-element example (described in the body text on
p. 354, immediately above footnote 4), formalized against the substrate
types in `Semantics/Supervaluation/TCS.lean`.

## The model

Four individuals `a, b, c, d` arranged in a similarity chain
`a ~ b ~ c ~ d` (with reflexivity and symmetry, no other pairs).
The classical extension of `tall` is `{a, b}`. The paper uses this
model to illustrate:

- The **extension hierarchy**: `{a} ⊆ {a,b} ⊆ {a,b,c}` (strict ⊆ classical ⊆ tolerant)
- **Borderline cases**: `b` and `c` are tolerantly tall AND tolerantly not-tall
- **Two-step tolerance limit**: `d` is NOT tolerantly tall (three steps from `a` exceeds Fact 3)
- **Sorites resolution**: each one-step inference `Pa, aIb ⊨ˢᵗ Pb` is
  valid; each two-step `Pa, aIb, bIc ⊨ˢᵗ Pc` is valid; but the
  three-step `Pa, aIb, bIc, cId ⊨ˢᵗ Pd` is **invalid**.

  Attribution: paper §3.4.1 (p. 372) demonstrates non-transitivity for
  `⊨ᶜᵗ` (the chain `Pa_1, a_1I_Pa_2, a_2I_Pa_3 ⊭ᶜᵗ Pa_3`); the `⊨ˢᵗ`
  version of the sorites is stated in §3.6 (Version 1, p. 376). The
  structural pattern — each step valid, chain fails — is §3.4.1's
  contribution; the `st`-instantiation here applies that pattern to
  the relation the paper ultimately advocates (paper p. 373).

## Cross-framework note

`tcs_supervaluation_disagree_concrete` instantiates the Theory-file
existence theorem `tcs_vs_supervaluation_borderline_contradiction` at
`(soritesModel, .tall, .b)`. Comparator caveat: the paper's headline
borderline-contradiction contrast (p. 356) is actually with **Hyde 1997
subvaluationism**, not with Fine 1975 supervaluation. Subvaluationism
*agrees* with TCS that `P ∧ ¬P` holds at borderline cases — they
disagree on framework foundations. The Lean theorem here formalises the
*formal-validity-side* contrast (p. 359) where TCS at `t` mode says ✓
and supervaluation says ✗. Subvaluationism is not formalised in linglib;
a proper "borderline-verdict comparator" theorem awaits its formalisation.

The asymmetric-engagement reciprocation: `LassiterGoodman2017PMF.lean::lg_literal_borderline_bounded`
proves L&G's literal-meaning rule predicts ≤ 25% acceptance for
borderline `tall ∧ ¬ tall`, well below the [alxatib-pelletier-2011]
empirical 44.7%. That paper's docstring cites TCS as the alternative
that handles the data; this file's `b_tolerant_contradiction` shows the
TCS prediction direction matches the data.

## Architecture

This file is anchored on the Cobreros-Egré-Ripley-van Rooij 2012 paper
itself. Per the "no bridge files" + "worked examples live in Studies, not
theory files" discipline, the worked example was extracted here from a
previous embedding inside `Semantics/Supervaluation/TCS.lean`.
-/

namespace CobrerosEtAl2012

open Semantics.Supervaluation.TCS
open Semantics.Supervaluation (SpecSpace superTrue)

-- ════════════════════════════════════════════════════
-- § 1. The 4-element domain (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- Four individuals — the elements of the paper's chain. -/
inductive Elt | a | b | c | d
  deriving Repr, DecidableEq

instance : Fintype Elt where
  elems := {.a, .b, .c, .d}
  complete x := by cases x <;> decide

/-- One vague predicate — "tall". -/
inductive VPred | tall
  deriving Repr, DecidableEq

instance : Fintype VPred where
  elems := {.tall}
  complete x := by cases x; decide

-- ════════════════════════════════════════════════════
-- § 2. Similarity relation (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- The similarity chain `a ~ b ~ c ~ d` with reflexivity + symmetry,
    nothing else. Implemented via a Bool-valued helper so the `Decidable`
    instance reduces through Bool equality, keeping the model fully
    computable for `decide`-based extension proofs. -/
def soritesSimBool : Elt → Elt → Bool
  | .a, .a => true | .a, .b => true
  | .b, .a => true | .b, .b => true | .b, .c => true
  | .c, .b => true | .c, .c => true | .c, .d => true
  | .d, .c => true | .d, .d => true
  | _, _ => false

/-- The similarity relation as a `Prop`, for direct integration with
    the modal-logic substrate's `box`/`diamond`. -/
def soritesSim (x y : Elt) : Prop := soritesSimBool x y = true

instance : DecidableRel soritesSim := λ x y =>
  inferInstanceAs (Decidable (soritesSimBool x y = true))

-- ════════════════════════════════════════════════════
-- § 3. The T-model itself (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- The paper's running 4-element model: `I(tall) = {a, b}`, similarity
    chain `a ~ b ~ c ~ d`. -/
def soritesModel : TModel Elt VPred where
  interp
    | .tall, .a => True
    | .tall, .b => True
    | .tall, .c => False
    | .tall, .d => False
  decInterp P x := by cases P; cases x <;> simp only [] <;> infer_instance
  sim _ := soritesSim
  sim_ktb _ := { refl := fun x => by cases x <;> decide
                 symm := fun x y h => by cases x <;> cases y <;> first | decide | exact h }

/-- Per-pair decidability of the model's sim relation. Needed for
    `decide`-style proofs of the extension theorems below. Since
    `soritesModel.sim P` ignores `P` (definitionally `soritesSim`),
    the instance reduces to `soritesSim`'s `DecidableRel`. The
    `DecidablePred (soritesModel.sim P x)` shape needed by `toleranceSpace`
    is auto-derived from this per-pair instance. -/
instance soritesModel_sim_dec (P : VPred) (x y : Elt) :
    Decidable (soritesModel.sim P x y) :=
  inferInstanceAs (Decidable (soritesSim x y))

-- ════════════════════════════════════════════════════
-- § 4. Atomic-level decidability (so `decide` works)
-- ════════════════════════════════════════════════════

/-- `StrictAt` is decidable on the sorites model: it's a finite
    universal over the 4 elements. -/
instance soritesModel_strict_dec (P : VPred) (x : Elt) :
    Decidable (StrictAt soritesModel P x) :=
  Fintype.decidableForallFintype

/-- `TolerantAt` is decidable on the sorites model: it's a finite
    existential. -/
instance soritesModel_tolerant_dec (P : VPred) (x : Elt) :
    Decidable (TolerantAt soritesModel P x) :=
  Fintype.decidableExistsFintype

instance soritesModel_borderline_dec (P : VPred) (x : Elt) :
    Decidable (IsBorderline soritesModel P x) :=
  inferInstanceAs (Decidable (TolerantAt soritesModel P x ∧ _))

-- ════════════════════════════════════════════════════
-- § 5. Extension verification
-- ════════════════════════════════════════════════════

/-- **Strict extension** of `tall`: `{a}` only. Other elements have
    similar individuals that aren't classically tall. -/
theorem strict_extension :
    StrictAt soritesModel .tall .a ∧
    ¬ StrictAt soritesModel .tall .b ∧
    ¬ StrictAt soritesModel .tall .c ∧
    ¬ StrictAt soritesModel .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Classical extension** of `tall`: `{a, b}` directly from `I(tall)`. -/
theorem classical_extension :
    soritesModel.interp .tall .a ∧
    soritesModel.interp .tall .b ∧
    ¬ soritesModel.interp .tall .c ∧
    ¬ soritesModel.interp .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [soritesModel]

/-- **Tolerant extension** of `tall`: `{a, b, c}`. `d` is too far from
    the classical extension to count as tolerantly tall (three steps
    from `a`, exceeding Fact 3's two-step limit). -/
theorem tolerant_extension :
    TolerantAt soritesModel .tall .a ∧
    TolerantAt soritesModel .tall .b ∧
    TolerantAt soritesModel .tall .c ∧
    ¬ TolerantAt soritesModel .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Borderline classification
-- ════════════════════════════════════════════════════

/-- `b` is borderline-tall: tolerantly tall (witness: `a`), but not
    strictly tall (counter-witness: `c`, which is similar to `b` but
    not classically tall). -/
theorem b_is_borderline : IsBorderline soritesModel .tall .b := by decide

/-- `c` is borderline-tall: tolerantly tall (witness: `b`), but not
    strictly tall (counter-witness: `d`). -/
theorem c_is_borderline : IsBorderline soritesModel .tall .c := by decide

/-- `a` is NOT borderline: strictly tall, hence not in `tolerant \ strict`. -/
theorem a_not_borderline : ¬ IsBorderline soritesModel .tall .a := by decide

/-- `d` is NOT borderline: not even tolerantly tall, hence not in `tolerant \ strict`. -/
theorem d_not_borderline : ¬ IsBorderline soritesModel .tall .d := by decide

-- ════════════════════════════════════════════════════
-- § 7. Tolerant contradictions at borderline cases (paraconsistent half)
-- ════════════════════════════════════════════════════

/-- At the borderline individual `b`, `tall ∧ ¬ tall` is **tolerantly true**
    in TCS — the paraconsistent feature. Compare with the same conjunction
    being super-FALSE in supervaluation: see §8 below. -/
theorem b_tolerant_contradiction :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .b)) (.neg (.atom (.pred .tall .b)))) := by
  exact (tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .b b_is_borderline).1

/-- Same for `c`. -/
theorem c_tolerant_contradiction :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .c)) (.neg (.atom (.pred .tall .c)))) :=
  (tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .c c_is_borderline).1

/-- At the **non-borderline** individual `a` (strictly tall), the
    contradiction `tall ∧ ¬ tall` is NOT tolerantly true. -/
theorem a_no_tolerant_contradiction :
    ¬ Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .a)) (.neg (.atom (.pred .tall .a)))) := by
  rintro ⟨_, hneg⟩
  -- hneg : ¬ Sat soritesModel .strict (.atom (.pred .tall .a))
  -- But a IS strictly tall — contradiction.
  exact hneg strict_extension.1

/-- Dually for `d` (not even tolerantly tall). -/
theorem d_no_tolerant_contradiction :
    ¬ Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .d)) (.neg (.atom (.pred .tall .d)))) := by
  rintro ⟨htol, _⟩
  exact tolerant_extension.2.2.2 htol

-- ════════════════════════════════════════════════════
-- § 8. Cross-framework divergence (TCS vs Fine 1975 supervaluation)
-- ════════════════════════════════════════════════════

/-- **Cross-framework divergence theorem**, instantiated at
    `(soritesModel, .tall, .b)`.

    On the same tolerance neighborhood `{d | b ~ d}`:
    - **TCS** says `tall(b) ∧ ¬ tall(b)` is **tolerantly true**
    - **Fine 1975 supervaluation** says it is **super-FALSE** (= `Trivalent.false`)

    The frameworks disagree on the *formal-validity-side* verdict.
    Caveat (per the file docstring): the paper's headline contrast on
    borderline contradictions (p. 356) is with **Hyde 1997
    subvaluationism**, which agrees with TCS on the verdict. Fine 1975
    supervaluation is the comparator we can formalise here because it's
    the only one of the two with a substrate in linglib. -/
theorem tcs_supervaluation_disagree_concrete :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .b)) (.neg (.atom (.pred .tall .b)))) ∧
    superTrue (λ e => soritesModel.interp .tall e && !soritesModel.interp .tall e)
      (toleranceSpace soritesModel .tall .b)
      = Trivalent.false :=
  tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .b b_is_borderline

-- ════════════════════════════════════════════════════
-- § 9. Genuine non-transitivity demonstration via similarity atoms
-- ════════════════════════════════════════════════════

/-- Named atoms used in the non-transitivity demonstration. Extracting
    them as private definitions avoids dotted-identifier elaboration
    issues in conjunctions and lists where the expected element type
    isn't propagated through the syntactic constructors. -/
private abbrev fmlPa : TCSFormula VPred Elt := .atom (.pred .tall .a)
private abbrev fmlPb : TCSFormula VPred Elt := .atom (.pred .tall .b)
private abbrev fmlPc : TCSFormula VPred Elt := .atom (.pred .tall .c)
private abbrev fmlPd : TCSFormula VPred Elt := .atom (.pred .tall .d)
private abbrev fmlIab : TCSFormula VPred Elt := .atom (.sim .tall .a .b)
private abbrev fmlIbc : TCSFormula VPred Elt := .atom (.sim .tall .b .c)
private abbrev fmlIcd : TCSFormula VPred Elt := .atom (.sim .tall .c .d)

/-! Non-transitivity in the full vocabulary with similarity predicates
    `Iₚ`. Each one-step `Pa, aIb ⊨ˢᵗ Pb` is valid (Fact 2, p. 354); each
    two-step `Pa, aIb, bIc ⊨ˢᵗ Pc` is valid (Fact 3, p. 354); but
    three-step `Pa, aIb, bIc, cId ⊨ˢᵗ Pd` is **invalid** because `d`
    requires three similarity steps from the classical extension `{a, b}`,
    exceeding Fact 3's two-step limit.

    Attribution: paper §3.4.1 (p. 372) demonstrates non-transitivity for
    `⊨ᶜᵗ` (the chain `Pa_1, a_1I_Pa_2, a_2I_Pa_3 ⊭ᶜᵗ Pa_3`), and
    footnote 14 formalises the simple-transitivity statement. The `⊨ˢᵗ`
    sorites version is in §3.6 (Version 1, p. 376). The structural
    pattern (each step valid, chain fails) is §3.4.1's contribution; the
    `st`-instantiation here transfers it to the relation the paper
    advocates. -/

/-- **One-step st-validity**, instantiated to the model: `tall(a), aIb ⊨ˢᵗ tall(b)`.
    The schema theorem `Semantics.Supervaluation.TCS.st_one_step_valid` instantiates here. -/
theorem st_one_step_a_to_b :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab] fmlPb :=
  st_one_step_valid (P := VPred.tall) (a := Elt.a) (b := Elt.b)

/-- **Two-step st-validity**: `tall(a), aIb, bIc ⊨ˢᵗ tall(c)`. -/
theorem st_two_step_a_to_c :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab, fmlIbc] fmlPc :=
  st_two_step_valid (P := VPred.tall) (a := Elt.a) (b := Elt.b) (c := Elt.c)

/-- **Three-step st-INVALIDITY**: `tall(a), aIb, bIc, cId ⊭ˢᵗ tall(d)`.

    Each step is individually st-valid (above), but the chain of three
    exhausts the two-step tolerance limit (Fact 3, p. 354), so the
    conclusion fails to hold even tolerantly at `d`. Structural pattern
    of paper §3.4.1; paper itself states the `⊨ᶜᵗ` version there and
    the `⊨ˢᵗ` sorites Version 1 in §3.6 (p. 376). -/
theorem st_three_step_invalid :
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab, fmlIbc, fmlIcd] fmlPd := by
  intro h
  have hprem : ∀ γ ∈ [fmlPa, fmlIab, fmlIbc, fmlIcd],
      Sat soritesModel .strict γ := by
    intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact strict_extension.1
    all_goals (simp only [Sat.atom_sim]; decide)
  exact tolerant_extension.2.2.2 (h soritesModel hprem)

/-- Convenience packaging: the chain of one-step + two-step st-valid
    inferences cannot be extended to three steps, even though each
    constituent step is valid. -/
theorem st_chain_breaks_at_step_three :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab] fmlPb ∧
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab, fmlIbc] fmlPc ∧
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab, fmlIbc, fmlIcd] fmlPd :=
  ⟨st_one_step_a_to_b, st_two_step_a_to_c, st_three_step_invalid⟩

-- ════════════════════════════════════════════════════
-- § 10. Cross-framework reciprocations (Lean-checkable)
-- ════════════════════════════════════════════════════

/-! Two Lean-checkable cross-framework theorems that close gaps flagged
    by the cross-framework reconciler:

    1. **TCS-vs-product-rule expressivity gap**: TCS predicts borderline
       contradictions *categorically* (the conjunction is true, not
       fractional); any framework that predicts them as a product of
       complementary probabilities is *fractionally bounded* by 1/4
       (AM-GM). The architectural divergence between TCS and L&G's
       literal rule is structural, not parametric.
    2. **Klein-delineation tension**: in `soritesModel`, two adjacent
       individuals are tolerantly similar AND both borderline, yet
       classically separated — exactly the configuration where any
       sound Klein delineation would over-impose a scalar relation. -/

/-- **TCS predicts borderline contradictions categorically.** Helper:
    for any T-model `M`, predicate `P`, and individual `a` that is
    borderline-`P`, the conjunction `P(a) ∧ ¬P(a)` is tolerantly true.
    Extracted from the TCS half of
    `tcs_vs_supervaluation_borderline_contradiction`. -/
theorem tcs_borderline_contradiction_categorical
    {D' Pred' : Type*} (M : TModel D' Pred') (P : Pred') (a : D')
    (hb : IsBorderline M P a) :
    Sat M .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) := by
  refine ⟨hb.1, ?_⟩
  simp only [Sat.neg_eq, SatMode.dual, Sat.atom_strict_pred]
  exact hb.2

/-- **TCS-vs-product-rule framework expressivity gap.** A framework-level
    contrast theorem with two simultaneous halves, witnessing that TCS
    and any "literal rule = product of complementary probabilities"
    framework (paradigmatically L&G:
    `Studies/LassiterGoodman2017PMF.lean::lg_literal_borderline_bounded`)
    diverge structurally on borderline contradictions:

    - **TCS half**: the conjunction `P(a) ∧ ¬P(a)` is tolerantly TRUE
      (not fractional) at every borderline `a`. This is a categorical
      framework prediction — independent of any parameter.
    - **Product-rule half**: any product `q · (1 - q)` for `q ∈ [0, 1]`
      is bounded above by `1/4` (AM-GM). This is the framework-level
      ceiling on any literal-meaning rule that multiplies a probability
      by its complement. L&G's `lg_literal_borderline_bounded` is the
      `PMF`-typed instance of this generic bound.

    The empirical Alxatib-Pelletier 2011 acceptance rate (44.7% — see
    the [alxatib-pelletier-2011] contrast section of
    `Studies/LassiterGoodman2017PMF.lean`)
    exceeds the product-rule's 25% ceiling, refuting the literal-rule
    framework empirically. TCS's categorical prediction is consistent
    with the empirical direction without committing to any specific
    fractional value. The structural divergence is what's interesting:
    L&G's framework architecture *cannot represent* the empirical
    direction (any literal-rule PMF is bounded ≤ 25%); TCS's framework
    architecture predicts it categorically. -/
theorem tcs_categorical_vs_product_bounded
    {D' Pred' : Type*} (M : TModel D' Pred') (P : Pred') (a : D')
    (hb : IsBorderline M P a) (q : ℝ) :
    Sat M .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) ∧
    q * (1 - q) ≤ (1 / 4 : ℝ) := by
  refine ⟨tcs_borderline_contradiction_categorical M P a hb, ?_⟩
  -- (q - 1/2)² ≥ 0 expands to q² - q + 1/4 ≥ 0 ⟹ q(1-q) ≤ 1/4 for ALL real q
  -- (no [0, 1] constraint needed — the bound is universal).
  nlinarith [sq_nonneg (q - 1/2)]

/-- **Klein-delineation tension witness**: in `soritesModel`, the
    individuals `b` and `c` are both borderline-tall AND tolerantly
    similar (`b ~_tall c`), yet classically separated (b is classically
    tall, c is classically not-tall). Any Klein-style sound delineation
    derived from `M.interp .tall` would impose a scalar relation
    `R b c` on this pair (per
    `Semantics/Degree/Delineation.lean::IsSoundDelineation`),
    over-generating where TCS says `b` and `c` are *both equally
    borderline* and the scalar relation should be unwarranted.

    This is the Lean-checkable witness for the prose tension flagged at
    `Comparison/Delineation.lean` lines 566-571. -/
theorem klein_delineation_tension_concrete :
    -- Both are borderline:
    IsBorderline soritesModel .tall .b ∧
    IsBorderline soritesModel .tall .c ∧
    -- They are tolerantly similar:
    soritesModel.sim .tall .b .c ∧
    -- Yet classically separated:
    soritesModel.interp .tall .b ∧
    ¬ soritesModel.interp .tall .c :=
  ⟨b_is_borderline, c_is_borderline, by decide, by simp [soritesModel], by simp [soritesModel]⟩

-- ════════════════════════════════════════════════════
-- § 11. Single-premise sorites unsoundness
-- ════════════════════════════════════════════════════

/-- Single-premise sorites unsoundness (the previous formalization's
    `sorites_chain_invalid`). Subsumed by `st_three_step_invalid` above
    but kept under the historical name. -/
theorem sorites_chain_invalid :
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [.atom (.pred .tall .a)] (.atom (.pred .tall .d)) := by
  intro h
  have hprem : ∀ γ ∈ [(.atom (.pred .tall .a) : TCSFormula VPred Elt)],
      Sat soritesModel .strict γ := by
    intro γ hγ
    simp at hγ
    subst hγ
    exact strict_extension.1
  have hconc := h soritesModel hprem
  exact tolerant_extension.2.2.2 hconc

end CobrerosEtAl2012
