import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.ThreeValuedLogic
import Linglib.Theories.Semantics.Presupposition.Heritage
import Linglib.Theories.Semantics.Presupposition.Accommodation
import Linglib.Theories.Semantics.Presupposition.DynamicBridge
import Linglib.Theories.Semantics.Presupposition.LocalContext

/-!
# Beaver (2001) @cite{beaver-2001}

Presupposition and Assertion in Dynamic Semantics: A Critical Review of
Linguistic Theories of Presupposition. CSLI Publications.

## Overview

Beaver's monograph is a comprehensive comparison of four families of
presupposition theory:

1. **Multivalence** (Ch. 2): Strong Kleene, Weak Kleene, Middle Kleene,
   supervaluation, partial functions
2. **Cancellation and filtering** (Ch. 3): Karttunen's heritage conditions,
   Heim's CCP
3. **Dynamic semantics** (Ch. 4): File Change Semantics, DPL, Update Semantics
4. **Accommodation** (Ch. 5): Lewis 1979, van der Sandt 1992, Fauconnier

Part II develops ABLE (Assertion-Based Logic for English), Beaver's own
dynamic presupposition logic with lexical presupposition-assertion separation.

## What We Formalize

- The symmetry problem for disjunction (trivalent vs. CCP predictions)
- Bridge theorems connecting heritage functions to filtering connectives
- Accommodation as the missing piece for deriving SCF
- Heim's observation: global accommodation preference ≈ Gazdar cancellation
- Conditional presupposition examples
-/

namespace Phenomena.Presupposition.Studies.Beaver2001

open Core.Duality
open Core.Presupposition
open Core.Proposition
open Core.Logic.ThreeValuedLogic

-- ══════════════════════════════════════════════════════════
-- § 1. The Symmetry Problem (@cite{beaver-2001} Ch. 2)
-- ══════════════════════════════════════════════════════════

/-! Strong Kleene disjunction is symmetric: `join a b = join b a`.
Middle Kleene disjunction is NOT: `joinMiddle a b ≠ joinMiddle b a` in general.
Natural language disjunction appears to be symmetric for presupposition
projection (both disjuncts can satisfy each other's presuppositions), which
favors the SK/heritage prediction over the CCP prediction. -/

/-- SK disjunction is symmetric for presupposition projection.
    @cite{beaver-2001} Ch. 2: this is the correct empirical prediction
    for natural language disjunction. -/
theorem sk_disjunction_symmetric (a b : Truth3) :
    Truth3.join a b = Truth3.join b a := by
  cases a <;> cases b <;> rfl

/-- MK disjunction is NOT symmetric.
    @cite{beaver-2001} Ch. 2: the asymmetry of MK captures
    left-to-right processing but overpredicts for disjunction. -/
theorem mk_disjunction_asymmetric :
    ∃ a b : Truth3, Truth3.joinMiddle a b ≠ Truth3.joinMiddle b a :=
  ⟨.true, .indet, by simp [Truth3.joinMiddle, Truth3.join]⟩

-- ══════════════════════════════════════════════════════════
-- § 2. Three Approaches Agree on Conditionals
-- (@cite{beaver-2001} Ch. 3)
-- ══════════════════════════════════════════════════════════

/-! Beaver shows that for conditionals, heritage functions, filtering
connectives, and CCP all make the same prediction: the consequent's
presupposition is filtered when the antecedent entails it. -/

/-- Heritage, filtering, and local contexts all agree on conditional
    presupposition projection. This is the core convergence result
    of @cite{beaver-2001} Chs. 2–4. -/
theorem conditional_projection_convergence (p q : PrProp W) :
    -- Heritage = filtering presupposition (by definition)
    Semantics.Presupposition.Heritage.heritageConditional.heritage p q =
    (PrProp.impFilter p q).presup :=
  Semantics.Presupposition.Heritage.heritage_eq_impFilter_presup p q

-- ══════════════════════════════════════════════════════════
-- § 3. Accommodation and Cancellation
-- (@cite{beaver-2001} Ch. 5.8.1)
-- ══════════════════════════════════════════════════════════

/-! Heim's observation: a preference for global over local accommodation
is equivalent to Gazdar's assumption that cancellation occurs only
under threat of inconsistency. -/

/-- Heim's synthesis: global preference selects global when consistent.
    This matches Karttunen's projection prediction. -/
theorem heim_synthesis_projection (c : Core.CommonGround.ContextSet W)
    (presup : BProp W)
    (h : Core.CommonGround.ContextSet.nonEmpty
           (Semantics.Presupposition.Accommodation.globalAccommodate c presup)) :
    Semantics.Presupposition.Accommodation.heimSelect c presup =
    .global :=
  Semantics.Presupposition.Accommodation.heim_projection_when_consistent c presup h

/-- Heim's synthesis: global preference selects local when inconsistent.
    This matches Gazdar's cancellation prediction. -/
theorem heim_synthesis_cancellation (c : Core.CommonGround.ContextSet W)
    (presup : BProp W)
    (h : ¬Core.CommonGround.ContextSet.nonEmpty
           (Semantics.Presupposition.Accommodation.globalAccommodate c presup)) :
    Semantics.Presupposition.Accommodation.heimSelect c presup =
    .local :=
  Semantics.Presupposition.Accommodation.heim_cancellation_equivalence c presup h

-- ══════════════════════════════════════════════════════════
-- § 4. Conditional Presuppositions
-- (@cite{beaver-2001} Ch. 5.6)
-- ══════════════════════════════════════════════════════════

/-! Beaver argues that presuppositions can themselves be conditional.

Example E154: "If Spaceman Spiff lands on Planet X, he will be
bothered by the fact that his weight is greater than it would be on Earth."

The presupposition (Spiff's weight > Earth weight) is not an unconditional
global presupposition — it is conditional on the antecedent (landing on
Planet X). Neither filtering, CCP, nor structural accommodation can
systematically produce conditional presuppositions. -/

/-- A world type for the Spaceman Spiff scenario. -/
inductive SpiffWorld where
  | onEarth           -- Spiff is on Earth (normal weight)
  | onPlanetX_heavy   -- Spiff landed on Planet X, heavier than on Earth
  | onPlanetX_light   -- Spiff landed on Planet X, lighter than on Earth
  | inSpace           -- Spiff is in space (weightless)
  deriving DecidableEq, Repr, Inhabited

/-- "Spiff lands on Planet X" — no presupposition. -/
def spiffLands : PrProp SpiffWorld where
  presup := λ _ => true
  assertion := λ w => match w with
    | .onPlanetX_heavy | .onPlanetX_light => true
    | _ => false

/-- "Spiff's weight is greater than on Earth" — presupposes being
    somewhere with weight (not in space). -/
def weightGreater : PrProp SpiffWorld where
  presup := λ w => match w with
    | .inSpace => false
    | _ => true
  assertion := λ w => match w with
    | .onPlanetX_heavy => true
    | _ => false

/-- Filtering correctly predicts: the conditional "if Spiff lands, he'll
    be bothered by fact that weight > Earth" does NOT globally presuppose
    that weight > Earth. The antecedent "Spiff lands" filters the
    presupposition to: "if Spiff lands, his weight is defined." -/
theorem spiff_conditional_filters :
    ∀ w, spiffLands.presup w = true →
    (spiffLands.assertion w = true → weightGreater.presup w = true) := by
  intro w _ ha
  cases w <;> simp_all [spiffLands, weightGreater]

/-- But the actual presupposition people infer is CONDITIONAL:
    "IF Spiff lands on Planet X, his weight > Earth weight."
    This is stronger than what filtering predicts (which only gives
    "if Spiff lands, his weight is defined"). @cite{beaver-2001} Ch. 5.6
    argues this shows filtering/CCP miss conditional presuppositions. -/
def conditionalPresup : BProp SpiffWorld :=
  λ w => match w with
    | .onPlanetX_heavy => true
    | .onPlanetX_light => false  -- lands but NOT heavier: violates conditional presup
    | _ => true  -- presup is vacuously true when antecedent is false

/-- The conditional presupposition is NOT equivalent to the filtering
    prediction. Filtering predicts only that the presupposition is
    defined (weight exists); the conditional presupposition additionally
    requires that weight > Earth in all landing worlds. -/
theorem conditional_presup_stronger_than_filtering :
    ∃ w, (PrProp.impFilter spiffLands weightGreater).presup w = true ∧
         conditionalPresup w = false := by
  exact ⟨.onPlanetX_light, by simp [PrProp.impFilter, spiffLands, weightGreater],
         by simp [conditionalPresup]⟩

-- ══════════════════════════════════════════════════════════
-- § 5. PrProp ↔ CCP Agreement
-- (@cite{beaver-2001} Chs. 3–4)
-- ══════════════════════════════════════════════════════════

/-- The static filtering connectives and the dynamic CCP approach
    agree for conditionals: when the context entails the antecedent's
    presupposition, the filtering implication's presupposition holds
    iff the CCP-derived local context entails the consequent's presup. -/
theorem static_dynamic_agreement_conditional
    (c : Core.CommonGround.ContextSet W) (p q : PrProp W)
    (h_presup : ∀ w, c w → p.presup w = true) :
    (∀ w, c w → (PrProp.impFilter p q).presup w = true) ↔
    (∀ w, c w → p.assertion w = true → q.presup w = true) :=
  Semantics.Presupposition.LocalContext.local_context_matches_impFilter c p q

end Phenomena.Presupposition.Studies.Beaver2001
