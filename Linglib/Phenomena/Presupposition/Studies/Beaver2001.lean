import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.ThreeValuedLogic
import Linglib.Theories.Semantics.Presupposition.Accommodation
import Linglib.Theories.Semantics.Presupposition.LocalContext

/-!
# Beaver (2001) @cite{beaver-2001}

Presupposition and Assertion in Dynamic Semantics: A Critical Review of
Linguistic Theories of Presupposition. CSLI Publications.

## Overview

Beaver's monograph compares four families of presupposition theory:

1. **Multivalence** (Ch. 2): Strong Kleene, Weak Kleene, Middle Kleene
2. **Cancellation and filtering** (Ch. 3): Karttunen's heritage, Heim's CCP
3. **Dynamic semantics** (Ch. 4): File Change Semantics, DPL, Update Semantics
4. **Accommodation** (Ch. 5): Lewis 1979, van der Sandt 1992, Fauconnier

## Structural Connection to PrProp

The central insight formalized here: Karttunen's heritage functions, Heim's
filtering connectives, and CCP-based local contexts all compute projection
from the same source — **PrProp.presup**.

- Heritage function for `p → q` = `(impFilter p q).presup` (by construction)
- Local context for q in `p → q` = `{ w ∈ c | p.assertion w }` (from PrProp)
- Accommodation operates on `p.presup` directly

No separate heritage type is needed. Filtering connectives ARE heritage
functions — the `.presup` field of a filtering connective IS the heritage
function output.
-/

namespace Phenomena.Presupposition.Studies.Beaver2001

open Core.Presupposition
open Core.Proposition
open Core.Duality

variable {W : Type*}

-- ══════════════════════════════════════════════════════════
-- § 1. The Symmetry Problem (@cite{beaver-2001} Ch. 2)
-- ══════════════════════════════════════════════════════════

/-! Strong Kleene disjunction is symmetric: `join a b = join b a`.
Middle Kleene disjunction is NOT: `joinMiddle a b ≠ joinMiddle b a` in general.
Natural language disjunction appears to be symmetric for presupposition
projection, which favors the SK/heritage prediction over CCP. -/

/-- SK disjunction is symmetric for presupposition projection.
    @cite{beaver-2001} Ch. 2: the correct empirical prediction. -/
theorem sk_disjunction_symmetric (a b : Truth3) :
    Truth3.join a b = Truth3.join b a := by
  cases a <;> cases b <;> rfl

/-- MK disjunction is NOT symmetric.
    @cite{beaver-2001} Ch. 2: MK captures left-to-right processing
    but overpredicts asymmetry for disjunction. -/
theorem mk_disjunction_asymmetric :
    ∃ a b : Truth3, Truth3.joinMiddle a b ≠ Truth3.joinMiddle b a :=
  ⟨.true, .indet, by simp [Truth3.joinMiddle, Truth3.join]⟩

-- ══════════════════════════════════════════════════════════
-- § 2. Heritage = Filtering (by construction)
-- (@cite{beaver-2001} Ch. 3)
-- ══════════════════════════════════════════════════════════

/-! Karttunen's heritage function for a connective is the presupposition
that the compound inherits from its parts. For filtering connectives,
this IS the `.presup` field — no separate heritage type needed.

The convergence of heritage, filtering, and CCP is @cite{beaver-2001}'s
central result for Chs. 2–4. We show it holds by construction: all three
read from the same `PrProp.presup` and `PrProp.assertion` fields. -/

/-- Heritage function for conditionals IS `.presup` of `impFilter`.
    @cite{beaver-2001} Ch. 3: heritage, filtering, and CCP agree. -/
example (p q : PrProp W) : (PrProp.impFilter p q).presup =
    (λ w => p.presup w && (!p.assertion w || q.presup w)) := rfl

/-- Heritage function for conjunction IS `.presup` of `andFilter`. -/
example (p q : PrProp W) : (PrProp.andFilter p q).presup =
    (λ w => p.presup w && (!p.assertion w || q.presup w)) := rfl

/-- Heritage function for disjunction IS `.presup` of `orFilter` (symmetric). -/
example (p q : PrProp W) : (PrProp.orFilter p q).presup =
    (λ w => (!p.assertion w || q.presup w) &&
            (!q.assertion w || p.presup w) &&
            (p.presup w || q.presup w)) := rfl

-- ══════════════════════════════════════════════════════════
-- § 3. Static ↔ Dynamic Agreement
-- (@cite{beaver-2001} Chs. 3–4)
-- ══════════════════════════════════════════════════════════

/-! The static filtering connectives and the dynamic CCP approach
agree for conditionals. Both compute projection from PrProp.presup
and PrProp.assertion — when the context entails p's presupposition,
filtering holds iff the local context (from p.assertion) entails
q's presupposition (from q.presup). -/

/-- Static filtering = dynamic local context for conditionals.
    Both derive from PrProp fields: `.presup` and `.assertion`. -/
theorem static_dynamic_agreement (c : Core.CommonGround.ContextSet W)
    (p q : PrProp W) :
    (∀ w, c w → (PrProp.impFilter p q).presup w = true) ↔
    (∀ w, c w → p.presup w = true ∧
                (p.assertion w = true → q.presup w = true)) :=
  Semantics.Presupposition.LocalContext.local_context_matches_impFilter c p q

-- ══════════════════════════════════════════════════════════
-- § 4. Accommodation and Cancellation
-- (@cite{beaver-2001} Ch. 5.8.1)
-- ══════════════════════════════════════════════════════════

/-! Heim's observation: global accommodation preference ≈ Gazdar cancellation.
Accommodation operates on `p.presup` directly — the structural connection
to PrProp is by construction. -/

open Semantics.Presupposition.Accommodation

/-- Heim's synthesis: global preference selects global when consistent.
    Accommodation input is `p.presup` — structurally connected to PrProp. -/
theorem heim_synthesis_projection (c : Core.CommonGround.ContextSet W)
    (p : PrProp W)
    (h : Core.CommonGround.ContextSet.nonEmpty
           (globalAccommodate c p.presup)) :
    heimSelect c p.presup = .global :=
  heim_projection_when_consistent c p.presup h

/-- Heim's synthesis: global preference selects local when inconsistent.
    This matches Gazdar's cancellation prediction. -/
theorem heim_synthesis_cancellation (c : Core.CommonGround.ContextSet W)
    (p : PrProp W)
    (h : ¬Core.CommonGround.ContextSet.nonEmpty
           (globalAccommodate c p.presup)) :
    heimSelect c p.presup = .local :=
  heim_cancellation_equivalence c p.presup h

-- ══════════════════════════════════════════════════════════
-- § 5. Conditional Presuppositions
-- (@cite{beaver-2001} Ch. 5.6)
-- ══════════════════════════════════════════════════════════

/-! Beaver argues that presuppositions can themselves be conditional.

Example E154: "If Spaceman Spiff lands on Planet X, he will be
bothered by the fact that his weight is greater than it would be on Earth."

The presupposition (Spiff's weight > Earth weight) is not an unconditional
global presupposition — it is conditional on the antecedent. Neither
filtering nor CCP can systematically produce conditional presuppositions. -/

inductive SpiffWorld where
  | onEarth | onPlanetX_heavy | onPlanetX_light | inSpace
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

/-- Filtering correctly predicts: the antecedent filters the
    consequent's presupposition. -/
theorem spiff_conditional_filters :
    ∀ w, spiffLands.presup w = true →
    (spiffLands.assertion w = true → weightGreater.presup w = true) := by
  intro w _ ha
  cases w <;> simp_all [spiffLands, weightGreater]

/-- The actual presupposition people infer is CONDITIONAL:
    "IF Spiff lands on Planet X, his weight > Earth weight."
    This is stronger than what filtering predicts. -/
def conditionalPresup : BProp SpiffWorld :=
  λ w => match w with
    | .onPlanetX_heavy => true
    | .onPlanetX_light => false
    | _ => true

/-- The conditional presupposition is NOT equivalent to the filtering
    prediction. Filtering predicts weight-is-defined; the conditional
    presupposition additionally requires weight > Earth. -/
theorem conditional_presup_stronger_than_filtering :
    ∃ w, (PrProp.impFilter spiffLands weightGreater).presup w = true ∧
         conditionalPresup w = false := by
  exact ⟨.onPlanetX_light, by simp [PrProp.impFilter, spiffLands, weightGreater],
         by simp [conditionalPresup]⟩

end Phenomena.Presupposition.Studies.Beaver2001
