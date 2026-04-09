import Linglib.Core.Semantics.PresuppositionContext

/-!
# Accommodation
@cite{lewis-1979} @cite{beaver-2001} @cite{van-der-sandt-1992}

Accommodation is the process by which a context is adjusted to satisfy
a presupposition that is not already entailed. @cite{lewis-1979} introduced
the concept: "If at time t something is said that requires presupposition P
to be acceptable, and if P is not presupposed just before t, then — ceteris
paribus — presupposition P comes into existence at t."

## Three Levels (@cite{beaver-2001} Ch. 5)

- **Global**: presupposition is added to the top-level common ground
- **Local**: presupposition is satisfied within the embedded context
- **Intermediate**: presupposition is added at an intermediate level
 (into the restrictor of a quantifier or antecedent of a conditional)

## Three Strategies

1. **Heim/Lewis preference**: prefer global > intermediate > local.
 Global preference + consistency constraint ≈ Gazdar's cancellation
 (@cite{beaver-2001} Ch. 5.8.1).
2. **Van der Sandt structural**: DRT-based move-α; presupposition DRS
 is moved to the highest accessible position (@cite{van-der-sandt-1992}).
3. **Fauconnier flotation**: presupposition floats upward through
 mental spaces, leaving a shadow at each level (@cite{beaver-2001} Ch. 5.8.3).

## Constraints (@cite{beaver-2001} Ch. 5.3)

- **Informativity**: accommodation must be informative (add new information)
- **Consistency**: accommodated content must be consistent with the context
- **Trapping**: bound presuppositions cannot escape their binder's scope
- **Binding preference**: anaphoric resolution is preferred over accommodation
-/

namespace Semantics.Presupposition.Accommodation

open Classical
open Core.Presupposition
open Core.Proposition
open Core.CommonGround
open Core.PresuppositionContext

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Accommodation Levels
-- ════════════════════════════════════════════════════════════════

/-- The level at which accommodation occurs.
 @cite{beaver-2001} Ch. 5, @cite{lewis-1979}, @cite{heim-1983}. -/
inductive AccommodationLevel where
 /-- Add presupposition to the global common ground. -/
 | global
 /-- Satisfy presupposition within the local embedded context. -/
 | local
 /-- Add presupposition at an intermediate level (e.g., restrictor
 of a quantifier, antecedent of a conditional).
 @cite{beaver-2001} Ch. 5.5 argues this is heavily restricted. -/
 | intermediate (depth : Nat)
 deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Global Accommodation
-- ════════════════════════════════════════════════════════════════

/-- Global accommodation: update the context to include the presupposition.
 @cite{lewis-1979}: "presupposition P comes into existence."

 Delegates to `Core.PresuppositionContext.accommodate`. -/
abbrev globalAccommodate (c : ContextSet W) (presup : Prop' W) : ContextSet W :=
 accommodate c presup

-- ════════════════════════════════════════════════════════════════
-- § 3. Accommodation Constraints
-- ════════════════════════════════════════════════════════════════

/-- Trapping: a presupposition with a bound variable cannot be
 accommodated above its binder. @cite{beaver-2001} Ch. 5.3.

 Modeled as a predicate on the accommodation level and a binding
 depth: accommodation at level `l` is trapped if the presupposition
 is bound at depth `d` and `l` would place it above `d`. -/
def isTrapped (bindingDepth : Nat) : AccommodationLevel → Bool
 | .global => true -- bound content cannot escape to global
 | .intermediate d => d < bindingDepth -- cannot go above binder
 | .local => false -- local is always below binder

/-- All constraints bundled together.
 Uses canonical operations from `Core.PresuppositionContext`. -/
structure AccommodationOK (c : ContextSet W) (presup : Prop' W) : Prop where
 informative : accommodationInformative c presup
 consistent : accommodationConsistent c presup

-- ════════════════════════════════════════════════════════════════
-- § 4. Accommodation Strategies
-- ════════════════════════════════════════════════════════════════

/-- An accommodation strategy determines which level of accommodation
 is preferred. @cite{beaver-2001} Ch. 5.8. -/
inductive AccommodationStrategy where
 /-- Heim/Lewis: prefer global, fall back to local if global is
 inconsistent. Global preference ≈ projection; local fallback
 ≈ cancellation. @cite{heim-1983}, @cite{lewis-1979}. -/
 | heimPreference
 /-- Van der Sandt: DRT-based move-α. Presupposition DRS is moved
 to the highest accessible position that satisfies binding
 constraints. @cite{van-der-sandt-1992}. -/
 | vanDerSandt
 /-- Fauconnier: presupposition floats upward through mental spaces,
 leaving a copy ("shadow") at each intermediate level.
 @cite{beaver-2001} Ch. 5.8.3. -/
 | fauconnierFlotation
 deriving DecidableEq, Repr

/-- Select accommodation level based on the Heim/Lewis strategy.

 Try global first; if inconsistent, fall back to local.

 @cite{heim-1983}: "by stipulating a ceteris paribus preference
 for global over local accommodation, we recapture the effect of
 Gazdar's assumption that presupposition cancellation occurs only
 under the threat of inconsistency." -/
noncomputable def heimSelect (c : ContextSet W) (presup : Prop' W) :
 AccommodationLevel :=
 if ContextSet.nonEmpty (globalAccommodate c presup)
 then .global
 else .local

-- ════════════════════════════════════════════════════════════════
-- § 5. Key Theorems
-- ════════════════════════════════════════════════════════════════

/-- **Heim's observation**: global accommodation preference is equivalent
 to Gazdar's cancellation under threat of inconsistency.

 When global accommodation would be inconsistent, we fall back to
 local accommodation — which has the same effect as Gazdar's
 presupposition cancellation.

 @cite{beaver-2001} Ch. 5.8.1: "with one short remark buried in a
 terse paper, Heim offers a simple synthesis between the two antitheses
 of 1970s presupposition theory." -/
theorem heim_cancellation_equivalence (c : ContextSet W) (presup : Prop' W)
 (h_inconsistent : ¬ContextSet.nonEmpty (globalAccommodate c presup)) :
 heimSelect c presup = .local := by
 simp only [heimSelect, h_inconsistent, ↓reduceIte]

/-- When global accommodation IS consistent, Heim's strategy projects
 the presupposition globally — matching Karttunen's projection. -/
theorem heim_projection_when_consistent (c : ContextSet W) (presup : Prop' W)
 (h_consistent : ContextSet.nonEmpty (globalAccommodate c presup)) :
 heimSelect c presup = .global := by
 simp only [heimSelect, h_consistent, ↓reduceIte]

/-- **Intermediate accommodation is problematic.**

 @cite{beaver-2001} Ch. 5.5 argues that intermediate accommodation
 (accommodation into the restrictor of a quantifier or antecedent
 of a conditional) is heavily restricted and only occurs with
 generic/habitual statements. Without intermediate accommodation,
 both Heim's CCP and van der Sandt's DRT make better predictions.

 This is formalized as: the Heim preference strategy never selects
 intermediate accommodation. -/
theorem heim_never_intermediate (c : ContextSet W) (presup : Prop' W) :
 ∀ d, heimSelect c presup ≠ .intermediate d := by
 intro d
 by_cases h : ContextSet.nonEmpty (globalAccommodate c presup)
 · rw [heim_projection_when_consistent c presup h]; exact AccommodationLevel.noConfusion
 · rw [heim_cancellation_equivalence c presup h]; exact AccommodationLevel.noConfusion

/-- Van der Sandt vs. Fauconnier: the key difference is whether
 accommodation leaves shadows at intermediate levels.

 - Van der Sandt: presupposition jumps to highest position,
 no trace at intermediate levels.
 - Fauconnier: presupposition floats up, leaving a copy at
 each level it passes through.

 @cite{beaver-2001} Ch. 5.8.3: Fauconnier's strategy correctly
 predicts that lexical triggers (factives) must hold at all
 intermediate levels, while anaphoric triggers (definites, 'too')
 only need to hold at the highest level. -/
inductive TriggerClass where
 /-- Anaphoric/resolution triggers: definites, 'too', 'again'.
 Collect entities from context. Use van der Sandt strategy. -/
 | anaphoric
 /-- Lexical triggers: factives ('know', 'regret').
 Impose conditions on concept application. Use Fauconnier strategy. -/
 | lexical
 deriving DecidableEq, Repr

/-- Select accommodation strategy based on trigger class.
 @cite{beaver-2001} Ch. 5.8, following Zeevat (1992). -/
def strategyForTrigger : TriggerClass → AccommodationStrategy
 | .anaphoric => .vanDerSandt
 | .lexical => .fauconnierFlotation

end Semantics.Presupposition.Accommodation
