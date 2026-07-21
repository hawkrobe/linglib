import Linglib.Semantics.Presupposition.Context

/-!
# Accommodation
[lewis-1979] [beaver-2001] [van-der-sandt-1992]

Accommodation is the process by which a context is adjusted to satisfy
a presupposition that is not already entailed. [lewis-1979] introduced
the concept: "If at time t something is said that requires presupposition P
to be acceptable, and if P is not presupposed just before t, then — ceteris
paribus — presupposition P comes into existence at t."

## Three Levels ([beaver-2001] Ch. 5)

- **Global**: presupposition is added to the top-level common ground
- **Local**: presupposition is satisfied within the embedded context
- **Intermediate**: presupposition is added at an intermediate level
 (into the restrictor of a quantifier or antecedent of a conditional)

## Three Strategies

1. **Heim/Lewis preference**: prefer global > intermediate > local.
 Global preference + consistency constraint ≈ Gazdar's cancellation
 ([beaver-2001] Ch. 5.8.1).
2. **Van der Sandt structural**: DRT-based move-α; presupposition DRS
 is moved to the highest accessible position ([van-der-sandt-1992]).
3. **Fauconnier flotation**: presupposition floats upward through
 mental spaces, leaving a shadow at each level ([beaver-2001] Ch. 5.8.3).

## Constraints ([beaver-2001] Ch. 5.3)

- **Informativity**: accommodation must be informative (add new information)
- **Consistency**: accommodated content must be consistent with the context
- **Trapping**: bound presuppositions cannot escape their binder's scope
- **Binding preference**: anaphoric resolution is preferred over accommodation
-/

namespace Semantics.Presupposition.Accommodation

open Classical
open Semantics.Presupposition
open CommonGround
open Semantics.Presupposition.Context

variable {W : Type*}

/-! ### Accommodation levels -/

/-- The level at which accommodation occurs.
 [beaver-2001] Ch. 5, [lewis-1979], [heim-1983]. -/
inductive AccommodationLevel where
 /-- Add presupposition to the global common ground. -/
 | global
 /-- Satisfy presupposition within the local embedded context. -/
 | local
 /-- Add presupposition at an intermediate level (e.g., restrictor
 of a quantifier, antecedent of a conditional).
 [beaver-2001] Ch. 5.5 argues this is heavily restricted. -/
 | intermediate (depth : Nat)
 deriving DecidableEq, Repr

/-! ### Global accommodation -/

/-- Global accommodation: update the context to include the presupposition.
 [lewis-1979]: "presupposition P comes into existence."

 Delegates to `Semantics.Presupposition.Context.accommodate`. -/
abbrev globalAccommodate (c : ContextSet W) (presup : Set W) : ContextSet W :=
 accommodate c presup

/-! ### Accommodation constraints -/

/-- Trapping: a presupposition with a bound variable cannot be
 accommodated above its binder. [beaver-2001] Ch. 5.3.

 Modeled as a predicate on the accommodation level and a binding
 depth: accommodation at level `l` is trapped if the presupposition
 is bound at depth `d` and `l` would place it above `d`. -/
def isTrapped (bindingDepth : Nat) : AccommodationLevel → Prop
 | .global => True -- bound content cannot escape to global
 | .intermediate d => d < bindingDepth -- cannot go above binder
 | .local => False -- local is always below binder

instance (bindingDepth : Nat) : DecidablePred (isTrapped bindingDepth) := fun l => by
 unfold isTrapped; cases l <;> infer_instance

/-- All constraints bundled together.
 Uses canonical operations from `Semantics.Presupposition.Context`. -/
structure AccommodationOK (c : ContextSet W) (presup : Set W) : Prop where
 informative : accommodationInformative c presup
 consistent : accommodationConsistent c presup

/-! ### The Heim/Lewis strategy -/

/-- Select accommodation level based on the Heim/Lewis strategy.

 Try global first; if inconsistent, fall back to local.

 [heim-1983]: "by stipulating a ceteris paribus preference
 for global over local accommodation, we recapture the effect of
 Gazdar's assumption that presupposition cancellation occurs only
 under the threat of inconsistency." -/
noncomputable def heimSelect (c : ContextSet W) (presup : Set W) :
 AccommodationLevel :=
 if Set.Nonempty (globalAccommodate c presup)
 then .global
 else .local

/-! ### Key theorems -/

/-- **Heim's observation**: global accommodation preference is equivalent
 to Gazdar's cancellation under threat of inconsistency.

 When global accommodation would be inconsistent, we fall back to
 local accommodation — which has the same effect as Gazdar's
 presupposition cancellation.

 [beaver-2001] Ch. 5.8.1: "with one short remark buried in a
 terse paper, Heim offers a simple synthesis between the two antitheses
 of 1970s presupposition theory." -/
theorem heim_cancellation_equivalence (c : ContextSet W) (presup : Set W)
 (h_inconsistent : ¬Set.Nonempty (globalAccommodate c presup)) :
 heimSelect c presup = .local := by
 simp only [heimSelect, h_inconsistent, ↓reduceIte]

/-- When global accommodation IS consistent, Heim's strategy projects
 the presupposition globally — matching Karttunen's projection. -/
theorem heim_projection_when_consistent (c : ContextSet W) (presup : Set W)
 (h_consistent : Set.Nonempty (globalAccommodate c presup)) :
 heimSelect c presup = .global := by
 simp only [heimSelect, h_consistent, ↓reduceIte]

/-- **Intermediate accommodation is problematic.**

 [beaver-2001] Ch. 5.5 argues that intermediate accommodation
 (accommodation into the restrictor of a quantifier or antecedent
 of a conditional) is heavily restricted and only occurs with
 generic/habitual statements. Without intermediate accommodation,
 both Heim's CCP and van der Sandt's DRT make better predictions.

 This is formalized as: the Heim preference strategy never selects
 intermediate accommodation. -/
theorem heim_never_intermediate (c : ContextSet W) (presup : Set W) :
 ∀ d, heimSelect c presup ≠ .intermediate d := by
 intro d
 by_cases h : Set.Nonempty (globalAccommodate c presup)
 · rw [heim_projection_when_consistent c presup h]; exact AccommodationLevel.noConfusion
 · rw [heim_cancellation_equivalence c presup h]; exact AccommodationLevel.noConfusion

end Semantics.Presupposition.Accommodation
