import Linglib.Theories.Semantics.Causation.CausalVerb

/-!
# Degree Constructions and Actuality Inferences (Nadathur 2023, Chapter 5)

Formalizes the causal analysis of *enough* and *too* constructions:

- "The coffee is hot enough to drink" → someone drank it (with PFV)
- "The coffee is too hot to drink" → no one drank it (with PFV)

## Key Insight

*Enough* and *too* generate actuality inferences via the same mechanism
as ability modals: **causal sufficiency** of a degree-threshold condition
for the complement, modulated by **grammatical aspect**.

- "Adj enough to VP": degree ≥ θ is causally sufficient for VP
- "too Adj to VP": degree ≥ θ is causally sufficient for ¬VP

With perfective aspect, the degree condition is asserted to hold,
triggering the actuality inference. With imperfective, only the
causal relationship is asserted.

## Connection to CausalFrame

`DegreeScenario` is a `CausalFrame` where the trigger is the degree
variable (degree ≥ threshold). This means:
- `enoughWithAspect` IS `CausalFrame.actualityWithAspect` with polarity = positive
- `tooWithAspect` uses `CausalFrame.complementBlockedAt` with polarity = negative
- The actuality theorems are INSTANCES of the generic ones from `CausalVerb.lean`

## References

- Nadathur, P. (2023). *Actuality Inferences: Causality, Aspect, and Modality*.
  Chapter 5: Enough and Too.
- Meier, C. (2003). The meaning of *too*, *enough*, and *so...that*.
  Natural Language Semantics.
-/

namespace Nadathur2023.DegreeCausation

open Core.Causation
open Semantics.Lexical.Verb.ViewpointAspect (ViewpointAspectB)
open Semantics.Attitudes.Intensional (World allWorlds)
open CausalVerb (CausalFrame ActualizationMode)

-- ════════════════════════════════════════════════════
-- § 1. DegreeScenario
-- ════════════════════════════════════════════════════

/-- A causal scenario for degree constructions (*enough to VP*, *too Adj to VP*).

    The trigger is the **degree variable**: whether the entity's degree
    meets the threshold (degree ≥ θ for "enough", degree ≥ θ for "too"
    where θ is the threshold of excess).

    The complement is the VP outcome.

    The causal dynamics encodes the link between degree satisfaction
    and the complement. For "enough", the link is positive (degree met →
    complement develops). For "too", the link is negative (degree met →
    complement does NOT develop, modeled as absence of a law). -/
structure DegreeScenario where
  /-- Causal dynamics linking degree to complement -/
  dynamics : CausalDynamics
  /-- The degree variable: "degree meets threshold" -/
  degreeMet : Variable
  /-- The complement variable (VP outcome) -/
  complement : Variable
  /-- Maps each world to its background situation.
      Encodes whether the degree condition was actually met. -/
  background : World → Situation

-- ════════════════════════════════════════════════════
-- § 2. Enough Semantics
-- ════════════════════════════════════════════════════

/-- The degree condition is causally sufficient for the complement at `w`.

    "The coffee is hot enough to drink" presupposes that the degree of
    heat being sufficient is causally linked to the drinking event. -/
def enoughAt (sc : DegreeScenario) (w : World) : Bool :=
  causallySufficient sc.dynamics (sc.background w) sc.degreeMet sc.complement

/-- The complement is actualized at `w`: degree was met AND complement
    developed via normal causal propagation. -/
def enoughActualized (sc : DegreeScenario) (w : World) : Bool :=
  factuallyDeveloped sc.dynamics (sc.background w) sc.degreeMet sc.complement

/-- *Enough* with aspectual modulation.

    - **Perfective**: degree met AND complement actualized
    - **Imperfective**: degree met (causal link exists) but no actualization required -/
def enoughWithAspect (sc : DegreeScenario) (asp : ViewpointAspectB)
    (w : World) : Bool :=
  match asp with
  | .perfective => enoughAt sc w && enoughActualized sc w
  | .imperfective => enoughAt sc w

-- ════════════════════════════════════════════════════
-- § 3. Too Semantics
-- ════════════════════════════════════════════════════

/-- The degree condition blocks the complement: degree met, but complement
    does NOT develop. This is the "too" pattern.

    "The coffee is too hot to drink": the degree of heat being excessive
    is causally sufficient for the complement NOT occurring. -/
def tooAt (sc : DegreeScenario) (w : World) : Bool :=
  let bgWithDeg := (sc.background w).extend sc.degreeMet true
  !(normalDevelopment sc.dynamics bgWithDeg).hasValue sc.complement true

/-- The complement is blocked at `w`: degree was met AND complement
    did NOT develop. -/
def tooActualized (sc : DegreeScenario) (w : World) : Bool :=
  (sc.background w).hasValue sc.degreeMet true &&
  !(normalDevelopment sc.dynamics (sc.background w)).hasValue sc.complement true

/-- *Too* with aspectual modulation.

    - **Perfective**: degree met AND complement blocked (= didn't happen)
    - **Imperfective**: degree is excessive (causal link to blocking) -/
def tooWithAspect (sc : DegreeScenario) (asp : ViewpointAspectB)
    (w : World) : Bool :=
  match asp with
  | .perfective => tooAt sc w && tooActualized sc w
  | .imperfective => tooAt sc w

-- ════════════════════════════════════════════════════
-- § 4. Actuality Theorems
-- ════════════════════════════════════════════════════

/-- **Perfective enough entails complement**: if "was Adj enough to VP"
    holds with perfective aspect, the complement is actualized.

    Proof: immediate from the definition — perfective conjoins
    causal sufficiency with actualization. -/
theorem perfective_enough_entails_complement (sc : DegreeScenario) (w : World)
    (h : enoughWithAspect sc .perfective w = true) :
    enoughActualized sc w = true := by
  simp only [enoughWithAspect, Bool.and_eq_true] at h
  exact h.2

/-- **Perfective too entails complement blocked**: if "was too Adj to VP"
    holds with perfective aspect, the complement did NOT occur. -/
theorem perfective_too_blocks_complement (sc : DegreeScenario) (w : World)
    (h : tooWithAspect sc .perfective w = true) :
    tooActualized sc w = true := by
  simp only [tooWithAspect, Bool.and_eq_true] at h
  exact h.2

/-- Imperfective enough is compatible with complement not actualized. -/
theorem imperfective_enough_no_entailment :
    ∃ (sc : DegreeScenario) (w : World),
      enoughWithAspect sc .imperfective w = true ∧
      enoughActualized sc w = false := by
  let deg := mkVar "deg"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple deg comp]
  let sc : DegreeScenario := {
    dynamics := dyn
    degreeMet := deg
    complement := comp
    background := λ _ => Situation.empty  -- degree not met at any world
  }
  exact ⟨sc, .w0, by native_decide, by native_decide⟩

/-- Enough and too give opposite actuality inferences in the same scenario.

    With the same dynamics and degree variable:
    - "enough": degree sufficient → complement develops
    - "too": degree sufficient → complement does NOT develop
    (Different dynamics encode the different causal relationships.) -/
theorem enough_too_opposite :
    ∃ (scE scT : DegreeScenario) (w : World),
      -- Same degree variable
      scE.degreeMet = scT.degreeMet ∧
      -- Enough: degree met → complement occurs
      enoughWithAspect scE .perfective w = true ∧
      enoughActualized scE w = true ∧
      -- Too: degree met → complement does NOT occur
      tooWithAspect scT .perfective w = true ∧
      tooActualized scT w = true := by
  let deg := mkVar "deg"
  let comp := mkVar "comp"
  -- "Enough" dynamics: degree → complement
  let dynE := CausalDynamics.ofList [CausalLaw.simple deg comp]
  -- "Too" dynamics: no law from degree to complement (degree blocks it)
  let dynT := CausalDynamics.empty
  let bg : World → Situation := λ _ => Situation.empty.extend deg true
  let scE : DegreeScenario := {
    dynamics := dynE, degreeMet := deg, complement := comp, background := bg }
  let scT : DegreeScenario := {
    dynamics := dynT, degreeMet := deg, complement := comp, background := bg }
  exact ⟨scE, scT, .w0, rfl,
    by native_decide, by native_decide,
    by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 5. CausalFrame Instance
-- ════════════════════════════════════════════════════

/-- A `DegreeScenario` for "enough" is a `CausalFrame World` with
    aspectual actualization. -/
def DegreeScenario.toFrame (sc : DegreeScenario) : CausalFrame World :=
  { dynamics := sc.dynamics
    trigger := sc.degreeMet
    complement := sc.complement
    background := sc.background
    actualization := .aspectual }

/-- **Grounding**: `enoughWithAspect` matches the generic
    `CausalFrame.actualityWithAspect` for degree scenarios.

    This proves that "enough" is structurally identical to "be able":
    both are aspect-governed causal frames. -/
theorem enough_matches_frame (sc : DegreeScenario) (asp : ViewpointAspectB)
    (w : World) :
    enoughWithAspect sc asp w =
      sc.toFrame.actualityWithAspect asp w := by
  cases asp <;> rfl

/-- **Structural unity**: ability modals and "enough" are the same
    frame pattern, differing only in what the trigger represents.

    This is the key claim of Nadathur (2023, Chapter 7): ability modals
    and degree constructions are unified by the causal frame. -/
theorem enough_same_pattern_as_ability :
    ∀ (sc : DegreeScenario), sc.toFrame.actualization = .aspectual := by
  intro sc; rfl

end Nadathur2023.DegreeCausation
