import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Pragmatic Blocking of High Circumstantial Readings

@cite{hacquard-2010} @cite{grice-1975}Formalizes the pragmatic blocking of circumstantial readings for
high modals. Content licensing does NOT
rule out circumstantial readings for high modals — `canProjectCircumstantial`
returns `true` for all event binders. Instead, circumstantial readings of
high modals are **pragmatically blocked** by more informative epistemic
readings.

## The Puzzle (Hacquard 2010, (49b, 49d))

Content licensing predicts:
- (49a) speech act + epistemic: ✓ attested
- (49b) speech act + circumstantial: ✓ semantically possible
- (49c) attitude + epistemic: ✓ attested
- (49d) attitude + circumstantial: ✓ semantically possible
- (49e) VP event + epistemic: ✗ ruled out (content licensing)
- (49f) VP event + circumstantial: ✓ attested

But (49b) and (49d) are generally unattested. WHY?

## Hacquard's Answer: Pragmatic Pre-emption

When a high modal can access BOTH epistemic and circumstantial backgrounds
(because the binding event is contentful), the epistemic reading is more
informative: it encodes the speaker's/holder's evidence about the world.
The circumstantial reading merely states facts about circumstances. A
pragmatic speaker would choose the more informative reading, pre-empting
the circumstantial one.

This is a Gricean Manner/Quantity reasoning: if the epistemic reading is
available and more informative, use it. The circumstantial reading is
blocked not by grammar but by pragmatic competition.

## Connection to RSA

This is a natural RSA application: a rational speaker would produce the
utterance that maximizes informativity. When both readings are available,
the epistemic one carries more information (it conveys the speaker's
evidence state), so it is pragmatically preferred.

-/

namespace Phenomena.Modality.Bridge.PragmaticBlockingBridge

open Semantics.Modality.EventRelativity
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Semantic Availability ≠ Pragmatic Availability
-- ════════════════════════════════════════════════════

/-- Content licensing allows circumstantial readings for ALL binders
(including high/contentful ones). This is correct: circumstantial
readings of high modals are not UNGRAMMATICAL, just pragmatically
dispreferred. -/
theorem circumstantial_always_semantically_available :
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    EventBinder.attitude.canProjectCircumstantial = true ∧
    EventBinder.vpEvent.canProjectCircumstantial = true :=
  ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 2. Competition: Epistemic vs Circumstantial
-- ════════════════════════════════════════════════════

/-- Informativity ordering on modal flavors.

Epistemic readings encode the speaker's EVIDENCE STATE — a specific
body of knowledge. Circumstantial readings encode surrounding
CIRCUMSTANCES — a more general and less constrained background.

When both are available, epistemic is more informative because it
commits to a specific body of evidence. -/
def informativity : ModalFlavor → Nat
  | .epistemic => 2       -- most informative (evidence-based)
  | .deontic => 1         -- intermediate (norm-based)
  | .circumstantial => 0  -- least informative (fact-based)

/-- Epistemic is more informative than circumstantial. -/
theorem epistemic_more_informative :
    informativity .epistemic > informativity .circumstantial := by decide


-- ════════════════════════════════════════════════════
-- § 3. Pragmatic Blocking Predicate
-- ════════════════════════════════════════════════════

/-- A reading is pragmatically blocked if a more informative reading
is available from the same binder. -/
def isPragmaticallyBlocked (b : EventBinder) (flavor : ModalFlavor) : Bool :=
  -- A flavor is blocked if there exists a more informative flavor
  -- available from the same binder
  let available := b.availableFlavors
  available.any λ f => f != flavor && informativity f > informativity flavor

/-- Circumstantial readings of speech act binders are pragmatically
blocked: epistemic is available and more informative. -/
theorem speechAct_circ_blocked :
    isPragmaticallyBlocked .speechAct .circumstantial = true := by native_decide

/-- Circumstantial readings of attitude binders are blocked too. -/
theorem attitude_circ_blocked :
    isPragmaticallyBlocked .attitude .circumstantial = true := by native_decide

/-- Epistemic readings are NEVER blocked (they're the most informative). -/
theorem epistemic_never_blocked :
    isPragmaticallyBlocked .speechAct .epistemic = false ∧
    isPragmaticallyBlocked .attitude .epistemic = false := by
  constructor <;> native_decide

/-- VP event binders: circumstantial is NOT blocked because epistemic
is not available (content licensing prevents it). No competition. -/
theorem vpEvent_circ_not_blocked :
    isPragmaticallyBlocked .vpEvent .circumstantial = false := by native_decide


-- ════════════════════════════════════════════════════
-- § 4. The Full (49a–f) Pattern Explained
-- ════════════════════════════════════════════════════

/-- Two filters determine whether a binder × flavor combination is
PRAGMATICALLY available:
1. Content licensing (semantic filter): epistemic requires content
2. Informativity competition (pragmatic filter): less informative
   readings are blocked when more informative ones are available -/
def pragmaticallyAvailable (b : EventBinder) (flavor : ModalFlavor) : Bool :=
  flavor ∈ b.availableFlavors && !isPragmaticallyBlocked b flavor

/-- The complete (49a–f) pattern from @cite{hacquard-2010}:

| Binder | Flavor | Semantic? | Blocked? | Pragmatic? | Status |
|--------|--------|-----------|----------|------------|--------|
| Speech act | Epistemic | ✓ | ✗ | ✓ | (49a) attested |
| Speech act | Circumstantial | ✓ | ✓ | ✗ | (49b) unattested |
| Attitude | Epistemic | ✓ | ✗ | ✓ | (49c) attested |
| Attitude | Circumstantial | ✓ | ✓ | ✗ | (49d) unattested |
| VP event | Epistemic | ✗ | — | ✗ | (49e) unattested |
| VP event | Circumstantial | ✓ | ✗ | ✓ | (49f) attested | -/
theorem hacquard_49_full_pattern :
    -- (49a) speech act + epistemic: pragmatically available
    pragmaticallyAvailable .speechAct .epistemic = true ∧
    -- (49b) speech act + circumstantial: pragmatically blocked
    pragmaticallyAvailable .speechAct .circumstantial = false ∧
    -- (49c) attitude + epistemic: pragmatically available
    pragmaticallyAvailable .attitude .epistemic = true ∧
    -- (49d) attitude + circumstantial: pragmatically blocked
    pragmaticallyAvailable .attitude .circumstantial = false ∧
    -- (49e) VP event + epistemic: semantically unavailable
    pragmaticallyAvailable .vpEvent .epistemic = false ∧
    -- (49f) VP event + circumstantial: pragmatically available
    pragmaticallyAvailable .vpEvent .circumstantial = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide


-- ════════════════════════════════════════════════════
-- § 5. Pragmatic vs Semantic Blocking
-- ════════════════════════════════════════════════════

/-- (49e) and (49b) are both unattested, but for DIFFERENT reasons:
- (49e) VP event + epistemic: SEMANTICALLY blocked (content licensing)
- (49b) speech act + circumstantial: PRAGMATICALLY blocked (competition)

This distinction matters: (49b) should be recoverable in special contexts
where the circumstantial reading is more relevant than the epistemic one.
(49e) is never recoverable — it's a grammatical restriction. -/
theorem different_blocking_mechanisms :
    -- (49e): semantically blocked (canProjectEpistemic = false)
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    -- (49b): semantically AVAILABLE but pragmatically blocked
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    isPragmaticallyBlocked .speechAct .circumstantial = true :=
  ⟨rfl, rfl, by native_decide⟩


end Phenomena.Modality.Bridge.PragmaticBlockingBridge
