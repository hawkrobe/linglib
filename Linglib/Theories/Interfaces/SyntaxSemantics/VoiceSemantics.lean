import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Montague.Variables

/-!
# Voice Semantics: Compositional Operations on Argument Structure

@cite{beavers-udayana-2022} @cite{kratzer-1996} @cite{alexiadou-schfer-2015}

Voice heads are type-changing compositional functions: they take a VP
denotation and return a clause-level meaning with modified argument
structure. This file defines the semantic operations; the theta-role
assignments are in `VoiceTheta.lean` (an independent interface).

## Independence from VoiceTheta

This file and `VoiceTheta.lean` are independent interfaces from the
syntactic voice head:

- **VoiceTheta**: Voice → theta role label (what the ext arg IS)
- **VoiceSemantics**: Voice → compositional operation (what the voice head DOES)

Same theta role, different operations: Agent is projected (active) or
suppressed-coreferent (reflexive). Same operation, different theta roles:
suppression can target agents (passive) or patients (antipassive).

## Key insight

The three Indonesian voice denotations have different Montague types:

- **⟦meN-⟧** : `(e ⇒ τ) → (e ⇒ τ)` — identity (preserves all arguments)
- **⟦di-⟧** : `(e ⇒ e ⇒ t) → (e ⇒ t)` — existentially binds external arg
- **⟦ber-⟧** : `(e ⇒ τ) → τ` — saturates first `e`-arg with open variable

The type change IS the argument-structure change. Active voice preserves
both arguments; passive and middle reduce arity by one.

## Polymorphism of ber-

`berSemG` is parametric in the result type `τ`. When applied to a VP of
type `e ⇒ t` (after FA with an object DP), it yields type `t` — the
external argument (agent) was suppressed. When applied to a VP of type
`e ⇒ e ⇒ t` (after noun incorporation), it yields type `e ⇒ t` — the
internal argument (patient) was suppressed and the agent remains as the
surface subject.

One Lean definition, two surface argument structures. The 2×2 typology
of @cite{beavers-udayana-2022} is a consequence of Montague composition,
not a stipulated data structure.
-/

namespace Theories.Interfaces.SyntaxSemantics.VoiceSemantics

open Semantics.Montague
open Semantics.Montague.Variables

-- ============================================================================
-- § 1: Active Voice — Identity
-- ============================================================================

/-- Active voice is the identity on VP meanings: it preserves the full
    argument structure.

    ⟦meN-⟧ = λP[P]    (@cite{beavers-udayana-2022}, (39a))

    In a type-driven system, "doing nothing" is itself a semantic
    contribution — it commits to projecting ALL arguments as DPs. -/
def activeSem {m : Model} {τ : Ty} (vp : m.interpTy (.e ⇒ τ))
    : m.interpTy (.e ⇒ τ) := vp

theorem activeSem_id {m : Model} {τ : Ty}
    (vp : m.interpTy (.e ⇒ τ)) : activeSem vp = vp := rfl

-- ============================================================================
-- § 2: Argument Suppression (ber-)
-- ============================================================================

/-- Argument suppression at a specific value: saturates the first
    `e`-argument of a VP with entity `z`.

    `suppressArg z VP = VP(z)` — the rest of the meaning is preserved.
    This is ⟦ber-⟧ evaluated at a particular assignment where the open
    variable has value `z`. -/
def suppressArg {m : Model} {τ : Ty}
    (z : m.Entity) (vp : m.interpTy (.e ⇒ τ)) : m.interpTy τ :=
  vp z

/-- Assignment-relative argument suppression: the suppressed argument is
    a free variable `g(n)`, interpreted relative to an assignment function.

    ⟦ber-⟧ₙ(VP)(g) = VP(g(n))(g)

    This is the paper's (43): `⟦ber-⟧ = λP_{⟨e,α⟩}[P(z̲)]`, where z̲ is
    the open variable g(n).

    The result type `τ` is parametric — Lean's implicit type argument
    captures the paper's subscript `⟨e,α⟩`:

    - `τ = .t` : VP was `e ⇒ t` (post-FA with object) → agent suppressed
    - `τ = .e ⇒ .t` : VP was `e ⇒ e ⇒ t` (post-incorporation) → patient
      suppressed, agent remains as surface subject -/
def berSemG {m : Model} {τ : Ty} (n : ℕ)
    (vp : DenotG m (.e ⇒ τ)) : DenotG m τ :=
  fun g => vp g (g n)

/-- `berSemG` at a specific assignment is just `suppressArg` with `g(n)`. -/
theorem berSemG_eq_suppressArg {m : Model} {τ : Ty} (n : ℕ)
    (vp : DenotG m (.e ⇒ τ)) (g : Assignment m) :
    berSemG n vp g = suppressArg (g n) (vp g) := rfl

-- ============================================================================
-- § 3: Passive (di-) — Existential Binding
-- ============================================================================

/-- Passive voice existentially binds the external argument (`Prop`-valued).

    ⟦di-⟧ₙ(VP)(patient)(g) = ∃x. VP(g[n↦x])(x)(patient)

    Simplified from the paper's (39b), omitting the presuppositional
    content (disjoint reference, ∂-operator) and event variables.

    The structural contrast with ber-: di- BINDS the suppressed variable;
    ber- leaves it FREE. This explains the diagnostic difference: di-
    passives license *oleh* 'by' phrases (the existential can be made
    explicit) while ber- middles do not (the variable is unbound). -/
def diSemProp {m : Model} (n : ℕ)
    (vp : DenotG m (.e ⇒ .e ⇒ .t))
    : Assignment m → m.Entity → Prop :=
  fun g patient => ∃ x : m.Entity, vp (g[n ↦ x]) x patient = true

-- ============================================================================
-- § 4: Noun Incorporation
-- ============================================================================

/-- Noun incorporation: conjoins an NP predicate with the VP's internal
    argument, preserving both argument positions.

    ⟦V_I⟧(P)(obj)(subj) = ⟦V⟧(obj)(subj) ∧ P(obj)

    Simplified from the paper's (49). The NP predicate P narrows the
    referent of the object position without saturating it. Both argument
    positions remain open — the difference from FA, where the object
    position is fully saturated.

    After incorporation, ber- suppresses the first argument (object),
    leaving the subject free for the agent. After FA, ber- suppresses the
    remaining argument (subject), making the patient the surface subject.
    Same ber-, different VP shape, different surface structure. -/
def incorporate {m : Model}
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (np : m.interpTy (.e ⇒ .t))
    : m.interpTy (.e ⇒ .e ⇒ .t) :=
  fun obj subj => verb obj subj && np obj

-- ============================================================================
-- § 5: Key Properties
-- ============================================================================

/-- Active voice preserves argument count: the output type matches the input. -/
theorem active_preserves_type {m : Model} {τ : Ty}
    (vp : m.interpTy (.e ⇒ τ)) :
    (activeSem vp : m.interpTy (.e ⇒ τ)) = vp := rfl

/-- Suppression after FA: when the VP has had its object saturated
    (type `e ⇒ t`), suppression yields a proposition (type `t`).

    The suppressed argument was the agent — the only remaining argument
    after FA. The patient (the FA-applied argument) becomes the surface
    subject. This is the dispositional/passive middle. -/
theorem suppression_after_FA {m : Model}
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (patient : m.Entity) (z : m.Entity) :
    suppressArg z (verb patient) = verb patient z := rfl

/-- Suppression after incorporation: when the VP retains both arguments
    (type `e ⇒ e ⇒ t`), suppression yields a property (type `e ⇒ t`).

    The suppressed argument was the object (first position). The agent
    (second position) remains as the surface subject. This is the
    incorporation middle. -/
theorem suppression_after_incorporation {m : Model}
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (np : m.interpTy (.e ⇒ .t))
    (z : m.Entity) (agent : m.Entity) :
    suppressArg z (incorporate verb np) agent =
    (verb z agent && np z) := rfl

/-- The core unification: `suppressArg` is the SAME function in both
    derivations. The difference in surface argument structure comes
    entirely from the type of the VP input, not from any difference in
    the suppression operation.

    This is the formal content of @cite{beavers-udayana-2022}'s claim
    that ber- is ONE operation producing FOUR surface types. -/
theorem same_operation_different_types {m : Model}
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (np : m.interpTy (.e ⇒ .t))
    (patient z : m.Entity) :
    -- Dispositional: suppress agent after FA with patient
    suppressArg z (verb patient) = verb patient z ∧
    -- Incorporation: suppress object, agent remains
    (fun agent => suppressArg z (incorporate verb np) agent) =
    (fun agent => verb z agent && np z) :=
  ⟨rfl, rfl⟩

/-- Incorporation preserves both arguments: the incorporated VP still
    has type `e ⇒ e ⇒ t`, unlike FA which reduces to `e ⇒ t`. -/
theorem incorporate_preserves_arity {m : Model}
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (np : m.interpTy (.e ⇒ .t)) :
    (incorporate verb np : m.interpTy (.e ⇒ .e ⇒ .t)) =
    fun obj subj => verb obj subj && np obj := rfl

/-- Assignment-relative suppression: berSemG does not fix how the open
    variable is interpreted — different assignments yield different
    values for g(n). The root class determines the DEFAULT assignment
    (coreferent or disjoint), but the operation itself is agnostic. -/
theorem berSemG_assignment_agnostic {m : Model} {τ : Ty} (n : ℕ)
    (vp : DenotG m (.e ⇒ τ))
    (g₁ g₂ : Assignment m) (h : g₁ n = g₂ n)
    (hvp : vp g₁ = vp g₂) :
    berSemG n vp g₁ = berSemG n vp g₂ := by
  simp only [berSemG, h, hvp]

end Theories.Interfaces.SyntaxSemantics.VoiceSemantics
