import Linglib.Theories.Semantics.Reference.Metasemantics.Defs

/-!
# Conceptions of reasonableness for metasemantics
@cite{ney-2026} @cite{king-2013}

A *conception of reasonableness* is the set of speaker intentions whose
intended referent the agent (implicitly or explicitly) believes every
competent, attentive, reasonable hearer would recognize.

@cite{ney-2026} §4: "An agent's conception of reasonableness ... is
constituted by that agent's (implicit and explicit) beliefs about which
referential intentions every reasonable hearer would recognise."

The notion is introduced to dissolve the prima facie challenge
@cite{ney-2026} poses for @cite{king-2013}'s coordination account. King's
account implicitly assumes a *single shared* conception (whose existence
makes the relevant facts available from the common ground); Ney's
revision uses the *joint* conception across speaker and actual hearer
(which need not be available from the common ground).

## Why a Prop and not a Set

`ConceptionOfReasonableness C W E` is `SpeakerIntention C W E → Prop`
(definitionally `Set (SpeakerIntention C W E)`). The choice keeps the
combinators algebraic — `shared₂` is `∧`, `joint₂` is `∨` — which makes
definitional unfolding in coordination proofs straightforward.

## Key combinators

- `shared₂ RS RH`: intersection of two agents' conceptions (King's
  implicit assumption: "every reasonable hearer")
- `joint₂ RS RH`: union of two agents' conceptions (@cite{ney-2026}'s
  revision: "reasonable by the lights of *at least one* of S, H")
- `shared`, `joint`: indexed-family generalizations

## Lemmas

- `shared₂_le_joint₂`: shared ≤ joint pointwise
- Same for the indexed forms (`shared_le_joint` under `[Nonempty ι]`)
-/

namespace Semantics.Reference.Metasemantics

universe u v w

/-- An agent's *conception of reasonableness*: the set of speaker
intentions whose intended referent the agent believes every competent,
attentive, reasonable hearer would recognize.

Definitionally `Set (SpeakerIntention C W E)`. The Prop-valued form is
preferred so that combinators reduce to logical connectives. -/
abbrev ConceptionOfReasonableness (C : Type u) (W : Type v) (E : Type w) :=
  SpeakerIntention C W E → Prop

namespace ConceptionOfReasonableness

variable {C : Type u} {W : Type v} {E : Type w}

/-! ## Binary combinators (the case Ney 2026 §4 actually argues about) -/

/-- Binary *shared* conception: an intention is shared-reasonable iff
both `RS` and `RH` cover it.

@cite{king-2013}'s coordination account implicitly invokes this, since
"every competent, attentive, reasonable hearer" requires a notion of
reasonableness both interlocutors agree on — i.e., the intersection. -/
def shared₂ (RS RH : ConceptionOfReasonableness C W E) :
    ConceptionOfReasonableness C W E :=
  fun s => RS s ∧ RH s

/-- Binary *joint* conception: an intention is joint-reasonable iff
`RS` or `RH` covers it.

@cite{ney-2026} §4: "every competent, attentive, reasonable hearer
*who is reasonable by the lights of at least one among the speaker
and the actual hearer*". -/
def joint₂ (RS RH : ConceptionOfReasonableness C W E) :
    ConceptionOfReasonableness C W E :=
  fun s => RS s ∨ RH s

/-- The shared conception is pointwise included in the joint:
`shared₂ ≤ joint₂` for any pair. -/
theorem shared₂_le_joint₂ (RS RH : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    shared₂ RS RH s → joint₂ RS RH s :=
  fun h => Or.inl h.left

/-- `shared₂` is commutative as a predicate (propositionally). -/
theorem shared₂_comm (RS RH : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    shared₂ RS RH s ↔ shared₂ RH RS s :=
  And.comm

/-- `joint₂` is commutative as a predicate (propositionally). -/
theorem joint₂_comm (RS RH : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    joint₂ RS RH s ↔ joint₂ RH RS s :=
  Or.comm

/-- When the two conceptions agree, `shared₂` collapses to either. -/
theorem shared₂_self (R : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    shared₂ R R s ↔ R s :=
  ⟨And.left, fun h => ⟨h, h⟩⟩

/-- When the two conceptions agree, `joint₂` collapses to either. -/
theorem joint₂_self (R : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    joint₂ R R s ↔ R s :=
  ⟨fun | Or.inl h => h | Or.inr h => h, Or.inl⟩

/-! ## Indexed-family generalizations (mathlib-style indexed inf/sup) -/

variable {ι : Sort*}

/-- The shared conception across an indexed family of agents. -/
def shared (cs : ι → ConceptionOfReasonableness C W E) :
    ConceptionOfReasonableness C W E :=
  fun s => ∀ i, cs i s

/-- The joint conception across an indexed family of agents. -/
def joint (cs : ι → ConceptionOfReasonableness C W E) :
    ConceptionOfReasonableness C W E :=
  fun s => ∃ i, cs i s

/-- For any nonempty family, the shared conception is pointwise
included in the joint. -/
theorem shared_le_joint [Nonempty ι] (cs : ι → ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) :
    shared cs s → joint cs s :=
  fun h => let ⟨i⟩ := ‹Nonempty ι›; ⟨i, h i⟩

end ConceptionOfReasonableness

end Semantics.Reference.Metasemantics
