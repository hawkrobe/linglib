import Linglib.Phenomena.Assertion.Basic
import Linglib.Theories.Pragmatics.Assertion.Gunlogson

/-!
Gunlogson Felicity ↔ Contextual Evidence Bias
@cite{bring-gunlogson-2000} @cite{gunlogson-2001} @cite{romero-2024}

Connects @cite{gunlogson-2001}'s felicity condition on rising declaratives
to the contextual evidence framework of @cite{bring-gunlogson-2000}.

## The Paper's Deepest Claim

The Contextual Bias Condition (CBC) — that rising declaratives require
the addressee to already be committed to p — is not stipulated. It
*follows* from the uninformativeness requirement on questioning:

1. Questioning requires uninformativeness for the addressee (Ch. 4 §4.1)
2. A rising declarative about p is uninformative for the addressee iff
   the addressee's commitment set already entails p
3. Therefore: rising declaratives can only question about p when the
   addressee is already committed to p (= the CBC)

This derivation is formalized in `Gunlogson.cbc_from_uninformativeness`.

-/

namespace BringGunlogson2000

open Pragmatics.Assertion.Gunlogson
open Core.Discourse.Commitment

-- ════════════════════════════════════════════════════
-- § 1. Felicity ↔ Evidence
-- ════════════════════════════════════════════════════

/-- Rising declaratives require exactly `forP` evidence (coarse version).

    This is the coarser formulation using the `ContextualEvidence` type
    shared with polar question bias. The precise version
    is `cbcMet`, which checks the addressee's actual commitment state. -/
theorem rising_requires_forP {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.Prop' W) :
    (s.risingDeclarativeFelicitous p .forP).isSome = true ∧
    (s.risingDeclarativeFelicitous p .neutral).isNone = true ∧
    (s.risingDeclarativeFelicitous p .againstP).isNone = true :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. The Three Generalizations (Ch. 2)
-- ════════════════════════════════════════════════════

/-- Generalization (8): Declaratives express bias.

    A falling declarative always adds a self-generated commitment to
    the speaker — the speaker is biased toward p. This is why
    falling declaratives cannot be used as neutral questions. -/
theorem declaratives_express_bias {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.Prop' W) :
    (s.fallingDeclarative p).speakerSlate.commitments.length =
    s.speakerSlate.commitments.length + 1 := by
  simp only [GunlogsonState.fallingDeclarative, TaggedSlate.add, List.length_cons]

/-- Generalization (9): Rising declaratives do not commit the speaker.

    The speaker's slate is unchanged — directly verified by
    definitional equality. -/
theorem rising_no_speaker_commitment' {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.Prop' W) :
    (s.risingDeclarative p).speakerSlate = s.speakerSlate := rfl

/-- Generalization (10): The CBC.

    Rising declaratives can only be used as questions when the
    addressee is already committed to p. This is the `cbcMet`
    condition, and it's derived (not stipulated) via
    `cbc_from_uninformativeness`. -/
theorem cbc_derived {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.Prop' W)
    (hcbc : s.cbcMet p) :
    s.uninformativeForAddressee p :=
  GunlogsonState.cbc_from_uninformativeness s p hcbc

-- ════════════════════════════════════════════════════
-- § 3. Response Dynamics
-- ════════════════════════════════════════════════════

/-- Rising from empty is unstable. Confirmation does NOT restore
    stability (the other-generated commitment persists). Rejection
    is a no-op (the state stays unstable). -/
theorem rising_response_dynamics {W : Type*}
    (p : Core.Proposition.Prop' W) :
    let s₀ := GunlogsonState.empty (W := W)
    let s₁ := s₀.risingDeclarative p
    let s₂ := s₁.confirm p
    let s₃ := s₁.reject
    s₀.isStable = true ∧
    s₁.isStable = false ∧
    s₂.isStable = false ∧  -- confirm doesn't remove other-generated
    s₃.isStable = false :=  -- reject is identity
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Rising Declaratives ≠ Questions
-- ════════════════════════════════════════════════════

/-- Rising declaratives are not questions: they do not partition
    the context set.

    A polar question {p, ¬p} partitions the context into p-worlds
    and ¬p-worlds, offering both as live options. A rising declarative
    about p puts p on the addressee's slate as other-generated —
    it has a *preferred* answer (p), unlike a neutral question.

    This is witnessed structurally: rising declaratives add a
    commitment (source-tagged), while questions add a partition.
    Gunlogson's `risingDeclarative` returns a `GunlogsonState` with
    a new commitment, not a set of alternative propositions. -/
theorem rising_is_not_partition {W : Type*}
    (p : Core.Proposition.Prop' W) :
    let s := GunlogsonState.empty.risingDeclarative p
    s.addresseeSlate.commitments.length = 1 :=
  rfl

end BringGunlogson2000
