import Linglib.Theories.Semantics.Reference.Metasemantics.Reasonableness

/-!
# Coordination accounts of demonstrative reference
@cite{king-2013} @cite{king-2014a} @cite{king-2014b} @cite{ney-2026}

The *coordination account* @cite{king-2013}: a speaker S's use of
demonstrative δ in context c has o as its semantic value iff

  (A) S intends o to be the semantic value of δ in c; and
  (B) a competent, reasonable, attentive hearer who knows the common
      ground would recognize that S so intends, in the way S intends
      to be recognized.

Different metasemantic accounts in this family vary clause (B) by
varying the *conception of reasonableness* on which "reasonable hearer"
is defined.

## King's literal account vs. Ney's binary reconstruction

@cite{king-2013} as written posits a *single* objective conception of
reasonableness — clause (B) refers to "every competent, attentive,
reasonable hearer who knows the common ground", not to a hearer
reasonable per any particular interlocutor's lights. This is the
parametric `coordination R` directly: King's literal account is
`coordination R` for some unspecified `R`.

@cite{ney-2026} §4 argues that, for the prima facie challenge to bite,
King's account must be reconstructed in interlocutor-relative terms:
the conception that's available from the common ground is at most the
*intersection* of speaker's and actual hearer's individual conceptions.
That is `coordination.kingNeyReconstruction RS RH := coordination
(shared₂ RS RH)`. Ney's revision then weakens intersection to union:
`coordination.neyRevision RS RH := coordination (joint₂ RS RH)`.

Both `kingNeyReconstruction` and `neyRevision` live in the binary-
conception framing Ney sets up for the comparison. King's text only
licenses `coordination R` for a single `R`.

## Other accounts in this family (not yet instantiated)

`coordination` shares the abstract shape of @cite{lewis-2020} (speaker-
authority), @cite{stojnic-2024} (felicitous underspecification), and
@cite{stojnic-stone-lepore-2017} (discourse-structured). They are not
yet written here; @cite{ney-2026}'s argument concerns King's specific
implementation, and adding the others is left for a later expansion of
the metasemantics literature in linglib.

## Key results

- `coordination_mono`: `coordination` is monotone in the conception
- `kingNeyReconstruction_le_neyRevision`: King's reconstruction is more
  restrictive than Ney's revision (pointwise, by `shared₂ ≤ joint₂`)
- `kingNeyReconstruction_eq_neyRevision_when_aligned`: when interlocutors
  share their conception, the two binary accounts coincide — the
  distinction matters only when conceptions diverge (typical of
  @cite{asher-lascarides-2013} strategic conversations)
-/

namespace Semantics.Reference.Metasemantics

open Core.CommonGround

universe u v w

namespace Account

variable {C : Type u} {W : Type v} {E : Type w}

/-! ## The parametric coordination account -/

/-- The parametric coordination account, @cite{king-2013}: succeed iff
the conception of reasonableness `R` covers the speaker's intention.

This is also King's account *as he literally wrote it* (a single
unspecified objective `R`). The two binary-conception variants below
(`kingNeyReconstruction` and `neyRevision`) are Ney 2026's framing for
comparing King with the revision; King's text only licenses
`coordination R` for a single `R`. -/
def coordination (R : ConceptionOfReasonableness C W E) : Account C W E :=
  fun s _cg => R s

/-- `coordination` is monotone in its conception parameter: a more
permissive `R` gives a more permissive account. -/
theorem coordination_mono {R₁ R₂ : ConceptionOfReasonableness C W E}
    (h : ∀ s, R₁ s → R₂ s) :
    ∀ s cg, coordination R₁ s cg → coordination R₂ s cg :=
  fun s _cg hs => h s hs

/-! ## King's account in Ney's binary-conception framing -/

/-- @cite{ney-2026} §4's reconstruction of @cite{king-2013}'s account
in interlocutor-relative terms: the conception of reasonableness is
the *shared* conception (`shared₂`) across the speaker's and the
actual hearer's conceptions.

This is the version @cite{ney-2026} §3 challenges. The challenge: under
the shared conception, whenever a hearer would in fact recognize the
unavowed referent, this *becomes available from the common ground*
(Ney's `<ONE>`-`<FOUR>` argument), contradicting the observed
deniability of the unavowed reference. -/
def coordination.kingNeyReconstruction
    (RS RH : ConceptionOfReasonableness C W E) : Account C W E :=
  coordination (ConceptionOfReasonableness.shared₂ RS RH)

/-! ## Ney's revision -/

/-- @cite{ney-2026} (end of §4): replace the shared conception with the
*joint* conception (`joint₂`) across speaker and actual hearer.

Verbatim revised condition: "every competent, attentive, reasonable
hearer *who is reasonable by the lights of at least one among the
speaker and the actual hearer* … would recognize that S intends o to
be the semantic value of δ in c". -/
def coordination.neyRevision
    (RS RH : ConceptionOfReasonableness C W E) : Account C W E :=
  coordination (ConceptionOfReasonableness.joint₂ RS RH)

/-! ## Relationship between the two binary accounts -/

/-- King's reconstruction is pointwise more restrictive than Ney's
revision: anything the reconstruction validates, Ney does too.

This is the formal counterpart of @cite{ney-2026}'s observation that
the revision is a *weakening* of clause (B), not a strengthening. -/
theorem kingNeyReconstruction_le_neyRevision
    (RS RH : ConceptionOfReasonableness C W E) :
    ∀ s cg, coordination.kingNeyReconstruction RS RH s cg →
            coordination.neyRevision RS RH s cg :=
  fun s _cg => ConceptionOfReasonableness.shared₂_le_joint₂ RS RH s

/-- When speaker and hearer fully share their conception of
reasonableness, the two binary accounts coincide.

The distinction matters only when conceptions diverge (typical of
@cite{asher-lascarides-2013} strategic conversations and the
not-fully-cooperative settings @cite{ney-2026} §2 highlights). -/
theorem kingNeyReconstruction_eq_neyRevision_when_aligned
    (R : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) (cg : CG W) :
    coordination.kingNeyReconstruction R R s cg ↔
    coordination.neyRevision R R s cg := by
  simp [coordination.kingNeyReconstruction, coordination.neyRevision,
        coordination,
        ConceptionOfReasonableness.shared₂_self,
        ConceptionOfReasonableness.joint₂_self]

end Account

end Semantics.Reference.Metasemantics
