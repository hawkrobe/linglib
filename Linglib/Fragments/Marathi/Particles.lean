/-!
# Marathi Utterance-Final Particles
@cite{deo-2025-bara} @cite{deo-2023}

Lexical entries for Marathi utterance-final discourse particles. The
semantic/pragmatic content lives in `Phenomena/SentenceMood/Studies/Deo2025.lean`;
this file just packages the basic morphological + clause-type-distribution data.
-/

namespace Fragments.Marathi.Particles

/-- A Marathi utterance-final particle entry, with the clause types and
    illocutionary acts it is felicitous in.

    Boolean-valued lookup fields would be the lower-tech encoding;
    `Prop` lets the felicity facts plug directly into proofs without a
    `decide` translation. -/
structure ParticleEntry where
  /-- Surface form (in IPA-ish romanization). -/
  form : String
  /-- Standard gloss. -/
  gloss : String
  /-- Felicitous in declaratives. -/
  inDeclaratives : Prop
  /-- Felicitous in imperatives. -/
  inImperatives : Prop
  /-- Felicitous in wh-interrogatives. -/
  inWhInterrogatives : Prop
  /-- Felicitous in polar interrogatives. @cite{deo-2025-bara} reports
      `bərə` is *never* used in polar interrogatives (§ 1, p. 387). -/
  inPolarInterrogatives : Prop
  /-- The particle conventionally signals a *preferential* commitment
      dimension on top of the clause-type-determined commitment.
      `bərə` does (@cite{deo-2025-bara} (20)); pure clause-typing particles
      like `ka` (polar Q) do not. -/
  carriesPreferentialCommitment : Prop

/-- *bərə* — utterance-final particle that conventionally signals the
    speaker's preference that the addressee take on the prejacent as a
    *dependent* doxastic or preferential commitment, with a felicity
    condition tying this uptake to a salient addressee-benefiting goal.

    @cite{deo-2025-bara} (20)–(21). The semantic/pragmatic apparatus
    lives in `Phenomena/SentenceMood/Studies/Deo2025.lean`. -/
def bara : ParticleEntry where
  form  := "bərə"
  gloss := "BARA"
  inDeclaratives := True
  inImperatives := True
  inWhInterrogatives := True
  inPolarInterrogatives := False
  carriesPreferentialCommitment := True

/-- *na* — utterance-final particle analyzed in @cite{deo-2023} as
    signalling preference for *independent* shared commitment (CG
    update; doxastic sourcehood mirror of `bərə`'s dependent-uptake
    convention).

    Stub entry — full lexical/semantic apparatus deferred to a future
    `Phenomena/SentenceMood/Studies/Deo2023.lean`. The clause-type
    distribution fields are placeholders; @cite{deo-2025-bara}
    footnote 6 (p. 392) only attests *na* as one of the four
    imperative-augmenting particles (*na, hã/h̆ə, ki, bərə*); the
    declarative/interrogative pattern is unverified pending the
    @cite{deo-2023} formalization.
    `carriesPreferentialCommitment := false` reflects @cite{deo-2023}'s
    framing as a *doxastic* (CG-update) particle, not preferential. -/
def na : ParticleEntry where
  form  := "na"
  gloss := "NA"
  inDeclaratives := True
  inImperatives := True
  inWhInterrogatives := False
  inPolarInterrogatives := False
  carriesPreferentialCommitment := False

/-- All Marathi utterance-final particles indexed in this file. -/
def allParticles : List ParticleEntry := [bara, na]

end Fragments.Marathi.Particles
