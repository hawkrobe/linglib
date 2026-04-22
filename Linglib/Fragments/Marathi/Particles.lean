/-!
# Marathi Utterance-Final Particles
@cite{deo-2025-bara} @cite{deo-2023}

Lexical entries for Marathi utterance-final discourse particles. The
semantic/pragmatic content lives in `Phenomena/SentenceMood/Studies/Deo2025.lean`;
this file just packages the basic morphological + clause-type-distribution data.
-/

namespace Fragments.Marathi.Particles

/-- A Marathi utterance-final particle entry, with the clause types and
    illocutionary acts it is felicitous in. -/
structure ParticleEntry where
  /-- Surface form (in IPA-ish romanization). -/
  form : String
  /-- Standard gloss. -/
  gloss : String
  /-- Felicitous in declaratives? -/
  inDeclaratives : Bool
  /-- Felicitous in imperatives? -/
  inImperatives : Bool
  /-- Felicitous in wh-interrogatives? -/
  inWhInterrogatives : Bool
  /-- Felicitous in polar interrogatives? @cite{deo-2025-bara} reports
      `bərə` is *never* used in polar interrogatives (§ 1, p. 387). -/
  inPolarInterrogatives : Bool
  /-- Whether the particle conventionally signals a *preferential*
      commitment dimension on top of the clause-type-determined commitment.
      `bərə` does (@cite{deo-2025-bara} (20)); pure clause-typing particles
      like `ka` (polar Q) do not. -/
  carriesPreferentialCommitment : Bool
  deriving Repr, BEq

/-- *bərə* — utterance-final particle that conventionally signals the
    speaker's preference that the addressee take on the prejacent as a
    *dependent* doxastic or preferential commitment, with a felicity
    condition tying this uptake to a salient addressee-benefiting goal.

    @cite{deo-2025-bara} (20)–(21). The semantic/pragmatic apparatus
    lives in `Phenomena/SentenceMood/Studies/Deo2025.lean`. -/
def bara : ParticleEntry where
  form  := "bərə"
  gloss := "BARA"
  inDeclaratives := true
  inImperatives := true
  inWhInterrogatives := true
  inPolarInterrogatives := false
  carriesPreferentialCommitment := true

/-- *na* — utterance-final particle analyzed in @cite{deo-2023} as
    signalling preference for *independent* shared commitment (the
    sourcehood mirror of `bərə`'s dependent-uptake convention).

    Stub entry — full lexical/semantic apparatus deferred to a future
    `Phenomena/SentenceMood/Studies/Deo2023.lean`. -/
def na : ParticleEntry where
  form  := "na"
  gloss := "NA"
  inDeclaratives := true
  inImperatives := true
  inWhInterrogatives := true
  inPolarInterrogatives := false
  carriesPreferentialCommitment := true

/-- All Marathi utterance-final particles indexed in this file. -/
def allParticles : List ParticleEntry := [bara, na]

end Fragments.Marathi.Particles
