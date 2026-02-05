/-!
# Japanese Interrogative Particles

Q-morphemes and related particles in Japanese, following Dayal (2025: §1.3).

Japanese has a three-way distinction in interrogative particles that maps
directly onto the three layers of the left periphery:

1. *ka/no*: Clause-typing particle (CP) — obligatory in subordinated interrogatives
2. *koto*: Appears in declaratives (contrast with *ka* in interrogatives)
3. *kke*: Meta question particle (MQP, SAP) — only in matrix and quotation

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- Sauerland, U. & K. Yatsushiro (2017). Remind-me presuppositions and speech-act
  decomposition. Linguistic Inquiry 48.
- Miyagawa, S. (2012). Agreements that occur mainly in the main clause.
-/

namespace Fragments.Japanese.Particles

/-- Layer of the left periphery that a particle occupies. -/
inductive Layer where
  | cp | perspP | sap
  deriving DecidableEq, Repr, BEq

/-- A Japanese particle entry. -/
structure ParticleEntry where
  form : String
  romaji : String
  layer : Layer
  /-- Does this particle appear in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Does this particle appear in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Does this particle appear in matrix questions? -/
  inMatrix : Bool
  deriving Repr, BEq

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated interrogatives,
    optional in matrix (can be dropped). Marks CP as +WH. -/
def ka : ParticleEntry :=
  { form := "か", romaji := "ka"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := true, inMatrix := true }

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : ParticleEntry :=
  { form := "の", romaji := "no"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := true, inMatrix := true }

/-- *koto* — complementizer for declarative clauses. Contrast with *ka*:
    having *ka* in the embedded clause suffices for interrogative interpretation,
    while *koto* marks a declarative (Dayal 2025: (15)). -/
def koto : ParticleEntry :=
  { form := "こと", romaji := "koto"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := false, inMatrix := false }

/-- *kke* — meta question particle (MQP). Only in matrix questions and quotations.
    Has a "remind-me" presupposition: speaker has forgotten Ans(Q) and believes
    the addressee knows it (Sauerland & Yatsushiro 2017). -/
def kke : ParticleEntry :=
  { form := "っけ", romaji := "kke"
  , layer := .sap
  , inSubordinated := false, inQuasiSub := false, inMatrix := true }

def allParticles : List ParticleEntry := [ka, no_, koto, kke]

end Fragments.Japanese.Particles
