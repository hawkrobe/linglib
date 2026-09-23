import Linglib.Syntax.Voice.Basic
import Linglib.Fragments.English.Adposition

/-!
# English diathesis alternations

The alternations of English that pair two argument frames of one verb, as `Voice` values:
the initial and the derived frame with the slot correspondence between them, the preposition
fixed where the alternation fixes it. The causative/inchoative and induced action
alternations are the anticausative and the causative of `Syntax/Voice/Basic.lean`; the
unexpressed object alternations drop the object with an interpretation; the dative and
benefactive alternations make the *to* and *for* phrase the first object; the conative,
substance/source, spray/load, swarm, material/product, total transformation, body-part
possessor ascension and instrument subject alternations are stated by their frames. The
middle, the passives, the postverbal-subject alternations and the constructions of
[levin-1993] chapter 7 are not pairs of frames and are not here. The sentences are
[levin-1993]'s.

## References

* [levin-1993]
-/

namespace English.Alternations

open Voice ArgumentFrame.Slot Adpositions

/-- *Janet broke the cup* ~ *The cup broke*: the anticausative. -/
abbrev causativeInchoative : Voice := anticausative

/-- *The horse jumped over the fence* ~ *Sylvia jumped the horse over the fence*: the
causative. -/
abbrev inducedAction : Voice := causative

/-- *Margaret cut the bread* ~ *Margaret cut at the bread*: the object becomes an *at*
phrase. -/
def conative : Voice := { antipassive with target := .pp (some at_) }

/-- *Heat radiates from the sun* ~ *The sun radiates heat*: the *from* phrase becomes the
subject and the subject the object. -/
def substanceSource : Voice :=
  { source := .pp (some from_), target := .np,
    correspondence := [(external, complement 0), (complement 0, external)] }

/-- The unexpressed object alternations: the object dropped with interpretation `i`. -/
def objectDrop (i : ImplicitInterp) : Voice :=
  { source := .np, target := .objectDrop (some i),
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- *Mike ate the cake* ~ *Mike ate*: the object understood as unspecified. -/
abbrev unspecifiedObject : Voice := objectDrop .indef

/-- *Mary waved her hand* ~ *Mary waved*: the object understood as a body part. -/
abbrev understoodBodyPartObject : Voice := objectDrop .bodyPart

/-- *Jill dressed herself* ~ *Jill dressed*: the object understood as the subject. -/
abbrev understoodReflexiveObject : Voice := objectDrop .reflexive

/-- *Anne met Cathy* ~ *Anne and Cathy met*: the object understood reciprocally. -/
abbrev understoodReciprocalObject : Voice := objectDrop .reciprocal

/-- The dative and benefactive alternations: the *p* phrase becomes the first object. -/
def toDoubleObject (p : Adposition) : Voice :=
  { source := .np_pp (some p), target := .np_np,
    correspondence := [(external, external), (complement 0, complement 1),
      (complement 1, complement 0)] }

/-- *Bill sold a car to Tom* ~ *Bill sold Tom a car*. -/
abbrev dative : Voice := toDoubleObject to_

/-- *Martha carved a toy for the baby* ~ *Martha carved the baby a toy*. -/
abbrev benefactive : Voice := toDoubleObject for_

/-- *Jack sprayed paint on the wall* ~ *Jack sprayed the wall with paint*: the spatial
phrase becomes the object and the object a *with* phrase. -/
def sprayLoad : Voice :=
  { source := ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    target := .np_pp (some with_),
    correspondence := [(external, external), (complement 0, complement 1),
      (complement 1, complement 0)] }

/-- *Bees are swarming in the garden* ~ *The garden is swarming with bees*: the intransitive
spray/load alternation, the spatial phrase becoming the subject and the subject a *with*
phrase. -/
def swarm : Voice :=
  { source := .pp none, target := .pp (some with_),
    correspondence := [(external, complement 0), (complement 0, external)] }

/-- *Jessica sprayed paint on the wall* ~ *Paint sprayed on the wall*: the causative/inchoative
alternation of the locative variant of `sprayLoad`. -/
def causativeInchoativeLocativeVariant : Voice :=
  { source := ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, target := .pp none,
    correspondence := [(complement 0, external), (complement 1, complement 0)] }

/-- *Jessica sprayed the wall with paint* ~ *The wall sprayed with paint*: the
causative/inchoative alternation of the *with* variant of `sprayLoad`. -/
def causativeInchoativeWithVariant : Voice :=
  { source := .np_pp (some with_), target := .pp (some with_),
    correspondence := [(complement 0, external), (complement 1, complement 0)] }

/-- *Martha carved a toy out of the piece of wood* ~ *Martha carved the piece of wood into a
toy*. -/
def materialProduct : Voice :=
  { source := .np_pp (some outOf), target := .np_pp (some into),
    correspondence := [(external, external), (complement 0, complement 1),
      (complement 1, complement 0)] }

/-- *The witch turned him into a frog* ~ *The witch turned him from a prince into a frog*.
-/
def totalTransformation : Voice :=
  { source := .np_pp (some into),
    target := ⟨some .nominal,
      [.nominal, .adpositional (some .spatial) (some from_),
        .adpositional (some .spatial) (some into)]⟩,
    correspondence := [(external, external), (complement 0, complement 0),
      (complement 1, complement 2)] }

/-- *Selina touched the horse's flank* ~ *Selina touched the horse on the flank*: the
possessor becomes the object and the body part an *on* phrase. -/
def bodyPartPossessorAscension : Voice :=
  { source := .np, target := .np_pp (some on),
    correspondence := [(external, external), (complement 0, complement 1)] }

/-- *David broke the window with a hammer* ~ *The hammer broke the window*: the *with* phrase
becomes the subject. -/
def instrumentSubject : Voice :=
  { source := .np_pp (some with_), target := .np,
    correspondence := [(complement 0, complement 0), (complement 1, external)] }

end English.Alternations
