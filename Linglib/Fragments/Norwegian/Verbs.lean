module

public import Linglib.Fragments.Norwegian.Conjugation
public import Linglib.Syntax.Category.Verb.Basic

/-!
# Norwegian verbs

This file defines the Bokmål verb as a lexical entry, the root `Verb` with its stem and its
formation, simplex or a verb phrase with a verbal particle. Faarlund, Lie and Vannebo's reference
grammar calls a preposition without a complement that goes with a verb a verbal particle, *kaste
bort* 'throw away', and describes the relation of such a verb phrase to the compound verb with
the same particle as its first member, *bortkaste*. The past participle takes the compound form
more readily than the other forms: after *ha* and *få* the participle of a verb phrase stays a
verb phrase, *Vi har gjort opp saka* 'we have settled the matter', while attributively and after
*være* and *bli* it is compound, *Saka er oppgjort* 'the matter is settled'. The entries are the
particle verbs whose participles the grammar lists and those of den Dikken's Norwegian examples,
with the simplex verbs they are formed on, conjugated by the grammar's classes.

## Main definitions

* `Norwegian.Verbs.Verb`: the entry, the root `Verb` with its stem and its formation.
* `Norwegian.Verbs.transitive`, `Norwegian.Verbs.particleVerb`: the transitive entry of a stem,
  and the verb phrase formed on an entry with a verbal particle.
* `Norwegian.Verbs.Verb.pastParticiple`, `Norwegian.Verbs.Verb.compoundParticiple`: the
  participle of the verb phrase and the compound participle.

## Main results

* `Norwegian.Verbs.compoundParticiple_particleVerb`: the compound participle puts the particle
  before the participle of the simplex verb.
* `Norwegian.Verbs.grammar_compound_participles`: the compound participles the grammar lists
  come out of the rule.

## Implementation notes

The entries are Bokmål with the *-et* forms of the first weak class; den Dikken's examples are
Nynorsk, *sparka*, *klipt*, and are recorded as rows of his study. Which verb phrases also
exist as compound verbs in all their forms, the grammar's three groups, is not recorded.

## References

* [faarlund-lie-vannebo-1997]
* [dendikken-1995]
-/

@[expose] public section

namespace Norwegian.Verbs

open ArgumentStructure Conjugation

/-- A verb is simplex or a verb phrase formed on a simplex verb with a verbal particle. -/
inductive Formation where
  | simplex
  | particle (form : String)
  deriving DecidableEq, Repr

/-- A Norwegian verb is the root entry with its stem and its formation. -/
structure Verb extends _root_.Verb where
  /-- The stem of the simplex verb. -/
  stem : Stem
  /-- The formation. -/
  formation : Formation := .simplex
  deriving BEq

namespace Verb

/-- The past participle of the verb, that of a verb phrase followed by its particle, the form
used after *ha* and *få*. -/
def pastParticiple (v : Verb) : String :=
  match v.formation with
  | .simplex => v.stem.participle
  | .particle p => v.stem.participle ++ " " ++ p

/-- The compound participle of a verb phrase, the particle prefixed to the participle of the
simplex verb, the form used attributively and after *være* and *bli*; a simplex verb has
none. -/
def compoundParticiple (v : Verb) : Option String :=
  match v.formation with
  | .simplex => none
  | .particle p => some (p ++ v.stem.participle)

end Verb

/-- `transitive s` is the transitive entry with the stem `s`. -/
def transitive (s : Stem) : Verb :=
  { form := s.infinitive, frames := [ArgumentFrame.np], stem := s }

/-- `particleVerb p v` is the verb phrase formed on `v` with the verbal particle `p`. -/
def particleVerb (p : String) (v : Verb) : Verb :=
  { v with form := v.form ++ " " ++ p, formation := .particle p }

/-- The compound participle puts the particle before the participle of the simplex verb. -/
theorem compoundParticiple_particleVerb (p : String) (v : Verb) :
    (particleVerb p v).compoundParticiple = some (p ++ v.stem.participle) := rfl

/-- The past participle of a verb phrase is that of the simplex verb followed by the particle. -/
theorem pastParticiple_particleVerb (p : String) (v : Verb) :
    (particleVerb p v).pastParticiple = v.stem.participle ++ " " ++ p := rfl

/-! ### Simplex verbs -/

/-- *kaste* 'throw', the paradigm verb of the first weak class. -/
def kaste : Verb := transitive (weak1 "kaste")

/-- *sparke* 'kick', of the first weak class like the other stems in *-rk*. -/
def sparke : Verb := transitive (weak1 "sparke")

/-- *klippe* 'cut', of the first weak class like the other stems in *-pp*. -/
def klippe : Verb := transitive (weak1 "klippe")

/-- *kjøre* 'drive', of the second weak class with *-te*, a stem in a long vowel and a single
consonant. -/
def kjore : Verb := transitive (weak2a "kjøre")

/-- *sende* 'send', of the second weak class with *-te*, a stem in *-nd*. -/
def sende : Verb := transitive (weak2a "sende")

/-- *sette* 'set', of the second weak class with *-te* and a vowel change, *satte*, *satt*. -/
def sette : Verb := transitive (principalParts "sette" "setter" "satte" "satt")

/-- *gjøre* 'do', of the second weak class with *-de* and a vowel change, *gjør*, *gjorde*,
*gjort*. -/
def gjore : Verb := transitive (principalParts "gjøre" "gjør" "gjorde" "gjort")

/-- *bygge* 'build', of the second weak class with *-de*, a stem in *-gg*. -/
def bygge : Verb := transitive (weak2b "bygge")

/-- *leie* 'rent', of the second weak class with *-de*, a stem in *-ei*. -/
def leie : Verb := transitive (weak2b "leie")

/-- *kle* 'dress', of the second weak class with *-dde*, a stem in a single vowel. -/
def kle : Verb := transitive (weak2c "kle")

/-! ### Verb phrases with a verbal particle -/

/-- *kaste bort* 'throw away', *bortkastet*. -/
def kasteBort : Verb := particleVerb "bort" kaste

/-- *sparke ut* 'kick out', *utsparket*. -/
def sparkeUt : Verb := particleVerb "ut" sparke

/-- *klippe av* 'cut off', *avklippet*. -/
def klippeAv : Verb := particleVerb "av" klippe

/-- *kjøre bort* 'drive away', *bortkjørt*. -/
def kjoreBort : Verb := particleVerb "bort" kjore

/-- *sende ut* 'send out', *utsendt*. -/
def sendeUt : Verb := particleVerb "ut" sende

/-- *sette ned* 'set down', *nedsatt*. -/
def setteNed : Verb := particleVerb "ned" sette

/-- *sette sammen* 'put together', *sammensatt*. -/
def setteSammen : Verb := particleVerb "sammen" sette

/-- *gjøre opp* 'settle', *oppgjort*. -/
def gjoreOpp : Verb := particleVerb "opp" gjore

/-- *bygge ut* 'expand', *utbygd*. -/
def byggeUt : Verb := particleVerb "ut" bygge

/-- *leie ut* 'rent out', *utleid*. -/
def leieUt : Verb := particleVerb "ut" leie

/-- *kle på* 'dress', *påkledd*. -/
def klePaa : Verb := particleVerb "på" kle

/-- The verb phrases with a verbal particle. -/
def particleVerbs : List Verb :=
  [kasteBort, sparkeUt, klippeAv, kjoreBort, sendeUt, setteNed, setteSammen, gjoreOpp, byggeUt,
    leieUt, klePaa]

/-- The compound participles the grammar lists for *gjøre opp*, *kle på*, *sette sammen*,
*bygge ut*, *leie ut* and *kaste bort* come out of the rule. -/
theorem grammar_compound_participles :
    [gjoreOpp, klePaa, setteSammen, byggeUt, leieUt, kasteBort].map Verb.compoundParticiple =
      [some "oppgjort", some "påkledd", some "sammensatt", some "utbygd", some "utleid",
        some "bortkastet"] := by decide

/-- Every verb phrase has a compound participle. -/
theorem particleVerbs_compoundParticiple_isSome :
    ∀ v ∈ particleVerbs, v.compoundParticiple.isSome := by decide

end Norwegian.Verbs
