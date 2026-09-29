module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Dutch verbs

This file defines the Dutch verb as a lexical entry: the root `Verb` with the simplex verb it
is formed on and its formation, simplex, with a separable particle or with an inseparable
prefix, from which its infinitive and past participle follow. Broekhuis and Corver's grammar
forms the past participle with the circumfix *ge-…-d*, *ge-…-t* or *ge-…-en*: *gestraft*
'punished'. A verb with an unstressed prefix, *be-*, *ver-*, *ont-* or *her-*, never realizes
the *ge-* part, *ontdekt* 'discovered', while a particle precedes it, *opgebeld* 'called up'
and not *geopbeld*, which shows that the particle does not form a morphological unit with the
verb; under verb second the particle is stranded, *Jan belde Marie gisteren op* 'Jan called
Marie yesterday'.

The perfect auxiliary follows from the verb on a frame (`Dutch.Verbs.perfect`). Transitive and
intransitive verbs take *hebben*, and unaccusative verbs take *zijn* when they are telic and
*hebben* when they are atelic; a directional phrase makes a verb of motion unaccusative and, if it
bounds the path, telic, so *De jongen heeft gewandeld* 'the boy walked' but *De jongen is naar
Groningen gewandeld* 'the boy walked to Groningen'. *Blijven* 'stay', whose state continues,
takes *zijn*.

## Main definitions

* `Dutch.Verbs.Verb`: the entry.
* `Dutch.Verbs.Verb.pastParticiple`: the past participle, from the formation.
* `Dutch.Verbs.Verb.withPath`: the entry with a path phrase.
* `Dutch.Verbs.perfect`: the auxiliary of the perfect of a verb on a frame.
* `Dutch.Verbs.inventory`: the entries.

## Main results

* `Dutch.Verbs.pastParticiple_particle`, `Dutch.Verbs.pastParticiple_prefix`: a particle
  precedes the *ge-* of the participle and a prefix replaces it.
* `Dutch.Verbs.opgebeld`, `Dutch.Verbs.ontdekt`: the grammar's examples.
* `Dutch.Verbs.perfect_withPath_intransitive`: a bounded directional phrase gives a dynamic
  intransitive verb *zijn*.

## Implementation notes

* The participle of the simplex verb is stored without its *ge-*, as `German.Conjugation.Stem`
  stores it, and the entry does not conjugate further. The syntax of the particle, which the
  grammar and den Dikken analyse, is left to the studies.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume I: Verbs and Verb Phrases 1:
  Characterization, Classification and Lexical Projection* (2026)][broekhuis-corver-2026e]
* [levin-hovav-1995]
* [sorace-2000]
-/

@[expose] public section

namespace Dutch.Verbs

open ArgumentStructure

/-- A verb is formed on a simplex verb either not at all, with a separable particle, which
precedes the *ge-* of the past participle, or with an unstressed inseparable prefix, whose past
participle has no *ge-*. -/
inductive Formation where
  | simplex
  | particle (form : String)
  | prefix (form : String)
  deriving DecidableEq, Repr

/-- The particle or prefix of a formation, empty for a simplex verb. -/
def Formation.form : Formation → String
  | .simplex => ""
  | .particle p => p
  | .prefix p => p

/-- A Dutch verb is the root entry with the simplex verb it is formed on and its formation. -/
structure Verb extends _root_.Verb where
  /-- The infinitive of the simplex verb. -/
  base : String
  /-- The past participle of the simplex verb without its *ge-*. -/
  participle : String
  /-- The formation. -/
  formation : Formation := .simplex
  deriving BEq

namespace Verb

/-- The infinitive puts the particle or prefix before the simplex verb. -/
def infinitive (v : Verb) : String := v.formation.form ++ v.base

/-- The past participle has *ge-* on the simplex verb, after a particle, and replaced by a
prefix. -/
def pastParticiple (v : Verb) : String :=
  match v.formation with
  | .simplex => "ge" ++ v.participle
  | .particle p => p ++ "ge" ++ v.participle
  | .prefix p => p ++ v.participle

/-- A verb is separable when it is formed with a particle. -/
def IsSeparable (v : Verb) : Prop := ∃ p, v.formation = .particle p

instance (v : Verb) : Decidable v.IsSeparable :=
  match h : v.formation with
  | .particle p => isTrue ⟨p, h⟩
  | .simplex => isFalse fun ⟨_, h'⟩ ↦ by simp [h] at h'
  | .prefix _ => isFalse fun ⟨_, h'⟩ ↦ by simp [h] at h'

end Verb

/-- `simplex inf pp` is the simplex transitive verb with the infinitive `inf` and the past
participle `pp`, given with its *ge-*. -/
def simplex (inf pp : String) : Verb :=
  { form := inf, frames := [ArgumentFrame.np], base := inf,
    participle := match pp.toList with
      | 'g' :: 'e' :: r => String.ofList r
      | _ => pp }

/-- `particleVerb p v` is the verb formed on `v` with the separable particle `p`. -/
def particleVerb (p : String) (v : Verb) : Verb :=
  { v with form := p ++ v.form, formation := .particle p }

/-- `prefixVerb p v` is the verb formed on `v` with the inseparable prefix `p`. -/
def prefixVerb (p : String) (v : Verb) : Verb :=
  { v with form := p ++ v.form, formation := .prefix p }

/-- A particle precedes the *ge-* of the past participle. -/
theorem pastParticiple_particle (p : String) (v : Verb) :
    (particleVerb p v).pastParticiple = p ++ "ge" ++ v.participle := rfl

/-- A prefix replaces the *ge-* of the past participle. -/
theorem pastParticiple_prefix (p : String) (v : Verb) :
    (prefixVerb p v).pastParticiple = p ++ v.participle := rfl

/-- A verb formed with a particle is separable and one formed with a prefix is not. -/
theorem isSeparable_particleVerb_not_prefixVerb (p : String) (v : Verb) :
    (particleVerb p v).IsSeparable ∧ ¬ (prefixVerb p v).IsSeparable :=
  ⟨⟨p, rfl⟩, fun ⟨_, h⟩ ↦ by simp [prefixVerb] at h⟩

/-! ### Simplex verbs -/

/-- *straffen* 'punish', *gestraft*. -/
def straffen : Verb := simplex "straffen" "gestraft"

/-- *kussen* 'kiss', *gekust*. -/
def kussen : Verb := simplex "kussen" "gekust"

/-- *bellen* 'call', *gebeld*. -/
def bellen : Verb := simplex "bellen" "gebeld"

/-- *voeren* 'carry', *gevoerd*. -/
def voeren : Verb := simplex "voeren" "gevoerd"

/-- *halen* 'fetch', *gehaald*. -/
def halen : Verb := simplex "halen" "gehaald"

/-- *dekken* 'cover', *gedekt*. -/
def dekken : Verb := simplex "dekken" "gedekt"

/-- *dienen* 'serve', *gediend*. -/
def dienen : Verb := simplex "dienen" "gediend"

/-! ### Particle verbs -/

/-- *opbellen* 'call up', formed on *bellen* with *op*, *opgebeld*. -/
def opbellen : Verb := particleVerb "op" bellen

/-- *uitvoeren* 'carry out', formed on *voeren* with *uit*, *uitgevoerd*. -/
def uitvoeren : Verb := particleVerb "uit" voeren

/-- *afhalen* 'pick up', formed on *halen* with *af*, *afgehaald*. -/
def afhalen : Verb := particleVerb "af" halen

/-! ### Prefixed verbs -/

/-- *ontdekken* 'discover', formed on *dekken* with *ont-*, *ontdekt*. -/
def ontdekken : Verb := prefixVerb "ont" dekken

/-- *bedekken* 'cover', formed on *dekken* with *be-*, *bedekt*. -/
def bedekken : Verb := prefixVerb "be" dekken

/-- *verdienen* 'deserve, earn', formed on *dienen* with *ver-*, *verdiend*. -/
def verdienen : Verb := prefixVerb "ver" dienen

/-- *herhalen* 'repeat', formed on *halen* with *her-*, *herhaald*. -/
def herhalen : Verb := prefixVerb "her" halen

/-! ### Monadic verbs

The monadic verbs of [sorace-2000]'s Dutch examples and of the grammar's discussion of motion
verbs, with the frame the grammar's unaccusativity tests assign them (§2.1). -/

/-- *komen* 'come', *kom - kwam - gekomen*, an unaccusative verb of motion to a goal. -/
def komen : Verb :=
  { simplex "komen" "gekomen" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement,
    direction := some .goal }

/-- *sterven* 'die', an unaccusative verb denoting a transition: *De oude man is gestorven*. -/
def sterven : Verb :=
  { simplex "sterven" "gestorven" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement }

/-- *groeien* 'grow', an unaccusative verb of change along a scale of size. -/
def groeien : Verb :=
  { simplex "groeien" "gegroeid" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .accomplishment,
    scaleDimension := some .generalSize }

/-- *stijgen* 'rise', an unaccusative verb of change along a scale of height. -/
def stijgen : Verb :=
  { simplex "stijgen" "gestegen" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .accomplishment,
    scaleDimension := some .height }

/-- *blijven* 'stay', an unaccusative verb expressing that a state continues to exist (§1.2), with
the auxiliary *zijn*: *Was dan ook wat langer gebleven!* 'You should have stayed a bit longer!'. -/
def blijven : Verb :=
  { simplex "blijven" "gebleven" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .state,
    phasal := some .continuation }

/-- *overblijven* 'remain, be left', formed on *blijven* with the particle *over*. -/
def overblijven : Verb := particleVerb "over" blijven

/-- *duren* 'last', stative. -/
def duren : Verb :=
  { simplex "duren" "geduurd" with
    frames := [ArgumentFrame.intransitive], vendlerClass := some .state }

/-- *staan* 'stand', a stative verb of location, an atelic unaccusative verb with *hebben*: *Jan
heeft lang op het perron gestaan*. -/
def staan : Verb :=
  { simplex "staan" "gestaan" with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .state }

/-- *bestaan* 'exist', formed on *staan* with the prefix *be-*. -/
def bestaan : Verb := prefixVerb "be" staan

/-- *blazen* 'blow', an intransitive activity with an agentive subject. -/
def blazen : Verb :=
  { simplex "blazen" "geblazen" with
    frames := [ArgumentFrame.intransitive], vendlerClass := some .activity,
    subjectEntailments := some activitySubjectProfile }

/-- *lopen* 'walk, run', *loop - liep - gelopen*, an agentive verb of manner of motion, intransitive
([levin-hovav-1995] p. 148). -/
def lopen : Verb :=
  { simplex "lopen" "gelopen" with
    frames := [ArgumentFrame.intransitive, ArgumentFrame.spatialPP], vendlerClass := some .activity,
    direction := some .place }

/-- *wandelen* 'walk', an intransitive verb of manner of motion: *De jongen heeft gewandeld*. -/
def wandelen : Verb :=
  { simplex "wandelen" "gewandeld" with
    frames := [ArgumentFrame.intransitive, ArgumentFrame.spatialPP], vendlerClass := some .activity,
    direction := some .place }

/-- *rollen* 'roll', a nonagentive verb of manner of motion, unaccusative ([levin-hovav-1995]
pp. 147–148) and atelic. -/
def rollen : Verb :=
  { simplex "rollen" "gerold" with
    frames := [ArgumentFrame.unaccusative, ArgumentFrame.spatialPP], vendlerClass := some .activity,
    direction := some .place }

/-! ### The perfect auxiliary -/

/-- The entry with a path phrase of reading `p`, its forms kept (`_root_.Verb.withPath`). -/
def Verb.withPath (v : Verb) (p : Adposition.SpatialReading) : Verb :=
  { v with toVerb := v.toVerb.withPath p }

@[simp] theorem Verb.toVerb_withPath (v : Verb) (p : Adposition.SpatialReading) :
    (v.withPath p).toVerb = v.toVerb.withPath p := rfl

/-- The auxiliary of the perfect of `v` on the frame `fr` ([broekhuis-corver-2026e] §§2.1–2.2):
*zijn* on an unaccusative frame when the verb is telic, and on an intransitive frame when a
directional phrase gives the verb of motion a path and makes it telic, since the phrase makes it
unaccusative; *hebben* otherwise, for transitive and intransitive verbs and for atelic
unaccusative ones; and *zijn* for *blijven*, whose state continues. -/
def perfect (v : Verb) (fr : ArgumentFrame) : ArgumentStructure.PerfectAux :=
  if v.phasal = some .continuation then .be
  else if (fr.IsUnaccusative ∨ fr.IsIntransitive ∧ v.direction.any (· != .place)) ∧
      v.vendlerClass.any (·.telicity == .telic) then .be
  else .have

/-- A bounded directional phrase gives a dynamic intransitive verb *zijn*: *De jongen is naar
Groningen gewandeld* (§2.2, (274b)). -/
theorem perfect_withPath_intransitive {v : Verb} {p : Adposition.SpatialReading}
    (hv : v.TakesSpatial) (hd : p.direction ≠ .place) (hb : p.bounded) {c : Aspect.VendlerClass}
    (hc : v.vendlerClass = some c) (hdyn : c.dynamicity = .dynamic) :
    perfect (v.withPath p) .intransitive = .be := by
  simp [perfect, Verb.withPath, hv, hd, hb, hc, ArgumentFrame.intransitive,
    ArgumentFrame.IsIntransitive, Aspect.VendlerClass.telicity_telicize hdyn]

/-- *Wandelen* takes *hebben*, with *zijn* under a directional phrase and *hebben* under a
locational one (§2.2, (273)–(275)). -/
example : perfect wandelen .intransitive = .have ∧
    perfect (wandelen.withPath Adposition.into) .intransitive = .be ∧
    perfect (wandelen.withPath Adposition.behind) .intransitive = .have := by
  decide

/-- The auxiliaries of [sorace-2000]'s Dutch examples: *zijn* for *komen* (1c), *sterven* (9b),
*groeien* (10a), *stijgen* (11), *overblijven* (18a) and *blijven* (19b); *hebben* for *duren*
(18b), *staan* (24a), *bestaan* (24b), *blazen* (33c), *lopen* (37b) and *rollen* (39a); and *zijn*
for *rollen* with a directional phrase (39b). -/
example :
    [perfect komen .unaccusative, perfect sterven .unaccusative, perfect groeien .unaccusative,
      perfect stijgen .unaccusative, perfect overblijven .unaccusative,
      perfect blijven .unaccusative] = [.be, .be, .be, .be, .be, .be] ∧
    [perfect duren .intransitive, perfect staan .unaccusative, perfect bestaan .unaccusative,
      perfect blazen .intransitive, perfect lopen .intransitive, perfect rollen .unaccusative] =
      [.have, .have, .have, .have, .have, .have] ∧
    perfect (rollen.withPath Adposition.into) .unaccusative = .be := by
  decide

/-! ### The inventory -/

/-- `inventory` lists the entries. -/
def inventory : List Verb :=
  [straffen, kussen, bellen, voeren, halen, dekken, dienen,
   opbellen, uitvoeren, afhalen, ontdekken, bedekken, verdienen, herhalen,
   komen, sterven, groeien, stijgen, blijven, overblijven, duren, staan, bestaan, blazen, lopen,
   wandelen, rollen]

/-- Every entry is cited by its infinitive. -/
theorem form_eq_infinitive : ∀ v ∈ inventory, v.form = v.infinitive := by decide

/-- Every verb of manner of motion selects a directional phrase, so that all of them take *zijn*
under one that bounds the path ([sorace-2000] §4.3, Dutch "the most systematic language in this
respect"). -/
theorem takesSpatial_of_direction_eq_place :
    ∀ v ∈ inventory, v.direction = some .place → v.TakesSpatial := by
  decide

/-- *opgebeld* and *uitgevoerd*, with the particle before *ge-*. -/
theorem opgebeld :
    opbellen.pastParticiple = "opgebeld" ∧ uitvoeren.pastParticiple = "uitgevoerd" := by
  decide

/-- *ontdekt* and *verdiend*, without *ge-*. -/
theorem ontdekt :
    ontdekken.pastParticiple = "ontdekt" ∧ verdienen.pastParticiple = "verdiend" := by
  decide

/-- An entry's participle has *ge-* after its particle or prefix exactly when the entry is
separable or simplex. -/
theorem ge_after_formation_iff :
    ∀ v ∈ inventory,
      (['g', 'e'] <+: (v.pastParticiple.toList.drop v.formation.form.length) ↔
        v.IsSeparable ∨ v.formation = .simplex) := by
  decide

end Dutch.Verbs
