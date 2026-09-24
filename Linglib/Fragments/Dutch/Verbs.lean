module

public import Linglib.Syntax.Category.Verb.Basic

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

## Main definitions

* `Dutch.Verbs.Verb`: the entry.
* `Dutch.Verbs.Verb.pastParticiple`: the past participle, from the formation.
* `Dutch.Verbs.inventory`: the entries.

## Main results

* `Dutch.Verbs.pastParticiple_particle`, `Dutch.Verbs.pastParticiple_prefix`: a particle
  precedes the *ge-* of the participle and a prefix replaces it.
* `Dutch.Verbs.opgebeld`, `Dutch.Verbs.ontdekt`: the grammar's examples.

## Implementation notes

* The participle of the simplex verb is stored without its *ge-*, as `German.Conjugation.Stem`
  stores it, and the entry does not conjugate further. The syntax of the particle, which the
  grammar and den Dikken analyse, is left to the studies.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume I: Verbs and Verb Phrases 1:
  Characterization, Classification and Lexical Projection* (2026)][broekhuis-corver-2026e]
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

/-! ### The inventory -/

/-- `inventory` lists the entries. -/
def inventory : List Verb :=
  [straffen, kussen, bellen, voeren, halen, dekken, dienen,
   opbellen, uitvoeren, afhalen, ontdekken, bedekken, verdienen, herhalen]

/-- Every entry is cited by its infinitive. -/
theorem form_eq_infinitive : ∀ v ∈ inventory, v.form = v.infinitive := by decide

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
