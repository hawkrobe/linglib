/-!
# Dutch Verb-Particle Constructions
@cite{dendikken-1995}

Lexical entries for Dutch separable verb-particle constructions
(*scheidbaar samengestelde werkwoorden*). Distinct from prefix verbs
(*ver-, be-, ent-*), which are inseparable derivational morphology.
@cite{dendikken-1995} chapter 3 uses Dutch dative-particle facts
extensively in the analysis of triadic constructions.

## Key empirical generalizations (textbook)

1. Separable VPCs surface adjacent in non-finite contexts (`opbellen`,
   `aankomen`) but split under V2 in main clauses
   (`Hij belt Hsu op` vs `dat hij Hsu opbelt`).
2. The particle is a head-final separable element; under V2 the verb
   raises to C while the particle stays in situ.
3. Inseparable prefix verbs (`verstaan`, `bezoeken`) never split — they
   are derivational, not particle constructions.

## Cross-references

- Phenomena/Constructions/ParticleVerbs/Studies/Dendikken1995.lean —
  the SC analysis applied to the English cognate facts.

-/

namespace Fragments.Dutch.VerbParticles

/-- A Dutch separable verb-particle entry.
    Records the citation form (P+V written together as in infinitive)
    and the constituent V and particle separately for V2-split contexts. -/
structure DutchVPCEntry where
  /-- Citation infinitive form (particle + verb concatenated). -/
  citationForm : String
  /-- Bare verb stem. -/
  verb         : String
  /-- Separable particle. -/
  particle     : String
  /-- English gloss. -/
  gloss        : String
  deriving Repr, DecidableEq

abbrev opbellen : DutchVPCEntry where
  citationForm := "opbellen"; verb := "bellen"; particle := "op"
  gloss := "phone, call up"

abbrev aankomen : DutchVPCEntry where
  citationForm := "aankomen"; verb := "komen"; particle := "aan"
  gloss := "arrive"

abbrev uitgaan : DutchVPCEntry where
  citationForm := "uitgaan"; verb := "gaan"; particle := "uit"
  gloss := "go out"

abbrev meedoen : DutchVPCEntry where
  citationForm := "meedoen"; verb := "doen"; particle := "mee"
  gloss := "participate"

abbrev doorwerken : DutchVPCEntry where
  citationForm := "doorwerken"; verb := "werken"; particle := "door"
  gloss := "work through"

def inventory : List DutchVPCEntry :=
  [opbellen, aankomen, uitgaan, meedoen, doorwerken]

/-- Each entry's citation form is the concatenation of particle + verb
    (verified per-entry to avoid List-membership unfolding). -/
theorem opbellen_citation : opbellen.citationForm = opbellen.particle ++ opbellen.verb := rfl
theorem aankomen_citation : aankomen.citationForm = aankomen.particle ++ aankomen.verb := rfl
theorem uitgaan_citation : uitgaan.citationForm = uitgaan.particle ++ uitgaan.verb := rfl
theorem meedoen_citation : meedoen.citationForm = meedoen.particle ++ meedoen.verb := rfl
theorem doorwerken_citation : doorwerken.citationForm = doorwerken.particle ++ doorwerken.verb := rfl

/-- All inventory entries have non-empty verb and particle. -/
theorem inventory_well_formed :
    inventory.all (fun e => decide (e.verb ≠ "") && decide (e.particle ≠ "")) = true := by decide

end Fragments.Dutch.VerbParticles
