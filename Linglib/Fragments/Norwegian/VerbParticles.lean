/-!
# Norwegian Verb-Particle Constructions
@cite{dendikken-1995}

Lexical entries for Norwegian (Bokmål) verb-particle constructions,
recording the active/passive word-order asymmetry that distinguishes
Norwegian from English.

## Key empirical generalization (Åfarli 1985 via @cite{dendikken-1995} §2.4.3)

In Norwegian active VPCs, the particle alternates freely between the
inner and outer order (`Han satte ned katten / Han satte katten ned`,
'he set down the cat / he set the cat down'). In **passive** VPCs,
unlike English, the particle may surface to the immediate left of the
participle as a prefix-like incorporation:

  `Vi har (ut)sparka hunden (ut)`   active  — both orders OK
  `Hunden vart (ut)sparka`           passive — leftward incorporation OK

This contrast was a central piece of evidence in @cite{dendikken-1995}
§2.3.3.5 ("The Norwegian parallel") for treating particle incorporation
as available cross-linguistically.

## Cross-references

- Phenomena/Constructions/ParticleVerbs/Studies/Dendikken1995.lean —
  the SC analysis; English does not have the passive incorporation
  option Norwegian shows.

-/

namespace Fragments.Norwegian.VerbParticles

/-- A Norwegian VPC entry. Records the citation infinitive plus the
    constituent verb and particle, and a flag for whether the particle
    can incorporate (prefix the participle) in passives. -/
structure NorwegianVPCEntry where
  /-- Citation form (verb + particle, conventionally written separately). -/
  citationForm           : String
  /-- Bare verb infinitive. -/
  verb                   : String
  /-- Particle. -/
  particle               : String
  /-- English gloss. -/
  gloss                  : String
  /-- Whether the particle may incorporate as a prefix on the passive
      participle (e.g. `(ut)sparka` 'kicked out'). Per @cite{dendikken-1995}
      §2.4.3 (citing Åfarli 1985), the productive pattern in Norwegian. -/
  passiveIncorporation   : Bool
  deriving Repr, DecidableEq

abbrev sparke_ut : NorwegianVPCEntry where
  citationForm := "sparke ut"; verb := "sparke"; particle := "ut"
  gloss := "kick out"; passiveIncorporation := true

abbrev sette_ned : NorwegianVPCEntry where
  citationForm := "sette ned"; verb := "sette"; particle := "ned"
  gloss := "set down"; passiveIncorporation := true

abbrev klippe_av : NorwegianVPCEntry where
  citationForm := "klippe av"; verb := "klippe"; particle := "av"
  gloss := "cut off"; passiveIncorporation := true

abbrev kjøre_bort : NorwegianVPCEntry where
  citationForm := "kjøre bort"; verb := "kjøre"; particle := "bort"
  gloss := "drive away"; passiveIncorporation := true

abbrev sende_ut : NorwegianVPCEntry where
  citationForm := "sende ut"; verb := "sende"; particle := "ut"
  gloss := "send out"; passiveIncorporation := true

def inventory : List NorwegianVPCEntry :=
  [sparke_ut, sette_ned, klippe_av, kjøre_bort, sende_ut]

/-- All inventory entries permit passive incorporation — the productive
    Norwegian pattern that contrasts with English. -/
theorem all_passive_incorporation :
    inventory.all (·.passiveIncorporation) = true := by decide

/-- Entries are well-formed: non-empty verb and particle. -/
theorem inventory_well_formed :
    inventory.all (fun e => decide (e.verb ≠ "") && decide (e.particle ≠ "")) = true := by decide

end Fragments.Norwegian.VerbParticles
