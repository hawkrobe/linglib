import Mathlib.Tactic.FinCases

/-!
# Norwegian Verb-Particle Constructions
@cite{dendikken-1995}

Lexical entries for Norwegian (Bokmål) verb-particle constructions,
recording the active word-order alternation and the **passive prefix
incorporation** that distinguishes Norwegian from English. In active
clauses the particle alternates freely between inner (V-Prt-NP) and
outer (V-NP-Prt) positions. In passives, unlike English, the particle
may surface to the immediate left of the participle as a prefix-like
incorporation: *Hunden vart utsparka* 'the dog was kicked out'. This
contrast was the central piece of evidence in @cite{dendikken-1995}
§2.3.3.5 ("The Norwegian parallel") for treating particle incorporation
as a cross-linguistically available operation.

## Main definitions

* `NorwegianVPCEntry` — a single entry with citation, surface forms,
  and the passive-incorporation flag.
* `inventory` — five canonical entries.

## Main results

* `inventory_citation_eq` — every entry's citation form is
  `verb ++ " " ++ particle` (Norwegian convention: VPCs written with
  space).
* `inventory_passive_incorporation` — every inventory entry permits
  passive prefix incorporation (the productive Norwegian pattern that
  contrasts with English).

-/

namespace Fragments.Norwegian.VerbParticles

/-- A Norwegian VPC entry. Records (i) the conventional space-separated
    citation form, (ii) the bare verb infinitive and particle, (iii) both
    active and (when available) passive surface participle forms, and
    (iv) the passive-incorporation availability flag. -/
structure NorwegianVPCEntry where
  /-- Citation form, conventionally written with a space:
      *sparke ut*, *sette ned*. -/
  citationForm         : String
  /-- Bare verb infinitive (without particle). -/
  verb                 : String
  /-- The particle. -/
  particle             : String
  /-- Active-clause past participle (verb-medial, particle stays):
      *sparket ut*, *satt ned*. -/
  pastParticipleActive : String
  /-- Whether the particle may prefix the participle in passives —
      the productive Norwegian pattern (per @cite{dendikken-1995}
      §2.3.3.5, citing Åfarli 1985). For all entries here, true. -/
  passiveIncorporation : Bool
  /-- Passive incorporated form (particle prefixed to participle):
      *utsparket*, *nedsatt*. `none` if `passiveIncorporation = false`. -/
  passiveIncorporated  : Option String
  /-- English gloss. -/
  gloss                : String

/-- An entry permits passive prefix incorporation. -/
def AllowsPassiveIncorporation (e : NorwegianVPCEntry) : Prop :=
  e.passiveIncorporation = true

instance : DecidablePred AllowsPassiveIncorporation :=
  fun e => decEq e.passiveIncorporation true

/-! ### Inventory -/

/-- *sparke ut* 'kick out'. Passive incorporation: *utsparket*
    (per @cite{dendikken-1995} §2.4.3 ex. 134, citing Åfarli 1985). -/
def sparke_ut : NorwegianVPCEntry where
  citationForm         := "sparke ut"
  verb                 := "sparke"
  particle             := "ut"
  pastParticipleActive := "sparket ut"
  passiveIncorporation := true
  passiveIncorporated  := some "utsparket"
  gloss                := "kick out"

/-- *sette ned* 'set down'. -/
def sette_ned : NorwegianVPCEntry where
  citationForm         := "sette ned"
  verb                 := "sette"
  particle             := "ned"
  pastParticipleActive := "satt ned"
  passiveIncorporation := true
  passiveIncorporated  := some "nedsatt"
  gloss                := "set down"

/-- *klippe av* 'cut off'. -/
def klippe_av : NorwegianVPCEntry where
  citationForm         := "klippe av"
  verb                 := "klippe"
  particle             := "av"
  pastParticipleActive := "klipt av"
  passiveIncorporation := true
  passiveIncorporated  := some "avklipt"
  gloss                := "cut off"

/-- *kjøre bort* 'drive away'. -/
def kjøre_bort : NorwegianVPCEntry where
  citationForm         := "kjøre bort"
  verb                 := "kjøre"
  particle             := "bort"
  pastParticipleActive := "kjørt bort"
  passiveIncorporation := true
  passiveIncorporated  := some "bortkjørt"
  gloss                := "drive away"

/-- *sende ut* 'send out'. -/
def sende_ut : NorwegianVPCEntry where
  citationForm         := "sende ut"
  verb                 := "sende"
  particle             := "ut"
  pastParticipleActive := "sendt ut"
  passiveIncorporation := true
  passiveIncorporated  := some "utsendt"
  gloss                := "send out"

/-- The canonical inventory. -/
def inventory : List NorwegianVPCEntry :=
  [sparke_ut, sette_ned, klippe_av, kjøre_bort, sende_ut]

/-! ### Properties -/

/-- An entry's citation form follows the Norwegian convention
    `verb ++ " " ++ particle`. -/
def IsCitationConcat (e : NorwegianVPCEntry) : Prop :=
  e.citationForm = e.verb ++ " " ++ e.particle

instance : DecidablePred IsCitationConcat :=
  fun e => decEq e.citationForm (e.verb ++ " " ++ e.particle)

/-- Every inventory entry's citation form is `verb ++ " " ++ particle`. -/
theorem inventory_citation_concat
    (e : NorwegianVPCEntry) (he : e ∈ inventory) :
    IsCitationConcat e := by
  fin_cases he <;> rfl

/-- Every inventory entry permits passive prefix incorporation — the
    productive Norwegian pattern that contrasts with English. -/
theorem inventory_passive_incorporation
    (e : NorwegianVPCEntry) (he : e ∈ inventory) :
    AllowsPassiveIncorporation e := by
  fin_cases he <;> rfl

/-- Every inventory entry has a recorded passive-incorporated form
    (consistent with `passiveIncorporation = true`). -/
theorem inventory_passive_incorporated_some
    (e : NorwegianVPCEntry) (he : e ∈ inventory) :
    e.passiveIncorporated.isSome = true := by
  fin_cases he <;> rfl

end Fragments.Norwegian.VerbParticles
