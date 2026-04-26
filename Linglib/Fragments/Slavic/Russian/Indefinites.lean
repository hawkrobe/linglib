import Linglib.Features.IndefiniteType
import Linglib.Core.Lexical.PolarityItem

/-!
# Russian Indefinite Pronoun Paradigm
@cite{haspelmath-1997} @cite{bubnov-2026} @cite{degano-aloni-2025}

Russian has a three-way split among indefinite pronouns that is central
to @cite{bubnov-2026}'s argument against nanosyntactic containment for
indefinites. The three series realize distinct Degano & Aloni indefinite
types with ABC morphology (no form shared across the three functions),
refuting the *ABA-based containment hierarchy proposed by @cite{dekier-2021}.

| Series     | Haspelmath function | D&A type        | D&A semantics | Gloss                  |
|------------|---------------------|-----------------|---------------|------------------------|
| *-nibud'*  | non-specific        | (iii) nonSpec   | var(v,x)      | 'some... or other'     |
| *-to*      | specific unknown    | (iv) epistemic  | var(∅,x)      | 'some (particular)'    |
| *koe-*     | specific known      | (v) specKnown   | dep(∅,x)      | 'some (I know which)'  |

Note on *-to*: @cite{bubnov-2026} §7 maps *-to* to ∃_epistemic with
semantics var(∅,x) — type (iv) epistemic. Its restriction to the
specific-unknown function (not also non-specific) is due to paradigmatic
competition with *-nibud'*, which is more specific for non-specific
contexts. The Degano & Aloni semantic profile of type (iv) permits both
SU and NS, but *-to*'s actual distribution is SU only.
-/

set_option autoImplicit false

namespace Fragments.Slavic.Russian.Indefinites

open Features.IndefiniteType

-- ============================================================================
-- §1. Russian Indefinite Entries
-- ============================================================================

/-- *-нибудь* (-nibud'): non-specific indefinite.
    Typically in imperatives, questions, irrealis contexts.
    "Купи что-нибудь" (Buy something [I don't care what]).
    D&A type (iii): var(v,x). -/
def nibudEntry : IndefiniteEntry where
  language := "Russian"
  form := "-нибудь (-nibud')"
  gloss := "some...or other (non-specific)"
  specType := .nonSpecific
  allowsSK := false
  allowsSU := false
  allowsNS := true
  source := "Haspelmath 1997"

/-- *-то* (-to): fills the specific-unknown function in Russian.
    Speaker believes there is a specific referent but doesn't know which.
    "Кто-то пришёл" (Someone [specific] came).

    @cite{bubnov-2026} §7 maps *-to* to ∃_epistemic with semantics
    var(∅,x) — D&A type (iv) epistemic. The semantic profile of type (iv)
    permits both SU and NS contexts, but *-to* only appears for SU because
    *-nibud'* (type iii) blocks it for NS. -/
def toEntry : IndefiniteEntry where
  language := "Russian"
  form := "-то (-to)"
  gloss := "some (particular, unknown)"
  specType := .epistemic
  allowsSK := false
  allowsSU := true
  allowsNS := false
  source := "Haspelmath 1997, Bubnov 2026 §7"

/-- *кое-* (koe-): specific known indefinite.
    Speaker knows the referent's identity.
    "Кое-кто пришёл" (Someone [I know who] came).
    D&A type (v): dep(∅,x). -/
def koeEntry : IndefiniteEntry where
  language := "Russian"
  form := "кое- (koe-)"
  gloss := "some (I know which)"
  specType := .specificKnown
  allowsSK := true
  allowsSU := false
  allowsNS := false
  source := "Haspelmath 1997"

/-- The Russian paradigm exhibits an ABC pattern: three distinct forms
    for three distinct functions. No morphological containment. -/
def paradigm : List IndefiniteEntry := [nibudEntry, toEntry, koeEntry]

-- ============================================================================
-- §2. ABC Pattern Verification
-- ============================================================================

/-- All three forms are distinct (ABC, not AAB/ABB/AAA). -/
theorem abc_all_distinct :
    nibudEntry.form ≠ toEntry.form ∧
    toEntry.form ≠ koeEntry.form ∧
    nibudEntry.form ≠ koeEntry.form :=
  ⟨by decide, by decide, by decide⟩

/-- All entries have consistent distributions (actual ⊆ semantic profile). -/
theorem paradigm_consistent : paradigm.all (·.distributionConsistent) := by decide

/-- *-to*'s actual distribution is narrower than its semantic profile:
    type (iv) epistemic permits NS, but *-to* doesn't appear there. -/
theorem to_distribution_narrower_than_profile :
    toEntry.specType.profileNS = true ∧
    toEntry.allowsNS = false := ⟨rfl, rfl⟩

end Fragments.Slavic.Russian.Indefinites
