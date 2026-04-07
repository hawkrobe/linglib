import Linglib.Core.Lexical.Pronouns
import Linglib.Theories.Semantics.Reference.Reciprocals

/-!
# Hungarian Reciprocal Fragment
@cite{rakosi-2019} @cite{dalrymple-haug-2024}

Hungarian uses the reciprocal pronoun *egymás* (literally 'one-another').
This is an NP/argument strategy (bivalent): the reciprocal occupies the
object position and preserves transitivity. It is distinct from the
reflexive *maga/maguk*.

## Morphological Invariance

*egymás* is morphologically invariable: it shows no φ-feature-related
variation (no person, number, or gender inflection). This contrasts
with the reflexive *maga*, which has the full paradigm
(*magam, magad, maga, magunk, magatok, maguk*).
@cite{rakosi-2019} fn. 1.

## Singular Antecedents (@cite{rakosi-2019})

Reciprocals tolerate morphosyntactically singular antecedents in four
construction types, while reflexives require morphosyntactic plurality
(plural noun head + plural verb agreement + plural anaphor form):

1. **Quantified NPs (§3)**: Hungarian quantified NPs are morphologically
   singular and take 3SG verbs, yet license *egymás*.
2. **Singular coordinate DPs (§4)**: Two conjoined singulars can trigger
   3SG agreement in Hungarian; *egymás* is fine, but plural reflexive
   *magukat* is blocked (only SG *magát* permitted with SG verb).
3. **Collective nouns (§5)**: Collective nouns (*személyzet* 'staff',
   *család* 'family') never trigger plural agreement, yet perfectly
   license *egymás*.
4. **Bound variable antecedents (§6)**: Embedded pro-dropped singular
   subject bound by a matrix coordination forces wide-scope
   (I-)reading. @cite{dalrymple-haug-2024} §2.
-/

namespace Fragments.Hungarian.Reciprocals

open Core.Pronouns
open Semantics.Reference.Reciprocals

/-- *egymás* — reciprocal pronoun 'each other'.
    Morphologically invariable: no φ-feature inflection.
    @cite{rakosi-2019} fn. 1. -/
def egymas : PronounEntry :=
  { form := "egymás", person := some .third, number := none }

/-- *maga* — reflexive pronoun (3SG form, for contrast).
    Unlike *egymás*, the reflexive inflects for number:
    *magá-t* (SG.ACC) vs. *maguk-at* (PL.ACC). -/
def maga : PronounEntry :=
  { form := "maga", person := some .third, number := some .sg }

/-- *maguk* — reflexive pronoun (3PL form). -/
def maguk : PronounEntry :=
  { form := "maguk", person := some .third, number := some .pl }

-- ════════════════════════════════════════════════════════════════
-- Antecedent Constructions (@cite{rakosi-2019} §§3-6)
-- ════════════════════════════════════════════════════════════════

/-- An antecedent configuration for anaphor licensing.
    `syntacticPl` = the antecedent bears plural morphology and triggers
    plural verb agreement. `semanticPl` = the antecedent denotes a
    plurality (multiple individuals). -/
structure AntecedentConfig where
  name : String
  /-- Morphosyntactically plural (plural noun head, plural verb agr) -/
  syntacticPl : Bool
  /-- Semantically plural (denotes multiple individuals) -/
  semanticPl : Bool
  /-- Verb agreement number -/
  verbAgr : Number
  deriving Repr

/-- §3: Quantified NPs. Hungarian quantified NPs are morphologically
    singular (no -ek suffix) and trigger 3SG verb agreement.
    Ex: "Két gyerek jól érezte magá-t/\*maguk-at."
    (Two child well felt.3SG self-ACC/\*selves-ACC)
    But: "Három kisgyerek kergeti egymás-t." (OK) -/
def quantifiedNP : AntecedentConfig :=
  { name := "Quantified NP (két/három/néhány + SG noun)"
    syntacticPl := false
    semanticPl := true
    verbAgr := .sg }

/-- §4: Singular coordinate DPs. Two conjoined singular NPs can
    trigger either SG or PL agreement from the left periphery.
    With SG verb: reflexive must be SG (*magát*), reciprocal is OK.
    Ex: "Kati és Éva kihúzta magát/\*magukat." (3SG → SG refl only)
    But: "Kati és Éva látta/látták egymás-t a tükörben." (both OK) -/
def singularCoordinate : AntecedentConfig :=
  { name := "Singular coordinate DP (X és Y + 3SG verb)"
    syntacticPl := false
    semanticPl := true
    verbAgr := .sg }

/-- §5: Collective nouns. Hungarian collective nouns never trigger
    plural agreement (\*voltak for *személyzet*).
    Ex: "A személyzet riadtan nézte egymás-t." (3SG, reciprocal OK)
    Ex: "Az egész család jól érezte magá-t/\*maguk-at." (SG refl only) -/
def collectiveNoun : AntecedentConfig :=
  { name := "Collective noun (személyzet, család, pár)"
    syntacticPl := false
    semanticPl := true
    verbAgr := .sg }

/-- §6: Bound variable antecedent. Embedded pro-dropped SG subject
    bound by matrix coordination. Forces wide-scope (I-)reading.
    Ex: "Péter és Éva azt gondolja, hogy (\*ő) szereti egymás-t."
    @cite{dalrymple-haug-2024} §2. -/
def boundVariable : AntecedentConfig :=
  { name := "Bound singular pro-drop (coordination in matrix)"
    syntacticPl := false
    semanticPl := true
    verbAgr := .sg }

/-- Standard plural antecedent (baseline).
    Ex: "A gyerek-ek látták egymás-t a tükörben." -/
def pluralAntecedent : AntecedentConfig :=
  { name := "Plural NP (standard)"
    syntacticPl := true
    semanticPl := true
    verbAgr := .pl }

/-- All four singular-antecedent constructions from @cite{rakosi-2019}. -/
def singularConstructions : List AntecedentConfig :=
  [quantifiedNP, singularCoordinate, collectiveNoun, boundVariable]

-- ════════════════════════════════════════════════════════════════
-- Licensing via PluralityRequirement
-- ════════════════════════════════════════════════════════════════

/-- Reciprocals require only semantic plurality. -/
def reciprocalReq : PluralityRequirement := anaphorPluralityReq true

/-- Reflexives require morphosyntactic plurality. -/
def reflexiveReq : PluralityRequirement := anaphorPluralityReq false

/-- Whether the reciprocal is licensed in a given antecedent config. -/
def reciprocalLicensed (cfg : AntecedentConfig) : Bool :=
  satisfiesPluralityReq reciprocalReq cfg.syntacticPl cfg.semanticPl

/-- Whether the plural reflexive (*maguk-at*) is licensed. -/
def pluralReflexiveLicensed (cfg : AntecedentConfig) : Bool :=
  satisfiesPluralityReq reflexiveReq cfg.syntacticPl cfg.semanticPl

-- ════════════════════════════════════════════════════════════════
-- Verification Theorems
-- ════════════════════════════════════════════════════════════════

/-- The core asymmetry: in ALL four singular constructions, the
    reciprocal is licensed but the plural reflexive is not. -/
theorem singular_asymmetry :
    singularConstructions.map reciprocalLicensed = [true, true, true, true] ∧
    singularConstructions.map pluralReflexiveLicensed = [false, false, false, false] := ⟨rfl, rfl⟩

/-- With a standard plural antecedent, both are licensed. -/
theorem plural_licenses_both :
    reciprocalLicensed pluralAntecedent = true ∧
    pluralReflexiveLicensed pluralAntecedent = true := ⟨rfl, rfl⟩

/-- *egymás* is formally distinct from both reflexive forms. -/
theorem recip_distinct_from_reflexive :
    egymas.form ≠ maga.form ∧ egymas.form ≠ maguk.form := by
  constructor <;> decide

/-- *egymás* is morphologically invariable (no number feature). -/
theorem egymas_invariable : egymas.number = none := rfl

/-- The reflexive DOES inflect for number. -/
theorem reflexive_inflects :
    maga.number = some .sg ∧ maguk.number = some .pl := ⟨rfl, rfl⟩

/-- When the local antecedent is a singular bound pronoun, only the
    wide-scope (I-)reading is available.
    @cite{dalrymple-haug-2024} §2. -/
def singularAntecedentForcesWideScope : Bool := true

end Fragments.Hungarian.Reciprocals
