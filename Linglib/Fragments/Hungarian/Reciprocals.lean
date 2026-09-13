import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Reciprocal
import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Hungarian Reciprocal Fragment
[rakosi-2019] [dalrymple-haug-2024]

Hungarian uses the reciprocal pronoun *egymás* (literally 'one-another').
This is an NP/argument strategy (bivalent): the reciprocal occupies the
object position and preserves transitivity. It is distinct from the
reflexive *maga/maguk*.

## Morphological Invariance

*egymás* is morphologically invariable: it shows no φ-feature-related
variation (no person, number, or gender inflection). This contrasts
with the reflexive *maga*, which has the full paradigm
(*magam, magad, maga, magunk, magatok, maguk*).
[rakosi-2019] fn. 1.

The antecedent constructions in which *egymás* tolerates a singular antecedent are the
rows of `Data/Examples/Rakosi2019.json`, studied in `Studies/Rakosi2019.lean`.
-/


namespace Hungarian.Reciprocals

open Pronoun

/-- *egymás* — reciprocal pronoun 'each other'.
    Morphologically invariable: no φ-feature inflection.
    [rakosi-2019] fn. 1. -/
def egymas : ReciprocalPronoun :=
  { form := "egymás", person := some .third, number := none }

/-- *maga* — reflexive pronoun (3SG form, for contrast).
    Unlike *egymás*, the reflexive inflects for number:
    *magá-t* (SG.ACC) vs. *maguk-at* (PL.ACC). -/
def maga : PersonalPronoun :=
  { form := "maga", person := some .third, number := some .singular }

/-- *maguk* — reflexive pronoun (3PL form). -/
def maguk : PersonalPronoun :=
  { form := "maguk", person := some .third, number := some .plural }

/-- *egymás* is formally distinct from both reflexive forms. -/
theorem recip_distinct_from_reflexive :
    egymas.form ≠ maga.form ∧ egymas.form ≠ maguk.form := by
  constructor <;> decide

/-- *egymás* is morphologically invariable (no number feature). -/
theorem egymas_invariable : egymas.number = none := rfl

/-- The reflexive DOES inflect for number. -/
theorem reflexive_inflects :
    maga.number = some .singular ∧ maguk.number = some .plural := ⟨rfl, rfl⟩

open Reciprocal in
/-- The reciprocal verbal suffix ([nordlinger-2023] ex. 19, citing
    [siloni-2008]). -/
def ozSuffix : Marker :=
  { form := "-óz-", strategy := .verbalAffix }

open Reciprocal in
/-- Marker inventory, primary strategy first: *-óz-* plus the reciprocal
    pronoun *egymás*. -/
def markers : List Marker :=
  [ozSuffix, egymas.toMarker]

end Hungarian.Reciprocals
