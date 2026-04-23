import Linglib.Features.Gender
import Linglib.Theories.Semantics.Quantification.Lexicon

/-! # Italian Determiners (Quantifiers)

Quantifier lexicon with syntactic and semantic properties. Reuses the
shared `QuantifierEntry` from
`Theories/Semantics/Quantification/Lexicon.lean` and extends it with
gender agreement.

Italian quantifiers agree in gender and/or number with their NP:
- *ogni* (every): invariant, singular
- *qualche* (some): invariant, singular
- *nessuno/nessuna* (no): gender-variable, singular, negative concord
- *tutti/tutte* (all): gender-variable, plural
- *alcuni/alcune* (some): gender-variable, plural
- *molti/molte* (many): gender-variable, plural
- *pochi/poche* (few): gender-variable, plural
-/

namespace Fragments.Italian.Determiners

open Features (SurfaceGender)
open Theories.Semantics.Quantification.Lexicon
  (QuantifierEntry QForce Monotonicity Strength)

/-- Italian quantifier entry: shared `QuantifierEntry` + gender. -/
structure ItalianQuantifierEntry extends QuantifierEntry where
  /-- Gender agreement (none = invariant) -/
  gender : Option SurfaceGender := none
  deriving Repr

/-- *ogni* — every (invariant, singular, universal). -/
def ogni : ItalianQuantifierEntry :=
  { form := "ogni"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .sg }

/-- *qualche* — some (invariant, singular, existential). -/
def qualche : ItalianQuantifierEntry :=
  { form := "qualche"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .sg }

/-- *nessuno* — no one (masculine, singular, negative concord). -/
def nessuno : ItalianQuantifierEntry :=
  { form := "nessuno"
  , qforce := .negative
  , monotonicity := .decreasing
  , numberRestriction := some .sg
  , gender := some .masculine }

/-- *nessuna* — no one (feminine, singular, negative concord). -/
def nessuna : ItalianQuantifierEntry :=
  { form := "nessuna"
  , qforce := .negative
  , monotonicity := .decreasing
  , numberRestriction := some .sg
  , gender := some .feminine }

/-- *tutti* — all (masculine, plural, universal). -/
def tutti : ItalianQuantifierEntry :=
  { form := "tutti"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .pl
  , gender := some .masculine }

/-- *tutte* — all (feminine, plural, universal). -/
def tutte : ItalianQuantifierEntry :=
  { form := "tutte"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .pl
  , gender := some .feminine }

/-- *alcuni* — some (masculine, plural, existential). -/
def alcuni : ItalianQuantifierEntry :=
  { form := "alcuni"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .pl
  , gender := some .masculine }

/-- *alcune* — some (feminine, plural, existential). -/
def alcune : ItalianQuantifierEntry :=
  { form := "alcune"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .pl
  , gender := some .feminine }

/-- *molti* — many (masculine, plural, proportional). -/
def molti : ItalianQuantifierEntry :=
  { form := "molti"
  , qforce := .proportional
  , monotonicity := .increasing
  , numberRestriction := some .pl
  , gender := some .masculine }

/-- *molte* — many (feminine, plural, proportional). -/
def molte : ItalianQuantifierEntry :=
  { form := "molte"
  , qforce := .proportional
  , monotonicity := .increasing
  , numberRestriction := some .pl
  , gender := some .feminine }

/-- *pochi* — few (masculine, plural, proportional, decreasing). -/
def pochi : ItalianQuantifierEntry :=
  { form := "pochi"
  , qforce := .proportional
  , monotonicity := .decreasing
  , numberRestriction := some .pl
  , gender := some .masculine }

/-- *poche* — few (feminine, plural, proportional, decreasing). -/
def poche : ItalianQuantifierEntry :=
  { form := "poche"
  , qforce := .proportional
  , monotonicity := .decreasing
  , numberRestriction := some .pl
  , gender := some .feminine }

/-- All Italian quantifier entries. -/
def allQuantifiers : List ItalianQuantifierEntry := [
  ogni, qualche, nessuno, nessuna, tutti, tutte,
  alcuni, alcune, molti, molte, pochi, poche
]

/-- Lookup by form. -/
def lookup (form : String) : Option ItalianQuantifierEntry :=
  allQuantifiers.find? λ q => q.form == form

/-- *ogni* is universal, increasing, and strong. -/
theorem ogni_universal :
    ogni.qforce = .universal ∧
    ogni.monotonicity = .increasing ∧
    ogni.strength = .strong := ⟨rfl, rfl, rfl⟩

/-- *nessuno* is negative and decreasing. -/
theorem nessuno_negative :
    nessuno.qforce = .negative ∧
    nessuno.monotonicity = .decreasing := ⟨rfl, rfl⟩

/-- *tutti* is universal, increasing, and strong. -/
theorem tutti_universal :
    tutti.qforce = .universal ∧
    tutti.monotonicity = .increasing ∧
    tutti.strength = .strong := ⟨rfl, rfl, rfl⟩

/-- *qualche* is existential and increasing. -/
theorem qualche_existential :
    qualche.qforce = .existential ∧
    qualche.monotonicity = .increasing := ⟨rfl, rfl⟩

/-- *pochi* is proportional and decreasing. -/
theorem pochi_decreasing :
    pochi.qforce = .proportional ∧
    pochi.monotonicity = .decreasing := ⟨rfl, rfl⟩

/-- Gender agreement: nessuno/nessuna are masculine/feminine forms of the same quantifier. -/
theorem nessuno_nessuna_gender :
    nessuno.gender = some .masculine ∧
    nessuna.gender = some .feminine ∧
    nessuno.qforce = nessuna.qforce := ⟨rfl, rfl, rfl⟩

/-- Gender agreement: tutti/tutte are masculine/feminine forms of the same quantifier. -/
theorem tutti_tutte_gender :
    tutti.gender = some .masculine ∧
    tutte.gender = some .feminine ∧
    tutti.qforce = tutte.qforce := ⟨rfl, rfl, rfl⟩

end Fragments.Italian.Determiners
