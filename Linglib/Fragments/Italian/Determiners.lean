import Linglib.Features.Gender.Basic
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Quantification.Lexicon

/-! # Italian Determiners (Quantifiers)

Quantifier lexicon with syntactic and semantic properties. Each entry
`extends Syntax.Determiner.Quantifier` (the marked-determiner base: `form`,
`numberRestriction`, `selectsMass`) and adds gender agreement plus the
typological metadata labels (`qforce`/`monotonicity`/`strength`) from
`Semantics/Quantification/Lexicon.lean`.

Italian quantifiers agree in gender and/or number with their NP:
- *ogni* (every): invariant, singular
- *qualche* (some): invariant, singular
- *nessuno/nessuna* (no): gender-variable, singular, negative concord
- *tutti/tutte* (all): gender-variable, plural
- *alcuni/alcune* (some): gender-variable, plural
- *molti/molte* (many): gender-variable, plural
- *pochi/poche* (few): gender-variable, plural
-/

namespace Italian.Determiners

open Quantification.Lexicon (QForce Monotonicity Strength)

/-- Italian quantifier entry: the marked `Quantifier` base + gender + the
    B&C typological metadata labels. -/
structure ItalianQuantifierEntry extends Quantifier where
  /-- Quantificational force (typological label). -/
  qforce : QForce
  /-- Monotonicity (typological label). -/
  monotonicity : Monotonicity := .increasing
  /-- Weak/strong (B&C Table II). -/
  strength : Strength := .weak
  /-- Gender agreement (none = invariant) -/
  gender : Option Gender := none
  deriving Repr

/-- *ogni* — every (invariant, singular, universal). -/
def ogni : ItalianQuantifierEntry :=
  { form := "ogni"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .singular }

/-- *qualche* — some (invariant, singular, existential). -/
def qualche : ItalianQuantifierEntry :=
  { form := "qualche"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .singular }

/-- *nessuno* — no one (masculine, singular, negative concord). -/
def nessuno : ItalianQuantifierEntry :=
  { form := "nessuno"
  , qforce := .negative
  , monotonicity := .decreasing
  , numberRestriction := some .singular
  , gender := some .masculine }

/-- *nessuna* — no one (feminine, singular, negative concord). -/
def nessuna : ItalianQuantifierEntry :=
  { form := "nessuna"
  , qforce := .negative
  , monotonicity := .decreasing
  , numberRestriction := some .singular
  , gender := some .feminine }

/-- *tutti* — all (masculine, plural, universal). -/
def tutti : ItalianQuantifierEntry :=
  { form := "tutti"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .plural
  , gender := some .masculine }

/-- *tutte* — all (feminine, plural, universal). -/
def tutte : ItalianQuantifierEntry :=
  { form := "tutte"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , numberRestriction := some .plural
  , gender := some .feminine }

/-- *alcuni* — some (masculine, plural, existential). -/
def alcuni : ItalianQuantifierEntry :=
  { form := "alcuni"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .plural
  , gender := some .masculine }

/-- *alcune* — some (feminine, plural, existential). -/
def alcune : ItalianQuantifierEntry :=
  { form := "alcune"
  , qforce := .existential
  , monotonicity := .increasing
  , numberRestriction := some .plural
  , gender := some .feminine }

/-- *molti* — many (masculine, plural, proportional). -/
def molti : ItalianQuantifierEntry :=
  { form := "molti"
  , qforce := .proportional
  , monotonicity := .increasing
  , numberRestriction := some .plural
  , gender := some .masculine }

/-- *molte* — many (feminine, plural, proportional). -/
def molte : ItalianQuantifierEntry :=
  { form := "molte"
  , qforce := .proportional
  , monotonicity := .increasing
  , numberRestriction := some .plural
  , gender := some .feminine }

/-- *pochi* — few (masculine, plural, proportional, decreasing). -/
def pochi : ItalianQuantifierEntry :=
  { form := "pochi"
  , qforce := .proportional
  , monotonicity := .decreasing
  , numberRestriction := some .plural
  , gender := some .masculine }

/-- *poche* — few (feminine, plural, proportional, decreasing). -/
def poche : ItalianQuantifierEntry :=
  { form := "poche"
  , qforce := .proportional
  , monotonicity := .decreasing
  , numberRestriction := some .plural
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

end Italian.Determiners
