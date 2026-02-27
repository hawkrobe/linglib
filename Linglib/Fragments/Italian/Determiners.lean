import Linglib.Core.Lexical.Word

/-! # Italian Determiners (Quantifiers)

Quantifier lexicon with syntactic and semantic properties, following
the `QuantifierEntry` pattern from `Fragments/English/Determiners.lean`
but extended with gender/number agreement for Italian.

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

-- ============================================================================
-- § 1: Shared Enums
-- ============================================================================

/-- Quantificational force. -/
inductive QForce where
  | universal
  | existential
  | negative
  | proportional
  deriving DecidableEq, Repr, BEq

/-- Monotonicity in the scope argument. -/
inductive Monotonicity where
  | increasing
  | decreasing
  | nonMonotone
  deriving DecidableEq, Repr, BEq

/-- Weak/strong classification (Barwise & Cooper 1981). -/
inductive Strength where
  | weak
  | strong
  deriving DecidableEq, Repr, BEq

/-- Gender for agreement. -/
inductive Gender where
  | masc | fem
  deriving DecidableEq, Repr, BEq

/-- Number for agreement. -/
inductive Number where
  | sg | pl
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: Quantifier Entry
-- ============================================================================

/-- Italian quantifier entry with gender/number agreement. -/
structure ItalianQuantifierEntry where
  form : String
  qforce : QForce
  monotonicity : Monotonicity := .increasing
  strength : Strength := .weak
  /-- Gender agreement (none = invariant) -/
  gender : Option Gender := none
  /-- Number restriction -/
  number : Option Number := none
  deriving Repr, BEq

-- ============================================================================
-- § 3: Quantifier Data
-- ============================================================================

/-- *ogni* — every (invariant, singular, universal). -/
def ogni : ItalianQuantifierEntry :=
  { form := "ogni"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , number := some .sg }

/-- *qualche* — some (invariant, singular, existential). -/
def qualche : ItalianQuantifierEntry :=
  { form := "qualche"
  , qforce := .existential
  , monotonicity := .increasing
  , number := some .sg }

/-- *nessuno* — no one (masculine, singular, negative concord). -/
def nessuno : ItalianQuantifierEntry :=
  { form := "nessuno"
  , qforce := .negative
  , monotonicity := .decreasing
  , gender := some .masc
  , number := some .sg }

/-- *nessuna* — no one (feminine, singular, negative concord). -/
def nessuna : ItalianQuantifierEntry :=
  { form := "nessuna"
  , qforce := .negative
  , monotonicity := .decreasing
  , gender := some .fem
  , number := some .sg }

/-- *tutti* — all (masculine, plural, universal). -/
def tutti : ItalianQuantifierEntry :=
  { form := "tutti"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , gender := some .masc
  , number := some .pl }

/-- *tutte* — all (feminine, plural, universal). -/
def tutte : ItalianQuantifierEntry :=
  { form := "tutte"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , gender := some .fem
  , number := some .pl }

/-- *alcuni* — some (masculine, plural, existential). -/
def alcuni : ItalianQuantifierEntry :=
  { form := "alcuni"
  , qforce := .existential
  , monotonicity := .increasing
  , gender := some .masc
  , number := some .pl }

/-- *alcune* — some (feminine, plural, existential). -/
def alcune : ItalianQuantifierEntry :=
  { form := "alcune"
  , qforce := .existential
  , monotonicity := .increasing
  , gender := some .fem
  , number := some .pl }

/-- *molti* — many (masculine, plural, proportional). -/
def molti : ItalianQuantifierEntry :=
  { form := "molti"
  , qforce := .proportional
  , monotonicity := .increasing
  , gender := some .masc
  , number := some .pl }

/-- *molte* — many (feminine, plural, proportional). -/
def molte : ItalianQuantifierEntry :=
  { form := "molte"
  , qforce := .proportional
  , monotonicity := .increasing
  , gender := some .fem
  , number := some .pl }

/-- *pochi* — few (masculine, plural, proportional, decreasing). -/
def pochi : ItalianQuantifierEntry :=
  { form := "pochi"
  , qforce := .proportional
  , monotonicity := .decreasing
  , gender := some .masc
  , number := some .pl }

/-- *poche* — few (feminine, plural, proportional, decreasing). -/
def poche : ItalianQuantifierEntry :=
  { form := "poche"
  , qforce := .proportional
  , monotonicity := .decreasing
  , gender := some .fem
  , number := some .pl }

-- ============================================================================
-- § 4: Lexicon Access
-- ============================================================================

/-- All Italian quantifier entries. -/
def allQuantifiers : List ItalianQuantifierEntry := [
  ogni, qualche, nessuno, nessuna, tutti, tutte,
  alcuni, alcune, molti, molte, pochi, poche
]

/-- Lookup by form. -/
def lookup (form : String) : Option ItalianQuantifierEntry :=
  allQuantifiers.find? λ q => q.form == form

-- ============================================================================
-- § 5: Verification Theorems
-- ============================================================================

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
    nessuno.gender = some .masc ∧
    nessuna.gender = some .fem ∧
    nessuno.qforce = nessuna.qforce := ⟨rfl, rfl, rfl⟩

/-- Gender agreement: tutti/tutte are masculine/feminine forms of the same quantifier. -/
theorem tutti_tutte_gender :
    tutti.gender = some .masc ∧
    tutte.gender = some .fem ∧
    tutti.qforce = tutte.qforce := ⟨rfl, rfl, rfl⟩

end Fragments.Italian.Determiners
