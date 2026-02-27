import Linglib.Core.Lexical.Word

/-! # Italian Negation Fragment

Italian sentential negation and negative concord (n-words).

## Negation Strategy

Italian uses the preverbal particle *non* for standard negation:
- *Non ho visto nessuno* 'NEG have seen nobody' = 'I didn't see anyone'

## Negative Concord

Italian is a negative concord language (like Spanish): n-words co-occur
with *non* in postverbal position, but can stand alone preverbally:
- Postverbal: *Non ho visto nessuno* (non required)
- Preverbal: *Nessuno è venuto* (non absent)

This matches the `.mixed` strategy in WALS Ch 115, paralleling Spanish.

## N-Words

Italian n-words: *nessuno/nessuna* (nobody), *niente/nulla* (nothing),
*mai* (never), *neanche/nemmeno/neppure* (not even).
-/

namespace Fragments.Italian.Negation

-- ============================================================================
-- § 1: Negation Marker
-- ============================================================================

/-- The Italian standard negation marker. -/
def negMarker : String := "non"

-- ============================================================================
-- § 2: N-Word Entries
-- ============================================================================

/-- An Italian n-word entry. -/
structure NWordEntry where
  /-- Surface form -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Can this n-word appear preverbally without *non*? -/
  preverbalAlone : Bool
  deriving Repr, BEq

/-- *nessuno* — nobody (masculine). Can appear preverbally alone. -/
def nessuno : NWordEntry :=
  { form := "nessuno", gloss := "nobody.M", preverbalAlone := true }

/-- *nessuna* — nobody (feminine). Can appear preverbally alone. -/
def nessuna : NWordEntry :=
  { form := "nessuna", gloss := "nobody.F", preverbalAlone := true }

/-- *niente* — nothing. Requires *non* postverbally;
    can appear preverbally alone. -/
def niente : NWordEntry :=
  { form := "niente", gloss := "nothing", preverbalAlone := true }

/-- *nulla* — nothing (formal). Same distribution as *niente*. -/
def nulla : NWordEntry :=
  { form := "nulla", gloss := "nothing.FORMAL", preverbalAlone := true }

/-- *mai* — never. Requires *non* (typically postverbal: *non ... mai*). -/
def mai : NWordEntry :=
  { form := "mai", gloss := "never", preverbalAlone := false }

/-- *neanche* — not even. Requires *non* postverbally;
    can appear preverbally alone. -/
def neanche : NWordEntry :=
  { form := "neanche", gloss := "not.even", preverbalAlone := true }

/-- *nemmeno* — not even (variant). Same distribution as *neanche*. -/
def nemmeno : NWordEntry :=
  { form := "nemmeno", gloss := "not.even", preverbalAlone := true }

def allNWords : List NWordEntry :=
  [nessuno, nessuna, niente, nulla, mai, neanche, nemmeno]

-- ============================================================================
-- § 3: Negative Concord Examples
-- ============================================================================

/-- A negative concord example: a sentence with *non* and an n-word. -/
structure NegConcordExample where
  /-- Italian sentence -/
  sentence : String
  /-- English translation -/
  translation : String
  /-- Is *non* present? -/
  hasNon : Bool
  /-- Position of the n-word -/
  nwordPosition : String  -- "preverbal" or "postverbal"
  deriving Repr, BEq

/-- Postverbal n-word requires *non*. -/
def ex_postverbal : NegConcordExample :=
  { sentence := "Non ho visto nessuno"
  , translation := "I didn't see anyone"
  , hasNon := true
  , nwordPosition := "postverbal" }

/-- Preverbal n-word stands alone (no *non*). -/
def ex_preverbal : NegConcordExample :=
  { sentence := "Nessuno è venuto"
  , translation := "Nobody came"
  , hasNon := false
  , nwordPosition := "preverbal" }

/-- Postverbal *mai* requires *non*. -/
def ex_mai : NegConcordExample :=
  { sentence := "Non ho mai visto Roma"
  , translation := "I have never seen Rome"
  , hasNon := true
  , nwordPosition := "postverbal" }

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- *nessuno* can appear preverbally without *non*. -/
theorem nessuno_preverbal : nessuno.preverbalAlone = true := rfl

/-- *mai* requires *non* (cannot appear preverbally alone). -/
theorem mai_requires_non : mai.preverbalAlone = false := rfl

/-- The negation marker is *non*. -/
theorem negMarker_is_non : negMarker = "non" := rfl

end Fragments.Italian.Negation
