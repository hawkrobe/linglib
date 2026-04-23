import Linglib.Core.Lexical.Word

/-!
# Be/Have Auxiliary Selection in European Perfects
@cite{burzio-1986} @cite{sorace-2000}

Many European languages select between *be* and *have* as the perfect auxiliary
based on the transitivity/unaccusativity of the lexical verb. The canonical
"Auxiliary Selection Hierarchy":

- **Unaccusative** verbs → *be* (Italian *è arrivato*, French *est arrivé*)
- **Unergative/transitive** verbs → *have* (Italian *ha mangiato*, French *a mangé*)

English has collapsed this distinction: all verbs take *have*.

## Bridge to Aspect

Vendler's achievement class (telic, punctual) correlates with unaccusativity:
canonical achievements (*arrive*, *die*, *fall*) are unaccusative and select *be*
in split-auxiliary languages.

-/

namespace Phenomena.AuxiliaryVerbs.Selection

/-! ## Types -/

/-- Perfect auxiliary choice. -/
inductive PerfectAux where
  | be   -- Italian *essere*, French *être*, German *sein*
  | have -- Italian *avere*, French *avoir*, German *haben*
  deriving DecidableEq, Repr

/-- Transitivity class relevant to auxiliary selection. -/
inductive TransitivityClass where
  | unaccusative  -- subject = theme (arrive, fall, die)
  | unergative    -- subject = agent, no object (run, laugh)
  | transitive    -- subject = agent, object = theme (eat, build)
  | reflexive     -- reflexive clitic triggers *be* in Romance (Italian/French), *have* in German
  deriving DecidableEq, Repr

/-- Language-level auxiliary selection rule. -/
inductive SelectionRule where
  | split    -- unaccusatives → be, rest → have (Italian, French, German, Dutch)
  | haveOnly -- all verbs → have (English, Spanish)
  | beOnly   -- all verbs → be (rare; some Sardinian dialects)
  | mixed    -- gradient/variable selection (some German dialects)
  deriving DecidableEq, Repr

/-! ## Functions -/

/-- Auxiliary selection driven by a single binary parameter: does the
    language treat reflexives as BE-selecting (Romance pattern) or
    HAVE-selecting (German pattern)? Unaccusatives always select BE,
    unergatives and transitives always select HAVE; the only point of
    cross-linguistic variation in this small typology is the reflexive
    row (@cite{burzio-1986}, @cite{sorace-2000}). -/
def selection (reflexIsBe : Bool) : TransitivityClass → PerfectAux
  | .unaccusative => .be
  | .reflexive    => if reflexIsBe then .be else .have
  | .unergative   => .have
  | .transitive   => .have

/-- Canonical (Romance) auxiliary selection: reflexives → *be*. -/
def canonicalSelection : TransitivityClass → PerfectAux := selection true

/-- German auxiliary selection: reflexives → *haben*, not *sein*
    (@cite{burzio-1986}). -/
def germanSelection : TransitivityClass → PerfectAux := selection false

/-- Does this transitivity class canonically select *be*?
    Defined off `canonicalSelection` so the equivalence is true by
    construction. -/
def SelectsBe (c : TransitivityClass) : Prop :=
  canonicalSelection c = .be

instance : DecidablePred SelectsBe := fun c => by
  unfold SelectsBe
  infer_instance

/-! ## Data -/

/-- A cross-linguistic auxiliary selection datum. -/
structure AuxSelectionDatum where
  language : String
  selectionRule : SelectionRule
  exampleVerb : String
  transitivityClass : TransitivityClass
  selectedAux : PerfectAux
  gloss : String := ""
  deriving Repr, BEq

/-- Italian *arrivare* (arrive) — unaccusative, selects *essere*
    (@cite{burzio-1986}). -/
def italianArrivare : AuxSelectionDatum :=
  { language := "Italian"
  , selectionRule := .split
  , exampleVerb := "arrivare"
  , transitivityClass := .unaccusative
  , selectedAux := .be
  , gloss := "è arrivato 'is arrived'" }

/-- Italian *mangiare* (eat) — transitive, selects *avere*
    (@cite{burzio-1986}). -/
def italianMangiare : AuxSelectionDatum :=
  { language := "Italian"
  , selectionRule := .split
  , exampleVerb := "mangiare"
  , transitivityClass := .transitive
  , selectedAux := .have
  , gloss := "ha mangiato 'has eaten'" }

/-- French *arriver* (arrive) — unaccusative, selects *être*
    (@cite{burzio-1986}). -/
def frenchArriver : AuxSelectionDatum :=
  { language := "French"
  , selectionRule := .split
  , exampleVerb := "arriver"
  , transitivityClass := .unaccusative
  , selectedAux := .be
  , gloss := "est arrivé 'is arrived'" }

/-- German *ankommen* (arrive) — unaccusative, selects *sein*
    (@cite{burzio-1986}). -/
def germanAnkommen : AuxSelectionDatum :=
  { language := "German"
  , selectionRule := .split
  , exampleVerb := "ankommen"
  , transitivityClass := .unaccusative
  , selectedAux := .be
  , gloss := "ist angekommen 'is arrived'" }

/-- Dutch *aankomen* (arrive) — unaccusative, selects *zijn*
    (@cite{sorace-2000}). -/
def dutchAankomen : AuxSelectionDatum :=
  { language := "Dutch"
  , selectionRule := .split
  , exampleVerb := "aankomen"
  , transitivityClass := .unaccusative
  , selectedAux := .be
  , gloss := "is aangekomen 'is arrived'" }

/-- English *arrive* — have-only system, canonical split is collapsed. -/
def englishArrive : AuxSelectionDatum :=
  { language := "English"
  , selectionRule := .haveOnly
  , exampleVerb := "arrive"
  , transitivityClass := .unaccusative
  , selectedAux := .have
  , gloss := "has arrived" }

def allData : List AuxSelectionDatum :=
  [italianArrivare, italianMangiare, frenchArriver,
   germanAnkommen, dutchAankomen, englishArrive]

/-! ## Theorems -/

/-- English *arrive* breaks the canonical pattern: the verb is unaccusative
    yet the language has a have-only perfect system, so the canonical
    Romance prediction (.be) and the actually-selected auxiliary (.have)
    disagree. This is the data point worth stating as a theorem; the
    other previously-listed equalities all reduce to `rfl` over the
    `selection` lookup table and have been removed. -/
theorem english_breaks_canonical :
    canonicalSelection englishArrive.transitivityClass ≠ englishArrive.selectedAux := by decide

end Phenomena.AuxiliaryVerbs.Selection
