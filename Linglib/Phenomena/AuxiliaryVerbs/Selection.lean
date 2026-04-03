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

/-- Canonical auxiliary selection (Burzio's generalization, Romance pattern):
    unaccusatives and reflexives → *be*, everything else → *have*.

    **NB**: This models the Romance pattern (Italian, French). German differs:
    reflexives take *haben* (e.g., *hat sich gewaschen* 'has REFL washed'),
    not *sein*. For German-specific selection, see `germanSelection`. -/
def canonicalSelection : TransitivityClass → PerfectAux
  | .unaccusative => .be
  | .unergative   => .have
  | .transitive   => .have
  | .reflexive    => .be

/-- German auxiliary selection: differs from Romance in that reflexives take
    *haben*, not *sein* (@cite{burzio-1986}). -/
def germanSelection : TransitivityClass → PerfectAux
  | .unaccusative => .be
  | .reflexive    => .have
  | _             => .have

/-- Does this transitivity class canonically select *be*? -/
def selectsBe : TransitivityClass → Bool
  | .unaccusative => true
  | .reflexive    => true
  | _             => false

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

/-- Unaccusatives canonically select *be*. -/
theorem unaccusative_selects_be :
    canonicalSelection .unaccusative = .be := rfl

/-- Transitives canonically select *have*. -/
theorem transitive_selects_have :
    canonicalSelection .transitive = .have := rfl

/-- Italian *arrivare* matches the canonical pattern. -/
theorem italian_arrivare_matches_canonical :
    canonicalSelection italianArrivare.transitivityClass = italianArrivare.selectedAux := rfl

/-- English *arrive* breaks the canonical pattern (have-only system). -/
theorem english_breaks_canonical :
    canonicalSelection englishArrive.transitivityClass ≠ englishArrive.selectedAux := by decide

/-- German reflexives take *haben*, not *sein* — unlike Romance. -/
theorem german_reflexive_takes_have :
    germanSelection .reflexive = .have := rfl

/-- Romance reflexives take *be* (canonical pattern). -/
theorem romance_reflexive_takes_be :
    canonicalSelection .reflexive = .be := rfl

/-- German and Romance agree on unaccusatives (both select *be*). -/
theorem german_romance_agree_on_unaccusative :
    germanSelection .unaccusative = canonicalSelection .unaccusative := rfl

end Phenomena.AuxiliaryVerbs.Selection
