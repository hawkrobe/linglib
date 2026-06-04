import Linglib.Core.UD.Basic
import Linglib.Features.Prominence

/-!
# Features.OntologicalCategory
[haspelmath-1997]

The ontological-category axis of pro-forms: the categories [haspelmath-1997]'s
"correlative pronoun" paradigm (his §3.1.3 Table 3.1) ranges over. The same axis is
shared by interrogative, demonstrative, relative, and indefinite pronoun types and by
their pronominal-adverb members (*where* / *when* / *how*), so it lives in `Features/`
as substrate that both `Typology/` and `Phenomena/` can type their data by.

## Provenance

Promoted from the former `Phenomena.Questions.WhSemanticType` (a Phenomena-layer enum,
hence unusable as substrate by `Typology/`). The wh-side `entity` case is split into
`person` / `thing` — the distinction [haspelmath-1997] notes is made "practically
everywhere" (*who* vs *what*), and the one indefinite and negative pronouns turn on
(*nobody* vs *nothing*). Renamings: `degree → amount`, `classificatory → property`,
`locative → place`, `temporal → time`; `reason` (*why*) is retained from the wh side.

## Main declarations

* `OntologicalCategory` — person/thing/property/place/time/manner/amount/reason.
* `OntologicalCategory.upos` — the part of speech a category realizes as
  (PRON / ADV / DET): the bridge deciding pronoun vs pronominal-adverb vs determiner.
* `OntologicalCategory.animacy` — projection to the [aissen-2003] `AnimacyLevel`.
-/

namespace Features

/-- The ontological category a pro-form ranges over ([haspelmath-1997] Table 3.1),
    shared by interrogative / demonstrative / relative / indefinite pronoun types. -/
inductive OntologicalCategory where
  | person     -- who, somebody, nobody — individuals (animate)
  | thing      -- what, something, nothing — individuals (inanimate)
  | property   -- what kind, some kind — sorts/kinds
  | place      -- where, somewhere, nowhere — locations
  | time       -- when, sometime, never — times
  | manner     -- how, somehow — manners
  | amount     -- how much, how many — degrees/quantities
  | reason     -- why — reasons/causes
  deriving DecidableEq, Repr, Inhabited

/-- The part of speech a category realizes as: person/thing → pronoun, place/time/
    manner/reason → (pronominal) adverb, property/amount → determiner. The bridge that
    decides whether an indefinite cell is a pronoun (*nobody*) or pro-adverb (*never*). -/
def OntologicalCategory.upos : OntologicalCategory → UD.UPOS
  | .person | .thing => .PRON
  | .place | .time | .manner | .reason => .ADV
  | .property | .amount => .DET

/-- Animacy of the category on the [aissen-2003] `AnimacyLevel` scale: only
    `person` is human; the remaining categories are inanimate. -/
def OntologicalCategory.animacy : OntologicalCategory → Prominence.AnimacyLevel
  | .person => .human
  | _       => .inanimate

end Features
