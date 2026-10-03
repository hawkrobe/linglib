module

public import Linglib.Syntax.Case.Basic

/-!
# Japanese case markers

Japanese marks the relations of a noun phrase with particles after it. Tsujimura separates the
case particles, the nominative *ga*, the accusative *o*, the dative *ni* and the genitive *no*,
from the postpositions, the counterparts of English prepositions, which cannot stand on their
own: *de* 'at', *e* 'to', *to* 'with', *made* 'until' and *kara* 'from'. The nominative and the
accusative, unlike case endings, may be dropped in casual speech, *Tomodati(-ga) kita?* 'Has my
friend come?', and replaced by *mo* 'also' and *sae* 'even'. Two markers are polysemous: *ni*
marks recipients, goals, times and the location of existence, and *de* the location of an
action and its instrument, so *ni* and *de* share the locative and *ni* and *e* the allative.
*Ga* is recorded as the nominative, setting aside the exhaustive-listing reading of Kuroda and
Kuno; *no* is also a nominalizer, *to* a quotative complementizer and *kara* a reason
conjunction, uses outside case marking. Sadakane and Koizumi's four *ni* lexemes refine the
single *ni* entry, the matter of `Studies/SadakaneKoizumi1995.lean`.

## Main definitions

* `Japanese.Case`, `Japanese.Case.form`: the four cases of the case particles, and the particles.
* `Japanese.Case.label`, `Japanese.Case.functions`: the comparative value each case is named for,
  and the values it expresses.
* `Japanese.Case.droppable`: the cases whose particles casual speech drops.
* `Japanese.Postposition`: the postpositions, with their forms and the case values they express.

## References

* [kuno-1973]
* [kuroda-1965]
* [sadakane-koizumi-1995]
* [tsujimura-2014]
-/

@[expose] public section

namespace Japanese

/-! ### Case particles -/

/-- The four cases the case particles mark. -/
inductive Case where
  /-- The nominative, *ga*. -/
  | nom
  /-- The accusative, *o*. -/
  | acc
  /-- The genitive, *no*. -/
  | gen
  /-- The dative, *ni*. -/
  | dat
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- `c.form` is the case particle of `c`, *ga* が, *o* を, *no* の or *ni* に. -/
def form : Case → String
  | nom => "ga"
  | acc => "o"
  | gen => "no"
  | dat => "ni"

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- `c.functions` are the comparative values `c` expresses; *ni* marks the recipient, the goal,
the time and the location of existence. -/
def functions : Case → Finset _root_.Case
  | dat => {.dat, .loc, .all, .tem}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

/-- The cases whose particles casual speech drops, the nominative and the accusative. -/
def droppable : Finset Case := {nom, acc}

end Case

/-! ### Postpositions -/

/-- The postpositions. -/
inductive Postposition where
  /-- *de* で 'at'. -/
  | de
  /-- *e* へ 'to'. -/
  | e
  /-- *to* と 'with'. -/
  | «to»
  /-- *kara* から 'from'. -/
  | kara
  /-- *made* まで 'until'. -/
  | made
  /-- *yori* より 'than', the standard marker of the comparative (`Japanese.Comparison.yori`). -/
  | yori
  deriving DecidableEq, Fintype, Repr

namespace Postposition

/-- The form of a postposition. -/
def form : Postposition → String
  | de => "de"
  | e => "e"
  | «to» => "to"
  | kara => "kara"
  | made => "made"
  | yori => "yori"

/-- `p.functions` are the comparative values `p` expresses. *De* marks the locative of an
action's place and the instrumental, *e* the allative, *to* the comitative, *kara* the ablative
of spatial and temporal sources, *made* the terminative of spatial and temporal endpoints, and
*yori* the ablative, as the separative standard of the comparative. -/
def functions : Postposition → Finset _root_.Case
  | de => {.loc, .inst}
  | e => {.all}
  | «to» => {.com}
  | kara => {.abl}
  | made => {.ter}
  | yori => {.abl}

end Postposition

end Japanese
