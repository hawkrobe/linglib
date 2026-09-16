import Linglib.Syntax.Case.Basic
import Linglib.Syntax.Number.Basic
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Romance Clitic Paradigm Schema
[munoz-perez-2026]

The shared schema for Romance object-clitic paradigms: the three-way
ACC/DAT/REFL paradigm contrast, the clitic entry record with its
capability instances, and the paradigm-derived syncretism predicates.
Italian (`Fragments/Italian/Pronouns.lean`) and Spanish
(`Fragments/Spanish/Clitics.lean`) instantiate it with their paradigm
data; the syncretism predicates drive [munoz-perez-2026]'s stylistic
applicatives.

REFL is a paradigm cell, not a case value. In the languages instantiated
here (Italian, Spanish) the third-person reflexive (*si*/*se*) is a
single form that does not determine the accusative/dative contrast — at
first/second person the contrast is syncretic throughout — so
`CliticCase.toCase` sends REFL to `none` while ACC/DAT project to the
analytical inventory. This is a commitment scoped to those languages:
Romanian contrasts reflexive accusative *se* with reflexive dative *își*,
so a Romanian instantiation must split the REFL cell (or make the
projection person-sensitive) rather than reuse this `toCase`.

The clitic is its own bespoke struct, with its own `HasPhi` instance and binding class,
not merged into `Pronoun`. Deficiency is
deliberately *not* a capability: it is per-series (a whole clitic paradigm
is `.clitic`), modelled by the per-language `cliticStrength` and the
`Strength` order, not by a per-element accessor.
-/

namespace Romance.Clitics

/-- The three-way paradigm contrast for Romance object clitics. -/
inductive CliticCase where
  | accusative
  | dative
  | reflexive
  deriving DecidableEq, Repr

/-- Project a paradigm cell to the analytical case inventory. REFL
    projects to `none`: in Italian/Spanish the reflexive does not
    determine the accusative/dative contrast. (Romanian, contrasting
    reflexive *se*/*își*, needs a split REFL cell instead.) -/
def CliticCase.toCase : CliticCase → Option Case
  | .accusative => some .acc
  | .dative => some .dat
  | .reflexive => none

/-- A single clitic form in a paradigm. -/
structure CliticEntry where
  form : String
  person : Person
  number : Number
  case_ : CliticCase
  deriving Repr, BEq

/-- A clitic bears its person and number. -/
instance : HasPhi CliticEntry := ⟨fun c ↦ Agreement.Bundle.pn c.person c.number⟩

/-- The binding class of a clitic, from its paradigm cell: a reflexive clitic is a Principle-A
anaphor and an accusative or dative object clitic a Principle-B pronominal. -/
def CliticEntry.bindingClass (c : CliticEntry) : Binding.BindingClass :=
  match c.case_ with | .reflexive => .reflexive | _ => .pronoun

/-- A clitic is a Principle-A anaphor when its binding class is. -/
abbrev CliticEntry.IsAnaphor (c : CliticEntry) : Prop := c.bindingClass.IsAnaphor

/-- A clitic is a Principle-B pronominal when its binding class is. -/
abbrev CliticEntry.IsPronominal (c : CliticEntry) : Prop := c.bindingClass.IsPronominal

/-- Look up the form for a given person, number, and paradigm cell. -/
def lookupForm (paradigm : List CliticEntry) (p : Person) (n : Number)
    (c : CliticCase) : Option String :=
  (paradigm.find? (fun e => e.person == p && e.number == n && e.case_ == c)).map
    (·.form)

/-- Are two paradigm cells syncretic for a given person/number
    combination? Derived from the paradigm data: syncretism holds iff the
    looked-up forms are identical (and both exist). -/
def isSyncretic (paradigm : List CliticEntry) (p : Person) (n : Number)
    (c1 c2 : CliticCase) : Bool :=
  match lookupForm paradigm p n c1, lookupForm paradigm p n c2 with
  | some f1, some f2 => f1 == f2
  | _, _ => false

/-- DAT/REFL syncretism for a given person/number — the key condition for
    SE-optionality ([munoz-perez-2026]). -/
def datReflSyncretic (paradigm : List CliticEntry) (p : Person) (n : Number) : Bool :=
  isSyncretic paradigm p n .dative .reflexive

end Romance.Clitics
