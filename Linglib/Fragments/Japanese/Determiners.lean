module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Fragments.Japanese.Coordination
public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese quantifiers

Japanese has no articles, and most of its quantifiers are built from an indeterminate pronoun of
`Japanese.Pronouns` (*dare* 'who', *dono* 'which', *nan-* 'how many') and a particle, *ka* for the
existential (*dare-ka* 'someone') and *mo* for the universal (*dare-mo* 'everyone', *dono* N *mo*
'every N'). The particles are the coordinators *ka* 'or' and *mo* 'and', and an indeterminate
quantifier applies its particle's coordination to the values its scope takes on the restrictor,
the supremum for *ka* and the infimum for *mo*, which are `Quantifier.GQ.some` and `every`. The
remaining quantifiers are words of their own, the carrier `QuantityWord` of *subete* 'all',
*hotondo* 'most' and *ryōhō* 'both'. Numeral quantifiers such as *nan-nin-ka* 'several people'
float away from their noun phrase, and *dare-mo* under clausemate negation is the negative
indefinite of `Fragments/Japanese/PolarityItems.lean`.

## Main definitions

* `Japanese.Determiners.Indefinite`: the quantifiers an indeterminate and a particle form.
* `Japanese.Determiners.Indefinite.reading`: the particle's coordination over the restrictor.
* `Japanese.Determiners.QuantityWord`: the quantifiers that are words of their own.
* `Japanese.Determiners.inventory`: the determiner inventory, quantifiers only.

## Main results

* `Indefinite.reading_of_disjunctive`, `Indefinite.reading_of_conjunctive`: the readings under
  *ka* and *mo* are `Quantifier.GQ.some` and `every`.

## References

* [chierchia-1998]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
-/

@[expose] public section

namespace Japanese.Determiners

open Quantifier
open scoped Semantics

universe u

/-- A quantifier built from an indeterminate and a particle, with the classifier between them
where there is one. -/
structure Indefinite where
  /-- The indeterminate. -/
  indeterminate : InterrogativePronoun
  /-- The particle, *ka* or *mo*. -/
  particle : Coordinator
  /-- The classifier after the indeterminate, as in *nan-nin-ka*. -/
  classifier : Option Classifier := none
  deriving DecidableEq

namespace Indefinite

variable (q : Indefinite)

/-- The form joins the indeterminate, its classifier and the particle by hyphens, and puts the
particle of the determiner *dono* after the noun the determiner takes. -/
def form : String :=
  let p := q.particle.morph.form
  if q.indeterminate.ontology = .determiner then q.indeterminate.form ++ " … " ++ p
  else q.indeterminate.form ++ (q.classifier.elim "" ("-" ++ ·.form)) ++ "-" ++ p

/-- An indeterminate quantifier's determiner entry records its form. -/
def toQuantifier : Quantifier := { form := q.form }

/-- The reading of an indeterminate quantifier applies its particle's coordination to the
values the scope takes on the restrictor. -/
def reading : GQ.Family.{u} :=
  fun _ _ R S ↦ q.particle.denote (S '' {x | R x})

/-- An indeterminate quantifier denotes its reading. -/
instance : Semantics.Denotes Indefinite (Set GQ.Family.{u}) where
  denote q := {q.reading}

variable {q}

/-- Under a disjunctive particle the reading is `Quantifier.GQ.some`. -/
theorem reading_of_disjunctive (h : q.particle.role = .disjunctive) :
    q.reading = GQ.Family.some.{u} := by
  funext _ _ R S
  rw [reading, Coordinator.denote_of_disjunctive h, ← GQ.some_eq_sSup_image]; rfl

/-- Under a conjunctive particle the reading is `every`. -/
theorem reading_of_conjunctive (h : q.particle.role = .conjunctive) :
    q.reading = GQ.Family.every.{u} := by
  funext _ _ R S
  rw [reading, Coordinator.denote_of_conjunctive h, ← GQ.every_eq_sInf_image]; rfl

/-- Under a negative particle the reading is `no`. -/
theorem reading_of_negative (h : q.particle.role = .negative) :
    q.reading = GQ.Family.no.{u} := by
  funext _ _ R S
  rw [reading, Coordinator.denote_of_negative h, ← GQ.no_eq_compl_sSup_image]; rfl

end Indefinite

/-- *Dare-ka* is 'someone'. -/
def dare_ka : Indefinite := ⟨Pronouns.dare, Coordination.ka, none⟩

/-- *Dare-mo* is 'everyone'. -/
def dare_mo : Indefinite := ⟨Pronouns.dare, Coordination.mo, none⟩

/-- *Dono* N *mo* is 'every N'. -/
def dono_N_mo : Indefinite := ⟨Pronouns.dono, Coordination.mo, none⟩

/-- *Nan-nin-ka* is 'several people', with the classifier *-nin*. -/
def nan_nin_ka : Indefinite := ⟨Pronouns.nan, Coordination.ka, some Classifiers.nin⟩

/-- `indefinites` lists the indeterminate quantifiers. -/
def indefinites : List Indefinite := [dare_ka, dare_mo, dono_N_mo, nan_nin_ka]

/-- The quantifiers that are words of their own are *subete* 'all', *hotondo* 'most' and *ryōhō*
'both'. -/
inductive QuantityWord where
  | subete | hotondo | ryoho
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The form of a word is its romanization. -/
def form : QuantityWord → String
  | .subete => "subete"
  | .hotondo => "hotondo"
  | .ryoho => "ryōhō"

/-- A word's determiner record carries its form. -/
def toQuantifier (w : QuantityWord) : Quantifier := { form := w.form }

/-- `toList` lists every word. -/
def toList : List QuantityWord := [.subete, .hotondo, .ryoho]

/-- *Subete* reads as `every`, *hotondo* as `most` and *ryōhō* as `both`. -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .subete => {Quantifier.GQ.Family.every}
    | .hotondo => {Quantifier.GQ.Family.most}
    | .ryoho => {Quantifier.GQ.Family.both}

end QuantityWord

/-- The determiner inventory has quantifiers only, there being no articles. -/
def inventory : Determiner.Inventory :=
  indefinites.map (.quantifier ·.toQuantifier) ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier)

/-- *Dare-ka* reads as `Quantifier.GQ.some`. -/
theorem denote_dare_ka : ⟦dare_ka⟧ = ({GQ.Family.some} : Set GQ.Family.{u}) := by
  rw [← Indefinite.reading_of_disjunctive (q := dare_ka) rfl]; rfl

/-- *Dare-mo* reads as `every`. -/
theorem denote_dare_mo : ⟦dare_mo⟧ = ({GQ.Family.every} : Set GQ.Family.{u}) := by
  rw [← Indefinite.reading_of_conjunctive (q := dare_mo) rfl]; rfl

end Japanese.Determiners
