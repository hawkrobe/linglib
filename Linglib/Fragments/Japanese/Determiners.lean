module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Lexicon
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation
public import Linglib.Fragments.Japanese.Coordination
public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese quantifiers

Japanese has no articles, and most of its quantifiers are built from an indeterminate pronoun of
`Japanese.Pronouns` (*dare* 'who', *dono* 'which', *nan-* 'how many') and a particle: with *ka* the
phrase is existential (*dare-ka* 'someone'), with *mo* universal (*dare-mo* 'everyone', *dono* N
*mo* 'every N'), the particles being the coordinators *ka* 'or' and *mo* 'and', so that the force of
the phrase is the Boolean operation of its particle. The remaining quantifiers are words of their
own, the carrier `QuantityWord` of *subete* 'all', *hotondo* 'most' and *ryōhō* 'both'. Both
carriers denote the readings available for their members, an indeterminate quantifier reading by the
force of its particle. Numeral quantifiers such as *nan-nin-ka* 'several people' float away from
their noun phrase, and *dare-mo* under clausemate negation is the negative indefinite of
`Fragments/Japanese/PolarityItems.lean`.

## Main definitions

* `Japanese.Determiners.Indefinite` — the quantifiers an indeterminate and a particle form, with
  the force `Indefinite.force` of the particle
* `Japanese.Determiners.QuantityWord` — the quantifiers that are words of their own
* `Japanese.Determiners.inventory` — the determiner inventory, quantifiers only

## References

* [chierchia-1998]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
-/

@[expose] public section

namespace Japanese.Determiners

open Quantifier.Lexicon

universe u

/-- The force a particle gives an indeterminate: existential for the disjunction *ka* and
universal for the conjunction *mo*. -/
def particleForce (p : Coordinator) : QForce :=
  match p.role with
  | .disjunctive => .existential
  | _ => .universal

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

/-- The form: the indeterminate, its classifier and the particle joined by hyphens, and for the
determiner *dono* the particle after the noun the determiner takes. -/
def form : String :=
  if q.indeterminate.ontology = .determiner then q.indeterminate.form ++ " … " ++ q.particle.form
  else q.indeterminate.form ++ (q.classifier.elim "" ("-" ++ ·.form)) ++ "-" ++ q.particle.form

/-- The force of the quantifier, that of its particle. -/
def force : QForce := particleForce q.particle

/-- The quantifier as a determiner entry. -/
def toQuantifier : Quantifier := { form := q.form }

/-- The reading available for an indeterminate quantifier is that of its particle's force,
`Quantifier.GQ.some` for the disjunction *ka* and `every` for the conjunction *mo*. -/
instance : Semantics.Denotes Indefinite (Set Quantifier.GQ.Family.{u}) where
  denote q :=
    match q.particle.role with
    | .disjunctive => {Quantifier.GQ.Family.some}
    | _ => {Quantifier.GQ.Family.every}

end Indefinite

/-- *dare-ka* 'someone'. -/
def dare_ka : Indefinite := ⟨Pronouns.dare, Coordination.ka, none⟩

/-- *dare-mo* 'everyone'. -/
def dare_mo : Indefinite := ⟨Pronouns.dare, Coordination.mo, none⟩

/-- *dono* N *mo* 'every N'. -/
def dono_N_mo : Indefinite := ⟨Pronouns.dono, Coordination.mo, none⟩

/-- *nan-nin-ka* 'several people', with the classifier *-nin*. -/
def nan_nin_ka : Indefinite := ⟨Pronouns.nan, Coordination.ka, some Classifiers.nin⟩

/-- The indeterminate quantifiers. -/
def indefinites : List Indefinite := [dare_ka, dare_mo, dono_N_mo, nan_nin_ka]

/-- The quantifiers that are words of their own: *subete* 'all', *hotondo* 'most' and *ryōhō*
'both'. -/
inductive QuantityWord where
  | subete | hotondo | ryoho
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The romanized form. -/
def form : QuantityWord → String
  | .subete => "subete"
  | .hotondo => "hotondo"
  | .ryoho => "ryōhō"

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : Quantifier := { form := w.form }

/-- All the words. -/
def toList : List QuantityWord := [.subete, .hotondo, .ryoho]

/-- The readings available for a word: *subete* reads as `every`, *hotondo* as `most`
and *ryōhō* as `both`. -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .subete => {Quantifier.GQ.Family.every}
    | .hotondo => {Quantifier.GQ.Family.most}
    | .ryoho => {Quantifier.GQ.Family.both}

end QuantityWord

/-- The determiner inventory: quantifiers only, there being no articles. -/
def inventory : Determiner.Inventory :=
  indefinites.map (.quantifier ·.toQuantifier) ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier)

/-- The universal indeterminates are the ones not built on the disjunction. -/
theorem Indefinite.force_eq_universal_iff (q : Indefinite) :
    q.force = .universal ↔ q.particle.role ≠ .disjunctive := by
  unfold Indefinite.force particleForce
  cases q.particle.role <;> simp

end Japanese.Determiners
