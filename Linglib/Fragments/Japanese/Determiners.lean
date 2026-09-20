import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Quantification.Lexicon
import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Denotation
import Linglib.Fragments.Japanese.Coordination

/-!
# Japanese quantifiers

Japanese has no articles, and most of its quantifiers are built from an indeterminate pronoun
(*dare* 'who', *nani* 'what', *dono* 'which', *nan* 'how many') and a particle: with *ka* the
phrase is existential (*dare-ka* 'someone'), with *mo* universal (*dare-mo* 'everyone', *dono*
N *mo* 'every N'), the particles being the coordinators *ka* 'or' and *mo* 'and', so that the
force of the phrase is the Boolean operation of its particle. The remaining quantifiers are
words of their own, the carrier `QuantityWord` of *subete* 'all', *hotondo* 'most' and *ryōhō*
'both'. Both carriers denote the readings available for their members, an indeterminate
quantifier reading by the force of its particle. Numeral quantifiers
such as *nan-nin-ka* 'several people' float away from their noun phrase, and *dare-mo* under
clausemate negation is the negative indefinite of `Fragments/Japanese/PolarityItems.lean`.

## Main definitions

* `Japanese.Determiners.Indeterminate`, `Japanese.Determiners.Indefinite` — the indeterminate
  pronouns and the quantifiers an indeterminate and a particle form, with the force
  `Indefinite.force` of the particle
* `Japanese.Determiners.QuantityWord` — the quantifiers that are words of their own
* `Japanese.Determiners.inventory` — the determiner inventory, quantifiers only

## References

* [chierchia-1998]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
-/

namespace Japanese.Determiners

open Quantifier.Lexicon

universe u

/-- The indeterminate pronouns. -/
inductive Indeterminate where
  /-- *dare* 'who'. -/
  | dare
  /-- *nani* 'what'. -/
  | nani
  /-- *dono* 'which', a determiner. -/
  | dono
  /-- *nan* 'how many', before a classifier. -/
  | nan
  deriving DecidableEq, Repr, Fintype

namespace Indeterminate

/-- The romanization. -/
def romaji : Indeterminate → String
  | .dare => "dare"
  | .nani => "nani"
  | .dono => "dono"
  | .nan => "nan"

/-- The kanji or kana form. -/
def form : Indeterminate → String
  | .dare => "誰"
  | .nani => "何"
  | .dono => "どの"
  | .nan => "何"

end Indeterminate

/-- The force a particle gives an indeterminate: existential for the disjunction *ka* and
universal for the conjunction *mo*. -/
def particleForce (p : Coordinator) : QForce :=
  match p.role with
  | .disjunctive => .existential
  | _ => .universal

/-- A quantifier built from an indeterminate and a particle, with the classifier or noun
between them where there is one. -/
structure Indefinite where
  /-- The indeterminate. -/
  indeterminate : Indeterminate
  /-- The particle, *ka* or *mo*. -/
  particle : Coordinator
  /-- What stands between the indeterminate and the particle. -/
  host : Option String := none
  deriving DecidableEq, Repr

namespace Indefinite

variable (q : Indefinite)

/-- The romanized form, the parts joined by hyphens. -/
def romaji : String :=
  q.indeterminate.romaji ++ "-" ++ (q.host.elim "" (· ++ "-")) ++ q.particle.form

/-- The force of the quantifier, that of its particle. -/
def force : QForce := particleForce q.particle

/-- The quantifier as a determiner entry. -/
def toQuantifier : Quantifier := { form := q.romaji }

/-- The reading available for an indeterminate quantifier is that of its particle's force,
`some_sem` for the disjunction *ka* and `every_sem` for the conjunction *mo*. -/
instance : Semantics.Denotes Indefinite (Set Quantifier.GQ.Family.{u}) where
  denote q :=
    match q.particle.role with
    | .disjunctive => {Quantifier.GQ.Family.some}
    | _ => {Quantifier.GQ.Family.every}

end Indefinite

/-- *dare-ka* 'someone'. -/
def dare_ka : Indefinite := ⟨.dare, Coordination.ka, none⟩

/-- *dare-mo* 'everyone'. -/
def dare_mo : Indefinite := ⟨.dare, Coordination.mo, none⟩

/-- *dono* N *mo* 'every N'. -/
def dono_N_mo : Indefinite := ⟨.dono, Coordination.mo, some "N"⟩

/-- *nan-nin-ka* 'several people', with the classifier *-nin*. -/
def nan_nin_ka : Indefinite := ⟨.nan, Coordination.ka, some "nin"⟩

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

/-- The readings available for a word: *subete* reads as `every_sem`, *hotondo* as `most_sem`
and *ryōhō* as `both_sem`. -/
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
