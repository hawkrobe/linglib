import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.BigOperators
import Linglib.Core.Relation.FactorsThroughOn
import Linglib.Data.UD.Basic

/-!
# Gender systems

This file defines a language's gender system over its own carrier of controller genders,
the comparative labels cross-linguistic comparison uses for them, and the assigned system
that gives every noun a controller gender.

A gender is a class of nouns that take the same agreements, so a language's genders are
language-particular: there is no universal inventory of gender values as there is of number
and person values, only a vocabulary of comparative labels, masculine, feminine, neuter,
common, animate and inanimate, that a system's genders may partially bear. The carrier of
controller genders is a type parameter, as the index type of a basis is, and the number of
genders is its cardinality; a carrier is faithful to agreement evidence when distinct
genders are distinguished by some target. The rules assigning nouns to genders are the
assignment systems of `Syntax/Gender/Assignment.lean`.

## Main definitions

* `Gender`: the comparative labels, with the Universal Dependencies realization
  `Gender.toUD` and ingestion `Gender.fromUD`, a partial inverse.
* `Gender.System`: a gender system over a carrier, a partial labelling and a morphosyntactic
  default.
* `Gender.Faithful`: a carrier is faithful to agreement evidence when the evidence is
  injective.

## Main results

* `Gender.Faithful.card_le_pow`: `f` forms on each of `t` targets support at most `f ^ t`
  controller genders.
* `Gender.factorsThrough_of_faithful`: when a faithful carrier mediates agreement,
  assignment factors through agreement behaviour, genders as agreement classes by theorem
  rather than by stipulation.

## Implementation notes

* The carrier is the controller-gender partition: singular and plural of one noun are one
  gender. Classifiers and declension classes trigger no agreement and are not carriers.
* The system makes no claim about where gender sits in the nominal spine; that is study
  content. Languages lacking gender, the majority, declare no system.
* Kramer's two-class minimum is the hypothesis `Nontrivial G` on the consumers that need
  it: one agreement pattern for all nouns is the absence of a system.
* Assignment systems, feature decompositions of the labels and the agreement classes of
  nouns are separate modules; fragments' gender enums are carriers, and their label maps
  the `label` field.

## References

* [corbett-1991] — genders as agreement classes, crediting [hockett-1958]
* [zaliznjak-1964] — agreement classes
* [kramer-2015] — the two-class minimum
* [corbett-fedden-2016] — canonical gender
* [harbour-2014] — the universal calculi of number and person, which gender lacks
-/

/-- Comparative-concept labels for controller genders ([corbett-1991]).

    These are the descriptive labels cross-linguistic comparison uses for a
    language's agreement classes — not a universal value inventory. A
    language's actual genders are the carrier of its `Gender.System`; `label`
    maps them (partially) into this vocabulary. -/
inductive Gender where
  /-- Masculine: male humans/higher animates; default in many sex-based systems. -/
  | masculine
  /-- Feminine: female humans/higher animates; marked in many sex-based systems. -/
  | feminine
  /-- Neuter: neither masculine nor feminine; inanimate default in 3-gender systems. -/
  | neuter
  /-- Common: merged masculine + feminine (Swedish, Danish). -/
  | common
  /-- Animate: animate referents in animacy-based systems (Algonquian). -/
  | animate
  /-- Inanimate: inanimate referents in animacy-based systems. -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

namespace Gender

/-! ### Realization: Universal Dependencies

`UD.Gender` is the surface tagset corpora annotate, not an analytical
inventory: animacy-based labels have no UD realization. -/

/-- Realize a comparative label as a UD gender tag, where one exists. -/
def toUD : Gender → Option UD.Gender
  | .masculine => some .Masc
  | .feminine  => some .Fem
  | .neuter    => some .Neut
  | .common    => some .Com
  | .animate   => none
  | .inanimate => none

/-- Ingest a UD gender tag. Total: every UD gender has a comparative label. -/
def fromUD : UD.Gender → Gender
  | .Masc => .masculine
  | .Fem  => .feminine
  | .Neut => .neuter
  | .Com  => .common

/-- Realization is a partial inverse of ingestion. -/
theorem isPartialInv_fromUD_toUD : Function.IsPartialInv fromUD toUD :=
  λ x y => by cases x <;> cases y <;> decide

@[simp] theorem toUD_fromUD (u : UD.Gender) : (fromUD u).toUD = some u :=
  isPartialInv_fromUD_toUD.eq u

/-- Labels with a UD realization round-trip. -/
theorem fromUD_of_toUD_eq_some {g : Gender} {u : UD.Gender} (h : g.toUD = some u) :
    fromUD u = g :=
  (isPartialInv_fromUD_toUD u g).1 h

/-! ### Gender systems

A gender system is language-particular: its values are the language's own
controller genders, supplied as the carrier type `G` (a fragment's gender
enum). The comparative labels above enter only through the partial `label`
field — the carrier itself is not constrained to fit them, which is what
accommodates Bantu-scale inventories that no label vocabulary covers. -/

variable {G : Type*}

/-- A language's gender system over its own carrier `G` of controller
    genders ([corbett-1991]; [kramer-2015]).

    The gender count is `Fintype.card G`; the two-class minimum is the
    hypothesis `Nontrivial G` on consumers that need it. Languages without
    gender agreement declare no `System`. -/
structure System (G : Type*) where
  /-- Partial comparative labeling of the controller genders. Bantu-style
      classes typically map to `none` outside a human/animate core. -/
  label : G → Option Gender
  /-- The morphosyntactic default: the gender realized when there are no
      gender features to agree with. Per-system data, not derivable
      ([kramer-2015]: feminine defaults are attested). A language may use
      distinct defaults in distinct contexts, clausal controllers against
      indeclinable nouns for instance; the system records the normal case,
      and a second default is study content. -/
  default : G

/-! ### Agreement faithfulness

Agreement evidence for a carrier `G` is a behaviour map `agr : G → T → F`, the form each
target shows for each gender. The carrier is faithful to the evidence when distinct genders
are distinguished by some target; a carrier that is not faithful has posited a spurious
distinction, since two genders that agree alike everywhere are one gender. The target and
form types are parameters: the substrate is neutral about what counts as a target, which is
where [kramer-2015]'s strict-Agree and loose-covariation definitions of gender differ. -/

section Faithful

variable {T F : Type*}

/-- A carrier `G` of controller genders is faithful to agreement evidence
    `agr` when distinct genders are distinguished by some target's form.

    An `abbrev` so that `Function.Injective`'s decidability instance (under
    `[Fintype G]`, `[DecidableEq T]`, `[DecidableEq F]`) applies: concrete
    fragments discharge faithfulness by `decide`. -/
abbrev Faithful (agr : G → T → F) : Prop :=
  Function.Injective agr

/-- A language whose agreement morphology shows `f` forms on each of `t`
    targets supports at most `f ^ t` controller genders. -/
theorem Faithful.card_le_pow [Fintype G] [Fintype T] [Fintype F] [DecidableEq T]
    {agr : G → T → F} (h : Faithful agr) :
    Fintype.card G ≤ Fintype.card F ^ Fintype.card T := by
  rw [← Fintype.card_fun]
  exact Fintype.card_le_of_injective agr h

end Faithful

/-! ### Assignment and agreement

An assignment gives every noun one controller gender, the Canonical Gender Principle of
[corbett-fedden-2016]. When noun-level agreement is the per-gender behaviour of the assigned
gender and the carrier is faithful, assignment factors through observable agreement
behaviour: genders are agreement classes in [zaliznjak-1964]'s sense, the starting point of
[corbett-1991]'s definition. Corbett's controller genders discount subgenders, inquorate
genders and overdifferentiated targets on the way from agreement classes to genders, and
those steps are not modelled here. -/

section Assignment

variable {N T F : Type*}

/-- Genders as agreement classes, derived rather than stipulated: if noun-level agreement
`nounAgr` is the per-gender behaviour `agr` of the assigned gender and the carrier is
faithful, then gender assignment factors through observable agreement behaviour. -/
theorem factorsThrough_of_faithful {assign : N → G} {nounAgr : N → T → F} {agr : G → T → F}
    (med : nounAgr = agr ∘ assign) (faith : Faithful agr) :
    Function.FactorsThrough assign nounAgr :=
  λ _ _ hab => faith (by simpa [med] using hab)

end Assignment

end Gender
