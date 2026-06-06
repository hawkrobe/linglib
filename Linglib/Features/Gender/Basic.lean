import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.BigOperators
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Data.UD.Basic

/-!
# Gender — comparative labels and per-language systems
[corbett-1991] [kramer-2015] [kramer-2020] [corbett-fedden-2016]
[sudo-spathas-2020]

Gender has no universal value inventory. A gender is a language-particular
equivalence class of agreement behavior ([corbett-1991], crediting Hockett;
[kramer-2015] def (1) p. 65; [sudo-spathas-2020] fn. 1) — so, unlike `Number`
and `Person`, whose values a universal feature calculus labels
language-independently ([harbour-2014], [harbour-2016]), the root `Gender`
type is *not* a canonical value inventory but a vocabulary of
comparative-concept labels. The canonical object is `Gender.System`: a
language's own finite carrier of controller genders. [kramer-2015]'s gender
feature calculus generates at most three genders (Table 11.1); beyond that it
requires per-class identity features (§11.2.2) — a language-particular
carrier in all but name. This file encodes the carrier directly, the way
`Basis ι R M` takes the index type as a parameter.

## Main declarations

* `Gender` — the six comparative labels (sex-based masculine, feminine,
  neuter, common; animacy-based animate, inanimate), with realization
  `Gender.toUD` and ingestion `Gender.fromUD` — `UD.Gender` is realization
  vocabulary, exactly as `UD.Number`/`UD.Person` are for `Number`/`Person`.
* `Gender.System` — a language's gender system over its own carrier `G` of
  controller genders: a partial comparative labeling and a morphosyntactic
  default. The gender count is `Fintype.card G`, and [kramer-2015]'s
  two-class minimum (def (7i), p. 70) is the mathlib typeclass
  `Nontrivial G` — one agreement pattern for all nouns is the absence of a
  system, not a one-gender system.
* `Gender.Faithful` — distinct genders are distinguished by some agreement
  target: injectivity of per-gender agreement behavior. Yields
  `Gender.Faithful.card_le_pow`: a language whose agreement shows `f` forms
  on each of `t` targets supports at most `f ^ t` controller genders.
* `Gender.System.Assigned` — a system with noun-level assignment.
  `SemanticCore` is [kramer-2015]'s (7ii) (Dahl's generalization: assignment
  is semantically determined on a nonempty core of animate nouns; "no
  language assigns genders completely randomly or completely formally",
  p. 70). `assign_factorsThrough` derives the Hockett–Corbett definition as a
  theorem: when agreement is mediated by gender and the carrier is faithful,
  assignment factors through observable agreement behavior.

## Implementation notes

* **Carrier discipline.** `G` is the *controller-gender* partition: singular
  and plural of one noun are one gender (Bantu "Class 1/2" convention,
  [kramer-2015] p. 252). Classifiers and declension class are out of scope —
  they do not trigger agreement ([kramer-2015] §4.1.1); nominal form classes
  (deriflection) are a distinct dimension and must not be conflated with the
  carrier.
* **Locus-neutral.** `System` makes no claim about where gender sits in the
  nominal spine (n vs Num vs D); locus claims are study content.
* Languages lacking gender — the majority ([kramer-2015] §11.2.4) — declare
  no `System`.
* Feature decompositions of the labels, interpretation, and resolution are
  separate modules; fragments' fine-grained gender enums are `System`
  carriers, and their ad-hoc label maps are the `label` field.
-/

set_option autoImplicit false

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

@[simp] theorem toUD_fromUD (u : UD.Gender) : (fromUD u).toUD = some u := by
  cases u <;> rfl

/-- Labels with a UD realization round-trip. -/
theorem fromUD_of_toUD_eq_some :
    ∀ {g : Gender} {u : UD.Gender}, g.toUD = some u → fromUD u = g := by
  decide

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
      ([kramer-2015]: feminine defaults are attested). -/
  default : G

/-! ### Agreement faithfulness

[corbett-1991]'s definition operationalized. Agreement evidence for a carrier
`G` is a behavior map `agr : G → T → F` — for each gender, the form each
target shows. The carrier is *faithful* to the evidence when distinct genders
are distinguished by some target; a carrier that is not faithful has posited
a spurious distinction (two "genders" that agree alike everywhere are one
gender). Target and form types are parameters: the substrate is neutral about
what counts as a target (predicate, attributive, pronoun), which is where
strict-Agree vs loose-covariation definitions of gender-hood differ
([kramer-2015] §4.1.2). -/

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

/-! ### Assigned systems and the semantic core

The assigned tier adds the noun-level assignment function — the Canonical
Gender Principle that each noun has a single gender value
([corbett-fedden-2016]) is its functionality. [kramer-2015]'s (7ii) lives
here: no attested system assigns gender completely randomly or completely
formally; some nonempty core of animate nouns is assigned by interpretation. -/

section Assigned

variable {N T F σ : Type*}

/-- A gender system together with its assignment: every noun of `N` gets
    exactly one controller gender. Paradigm-only fragments stay at the
    `System` tier. -/
structure System.Assigned (N G : Type*) extends System G where
  /-- Gender assignment. -/
  assign : N → G

namespace System.Assigned

variable (S : System.Assigned N G)

/-- The assignment has a *semantic core*: a nonempty set of nouns on which a
    semantic classification `sem` determines gender ([kramer-2015], after
    Dahl). Arbitrary assignment is permitted off the core. -/
def SemanticCore (core : Set N) (sem : N → σ) : Prop :=
  core.Nonempty ∧ Function.FactorsThroughOn S.assign sem core

/-- The system mediates noun-level agreement evidence `nounAgr` via the
    per-gender behavior `agr`: a noun's agreement behavior is its gender's. -/
def Mediates (nounAgr : N → T → F) (agr : G → T → F) : Prop :=
  ∀ n, nounAgr n = agr (S.assign n)

/-- The Hockett–Corbett definition of gender, derived rather than stipulated:
    if agreement is mediated by gender and the carrier is faithful, then
    gender assignment factors through observable agreement behavior. -/
theorem assign_factorsThrough {nounAgr : N → T → F} {agr : G → T → F}
    (med : S.Mediates nounAgr agr) (faith : Faithful agr) :
    Function.FactorsThrough S.assign nounAgr :=
  λ a b hab => faith (((med a).symm.trans hab).trans (med b))

end System.Assigned

end Assigned

end Gender
