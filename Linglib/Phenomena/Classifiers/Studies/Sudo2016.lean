import Linglib.Theories.Semantics.Classifier.Defs
import Linglib.Theories.Semantics.Classifier.TypeN
import Linglib.Theories.Semantics.Classifier.Composition
import Linglib.Fragments.Japanese.Classifier
import Linglib.Phenomena.Classifiers.Typology
import Linglib.Phenomena.Classifiers.Studies.Chierchia1998

/-!
# Sudo (2016) — The Semantic Role of Classifiers in Japanese
@cite{sudo-2016}

Yasutada Sudo. *The Baltic International Yearbook of Cognition, Logic and
Communication* 11. DOI: 10.4148/1944-3676.1108

## Central Claim

Sudo argues that what makes Japanese an *obligatory classifier language* is
not the semantics of nouns (contra @cite{chierchia-1998}, @cite{krifka-2008},
@cite{borer-2005}, @cite{rothstein-2010}, @cite{nemoto-2005}, @cite{li-2011})
but the semantics of numerals. His core proposal:

1. In *all* natural languages, numerals denote singular terms of type `n`
   (constant intensions `λw. n`, modeled here by `NumeralIntens.const`).
2. Languages are equipped with a phonologically silent ∪-operator
   (`Semantics.Classifier.upNum`) that lifts numerals from type `⟨s,n⟩` to
   predicates of type `⟨s,⟨e,t⟩⟩`.
3. Following @cite{chierchia-1998}'s Blocking Principle, ∪ is *blocked* in
   languages whose lexicon contains overt items playing the same role —
   namely classifiers. In Japanese the classifiers `-rin`, `-hiki`, `-nin`,
   `-mai`, `-hon`, `-ko`, ... are precisely such items, so ∪ is unavailable
   and predicative numerals like *"okyakusan-wa juu-ni-da"* (eq. 15) are
   ruled out.
4. The inverse ∩-operator (`Semantics.Classifier.downNum`) maps certain
   properties back to numeral intensions and has no overt counterpart in
   either English or Japanese, so it is freely available in both — explaining
   the well-formedness of Japanese type-n classifier phrases like
   *"juu-ni-nin-da"* (eq. 22a).

## Cross-paper disagreement

`Chierchia1998.japaneseStrategy = .forNoun` (CLF atomizes a kind-denoting
noun) and `Sudo2016.japaneseStrategy = .sudoBlocking` (CLF blocks the
silent ∪-operator on numerals) commit to incompatible analyses of the
same empirical fact (Japanese requires classifiers). The disagreement is
proved structurally in `sudo_disagrees_with_chierchia_on_japanese` below
and propagates to divergent empirical predictions through LMR's
diagnostic battery (`LittleMoroneyRoyer2022.predictionsOf`).

## What is formalized

- Per-classifier `ClassifierDenot` instances for the six core atomic-sortal
  classifiers Sudo cites or instantiates: `-rin`, `-hiki`, `-nin`, `-mai`,
  `-hon`, `-ko`.
- The four empirical paradigms (15)/(16)/(17a/b)/(22) at the level of the
  Sudo apparatus: predicative numerals require ∪, ∪ is blocked in Japanese
  by the presence of overt classifiers, ∩ is available so type-n classifier
  phrases compose.
- A cross-paper theorem locating the disagreement with the
  `chierchia-1998` strategy assignment in the typology file.

## Out of scope

- Non-atomic classifiers `-kumi` (pair) and `-daasu` (dozen) per Sudo (9a/b)
  require explicit mereological joins of disjoint pairs.
- Sudo's optional-classifier-language follow-up (Armenian, Hausa) per
  @cite{bale-khanjian-2008}, @cite{bale-khanjian-2014}, @cite{doetjes-2013}
  is left as a separate study file.
- The full presupposition-tracking ∪-Shifted FA / PM compositional rules
  (Sudo eqs. 11/19/26) are referenced via the type-shift signatures in
  `Composition.lean`; their full domain-of-definition machinery is not
  implemented here.
-/

namespace Sudo2016

open Semantics.Classifier
open Core.Intension (rigid)

universe u

/-! ## §1: Toy Domain

A minimal world type and entity domain sufficient to instantiate Sudo's
sortal classifiers. The domain is intentionally small — Sudo's argument is
type-theoretic, not data-driven. -/

/-- The toy world type. Sudo's intensional analysis is parameterized over
    worlds; for the purposes of demonstrating type-shifts, a singleton
    world suffices. Real applications would parameterize over a richer
    `World` type from `Core.IntensionalLogic.Frame`. -/
abbrev World := Unit

/-- A toy entity domain: a person, a flower, an animal (small), and a
    book. Six core classifiers can be selectively defined over this
    minimal domain. -/
inductive Entity where
  | hanako   -- a person
  | hana     -- a flower
  | inu      -- a small animal (dog)
  | hon      -- a book
  | ringo    -- a round object (apple)
  | kami     -- a flat object (paper)
  deriving DecidableEq, Repr

instance : PartialOrder Entity where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

/-! ## §2: Sortal Predicates

Each is a constant intension (rigid) over the toy domain. Named here
(rather than inlined into `japaneseSudoDenot`) so that `apply`-computation
theorems can reference them directly. -/

/-- `flower(x)`: sortal for `-rin` (Sudo eq. 4). -/
def flowerIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .hana)

/-- `human(x)`: sortal for `-nin` (Sudo eq. 8a). -/
def humanIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .hanako)

/-- `small_animal(x)`: sortal for `-hiki` (Sudo eq. 8b's atomic-sortal core). -/
def smallAnimalIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .inu)

/-- `bound_volume(x)`: sortal for `-satsu`. -/
def bookIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .hon)

/-- `round(x)`: sortal for `-ko`. -/
def roundIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .ringo)

/-- `flat(x)`: sortal for `-mai`. -/
def flatIntens : Core.Intension World (Entity → Prop) :=
  Core.Intension.rigid (· = .kami)

/-! ## §3: Per-Classifier Denotations

The exhaustive map from `Fragments.Japanese.Classifier` to `ClassifierDenot`.
Pattern matching on the typed inventory forces every classifier to either
get a denotation or an explicit `none` for the deferred cases (mensural
`-hai`/`-shoku`/`-teki`, non-atomic `-kumi`/`-daasu`, function-based
classifiers without a sortal predicate over our toy domain). Adding a
classifier to the fragment requires extending this match — the type checker
catches missing cases, replacing the prior floating-`def` style. -/

/-- Atomic-sortal denotation builder for the six classifiers Sudo formalizes
    over our toy domain. `none` for classifiers we haven't formalized
    (most function-based ones, mensural ones, non-atomic group ones). -/
def japaneseSudoDenot : Fragments.Japanese.Classifier →
    Option (ClassifierDenot World Entity)
  -- Atomic-sortal classifiers Sudo eqs. 4, 8a, 8b
  | .rin => some <| .ofSortal flowerIntens
  | .nin => some <| .ofSortal humanIntens
  | .hiki => some <| .ofSortal smallAnimalIntens
  | .satsu => some <| .ofSortal bookIntens
  | .ko => some <| .ofSortal roundIntens
  | .mai => some <| .ofSortal flatIntens
  -- Mensural classifiers (need non-atomic counting; deferred per Sudo §2.2)
  | .hai => none
  | .shoku => none
  | .teki => none
  -- Non-atomic group classifiers (Sudo eqs. 9a/9b; deferred)
  | .kumi => none
  | .daasu => none
  -- Default classifier `tsu` is semantically bleached; no sortal
  | .tsu => none
  -- Animacy/shape classifiers not formalized over the toy domain
  | .mei | .tou | .wa | .hon | .tsubu | .sao => none
  -- Function-based classifiers (no atomic-sortal Sudo formulation)
  | .dai | .kenBuilding | .kenIncident | .ki | .ku | .kyoku | .mon | .mune
  | .seki | .soku | .soo | .ten | .toori | .tsuu | .kabu
  | .furi | .zen | .kyaku => none

/-- The classifiers Sudo formalizes (the six atomic-sortal cases). -/
def sudoFormalized : List Fragments.Japanese.Classifier :=
  Fragments.Japanese.Classifier.all.filter
    (fun c => (japaneseSudoDenot c).isSome)

/-- Exactly six classifiers have a Sudo-style denotation in this file. -/
theorem six_classifiers_formalized : sudoFormalized.length = 6 := by decide

/-! ## §4: Sudo's Paradigms (eqs. 15, 16, 17, 22)

The empirical contrast that motivates the analysis. Sudo's argument
structure: (a) numerals can't predicate in Japanese (eq. 15); (b) adding
a classifier rescues the predication (eq. 16); (c) the same pattern
repeats with non-human classifiers (eq. 17). The numeral+classifier
phrase is type-n by ∩ (eq. 22). -/

/-- The numeral *six* as a Sudo-style type-n singular term: `λw. 6`. -/
def six : NumeralIntens World := NumeralIntens.const 6

/-- The numeral *twelve* as a Sudo-style type-n singular term: `λw. 12`. -/
def twelve : NumeralIntens World := NumeralIntens.const 12

/-- The numeral *four* as a Sudo-style type-n singular term: `λw. 4`. -/
def four : NumeralIntens World := NumeralIntens.const 4

/-- Whether Japanese has overt classifiers in the lexicon. Derived
    from the Japanese fragment's classifier inventory being non-empty.
    Sudo's blocking argument depends on this fragment-level fact. -/
def japaneseHasOvertClassifiers : Bool :=
  !Fragments.Japanese.Classifier.all.isEmpty

/-! ## §5: The Blocking Argument (Sudo §3)

Sudo eq. 15 (*kyoo-no okyakusan-wa juu-ni-da, intended: 'the guests today
are twelve'): a predicative numeral is ungrammatical in Japanese, despite
being grammatical in English (Rothstein 2013). Sudo derives this from
@cite{chierchia-1998}'s Blocking Principle: the silent ∪-operator that
would type-shift the numeral is unavailable in Japanese because
classifiers in the lexicon already do that work. -/

/-- The ∪-shift on numerals is **blocked** in Japanese. This is a
    corollary of the Blocking Principle applied to the fragment-level
    fact that Japanese has classifiers. -/
theorem japanese_blocks_upShift :
    upAvailability japaneseHasOvertClassifiers = .blocked := rfl

/-- Empirical content (Sudo eq. 15 → eq. 16): predicative numerals are
    out in Japanese; adding a classifier rescues the predication.
    This holds at the level of ∪-availability: the bare numeral has
    no shift to ⟨s,⟨e,t⟩⟩, so it cannot serve as a predicate. -/
theorem predicative_numerals_blocked :
    upAvailability japaneseHasOvertClassifiers ≠ .available := by
  decide

/-! ## §6: ∩ Is Available (Sudo §4, eq. 22)

Sudo eq. 22a (*kyoo-no okyakusan-no kazu-wa juu-ni-nin-da, 'the number of
guests today is twelve'): a numeral+classifier phrase serves as a type-n
singular term, identifying the cardinality 12. Sudo derives this from the
∩-operator, which has no overt counterpart in either English or Japanese,
so it is freely available in both languages. -/

/-! Note: The ∩-operator (`downNum`) has no overt classifier counterpart
and is therefore not subject to the Blocking Principle. The empirical
content is that numeral+classifier phrases can be type-n singular terms;
no language-by-language stipulation is needed here. -/

/-! ## §6b: `apply`-computation theorems (load-bearing denotations)

These theorems exercise the `ClassifierDenot.apply` body on concrete
toy-domain inputs, demonstrating that `japaneseSudoDenot` denotations
actually compute Sudo's eq. 4 / eq. 8 semantics rather than functioning
as a typed-but-inert classification table. -/

private lemma ncard_part_singleton (x : Entity) (P : Entity → Prop) (hP : P x) :
    {y : Entity | y ≤ x ∧ P y}.ncard = 1 := by
  have hSet : {y : Entity | y ≤ x ∧ P y} = {x} := by
    ext y
    refine ⟨fun ⟨hy, _⟩ => hy, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h
    exact ⟨h.le, h ▸ hP⟩
  rw [hSet, Set.ncard_singleton]

/-- Sudo eq. 8a applied at numeral 1 to `.hanako`: `-nin` recognises
    a single-human individual. The denotation `(japaneseSudoDenot .nin)`
    actually computes a true conjunction (sortal holds + count = 1). -/
theorem nin_one_hanako :
    ClassifierDenot.apply (.ofSortal humanIntens) () 1 .hanako :=
  ⟨rfl, ncard_part_singleton _ _ rfl⟩

/-- Sudo eq. 4 applied at numeral 1 to `.hana`: `-rin` recognises
    a single-flower individual. -/
theorem rin_one_hana :
    ClassifierDenot.apply (.ofSortal flowerIntens) () 1 .hana :=
  ⟨rfl, ncard_part_singleton _ _ rfl⟩

/-- Sudo eq. 8b applied at numeral 1 to `.inu`: `-hiki` recognises
    a single small-animal individual. -/
theorem hiki_one_inu :
    ClassifierDenot.apply (.ofSortal smallAnimalIntens) () 1 .inu :=
  ⟨rfl, ncard_part_singleton _ _ rfl⟩

/-- Sortal failure: `-nin` does *not* recognise the dog `.inu` as
    one human, because the `human` sortal presupposition fails on
    `.inu`. The first conjunct of `apply` is `False`. -/
theorem nin_not_inu :
    ¬ ClassifierDenot.apply (.ofSortal humanIntens) () 1 .inu := by
  intro ⟨h_human, _⟩
  -- humanIntens () .inu = (.inu = .hanako) which is false
  exact Entity.noConfusion h_human

/-- The denotations of distinct atomic-sortal classifiers differ:
    `-nin` and `-hiki` carry incompatible sortal predicates, so substituting
    one for the other on a `-nin`-positive input contradicts. -/
theorem nin_ne_hiki :
    japaneseSudoDenot .nin ≠ japaneseSudoDenot .hiki := by
  intro h
  -- nin-denot on hanako with n=1 holds; hiki-denot on hanako with n=1 fails.
  have hOk : ClassifierDenot.apply (.ofSortal humanIntens) () 1 .hanako :=
    nin_one_hanako
  have hBad : ¬ ClassifierDenot.apply (.ofSortal smallAnimalIntens) () 1 .hanako := by
    rintro ⟨hAnimal, _⟩; exact Entity.noConfusion hAnimal
  -- The Option-injection turns h into equality of the underlying denotations.
  have hEq : (ClassifierDenot.ofSortal humanIntens : ClassifierDenot World Entity)
           = .ofSortal smallAnimalIntens := Option.some.inj h
  exact hBad (hEq ▸ hOk)

/-! ## §7: Sudo's Per-Language Strategy Assignment + Cross-Paper Engagement

Per-language strategy assignments live in study files (not as metadata on
`NounCategorizationSystem`). Sudo's view is now a first-class constructor
of `ClassifierStrategy` (`.sudoBlocking`), so the disagreement with
@cite{chierchia-1998} reduces to a single decidable inequality. -/

/-- Sudo's strategy assignment for Japanese: classifier blocks the silent
    ∪-operator on numerals (Sudo §3, eqs. 15–16). -/
def japaneseStrategy : Core.NounCategorization.ClassifierStrategy := .sudoBlocking

/-- Sudo and Chierchia disagree about which strategy Japanese exhibits:
    Chierchia's analysis assigns `.forNoun` (CLF atomizes a kind-denoting
    noun); Sudo's assigns `.sudoBlocking` (CLF blocks the silent ∪-operator
    on numerals). The disagreement is structural, not editorial.

    The two also disagree on the *empirical predictions* this generates
    under @cite{little-moroney-royer-2022}'s diagnostic battery — see
    `LittleMoroneyRoyer2022.predictionsOf` for the per-strategy profiles. -/
theorem sudo_disagrees_with_chierchia_on_japanese :
    japaneseStrategy ≠ Chierchia1998.japaneseStrategy := by decide

/-! ## §8: Framework-applicability

Sudo's blocking-principle account (eqs. 10/15/16) presupposes that the
target language has *obligatory overt classifiers in the lexicon* —
that is what blocks the silent ∪-operator. The general predicate
`Core.Typology.LanguageProfile.hasObligatoryClassifierSystem` is the
input-shape requirement; Sudo's framework applies iff a language
satisfies it. Languages where numerals combine with bare nouns
(no obligatory CL) do not provide the right input.

Defined at the `LanguageProfile` level (not paper-specific) so older
study files like `BaleKhanjian2014` can use it without violating the
chronology rule (study files cannot import newer study files). -/

/-- Sudo's framework applies to language `p` iff `p` has obligatory
    classifier morphology — the lexical input that Sudo's silent
    ∪-operator gets blocked by. Defined as a local alias for
    `LanguageProfile.hasObligatoryClassifierSystem` so the connection
    to Sudo's framework is greppable. -/
abbrev frameworkApplies (p : Core.Typology.LanguageProfile) : Prop :=
  p.hasObligatoryClassifierSystem

end Sudo2016
