import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Basic
import Linglib.Semantics.Intensional.Rigidity
import Linglib.Core.Order.Comparison
import Linglib.Fragments.Japanese.Classifier
import Linglib.Studies.Aikhenvald2000
import Linglib.Studies.Chierchia1998

/-!
# Sudo (2016) — The Semantic Role of Classifiers in Japanese
[sudo-2016]

Yasutada Sudo. *The Baltic International Yearbook of Cognition, Logic and
Communication* 11. DOI: 10.4148/1944-3676.1108

## Central Claim

Sudo argues that what makes Japanese an *obligatory classifier language* is
not the semantics of nouns (contra [chierchia-1998], [krifka-2008],
[borer-2005], [rothstein-2010], [nemoto-2005], [li-2011])
but the semantics of numerals. His core proposal:

1. In *all* natural languages, numerals denote singular terms of type `n`
   (constant intensions `λw. n`, modeled here by `NumeralIntens.const`).
2. Languages are equipped with a phonologically silent ∪-operator
   (`Semantics.Classifier.upNum`) that lifts numerals from type `⟨s,n⟩` to
   predicates of type `⟨s,⟨e,t⟩⟩`.
3. Following [chierchia-1998]'s Blocking Principle, ∪ is *blocked* in
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

`NMP.japaneseStrategy = .forNoun` (CLF atomizes a kind-denoting
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
  [bale-khanjian-2008], [bale-khanjian-2014], [doetjes-2013]
  is left as a separate study file.
- The full presupposition-tracking ∪-Shifted FA / PM compositional rules
  (Sudo eqs. 11/19/26) are referenced via the type-shift signatures in
  the composition section below; their full domain-of-definition
  machinery is not implemented here.
-/

/-!
## Classifier denotations (Sudo eq. 4)
[sudo-2016]

A classifier denotation in Sudo's framework: at each world `w`, the classifier
takes a numeral `n` and an entity `x`, presupposes a sortal predicate `P_w(x)`,
and asserts that `x` is the join of `n` atomic `P`-parts.

Concretely, Sudo (2016, eq. 4):
  ⟦-rin⟧ = λw. λn. λx : *flower_w(x). |{y ⊑ x : flower_w(y)}| = n

This contrasts with the Chierchia / Little-Moroney-Royer framework in
`Semantics/Classifier.lean`, where the classifier is a *noun-side*
predicate transformer `(E → Prop) → (E → Prop)` that atomizes the noun
denotation without reference to a numeral. The two views are different
theoretical commitments.

## Key types

- `ClassifierDenot W E` — sortal + counting predicates (intensional)
- `ClassifierDenot.apply` — Sudo's body: `sortal_w(x) ∧ |{y ≤ x : counted_w(y)}| = n`
- `ClassifierDenot.ofSortal` — atomic-sortal constructor (the common case)

## Out of scope

Non-atomic classifiers like `-kumi` (pair) and `-daasu` (dozen) per Sudo
(9a/b) require explicit mereological joins of disjoint pairs and are not
expressible via `ofSortal`. A separate constructor will be added when the
non-atomic case is needed.
-/

namespace Semantics.Classifier

universe u v

/-- A Sudo-style classifier denotation: at each world, a sortal presupposition
    plus a predicate whose ⊑-atomic parts of `x` are counted.

    For atomic-sortal classifiers (the common case: `-rin`, `-hiki`, `-nin`,
    `-mai`, `-hon`, `-ko`, `-tou`), `sortal = counted`. For mensural
    classifiers like `-hai` (cupful), the relationship is more nuanced and
    handled by separate constructors. -/
structure ClassifierDenot (W : Type u) (E : Type v) [PartialOrder E] where
  /-- The sortal presupposition. ⟦-rin⟧ presupposes `flower`; ⟦-nin⟧
      presupposes `human`; ⟦-hiki⟧ presupposes `animal ∧ small`. -/
  sortal : Intensional.Intension W (E → Prop)
  /-- The countable base whose atomic ⊑-parts of `x` are counted.
      For atomic-sortal classifiers, `counted = sortal` (see `ofSortal`). -/
  counted : Intensional.Intension W (E → Prop)

/-- The atom-count measure: the number of ⊑-atomic `P`-parts of `x` in world
    `w`. Noncomputable (`Set.ncard`); this is the `μ` over which classifier
    counting is ordinary numeral comparison (`Comparison.eq.over`), and the same
    set the Sudo ∪/∩ operators (`upNum`/`downNum`) count. -/
noncomputable def atomCount {W : Type u} {E : Type v} [PartialOrder E]
    (P : Intensional.Intension W (E → Prop)) (w : W) (x : E) : ℕ :=
  {y : E | y ≤ x ∧ P w y}.ncard

namespace ClassifierDenot

variable {W : Type u} {E : Type v} [PartialOrder E]

/-- Construct an atomic-sortal classifier from a single predicate.
    The sortal and the counting base coincide — the standard case in
    Sudo (4) for `-rin`, (8a) for `-nin`, (8b) for `-hiki` (with the
    sortal being a conjunction `small ∧ animal`). -/
def ofSortal (P : Intensional.Intension W (E → Prop)) : ClassifierDenot W E where
  sortal := P
  counted := P

/-- The body of Sudo's denotation (eq. 4): `apply cl w n x` iff `sortal_w(x)`
    AND the count of `x`'s ⊑-atomic `counted`-parts equals `n`.

    The counting clause is the **exact (`=`) case of the shared
    comparison-over-a-measure primitive** `Core.Order.Comparison.over`, with the
    measure being the atom-count `λx. |{y ⊑ x : counted_w(y)}|` — classifier
    counting *is* numeral comparison with `μ = atom-count`, the same primitive
    measure phrases and bare cardinals use. (`Set.ncard` returns 0 on infinite
    sets; for natural-language counting the relevant sets are finite.) -/
def apply (cl : ClassifierDenot W E) (w : W) (n : ℕ) (x : E) : Prop :=
  cl.sortal w x ∧ x ∈ Core.Order.Comparison.eq.over (atomCount cl.counted w) n

@[simp] lemma ofSortal_sortal (P : Intensional.Intension W (E → Prop)) :
    (ofSortal P).sortal = P := rfl

@[simp] lemma ofSortal_counted (P : Intensional.Intension W (E → Prop)) :
    (ofSortal P).counted = P := rfl

/-- For atomic-sortal classifiers, the body reduces to the join of the
    sortal presupposition and the cardinality constraint over `P`. -/
lemma apply_ofSortal (P : Intensional.Intension W (E → Prop)) (w : W) (n : ℕ) (x : E) :
    apply (ofSortal P) w n x ↔
      P w x ∧ {y : E | y ≤ x ∧ P w y}.ncard = n := Iff.rfl

end ClassifierDenot

end Semantics.Classifier

/-!
## Numerals as type-n singular terms
[sudo-2016]

Sudo's central typed-semantic claim: in *all* natural languages, numerals
denote singular terms of type `n` (an abstract numerical type). They are
constant intensions `λw_s. n` (Sudo eq. 2):

  ⟦roku⟧ = ⟦six⟧ = λw_s. 6

In English (and other non-classifier languages), numerals can also be
type-shifted to predicates/modifiers via a phonologically silent
∪-operator (Sudo eq. 10). In Japanese (and other obligatory-classifier
languages), the ∪-operator is *blocked* by the lexical presence of
classifiers (Chierchia 1998's Blocking Principle); numerals must combine
with a classifier to acquire a predicative type.

The inverse ∩-operator maps certain properties back to type-n constants
(Sudo eq. 24). Unlike ∪, ∩ has no overt counterpart in English or
Japanese — it is freely available as a covert type-shift in both.

## Architecture

`NumeralIntens W` is `Intension W ℕ` — a constant intension at a numeral
value is a "type-n singular term" in Sudo's sense. The ∪/∩ operators
specialized to numerals are defined in `Composition.lean`, where they
combine with the classifier denotations from `Defs.lean`.

This file deliberately avoids committing to whether type `n` is "the
naturals" `ℕ`, "the integers" `ℤ`, "abstract amounts" (Scontras 2014),
or "kinds whose extension is a fixed cardinal" — Sudo's empirical
arguments are agnostic about the deep ontology. We use `ℕ` for
formalization convenience.
-/

namespace Semantics.Classifier

universe u

/-- A numeral intension: a function from worlds to natural-number meanings.
    [sudo-2016] (eq. 2) ⟦six⟧ = λw_s. 6 is a `NumeralIntens W` for any
    world type `W`. -/
abbrev NumeralIntens (W : Type u) := Intensional.Intension W ℕ

/-- The rigid numeral intension: a numeral `n` denotes the constant function
    `λw. n`. This is `Intension.rigid` specialized to `ℕ`. -/
def NumeralIntens.const {W : Type u} (n : ℕ) : NumeralIntens W :=
  Intensional.Intension.rigid n

@[simp] lemma NumeralIntens.const_apply {W : Type u} (n : ℕ) (w : W) :
    NumeralIntens.const n w = n := rfl

/-- Every constant numeral intension is rigid. Sudo's empirical claim that
    numerals do not vary across worlds is the rigidity of `NumeralIntens.const`. -/
theorem NumeralIntens.const_isRigid {W : Type u} (n : ℕ) :
    Intensional.Intension.IsRigid (NumeralIntens.const (W := W) n) :=
  Intensional.Intension.rigid_isRigid n

end Semantics.Classifier

/-!
## Composition rules: type-shifters and blocking
[sudo-2016] [chierchia-1998]

The compositional apparatus that allows numerals (type `⟨s,n⟩`) and
classifier-modified numeral phrases (type `⟨s,⟨e,t⟩⟩` after classifier
application) to combine with noun denotations.

## Sudo's Three Type-Shifters

- **∪-operator** (Sudo eq. 10): `∪(λw. n) = λw. λx. |{y ⊑ x : atomic_w(y)}| = n`.
  Lifts a numeral intension `⟨s,n⟩` to a predicate `⟨s,⟨e,t⟩⟩` over entities
  with exactly `n` atomic parts.
- **∩-operator** (Sudo eq. 24): the partial inverse of ∪. Maps certain
  properties back to numeral intensions.
- The composition rules **∪-Shifted PM** (eq. 11), **∪-Shifted FA v1/v2**
  (eqs. 19a, 19b, 26a, 26b), and **∩-Shifted FA** (eq. 26c) lift Heim &
  Kratzer's standard FA / PM by inserting ∪/∩ at type mismatches.

## The Blocking Principle (Chierchia 1998, applied by Sudo 2016 §2.3)

The crucial cross-linguistic asymmetry is that Sudo's ∪-operator is
**blocked in Japanese** by the presence of overt classifiers in the
lexicon — but **available in English**, where there is no equivalent
overt operator. This is Chierchia (1998)'s Blocking Principle applied
to a phonologically silent type-shifter on numerals.

We formalize blocking as an `UpAvailability` enum derived from whether
the language has classifiers in its lexicon. The downstream consequence —
that predicative numerals like *"The guests are twelve"* (English ✓) vs
*"okyakusan-wa juu-ni-da"* (Japanese ✗, Sudo eq. 15) — is then a
corollary, not a stipulation.

## Scope

This file defines the type signatures and the blocking machinery.
The presupposition-tracking compositional rules (PM/FA with full
domain-of-definition checking per Sudo eqs. 11/19/26) are out of scope
for the first pass; they require partial-function plumbing that is
peripheral to the cross-paper argument the file is meant to enable.
-/

namespace Semantics.Classifier

universe u v

variable {W : Type u} {E : Type v} [PartialOrder E]

/-- Sudo's ∪-operator on numeral intensions (eq. 10):
    `∪(n)(w)(x)` iff `x` has exactly `n w` atomic ⊑-parts according to
    the contextually-supplied atomicity predicate `atomic`.

    In the type-theoretic semantics literature this is a type shift
    `⟨s,n⟩ → ⟨s,⟨e,t⟩⟩`. -/
def upNum (atomic : Intensional.Intension W (E → Prop)) (n : NumeralIntens W) :
    Intensional.Intension W (E → Prop) :=
  fun w x => atomCount atomic w x = n w

@[simp] lemma upNum_apply (atomic : Intensional.Intension W (E → Prop))
    (n : NumeralIntens W) (w : W) (x : E) :
    upNum atomic n w x ↔ {y : E | y ≤ x ∧ atomic w y}.ncard = n w := Iff.rfl

/-- Sudo's ∩-operator (eq. 24): a partial inverse of `upNum`.
    `downNum P w` returns the cardinality of atomic `P`-parts of any element of
    `P w`, packaged as a `Option ℕ` to model partiality (Sudo notes ∩ is only
    defined for "certain properties").

    This is a placeholder signature; a fuller treatment would parameterize
    over a uniqueness-of-cardinality witness and would establish ∪ ∘ ∩ = id
    on the property image of ∪. Marked `noncomputable` because the inverse
    of an arbitrary intensional property is not constructively decidable. -/
noncomputable def downNum (atomic P : Intensional.Intension W (E → Prop)) (w : W) :
    Option ℕ :=
  open Classical in
  if h : ∃ x, P w x then
    some (atomCount atomic w h.choose)
  else none

/-- Whether the silent ∪-shift on numerals is available in a language.

    Sudo (2016, §2.3) follows Chierchia (1998)'s Blocking Principle: a
    silent operator is blocked when there are overt lexical items playing
    the same role. In Japanese, the classifiers `-rin`/`-hiki`/`-nin`/...
    play the role ∪ would play (turning numerals into predicates), so ∪
    is blocked. In English, no such overt items exist, so ∪ is available. -/
inductive UpAvailability where
  /-- No overt classifier blocks the silent ∪-operator (English-like). -/
  | available
  /-- An overt classifier in the lexicon blocks ∪ (Japanese-like). -/
  | blocked
  deriving DecidableEq, Repr

/-- Derivation of `UpAvailability` from lexicon facts:
    ∪ is available iff the language has no classifiers in its lexicon.

    This is *not* a stipulation about which languages allow predicative
    numerals — it is a derivation of that fact from the deeper Blocking
    Principle. Whether a particular language has classifiers is a fragment-
    level fact (`Fragments.{Lang}.Classifiers.allClassifiers`); whether
    predicative numerals are licit is a downstream consequence. -/
def upAvailability (hasOvertClassifiers : Bool) : UpAvailability :=
  if hasOvertClassifiers then .blocked else .available

@[simp] lemma upAvailability_true :
    upAvailability true = .blocked := rfl

@[simp] lemma upAvailability_false :
    upAvailability false = .available := rfl

/-- A language with overt classifiers blocks the silent ∪-shift.
    The empirical content (Sudo eq. 15: *"okyakusan-wa juu-ni-da"* in
    Japanese) is a downstream consequence of this. -/
theorem classifiers_block_up :
    upAvailability true = .blocked := rfl

/-- A language without overt classifiers leaves the silent ∪-shift available.
    The empirical content (Sudo eq. 13: *"The number of guests is twelve"*
    in English) follows. -/
theorem no_classifiers_leave_up_available :
    upAvailability false = .available := rfl

end Semantics.Classifier

namespace Sudo2016

open Semantics.Classifier
open Intensional.Intension (rigid)

universe u

/-! ## §1: Toy Domain

A minimal world type and entity domain sufficient to instantiate Sudo's
sortal classifiers. The domain is intentionally small — Sudo's argument is
type-theoretic, not data-driven. -/

/-- The toy world type. Sudo's intensional analysis is parameterized over
    worlds; for the purposes of demonstrating type-shifts, a singleton
    world suffices. Real applications would parameterize over a richer
    `World` type from `Intensional.Defs`. -/
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
def flowerIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .hana)

/-- `human(x)`: sortal for `-nin` (Sudo eq. 8a). -/
def humanIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .hanako)

/-- `small_animal(x)`: sortal for `-hiki` (Sudo eq. 8b's atomic-sortal core). -/
def smallAnimalIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .inu)

/-- `bound_volume(x)`: sortal for `-satsu`. -/
def bookIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .hon)

/-- `round(x)`: sortal for `-ko`. -/
def roundIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .ringo)

/-- `flat(x)`: sortal for `-mai`. -/
def flatIntens : Intensional.Intension World (Entity → Prop) :=
  Intensional.Intension.rigid (· = .kami)

/-! ## §3: Per-Classifier Denotations

The exhaustive map from `Japanese.Classifier` to `ClassifierDenot`.
Pattern matching on the typed inventory forces every classifier to either
get a denotation or an explicit `none` for the deferred cases (mensural
`-hai`/`-shoku`/`-teki`, non-atomic `-kumi`/`-daasu`, function-based
classifiers without a sortal predicate over our toy domain). Adding a
classifier to the fragment requires extending this match — the type checker
catches missing cases, replacing the prior floating-`def` style. -/

/-- Atomic-sortal denotation builder for the six classifiers Sudo formalizes
    over our toy domain. `none` for classifiers we haven't formalized
    (most function-based ones, mensural ones, non-atomic group ones). -/
def japaneseSudoDenot : Japanese.Classifier →
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
def sudoFormalized : List Japanese.Classifier :=
  Japanese.Classifier.all.filter
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
  !Japanese.Classifier.all.isEmpty

/-! ## §5: The Blocking Argument (Sudo §3)

Sudo eq. 15 (*kyoo-no okyakusan-wa juu-ni-da, intended: 'the guests today
are twelve'): a predicative numeral is ungrammatical in Japanese, despite
being grammatical in English (Rothstein 2013). Sudo derives this from
[chierchia-1998]'s Blocking Principle: the silent ∪-operator that
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
`System`). Sudo's view is now a first-class constructor
of `ClassifierStrategy` (`.sudoBlocking`), so the disagreement with
[chierchia-1998] reduces to a single decidable inequality. -/

/-- Sudo's strategy assignment for Japanese: classifier blocks the silent
    ∪-operator on numerals (Sudo §3, eqs. 15–16). -/
def japaneseStrategy : NounCategorization.ClassifierStrategy := .sudoBlocking

/-- Sudo and Chierchia disagree about which strategy Japanese exhibits:
    Chierchia's analysis assigns `.forNoun` (CLF atomizes a kind-denoting
    noun); Sudo's assigns `.sudoBlocking` (CLF blocks the silent ∪-operator
    on numerals). The disagreement is structural, not editorial.

    The two also disagree on the *empirical predictions* this generates
    under [little-moroney-royer-2022]'s diagnostic battery — see
    `LittleMoroneyRoyer2022.predictionsOf` for the per-strategy profiles. -/
theorem sudo_disagrees_with_chierchia_on_japanese :
    japaneseStrategy ≠ NMP.japaneseStrategy := by decide

/-! ## §8: Framework-applicability

Sudo's blocking-principle account (eqs. 10/15/16) presupposes that the
target language has *obligatory overt classifiers in the lexicon* —
that is what blocks the silent ∪-operator.
`System.IsObligatory` is the input-shape requirement;
Sudo's framework applies iff it holds. Languages where numerals combine
with bare nouns (no obligatory CL) do not provide the right input. -/

/-- Sudo's framework applies to a language with classifier system `cs`
    iff `cs.IsObligatory` — the lexical input that Sudo's silent
    ∪-operator gets blocked by. -/
abbrev frameworkApplies (cs : NounCategorization.System) : Prop :=
  cs.IsObligatory

end Sudo2016
