import Linglib.Semantics.Mereology
import Linglib.Features.ContainmentPair
import Linglib.Features.Number.Decomposition
import Linglib.Features.Person.Decomposition
import Linglib.Features.Gender.Decomposition
import Linglib.Semantics.Presupposition.Basic

/-!
# Presuppositional Semantics of Phi-Features
[sauerland-2003] [sauerland-2008] [harbour-2016] [heim-1991] [wang-r-2023]

Phi-features (number, person, definiteness) are **presuppositional partial
identity functions** on the entity domain, ordered by presuppositional
strength via `Features.ContainmentPair.specLevel`.

The core mathematical object is `phiPresup`: a single function that maps
each `ContainmentPair` cell to a `PartialProp`, using two predicates (innerP,
outerP) corresponding to the inner and outer privative features. Since
the three well-formed cells have 2, 1, and 0 marked features respectively,
their presuppositions are automatically nested — more marked features =
stronger presupposition = smaller domain.

## Domains

| Domain       | innerP           | outerP                        | maximal (2) | intermediate (1) | minimal (0) |
|-------------|------------------|-------------------------------|-------------|-------------------|-------------|
| Number      | Atom             | MinimalGroup                  | singular    | dual              | plural      |
| Person      | speaker ≤ ·      | speaker ≤ · ∨ addressee ≤ ·   | 1st         | 2nd               | 3rd         |
| Gender      | isInanimate      | isFemale                      | neuter      | feminine          | masculine   |
| Definiteness| familiar/unique  | —                             | definite    | —                 | indefinite  |

## Semantic Markedness ([wang-r-2023])

The semantically **unmarked** values (plural, 3rd person, indefinite) are
precisely those at the minimal cell (specLevel 0) with vacuous
presuppositions. These are the values recruited cross-linguistically for
honorification — an observation that falls out from the presuppositional
framework without stipulation.

## Architecture

This file was extracted from `Sauerland2003` to
separate general phi-feature presuppositional theory (which belongs in
`Theories/`) from Sauerland's specific arguments about number (which
belong in `Studies/`).
-/

namespace Presupposition.PhiFeatures

open Mereology (Atom)
open Features (ContainmentPair ContainmentPairLike)
open Presupposition

-- ============================================================================
-- §1  Generic Presuppositional Denotations
-- ============================================================================

/-- Generic presuppositional denotation from a privative feature pair.

    Maps each `ContainmentPair` cell to a `PartialProp` using two predicates:
    `innerP` for [±inner] and `outerP` for [±outer].

    | Cell         | outer | inner | Presupposition |
    |--------------|-------|-------|----------------|
    | maximal      |   +   |   +   | innerP         |
    | intermediate |   +   |   −   | outerP         |
    | minimal      |   −   |   −   | vacuous        |

    Since [+inner] → [+outer] (privative containment), `innerP`
    implies `outerP`. So maximal's presupposition (innerP) is the
    strongest — no need to separately conjoin outerP. -/
def phiPresup {E : Type*} (innerP outerP : E → Prop) :
    ContainmentPair → PartialProp E
  | ⟨true, true⟩ => { presup := innerP, assertion := fun _ => True }
  | ⟨true, false⟩ => { presup := outerP, assertion := fun _ => True }
  | ⟨false, _⟩ => { presup := fun _ => True, assertion := fun _ => True }

/-- **Feature-Subset Principle, derived from privative geometry.**

    If innerP → outerP (the containment [+inner] → [+outer]), then
    more specified cells have smaller presuppositional domains. This
    is the semantic content of `ContainmentPair.spec_strict_order` —
    not a stipulation but a consequence of the algebraic structure. -/
theorem phiPresup_nesting {E : Type*}
    {innerP outerP : E → Prop} (hContain : ∀ x, innerP x → outerP x)
    {c₁ c₂ : ContainmentPair}
    (hw₁ : c₁.WellFormed) (hw₂ : c₂.WellFormed)
    (hSpec : c₁.specLevel ≥ c₂.specLevel) (x : E)
    (h : (phiPresup innerP outerP c₁).defined x) :
    (phiPresup innerP outerP c₂).defined x := by
  rcases ContainmentPair.classification c₁ hw₁ with rfl | rfl | rfl <;>
    rcases ContainmentPair.classification c₂ hw₂ with rfl | rfl | rfl <;>
      simp_all [ContainmentPair.maximal, ContainmentPair.intermediate,
        ContainmentPair.minimal, ContainmentPair.specLevel, Bool.toNat,
        phiPresup, PartialProp.defined]

/-- All `phiPresup` cells have the same (trivial) assertive content.
    This is the privative-geometric reason why φ-feature competition
    is presuppositional, not at-issue. -/
theorem phiPresup_same_assertion {E : Type*}
    (innerP outerP : E → Prop) (c₁ c₂ : ContainmentPair) (x : E) :
    (phiPresup innerP outerP c₁).assertion x ↔
    (phiPresup innerP outerP c₂).assertion x := by
  cases c₁ with | mk o₁ i₁ =>
  cases c₂ with | mk o₂ i₂ =>
  cases o₁ <;> cases i₁ <;> cases o₂ <;> cases i₂ <;> simp [phiPresup]

-- ============================================================================
-- §2  Number Presuppositions
-- ============================================================================

/-- ⟦Sg⟧: presupposes atomicity. The identity function restricted to
    atoms — defined only when the referent is an atom. -/
def sgSem (E : Type*) [PartialOrder E] : PartialProp E where
  presup := Atom
  assertion := fun _ => True

/-- ⟦Pl⟧: no inherent presupposition. The unrestricted identity function.
    Its distribution is constrained pragmatically by Maximize Presupposition,
    not by any semantic content. -/
def plSem (E : Type*) : PartialProp E where
  presup := fun _ => True
  assertion := fun _ => True

/-- ⟦Du⟧: presupposes minimality (no proper non-atomic subpart).
    The intermediate cell (specLevel 1). -/
def dualSem {E : Type*} (minimalP : E → Prop) : PartialProp E where
  presup := minimalP
  assertion := fun _ => True

-- ── Number denotations as `phiPresup` instances ─────

/-- `sgSem` is `phiPresup` at the maximal cell. -/
@[simp] theorem sgSem_eq_phiPresup {E : Type*} [PartialOrder E]
    (outerP : E → Prop) :
    phiPresup Atom outerP .maximal = sgSem E := rfl

/-- `dualSem` is `phiPresup` at the intermediate cell. -/
@[simp] theorem dualSem_eq_phiPresup {E : Type*} [PartialOrder E]
    (minimalP : E → Prop) :
    phiPresup (E := E) Atom minimalP .intermediate = dualSem minimalP := rfl

/-- `plSem` is `phiPresup` at the minimal cell. -/
@[simp] theorem plSem_eq_phiPresup {E : Type*} (innerP outerP : E → Prop) :
    phiPresup innerP outerP .minimal = plSem E := rfl

-- ── Bridge to Number ─────

/-- Singular features map to the maximal `ContainmentPair` cell (specLevel 2). -/
@[simp] theorem sg_is_maximal_cell :
    ContainmentPairLike.toPair Number.singularF = .maximal := rfl

/-- Plural features map to the minimal cell (specLevel 0). -/
@[simp] theorem pl_is_minimal_cell :
    ContainmentPairLike.toPair Number.pluralF = .minimal := rfl

/-- The presuppositional asymmetry tracks specification level:
    singular (specLevel 2) has content; plural (specLevel 0) is vacuous. -/
theorem presup_strength_tracks_specLevel :
    ContainmentPairLike.specLevel Number.singularF >
    ContainmentPairLike.specLevel Number.pluralF := by decide

-- ============================================================================
-- §3  Person Presuppositions
-- ============================================================================

section PersonPresuppositions

variable {E : Type*} [PartialOrder E]

/-- ⟦1st⟧: presupposes the referent includes the speaker.
    Maximal cell [+author, +participant] (specLevel 2). -/
def firstSem (speaker : E) : PartialProp E where
  presup := fun x => speaker ≤ x
  assertion := fun _ => True

/-- ⟦2nd⟧: presupposes the referent includes a speech-act participant.
    Intermediate cell [−author, +participant] (specLevel 1). -/
def secondSem (speaker addressee : E) : PartialProp E where
  presup := fun x => speaker ≤ x ∨ addressee ≤ x
  assertion := fun _ => True

/-- ⟦3rd⟧: vacuous presupposition.
    Minimal cell [−author, −participant] (specLevel 0). -/
def thirdSem : PartialProp E where
  presup := fun _ => True
  assertion := fun _ => True

/-- Person domain nesting: dom(1st) ⊆ dom(2nd) ⊆ dom(3rd). -/
theorem person_domain_nesting (speaker addressee : E) :
    (∀ x, (firstSem speaker).defined x →
          (secondSem speaker addressee).defined x) ∧
    (∀ x, (secondSem speaker addressee).defined x →
          (thirdSem (E := E)).defined x) :=
  ⟨fun _ h => Or.inl h, fun _ _ => trivial⟩

-- ── Person as `phiPresup` instances ─────

theorem firstSem_eq_phiPresup (speaker addressee : E) :
    phiPresup (fun x => speaker ≤ x)
              (fun x => speaker ≤ x ∨ addressee ≤ x)
              .maximal = firstSem speaker := rfl

theorem secondSem_eq_phiPresup (speaker addressee : E) :
    phiPresup (fun x => speaker ≤ x)
              (fun x => speaker ≤ x ∨ addressee ≤ x)
              .intermediate = secondSem speaker addressee := rfl

theorem thirdSem_eq_phiPresup (speaker addressee : E) :
    phiPresup (fun x => speaker ≤ x)
              (fun x => speaker ≤ x ∨ addressee ≤ x)
              .minimal = (thirdSem : PartialProp E) := rfl

/-- Person nesting is a corollary of `phiPresup_nesting` — the same
    theorem that derives number nesting also derives person nesting,
    because both use the same `ContainmentPair` structure. -/
theorem person_nesting_from_phi (speaker addressee : E)
    {c₁ c₂ : ContainmentPair}
    (hw₁ : c₁.WellFormed) (hw₂ : c₂.WellFormed)
    (hSpec : c₁.specLevel ≥ c₂.specLevel) (x : E)
    (h : (phiPresup (fun x => speaker ≤ x)
                     (fun x => speaker ≤ x ∨ addressee ≤ x) c₁).defined x) :
    (phiPresup (fun x => speaker ≤ x)
               (fun x => speaker ≤ x ∨ addressee ≤ x) c₂).defined x :=
  phiPresup_nesting (fun _ h => Or.inl h) hw₁ hw₂ hSpec x h

/-- Person and number have the same `specLevel` ordering — this is the
    semantic content of [harbour-2016]'s phi kernel isomorphism.
    Both are `phiPresup` instances over the same `ContainmentPair` cells,
    so `phiPresup_nesting` applies to both: the nesting is structural,
    not a per-domain coincidence. -/
theorem person_number_isomorphism :
    ContainmentPairLike.specLevel Person.firstF =
      ContainmentPairLike.specLevel Number.singularF ∧
    ContainmentPairLike.specLevel Person.secondF =
      ContainmentPairLike.specLevel Number.dualF ∧
    ContainmentPairLike.specLevel Person.thirdF =
      ContainmentPairLike.specLevel Number.pluralF :=
  ⟨rfl, rfl, rfl⟩

end PersonPresuppositions

-- ============================================================================
-- §3b  Gender Presuppositions
-- ============================================================================

/-!
## §3b: Gender Presuppositions ([sauerland-2008])

Gender features [±feminine, ±neuter] form a third `ContainmentPair` instance,
with containment [+neuter] → [+feminine] (see `Gender.Features`).

The presuppositional semantics mirrors number and person:
- **neuter** (maximal, specLevel 2): presupposes inanimate
- **feminine** (intermediate, specLevel 1): presupposes female
- **masculine** (minimal, specLevel 0): vacuous (default/unmarked)

**Idealization.** The neuter↦inanimate cell and the gender containment
geometry are far less established than the person/number columns —
German *das Mädchen* 'the girl' (neuter, animate, female) is the
standard counterexample. The established core is feminine presupposing
female with masculine unmarked ([sauerland-2008]).

[wang-r-2023]: masculine, as the semantically unmarked gender,
is available for honorific use cross-linguistically — paralleling the
use of plural (unmarked number) and 3rd person (unmarked person) for
politeness.
-/

section GenderPresuppositions

variable {E : Type*}

/-- ⟦Neut⟧: presupposes the referent is inanimate.
    Maximal cell [+feminine, +neuter] (specLevel 2). -/
def neutSem (isInanimate : E → Prop) : PartialProp E where
  presup := isInanimate
  assertion := fun _ => True

/-- ⟦Fem⟧: presupposes the referent is female.
    Intermediate cell [+feminine, −neuter] (specLevel 1). -/
def femSem (isFemale : E → Prop) : PartialProp E where
  presup := isFemale
  assertion := fun _ => True

/-- ⟦Masc⟧: vacuous presupposition.
    Minimal cell [−feminine, −neuter] (specLevel 0). -/
def mascSem : PartialProp E where
  presup := fun _ => True
  assertion := fun _ => True

-- ── Gender denotations as `phiPresup` instances ─────

/-- `neutSem` is `phiPresup` at the maximal cell. -/
@[simp] theorem neutSem_eq_phiPresup (isInanimate isFemale : E → Prop) :
    phiPresup isInanimate isFemale .maximal = neutSem isInanimate := rfl

/-- `femSem` is `phiPresup` at the intermediate cell. -/
@[simp] theorem femSem_eq_phiPresup (isInanimate isFemale : E → Prop) :
    phiPresup isInanimate isFemale .intermediate = femSem isFemale := rfl

/-- `mascSem` is `phiPresup` at the minimal cell. -/
@[simp] theorem mascSem_eq_phiPresup (innerP outerP : E → Prop) :
    phiPresup innerP outerP .minimal = (mascSem : PartialProp E) := rfl

-- ── Bridge to Features.Gender ─────

/-- Neuter features map to the maximal `ContainmentPair` cell (specLevel 2). -/
@[simp] theorem neut_is_maximal_cell :
    ContainmentPairLike.toPair Gender.neuterF = .maximal := rfl

/-- Feminine features map to the intermediate cell (specLevel 1). -/
@[simp] theorem fem_is_intermediate_cell :
    ContainmentPairLike.toPair Gender.feminineF = .intermediate := rfl

/-- Masculine features map to the minimal cell (specLevel 0). -/
@[simp] theorem masc_is_minimal_cell :
    ContainmentPairLike.toPair Gender.masculineF = .minimal := rfl

/-- Gender domain nesting: dom(Neut) ⊆ dom(Fem) ⊆ dom(Masc).
    Parallels number (sg ⊆ pl) and person (1st ⊆ 3rd). -/
theorem gender_domain_nesting (isInanimate isFemale : E → Prop)
    (hContain : ∀ x, isInanimate x → isFemale x) :
    (∀ x, (neutSem isInanimate).defined x →
          (femSem isFemale).defined x) ∧
    (∀ x, (femSem isFemale).defined x →
          (mascSem (E := E)).defined x) :=
  ⟨fun _ h => hContain _ h, fun _ _ => trivial⟩

/-- Gender nesting via `phiPresup_nesting` — structurally identical
    to person nesting and number nesting. -/
theorem gender_nesting_from_phi (isInanimate isFemale : E → Prop)
    (hContain : ∀ x, isInanimate x → isFemale x)
    {c₁ c₂ : ContainmentPair}
    (hw₁ : c₁.WellFormed) (hw₂ : c₂.WellFormed)
    (hSpec : c₁.specLevel ≥ c₂.specLevel) (x : E)
    (h : (phiPresup isInanimate isFemale c₁).defined x) :
    (phiPresup isInanimate isFemale c₂).defined x :=
  phiPresup_nesting hContain hw₁ hw₂ hSpec x h

/-- Gender, person, and number have the same `specLevel` ordering —
    all three domains share the phi kernel structure. -/
theorem gender_person_number_isomorphism :
    ContainmentPairLike.specLevel Gender.neuterF =
      ContainmentPairLike.specLevel Person.firstF ∧
    ContainmentPairLike.specLevel Gender.neuterF =
      ContainmentPairLike.specLevel Number.singularF ∧
    ContainmentPairLike.specLevel Gender.feminineF =
      ContainmentPairLike.specLevel Person.secondF ∧
    ContainmentPairLike.specLevel Gender.masculineF =
      ContainmentPairLike.specLevel Person.thirdF :=
  ⟨rfl, rfl, rfl, rfl⟩

end GenderPresuppositions

-- ============================================================================
-- §4  Definiteness Presuppositions
-- ============================================================================

/-!
## §4: Definiteness as Presupposition

Definiteness exhibits the same presuppositional asymmetry as number and
person: definites carry a familiarity/uniqueness presupposition
([heim-1991], [strawson-1950]), while indefinites carry no
presupposition. Unlike number and person, definiteness is a binary
contrast (no intermediate cell), so we instantiate `phiPresup` at the
maximal and minimal cells only.

[wang-r-2023] relies on this: indefinites are semantically unmarked
(vacuous presupposition), so they are recruited for honorification in
languages like Ainu.
-/

section DefinitePresuppositions

variable {E : Type*}

/-- ⟦DEF⟧: presupposes the referent satisfies a contextual familiarity
    or uniqueness condition. The predicate `familiar` is abstract —
    concretely it may be Heim's familiarity or Russell's uniqueness
    (cf. `Definiteness.DefPresupType`). -/
def defSem (familiar : E → Prop) : PartialProp E where
  presup := familiar
  assertion := fun _ => True

/-- ⟦INDEF⟧: no presupposition. Like `plSem` and `thirdSem`, its
    distribution is constrained pragmatically by Maximize Presupposition.
    Using an indefinite when a definite's presupposition is satisfied
    would violate MP!. -/
def indefSem : PartialProp E where
  presup := fun _ => True
  assertion := fun _ => True

/-- `defSem` is `phiPresup` at the maximal cell (with outerP = familiar). -/
@[simp] theorem defSem_eq_phiPresup (familiar : E → Prop) :
    phiPresup familiar familiar .maximal = defSem familiar := rfl

/-- `indefSem` is `phiPresup` at the minimal cell. -/
@[simp] theorem indefSem_eq_phiPresup (innerP outerP : E → Prop) :
    phiPresup innerP outerP .minimal = (indefSem : PartialProp E) := rfl

/-- Definiteness domain nesting: dom(DEF) ⊆ dom(INDEF). -/
theorem def_domain_subset_indef (familiar : E → Prop) (x : E) :
    (defSem familiar).defined x → (indefSem (E := E)).defined x :=
  fun _ => trivial

/-- The containment is strict: there exist unfamiliar entities in
    dom(INDEF) \ dom(DEF). -/
theorem def_strictly_stronger (familiar : E → Prop)
    (x : E) (hUnfamiliar : ¬familiar x) :
    (indefSem (E := E)).defined x ∧ ¬(defSem familiar).defined x :=
  ⟨trivial, hUnfamiliar⟩

end DefinitePresuppositions

-- ============================================================================
-- §5  Semantic Markedness
-- ============================================================================

/-!
## §5: Semantic Markedness ([wang-r-2023])

A phi-feature value is **semantically unmarked** iff its presupposition is
vacuous — i.e., it is at the minimal `ContainmentPair` cell (specLevel 0).
Semantically unmarked values are compatible with a wider range of
contexts, making them available for pragmatic co-optation (honorification).

This definition is domain-general: it applies uniformly to number
(plural), person (3rd), and definiteness (indefinite).
-/

/-- A phi-feature value is semantically unmarked iff its specLevel is 0
    (vacuous presupposition). -/
def isSemanticUnmarked (c : ContainmentPair) : Bool := c.specLevel == 0

/-- A phi-feature value is semantically marked iff its specLevel is > 0
    (substantive presupposition). -/
def isSemanticMarked (c : ContainmentPair) : Bool := c.specLevel > 0

/-- The minimal cell is the unique unmarked cell. -/
@[simp] theorem minimal_is_unmarked : isSemanticUnmarked .minimal = true := rfl

/-- The maximal cell is marked. -/
@[simp] theorem maximal_is_marked : isSemanticMarked .maximal = true := rfl

/-- The intermediate cell is marked. -/
@[simp] theorem intermediate_is_marked : isSemanticMarked .intermediate = true := rfl

/-- Only the minimal cell is unmarked among well-formed cells. -/
theorem unmarked_iff_minimal (c : ContainmentPair) (hw : c.WellFormed) :
    isSemanticUnmarked c = true ↔ c = .minimal := by
  rcases ContainmentPair.classification c hw with rfl | rfl | rfl <;> decide

/-- Unmarked cells have vacuous presuppositions via `phiPresup`. -/
theorem unmarked_vacuous_presup {E : Type*} (innerP outerP : E → Prop)
    (c : ContainmentPair) (hw : c.WellFormed)
    (hu : isSemanticUnmarked c = true) (x : E) :
    (phiPresup innerP outerP c).defined x := by
  have hmin := (unmarked_iff_minimal c hw).mp hu
  subst hmin; trivial

-- ============================================================================
-- §6  Presuppositional Strength
-- ============================================================================

/-- Well-formed cells have specLevel ≤ 2. This follows from the
    three-cell structure of `ContainmentPair` — the maximum is
    `maximal.specLevel = 2`. -/
theorem wellFormed_specLevel_le_two (c : ContainmentPair)
    (hw : c.WellFormed) : c.specLevel ≤ 2 := by
  rcases ContainmentPair.classification c hw with rfl | rfl | rfl <;> decide

/-- Presuppositional strength = specLevel. Higher specLevel = stronger
    presupposition = smaller domain. -/
def presupStrength (c : ContainmentPair) : Nat := c.specLevel

/-- `c₁` has a weaker presupposition than `c₂`. -/
def presupWeakerThan (c₁ c₂ : ContainmentPair) : Bool :=
  c₁.specLevel < c₂.specLevel

/-- `c₁` has a stronger presupposition than `c₂`. -/
def presupStrongerThan (c₁ c₂ : ContainmentPair) : Bool :=
  c₁.specLevel > c₂.specLevel

/-- Minimal has the weakest presupposition among all cells. -/
theorem minimal_weakest (c : ContainmentPair) (hw : c.WellFormed)
    (hne : c ≠ .minimal) :
    presupWeakerThan .minimal c = true := by
  rcases ContainmentPair.classification c hw with rfl | rfl | rfl <;>
    first | decide | exact absurd rfl hne

/-- Maximal has the strongest presupposition among all cells. -/
theorem maximal_strongest (c : ContainmentPair) (hw : c.WellFormed)
    (hne : c ≠ .maximal) :
    presupStrongerThan .maximal c = true := by
  rcases ContainmentPair.classification c hw with rfl | rfl | rfl <;>
    first | decide | exact absurd rfl hne

end Presupposition.PhiFeatures
