import Linglib.Core.Mereology
import Linglib.Core.PrivativePair
import Linglib.Core.Number
import Linglib.Core.Person
import Linglib.Core.Semantics.Presupposition

/-!
# Presuppositional Semantics of Phi-Features
@cite{sauerland-2003} @cite{sauerland-2008b} @cite{harbour-2016} @cite{heim-1991} @cite{wang-r-2023}

Phi-features (number, person, definiteness) are **presuppositional partial
identity functions** on the entity domain, ordered by presuppositional
strength via `Core.PrivativePair.specLevel`.

The core mathematical object is `phiPresup`: a single function that maps
each `PrivativePair` cell to a `PrProp`, using two predicates (innerP,
outerP) corresponding to the inner and outer privative features. Since
the three well-formed cells have 2, 1, and 0 marked features respectively,
their presuppositions are automatically nested — more marked features =
stronger presupposition = smaller domain.

## Domains

| Domain       | innerP           | outerP                        | maximal (2) | intermediate (1) | minimal (0) |
|-------------|------------------|-------------------------------|-------------|-------------------|-------------|
| Number      | Atom             | MinimalGroup                  | singular    | dual              | plural      |
| Person      | speaker ≤ ·      | speaker ≤ · ∨ addressee ≤ ·   | 1st         | 2nd               | 3rd         |
| Definiteness| familiar/unique  | —                             | definite    | —                 | indefinite  |

## Semantic Markedness (@cite{wang-r-2023})

The semantically **unmarked** values (plural, 3rd person, indefinite) are
precisely those at the minimal cell (specLevel 0) with vacuous
presuppositions. These are the values recruited cross-linguistically for
honorification — an observation that falls out from the presuppositional
framework without stipulation.

## Architecture

This file was extracted from `Phenomena.Plurals.Studies.Sauerland2003` to
separate general phi-feature presuppositional theory (which belongs in
`Theories/`) from Sauerland's specific arguments about number (which
belong in `Phenomena/Plurals/Studies/`).
-/

set_option autoImplicit false

namespace Presupposition.PhiFeatures

open Mereology (Atom)
open Core (PrivativePair PhiFeatures)
open Core.Presupposition (PrProp)

-- ============================================================================
-- §1  Generic Presuppositional Denotations
-- ============================================================================

/-- Generic presuppositional denotation from a privative feature pair.

    Maps each `PrivativePair` cell to a `PrProp` using two predicates:
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
    PrivativePair → PrProp E
  | ⟨true, true⟩ => { presup := innerP, assertion := fun _ => True }
  | ⟨true, false⟩ => { presup := outerP, assertion := fun _ => True }
  | ⟨false, _⟩ => { presup := fun _ => True, assertion := fun _ => True }

/-- **Feature-Subset Principle, derived from privative geometry.**

    If innerP → outerP (the containment [+inner] → [+outer]), then
    more specified cells have smaller presuppositional domains. This
    is the semantic content of `PrivativePair.spec_strict_order` —
    not a stipulation but a consequence of the algebraic structure. -/
theorem phiPresup_nesting {E : Type*}
    {innerP outerP : E → Prop} (hContain : ∀ x, innerP x → outerP x)
    {c₁ c₂ : PrivativePair}
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true)
    (hSpec : c₁.specLevel ≥ c₂.specLevel) (x : E)
    (h : (phiPresup innerP outerP c₁).defined x) :
    (phiPresup innerP outerP c₂).defined x := by
  cases c₁ with | mk o₁ i₁ =>
  cases c₂ with | mk o₂ i₂ =>
  cases o₁ <;> cases i₁ <;> cases o₂ <;> cases i₂ <;>
    simp_all [PrivativePair.wellFormed, PrivativePair.specLevel, Bool.toNat,
              phiPresup, PrProp.defined]

/-- All `phiPresup` cells have the same (trivial) assertive content.
    This is the privative-geometric reason why φ-feature competition
    is presuppositional, not at-issue. -/
theorem phiPresup_same_assertion {E : Type*}
    (innerP outerP : E → Prop) (c₁ c₂ : PrivativePair) (x : E) :
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
def sgSem (E : Type*) [PartialOrder E] : PrProp E where
  presup := Atom
  assertion := fun _ => True

/-- ⟦Pl⟧: no inherent presupposition. The unrestricted identity function.
    Its distribution is constrained pragmatically by Maximize Presupposition,
    not by any semantic content. -/
def plSem (E : Type*) : PrProp E where
  presup := fun _ => True
  assertion := fun _ => True

/-- ⟦Du⟧: presupposes minimality (no proper non-atomic subpart).
    The intermediate cell (specLevel 1). -/
def dualSem {E : Type*} (minimalP : E → Prop) : PrProp E where
  presup := minimalP
  assertion := fun _ => True

-- ── Number denotations as `phiPresup` instances ─────

/-- `sgSem` is `phiPresup` at the maximal cell. -/
theorem sgSem_eq_phiPresup {E : Type*} [PartialOrder E]
    (outerP : E → Prop) :
    phiPresup Atom outerP .maximal = sgSem E := rfl

/-- `dualSem` is `phiPresup` at the intermediate cell. -/
theorem dualSem_eq_phiPresup {E : Type*} [PartialOrder E]
    (minimalP : E → Prop) :
    phiPresup (E := E) Atom minimalP .intermediate = dualSem minimalP := rfl

/-- `plSem` is `phiPresup` at the minimal cell. -/
theorem plSem_eq_phiPresup {E : Type*} (innerP outerP : E → Prop) :
    phiPresup innerP outerP .minimal = plSem E := rfl

-- ── Bridge to Core.Number ─────

/-- Singular features map to the maximal `PrivativePair` cell (specLevel 2). -/
theorem sg_is_maximal_cell :
    PhiFeatures.toPair Core.Number.singularF = .maximal := rfl

/-- Plural features map to the minimal cell (specLevel 0). -/
theorem pl_is_minimal_cell :
    PhiFeatures.toPair Core.Number.pluralF = .minimal := rfl

/-- The presuppositional asymmetry tracks specification level:
    singular (specLevel 2) has content; plural (specLevel 0) is vacuous. -/
theorem presup_strength_tracks_specLevel :
    PhiFeatures.specLevel Core.Number.singularF >
    PhiFeatures.specLevel Core.Number.pluralF := by decide

-- ============================================================================
-- §3  Person Presuppositions
-- ============================================================================

section PersonPresuppositions

variable {E : Type*} [PartialOrder E]

/-- ⟦1st⟧: presupposes the referent includes the speaker.
    Maximal cell [+author, +participant] (specLevel 2). -/
def firstSem (speaker : E) : PrProp E where
  presup := fun x => speaker ≤ x
  assertion := fun _ => True

/-- ⟦2nd⟧: presupposes the referent includes a speech-act participant.
    Intermediate cell [−author, +participant] (specLevel 1). -/
def secondSem (speaker addressee : E) : PrProp E where
  presup := fun x => speaker ≤ x ∨ addressee ≤ x
  assertion := fun _ => True

/-- ⟦3rd⟧: vacuous presupposition.
    Minimal cell [−author, −participant] (specLevel 0). -/
def thirdSem : PrProp E where
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
              .minimal = (thirdSem : PrProp E) := rfl

/-- Person nesting is a corollary of `phiPresup_nesting` — the same
    theorem that derives number nesting also derives person nesting,
    because both use the same `PrivativePair` structure. -/
theorem person_nesting_from_phi (speaker addressee : E)
    {c₁ c₂ : PrivativePair}
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true)
    (hSpec : c₁.specLevel ≥ c₂.specLevel) (x : E)
    (h : (phiPresup (fun x => speaker ≤ x)
                     (fun x => speaker ≤ x ∨ addressee ≤ x) c₁).defined x) :
    (phiPresup (fun x => speaker ≤ x)
               (fun x => speaker ≤ x ∨ addressee ≤ x) c₂).defined x :=
  phiPresup_nesting (fun _ h => Or.inl h) hw₁ hw₂ hSpec x h

/-- Person and number have the same `specLevel` ordering — this is the
    semantic content of @cite{harbour-2016}'s phi kernel isomorphism.
    Both are `phiPresup` instances over the same `PrivativePair` cells,
    so `phiPresup_nesting` applies to both: the nesting is structural,
    not a per-domain coincidence. -/
theorem person_number_isomorphism :
    PhiFeatures.specLevel Core.Person.first =
      PhiFeatures.specLevel Core.Number.singularF ∧
    PhiFeatures.specLevel Core.Person.second =
      PhiFeatures.specLevel Core.Number.dualF ∧
    PhiFeatures.specLevel Core.Person.third =
      PhiFeatures.specLevel Core.Number.pluralF :=
  ⟨rfl, rfl, rfl⟩

end PersonPresuppositions

-- ============================================================================
-- §4  Definiteness Presuppositions
-- ============================================================================

/-!
## §4: Definiteness as Presupposition

Definiteness exhibits the same presuppositional asymmetry as number and
person: definites carry a familiarity/uniqueness presupposition
(@cite{heim-1991}, @cite{strawson-1950}), while indefinites carry no
presupposition. Unlike number and person, definiteness is a binary
contrast (no intermediate cell), so we instantiate `phiPresup` at the
maximal and minimal cells only.

@cite{wang-r-2023} relies on this: indefinites are semantically unmarked
(vacuous presupposition), so they are recruited for honorification in
languages like Ainu.
-/

section DefinitePresuppositions

variable {E : Type*}

/-- ⟦DEF⟧: presupposes the referent satisfies a contextual familiarity
    or uniqueness condition. The predicate `familiar` is abstract —
    concretely it may be Heim's familiarity or Russell's uniqueness
    (cf. `Core.Definiteness.DefPresupType`). -/
def defSem (familiar : E → Prop) : PrProp E where
  presup := familiar
  assertion := fun _ => True

/-- ⟦INDEF⟧: no presupposition. Like `plSem` and `thirdSem`, its
    distribution is constrained pragmatically by Maximize Presupposition.
    Using an indefinite when a definite's presupposition is satisfied
    would violate MP!. -/
def indefSem : PrProp E where
  presup := fun _ => True
  assertion := fun _ => True

/-- `defSem` is `phiPresup` at the maximal cell (with outerP = familiar). -/
theorem defSem_eq_phiPresup (familiar : E → Prop) :
    phiPresup familiar familiar .maximal = defSem familiar := rfl

/-- `indefSem` is `phiPresup` at the minimal cell. -/
theorem indefSem_eq_phiPresup (innerP outerP : E → Prop) :
    phiPresup innerP outerP .minimal = (indefSem : PrProp E) := rfl

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
## §5: Semantic Markedness (@cite{wang-r-2023})

A phi-feature value is **semantically unmarked** iff its presupposition is
vacuous — i.e., it is at the minimal `PrivativePair` cell (specLevel 0).
Semantically unmarked values are compatible with a wider range of
contexts, making them available for pragmatic co-optation (honorification).

This definition is domain-general: it applies uniformly to number
(plural), person (3rd), and definiteness (indefinite).
-/

/-- A phi-feature value is semantically unmarked iff its specLevel is 0
    (vacuous presupposition). -/
def isSemanticUnmarked (c : PrivativePair) : Bool := c.specLevel == 0

/-- A phi-feature value is semantically marked iff its specLevel is > 0
    (substantive presupposition). -/
def isSemanticMarked (c : PrivativePair) : Bool := c.specLevel > 0

/-- The minimal cell is the unique unmarked cell. -/
theorem minimal_is_unmarked : isSemanticUnmarked .minimal = true := rfl

/-- The maximal cell is marked. -/
theorem maximal_is_marked : isSemanticMarked .maximal = true := rfl

/-- The intermediate cell is marked. -/
theorem intermediate_is_marked : isSemanticMarked .intermediate = true := rfl

/-- Only the minimal cell is unmarked among well-formed cells. -/
theorem unmarked_iff_minimal (c : PrivativePair) (hw : c.wellFormed = true) :
    isSemanticUnmarked c = true ↔ c = .minimal := by
  cases c with | mk o i =>
  cases o <;> cases i <;>
    simp_all [isSemanticUnmarked, PrivativePair.specLevel, Bool.toNat,
              PrivativePair.wellFormed, PrivativePair.minimal]

/-- Unmarked cells have vacuous presuppositions via `phiPresup`. -/
theorem unmarked_vacuous_presup {E : Type*} (innerP outerP : E → Prop)
    (c : PrivativePair) (hw : c.wellFormed = true)
    (hu : isSemanticUnmarked c = true) (x : E) :
    (phiPresup innerP outerP c).defined x := by
  have hmin := (unmarked_iff_minimal c hw).mp hu
  subst hmin; trivial

-- ============================================================================
-- §6  Presuppositional Strength
-- ============================================================================

/-- Well-formed cells have specLevel ≤ 2. This follows from the
    three-cell structure of `PrivativePair` — the maximum is
    `maximal.specLevel = 2`. -/
theorem wellFormed_specLevel_le_two (c : PrivativePair)
    (hw : c.wellFormed = true) : c.specLevel ≤ 2 := by
  cases c with | mk o i =>
  cases o <;> cases i <;>
    simp_all [PrivativePair.specLevel, Bool.toNat, PrivativePair.wellFormed]

/-- Presuppositional strength = specLevel. Higher specLevel = stronger
    presupposition = smaller domain. -/
def presupStrength (c : PrivativePair) : Nat := c.specLevel

/-- `c₁` has a weaker presupposition than `c₂`. -/
def presupWeakerThan (c₁ c₂ : PrivativePair) : Bool :=
  c₁.specLevel < c₂.specLevel

/-- `c₁` has a stronger presupposition than `c₂`. -/
def presupStrongerThan (c₁ c₂ : PrivativePair) : Bool :=
  c₁.specLevel > c₂.specLevel

/-- Minimal has the weakest presupposition among all cells. -/
theorem minimal_weakest (c : PrivativePair) (hw : c.wellFormed = true)
    (hne : c ≠ .minimal) :
    presupWeakerThan .minimal c = true := by
  cases c with | mk o i =>
  cases o <;> cases i <;>
    simp_all [presupWeakerThan, PrivativePair.specLevel, Bool.toNat,
              PrivativePair.wellFormed, PrivativePair.minimal]

/-- Maximal has the strongest presupposition among all cells. -/
theorem maximal_strongest (c : PrivativePair) (hw : c.wellFormed = true)
    (hne : c ≠ .maximal) :
    presupStrongerThan .maximal c = true := by
  cases c with | mk o i =>
  cases o <;> cases i <;>
    simp_all [presupStrongerThan, PrivativePair.specLevel, Bool.toNat,
              PrivativePair.wellFormed, PrivativePair.maximal]

end Presupposition.PhiFeatures
