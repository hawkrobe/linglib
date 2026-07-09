import Linglib.Features.Case.Basic
import Linglib.Data.UD.Basic
import Linglib.Features.Number.Capabilities
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Extraction

/-!
# K'iche' Agreement Fragment [mondloch-2017]

Theory-neutral typological metadata for K'iche' (K'ichean Mayan)
agreement morphology, following [mondloch-2017] Lessons 4, 7–8,
9, 15. K'iche' is uniformly ergative-absolutive (Set B = ABS, Set A
= ERG); unlike its sister Kaqchikel it has no construction-specific
inverted alignment.

## The System

K'iche' has an **ergative-absolutive** alignment system realized through
two agreement paradigms on the verb:

- **Set B** (ABS): absolutive markers that cross-reference the sole
  argument of intransitives (S) and the object of transitives (P).
  These appear between the aspect marker and the verb root.
- **Set A** (ERG): ergative markers that cross-reference the subject
  of transitives (A). These appear between the object marker and the
  root. Set A markers are identical to the possessive pronouns used
  before consonant-initial nouns (Lesson 7).

## Paradigms

### Set B (Absolutive) — Lesson 9

| Person | Singular | Plural |
|--------|----------|--------|
| 1      | in-      | oj-    |
| 2      | at-      | ix-    |
| 3      | Ø-       | ee-    |
| 2.FORM | la (postverbal) | alaq (postverbal) |

### Set A (Ergative, preconsonantal) — Lessons 7, 15

| Person | Singular | Plural |
|--------|----------|--------|
| 1      | nu‑ / in‑  | qa-    |
| 2      | a-       | i-     |
| 3      | u-       | ki-    |
| 2.FORM | la (postverbal) | alaq (postverbal) |

### Set A (Ergative, prevocalic) — Lesson 8

| Person | Singular | Plural |
|--------|----------|--------|
| 1      | w-       | q-     |
| 2      | aw-      | iw-    |
| 3      | r-       | k-     |
| 2.FORM | la (postverbal) | alaq (postverbal) |

## Alignment

The alignment is ergative-absolutive: Set B groups S and P together
(both trigger the same paradigm), while A triggers a distinct paradigm
(Set A). This contrasts with Mam, which shows morphologically
**tripartite** alignment (S, A, and P each trigger distinct patterns;
[scott-2023]).

## Formal address

K'iche' has two levels of formality for 2nd person: informal and
formal. The formal forms (laal SG, alaq PL) are syntactically
postverbal and do not participate in the prefix paradigm.
-/


namespace Kiche

-- ============================================================================
-- § 1: Person/Number/Formality Features
-- ============================================================================

/-- Formality level for 2nd person. K'iche'-specific: the formal
    forms (laal SG, alaq PL) are postverbal and pattern outside the
    prefix paradigm. -/
inductive Formality where
  | informal | formal
  deriving DecidableEq, Repr

/-- A person/number/formality specification. Uses canonical
    `Person` for cross-language compatibility;
    Formality is K'iche'-specific. -/
structure PhiFeatures where
  person : Person
  number : Number
  formality : Formality
  deriving DecidableEq, Repr

/-- A K'iche' φ-bundle bears its number slot (`HasNumber`). -/
instance : HasNumber PhiFeatures := ⟨fun φ => some φ.number⟩

instance : HasPerson PhiFeatures := ⟨fun φ => some φ.person⟩

/-- Shorthand for informal phi features. -/
abbrev phi (p : Person) (n : Number) : PhiFeatures :=
  ⟨p, n, .informal⟩

-- ============================================================================
-- § 2: Set B (Absolutive) Markers — Lesson 9
-- ============================================================================

/-- Set B (absolutive) agreement markers.
    These are verbal prefixes (or postverbal particles for formal forms)
    that cross-reference S (intransitive subject) and P (transitive
    object). [mondloch-2017] Lessons 9, 15. -/
def setBMarker : PhiFeatures → String
  | ⟨.first,  .singular, .informal⟩ => "in-"
  | ⟨.second, .singular, .informal⟩ => "at-"
  | ⟨.third,  .singular, .informal⟩ => "∅"
  | ⟨.first,  .plural, .informal⟩ => "oj-"
  | ⟨.second, .plural, .informal⟩ => "ix-"
  | ⟨.third,  .plural, .informal⟩ => "ee-"
  | ⟨.second, .singular, .formal⟩   => "la"
  | ⟨.second, .plural, .formal⟩   => "alaq"
  -- Non-binary number falls through to plural; formal non-2nd is Ø
  | ⟨.first,  _, .informal⟩ | ⟨.firstInclusive, _, .informal⟩
  | ⟨.firstExclusive, _, .informal⟩ => "oj-"
  | ⟨.zero, _, .informal⟩ => "∅"  -- no zero-person cell in the paradigm
  | ⟨.second, _, .informal⟩   => "ix-"
  | ⟨.third,  _, .informal⟩   => "ee-"
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 3: Set A (Ergative) Markers — Lessons 7, 15
-- ============================================================================

/-- Set A (ergative) markers before consonant-initial roots.
    These cross-reference A (transitive subject) and are identical to
    possessive pronouns before consonant-initial nouns.
    [mondloch-2017] Lessons 7, 15. -/
def setAPreC : PhiFeatures → String
  | ⟨.first,  .singular, .informal⟩ => "nu-/in-"
  | ⟨.second, .singular, .informal⟩ => "a-"
  | ⟨.third,  .singular, .informal⟩ => "u-"
  | ⟨.first,  .plural, .informal⟩ => "qa-"
  | ⟨.second, .plural, .informal⟩ => "i-"
  | ⟨.third,  .plural, .informal⟩ => "ki-"
  | ⟨.second, .singular, .formal⟩   => "la"
  | ⟨.second, .plural, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩ | ⟨.firstInclusive, _, .informal⟩
  | ⟨.firstExclusive, _, .informal⟩ => "qa-"
  | ⟨.zero, _, .informal⟩ => "∅"  -- no zero-person cell in the paradigm
  | ⟨.second, _, .informal⟩   => "i-"
  | ⟨.third,  _, .informal⟩   => "ki-"
  | ⟨_, _, .formal⟩            => "Ø"

/-- Set A (ergative) markers before vowel-initial roots.
    [mondloch-2017] Lesson 8. -/
def setAPreV : PhiFeatures → String
  | ⟨.first,  .singular, .informal⟩ => "w-"
  | ⟨.second, .singular, .informal⟩ => "aw-"
  | ⟨.third,  .singular, .informal⟩ => "r-"
  | ⟨.first,  .plural, .informal⟩ => "q-"
  | ⟨.second, .plural, .informal⟩ => "iw-"
  | ⟨.third,  .plural, .informal⟩ => "k-"
  | ⟨.second, .singular, .formal⟩   => "la"
  | ⟨.second, .plural, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩ | ⟨.firstInclusive, _, .informal⟩
  | ⟨.firstExclusive, _, .informal⟩ => "q-"
  | ⟨.zero, _, .informal⟩ => "∅"  -- no zero-person cell in the paradigm
  | ⟨.second, _, .informal⟩   => "iw-"
  | ⟨.third,  _, .informal⟩   => "k-"
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 4: Morphological Positions (Prop-valued)
-- ============================================================================

/-- Is a Set B marker a prefix (appearing before the root) or a
    postverbal particle? Formal forms are postverbal; all others
    are prefixes. [mondloch-2017] Lesson 9. -/
def SetBIsPrefix (φ : PhiFeatures) : Prop := φ.formality = .informal

instance (φ : PhiFeatures) : Decidable (SetBIsPrefix φ) :=
  inferInstanceAs (Decidable (φ.formality = .informal))

/-- Is a Set A marker a prefix or postverbal?
    Same distribution as Set B: formal forms are postverbal. -/
def SetAIsPrefix (φ : PhiFeatures) : Prop := φ.formality = .informal

instance (φ : PhiFeatures) : Decidable (SetAIsPrefix φ) :=
  inferInstanceAs (Decidable (φ.formality = .informal))

-- ============================================================================
-- § 5: Argument Positions and Alignment (substrate-anchored)
-- ============================================================================

/-- Argument positions in a K'iche' clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. Use the canonical
    constructor names `.A` / `.P` / `.S` directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Which agreement set cross-references each argument position? -/
inductive AgreementSet where
  | setA  -- Ergative markers
  | setB  -- Absolutive markers
  | none  -- No agreement (e.g., for ditransitive R/T not modeled here)
  deriving DecidableEq, Repr

/-- The agreement set triggered by each argument position.
    S and P both trigger Set B (= absolutive grouping).
    A triggers Set A (= ergative). Ditransitive R/T default to `.none`
    (not modeled in this fragment). -/
def ArgPosition.agreementSet : ArgPosition → AgreementSet
  | .A => .setA  -- A → Set A (ergative)
  | .P => .setB  -- P → Set B (absolutive)
  | .S => .setB  -- S → Set B (absolutive)
  | .R | .T => .none

/-- The case associated with each argument position. Definitionally
    equal to `Mayan.ergCaseKiche`, which derives from
    `Alignment.ergative.assignCase` in `Syntax/Case/Alignment.lean`. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseKiche

-- ============================================================================
-- § 6: Alignment Theorems
-- ============================================================================

/-- K'iche' groups S and P together (both trigger Set B):
    ergative-absolutive alignment. -/
theorem ergative_absolutive_alignment :
    ArgPosition.agreementSet .S = ArgPosition.agreementSet .P ∧
    ArgPosition.agreementSet .A ≠ ArgPosition.agreementSet .P :=
  ⟨rfl, by decide⟩

/-- A receives ERG while P and S share a case (ABS) — the ergative
    partition, re-exported from `Alignment.ergative_distinguishes_A`. -/
theorem erg_abs_pattern :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .P = ArgPosition.case .S :=
  Alignment.ergative_distinguishes_A

/-- K'iche' alignment contrast with Mam: K'iche' is ergative-absolutive
    (S = P ≠ A), while Mam is tripartite (S ≠ A ≠ P, all three
    receive distinct cases). In K'iche', both P and S trigger Set B;
    in Mam, P triggers no agreement at all. -/
theorem kiche_not_tripartite :
    ArgPosition.case .S = ArgPosition.case .P := rfl

-- ============================================================================
-- § 7: Set B Per-Cell Verification
-- ============================================================================

/-- 1SG absolutive: in- -/
theorem setB_1sg : setBMarker (phi .first .singular) = "in-" := rfl
/-- 2SG absolutive: at- -/
theorem setB_2sg : setBMarker (phi .second .singular) = "at-" := rfl
/-- 3SG absolutive: ∅ (null morpheme) -/
theorem setB_3sg : setBMarker (phi .third .singular) = "∅" := rfl
/-- 1PL absolutive: oj- -/
theorem setB_1pl : setBMarker (phi .first .plural) = "oj-" := rfl
/-- 2PL absolutive: ix- -/
theorem setB_2pl : setBMarker (phi .second .plural) = "ix-" := rfl
/-- 3PL absolutive: ee- -/
theorem setB_3pl : setBMarker (phi .third .plural) = "ee-" := rfl
/-- 2SG.FORM: la (postverbal) -/
theorem setB_2sg_form : setBMarker ⟨.second, .singular, .formal⟩ = "la" := rfl
/-- 2PL.FORM: alaq (postverbal) -/
theorem setB_2pl_form : setBMarker ⟨.second, .plural, .formal⟩ = "alaq" := rfl

-- ============================================================================
-- § 8: Set A Per-Cell Verification
-- ============================================================================

/-- 1SG ergative (preC): nu‑ or in‑ -/
theorem setA_1sg : setAPreC (phi .first .singular) = "nu-/in-" := rfl
/-- 2SG ergative (preC): a- -/
theorem setA_2sg : setAPreC (phi .second .singular) = "a-" := rfl
/-- 3SG ergative (preC): u- -/
theorem setA_3sg : setAPreC (phi .third .singular) = "u-" := rfl
/-- 1PL ergative (preC): qa- -/
theorem setA_1pl : setAPreC (phi .first .plural) = "qa-" := rfl
/-- 2PL ergative (preC): i- -/
theorem setA_2pl : setAPreC (phi .second .plural) = "i-" := rfl
/-- 3PL ergative (preC): ki- -/
theorem setA_3pl : setAPreC (phi .third .plural) = "ki-" := rfl

/-- 1SG ergative (preV): w- -/
theorem setA_preV_1sg : setAPreV (phi .first .singular) = "w-" := rfl
/-- 2SG ergative (preV): aw- -/
theorem setA_preV_2sg : setAPreV (phi .second .singular) = "aw-" := rfl
/-- 3SG ergative (preV): r- -/
theorem setA_preV_3sg : setAPreV (phi .third .singular) = "r-" := rfl

-- ============================================================================
-- § 9: Set A / Set B Identity (Possessives = Set A)
-- ============================================================================

/-- Set A markers are identical to possessive pronouns: the transitive
    subject markers (Lesson 15) are the same forms as the possessive
    prefixes (Lessons 7–8). This is a hallmark of ergative-absolutive
    languages, where ERG agreement and possession share the same
    morphological paradigm. [mondloch-2017] Lesson 15 explicitly
    notes this identity. -/
theorem possessives_equal_setA :
    setAPreC (phi .first .plural) = "qa-" ∧
    setAPreC (phi .second .singular) = "a-" ∧
    setAPreC (phi .third .singular) = "u-" ∧
    setAPreC (phi .third .plural) = "ki-" :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Formal Markers Are Postverbal
-- ============================================================================

/-- All informal Set B markers are prefixes. -/
theorem setB_informal_prefix :
    SetBIsPrefix (phi .first .singular) ∧
    SetBIsPrefix (phi .second .singular) ∧
    SetBIsPrefix (phi .third .singular) ∧
    SetBIsPrefix (phi .first .plural) ∧
    SetBIsPrefix (phi .second .plural) ∧
    SetBIsPrefix (phi .third .plural) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Formal Set B markers are NOT prefixes (they're postverbal). -/
theorem setB_formal_postverbal :
    ¬ SetBIsPrefix ⟨.second, .singular, .formal⟩ ∧
    ¬ SetBIsPrefix ⟨.second, .plural, .formal⟩ :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- § 11: Independent Pronouns — Lesson 4
-- ============================================================================

/-- Independent (free) personal pronouns. These are used in nonverbal
    sentences and as emphatic/contrastive pronouns in verbal sentences.
    [mondloch-2017] Lesson 4. -/
def independentPronoun : PhiFeatures → String
  | ⟨.first,  .singular, .informal⟩ => "in"
  | ⟨.second, .singular, .informal⟩ => "at"
  | ⟨.third,  .singular, .informal⟩ => "are'"
  | ⟨.first,  .plural, .informal⟩ => "oj"
  | ⟨.second, .plural, .informal⟩ => "ix"
  | ⟨.third,  .plural, .informal⟩ => "a're'"
  | ⟨.second, .singular, .formal⟩   => "laal"
  | ⟨.second, .plural, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩ | ⟨.firstInclusive, _, .informal⟩
  | ⟨.firstExclusive, _, .informal⟩ => "oj"
  | ⟨.zero, _, .informal⟩ => "∅"  -- no zero-person cell in the paradigm
  | ⟨.second, _, .informal⟩   => "ix"
  | ⟨.third,  _, .informal⟩   => "a're'"
  | ⟨_, _, .formal⟩            => "are'"

/-- Independent pronouns correspond to Set B (absolutive) markers in
    form: 1SG *in* = Set B *in-*, 2SG *at* = Set B *at-*, etc.
    This is expected for an ergative language where the independent
    pronouns pattern with absolutive agreement. -/
theorem pronoun_setB_correspondence :
    independentPronoun (phi .first .singular)  = "in"  ∧
    independentPronoun (phi .second .singular) = "at"  ∧
    independentPronoun (phi .first .plural)  = "oj"  ∧
    independentPronoun (phi .second .plural) = "ix"  :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: Cross-Mayan Canonical Wrappers
-- ============================================================================

open Mayan (MarkerLinearity ExponentTable)
open Agreement

/-- K'iche' is HIGH-ABS: Set B markers appear pre-stem on Infl. -/
def absPosition : Mayan.ABSPosition := .high

/-- Set A linearity: prefixal (per Mondloch Lessons 7-8). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B linearity: prefixal (HIGH-ABS K'ichean morphology). -/
def setBLinearity : MarkerLinearity := .prefixal

/-- Canonical Set A exponent table (pre-consonantal allomorph; informal),
    keyed on the canonical φ-cell `Agreement.Cell` for cross-Mayan consumption. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, setAPreC (phi .first  .singular)),
   (.pn .second .Sing, setAPreC (phi .second .singular)),
   (.pn .third .Sing, setAPreC (phi .third  .singular)),
   (.pn .first .Plur, setAPreC (phi .first  .plural)),
   (.pn .second .Plur, setAPreC (phi .second .plural)),
   (.pn .third .Plur, setAPreC (phi .third  .plural))]

/-- Canonical Set B exponent table (informal) keyed on the canonical φ-cell
    `Agreement.Cell`. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, setBMarker (phi .first  .singular)),
   (.pn .second .Sing, setBMarker (phi .second .singular)),
   (.pn .third .Sing, setBMarker (phi .third  .singular)),
   (.pn .first .Plur, setBMarker (phi .first  .plural)),
   (.pn .second .Plur, setBMarker (phi .second .plural)),
   (.pn .third .Plur, setBMarker (phi .third  .plural))]

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches per [kaufman-norman-1984] Table 8. **Not**
    pan-Mayan: see Mam exception via `MayanLang.isStandard`. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some "∅" := rfl

/-- K'iche''s extraction profile (language "K'iche'"): Agent-Focus
    Antipassive is productive ([mondloch-2017] Lesson 22, with parallel
    coverage at Lessons 30 + 33 for radical TV and perfect aspect). The
    voice marker is *-n* (shared morphologically with the Absolutive
    Antipassive of Lesson 21; the AF vs absolutive-antipassive alternation
    is *syntactic* — both arguments overt for AF, object suppressed for
    absolutive antipassive — not morphological). HIGH-ABS K'ichean,
    structurally analogous to Kaqchikel. Notes: AF (-n) for A-extraction;
    HIGH-ABS K'ichean (Mondloch 2017 Lesson 22). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

end Kiche
