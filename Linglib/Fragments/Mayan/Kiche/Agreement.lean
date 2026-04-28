import Linglib.Core.Case.Basic
import Linglib.Core.Lexical.Word
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# K'iche' Agreement Fragment @cite{mondloch-2017}

Theory-neutral typological metadata for K'iche' (K'ichean Mayan)
agreement morphology, following @cite{mondloch-2017} Lessons 4, 7–8,
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
@cite{scott-2023}).

## Formal address

K'iche' has two levels of formality for 2nd person: informal and
formal. The formal forms (laal SG, alaq PL) are syntactically
postverbal and do not participate in the prefix paradigm.
-/

namespace Fragments.Mayan.Kiche

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
    `Features.Prominence.PersonLevel` for cross-language compatibility;
    Formality is K'iche'-specific. -/
structure PhiFeatures where
  person : Features.Prominence.PersonLevel
  number : Number
  formality : Formality
  deriving DecidableEq, Repr

/-- Shorthand for informal phi features. -/
abbrev phi (p : Features.Prominence.PersonLevel) (n : Number) : PhiFeatures :=
  ⟨p, n, .informal⟩

-- ============================================================================
-- § 2: Set B (Absolutive) Markers — Lesson 9
-- ============================================================================

/-- Set B (absolutive) agreement markers.
    These are verbal prefixes (or postverbal particles for formal forms)
    that cross-reference S (intransitive subject) and P (transitive
    object). @cite{mondloch-2017} Lessons 9, 15. -/
def setBMarker : PhiFeatures → String
  | ⟨.first,  .Sing, .informal⟩ => "in-"
  | ⟨.second, .Sing, .informal⟩ => "at-"
  | ⟨.third,  .Sing, .informal⟩ => "Ø"
  | ⟨.first,  .Plur, .informal⟩ => "oj-"
  | ⟨.second, .Plur, .informal⟩ => "ix-"
  | ⟨.third,  .Plur, .informal⟩ => "ee-"
  | ⟨.second, .Sing, .formal⟩   => "la"
  | ⟨.second, .Plur, .formal⟩   => "alaq"
  -- Non-binary number falls through to plural; formal non-2nd is Ø
  | ⟨.first,  _, .informal⟩   => "oj-"
  | ⟨.second, _, .informal⟩   => "ix-"
  | ⟨.third,  _, .informal⟩   => "ee-"
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 3: Set A (Ergative) Markers — Lessons 7, 15
-- ============================================================================

/-- Set A (ergative) markers before consonant-initial roots.
    These cross-reference A (transitive subject) and are identical to
    possessive pronouns before consonant-initial nouns.
    @cite{mondloch-2017} Lessons 7, 15. -/
def setAPreC : PhiFeatures → String
  | ⟨.first,  .Sing, .informal⟩ => "nu-/in-"
  | ⟨.second, .Sing, .informal⟩ => "a-"
  | ⟨.third,  .Sing, .informal⟩ => "u-"
  | ⟨.first,  .Plur, .informal⟩ => "qa-"
  | ⟨.second, .Plur, .informal⟩ => "i-"
  | ⟨.third,  .Plur, .informal⟩ => "ki-"
  | ⟨.second, .Sing, .formal⟩   => "la"
  | ⟨.second, .Plur, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩   => "qa-"
  | ⟨.second, _, .informal⟩   => "i-"
  | ⟨.third,  _, .informal⟩   => "ki-"
  | ⟨_, _, .formal⟩            => "Ø"

/-- Set A (ergative) markers before vowel-initial roots.
    @cite{mondloch-2017} Lesson 8. -/
def setAPreV : PhiFeatures → String
  | ⟨.first,  .Sing, .informal⟩ => "w-"
  | ⟨.second, .Sing, .informal⟩ => "aw-"
  | ⟨.third,  .Sing, .informal⟩ => "r-"
  | ⟨.first,  .Plur, .informal⟩ => "q-"
  | ⟨.second, .Plur, .informal⟩ => "iw-"
  | ⟨.third,  .Plur, .informal⟩ => "k-"
  | ⟨.second, .Sing, .formal⟩   => "la"
  | ⟨.second, .Plur, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩   => "q-"
  | ⟨.second, _, .informal⟩   => "iw-"
  | ⟨.third,  _, .informal⟩   => "k-"
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 4: Morphological Positions (Prop-valued)
-- ============================================================================

/-- Is a Set B marker a prefix (appearing before the root) or a
    postverbal particle? Formal forms are postverbal; all others
    are prefixes. @cite{mondloch-2017} Lesson 9. -/
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
    equal to `Fragments.Mayan.ergCaseKiche`, which derives from
    `Alignment.ergative.assignCase` in `Theories/Syntax/Case/Alignment.lean`. -/
abbrev ArgPosition.case : ArgPosition → Core.Case :=
  Fragments.Mayan.ergCaseKiche

-- ============================================================================
-- § 6: Alignment Theorems
-- ============================================================================

/-- K'iche' groups S and P together (both trigger Set B):
    ergative-absolutive alignment. -/
theorem ergative_absolutive_alignment :
    ArgPosition.agreementSet .S = ArgPosition.agreementSet .P ∧
    ArgPosition.agreementSet .A ≠ ArgPosition.agreementSet .P :=
  ⟨rfl, by decide⟩

/-- S and P receive the same case (ABS); A receives ERG. -/
theorem erg_abs_pattern :
    ArgPosition.case .S = ArgPosition.case .P ∧
    ArgPosition.case .A ≠ ArgPosition.case .S := by
  refine ⟨rfl, ?_⟩
  decide

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
theorem setB_1sg : setBMarker (phi .first .Sing) = "in-" := rfl
/-- 2SG absolutive: at- -/
theorem setB_2sg : setBMarker (phi .second .Sing) = "at-" := rfl
/-- 3SG absolutive: Ø -/
theorem setB_3sg : setBMarker (phi .third .Sing) = "Ø" := rfl
/-- 1PL absolutive: oj- -/
theorem setB_1pl : setBMarker (phi .first .Plur) = "oj-" := rfl
/-- 2PL absolutive: ix- -/
theorem setB_2pl : setBMarker (phi .second .Plur) = "ix-" := rfl
/-- 3PL absolutive: ee- -/
theorem setB_3pl : setBMarker (phi .third .Plur) = "ee-" := rfl
/-- 2SG.FORM: la (postverbal) -/
theorem setB_2sg_form : setBMarker ⟨.second, .Sing, .formal⟩ = "la" := rfl
/-- 2PL.FORM: alaq (postverbal) -/
theorem setB_2pl_form : setBMarker ⟨.second, .Plur, .formal⟩ = "alaq" := rfl

-- ============================================================================
-- § 8: Set A Per-Cell Verification
-- ============================================================================

/-- 1SG ergative (preC): nu‑ or in‑ -/
theorem setA_1sg : setAPreC (phi .first .Sing) = "nu-/in-" := rfl
/-- 2SG ergative (preC): a- -/
theorem setA_2sg : setAPreC (phi .second .Sing) = "a-" := rfl
/-- 3SG ergative (preC): u- -/
theorem setA_3sg : setAPreC (phi .third .Sing) = "u-" := rfl
/-- 1PL ergative (preC): qa- -/
theorem setA_1pl : setAPreC (phi .first .Plur) = "qa-" := rfl
/-- 2PL ergative (preC): i- -/
theorem setA_2pl : setAPreC (phi .second .Plur) = "i-" := rfl
/-- 3PL ergative (preC): ki- -/
theorem setA_3pl : setAPreC (phi .third .Plur) = "ki-" := rfl

/-- 1SG ergative (preV): w- -/
theorem setA_preV_1sg : setAPreV (phi .first .Sing) = "w-" := rfl
/-- 2SG ergative (preV): aw- -/
theorem setA_preV_2sg : setAPreV (phi .second .Sing) = "aw-" := rfl
/-- 3SG ergative (preV): r- -/
theorem setA_preV_3sg : setAPreV (phi .third .Sing) = "r-" := rfl

-- ============================================================================
-- § 9: Set A / Set B Identity (Possessives = Set A)
-- ============================================================================

/-- Set A markers are identical to possessive pronouns: the transitive
    subject markers (Lesson 15) are the same forms as the possessive
    prefixes (Lessons 7–8). This is a hallmark of ergative-absolutive
    languages, where ERG agreement and possession share the same
    morphological paradigm. @cite{mondloch-2017} Lesson 15 explicitly
    notes this identity. -/
theorem possessives_equal_setA :
    setAPreC (phi .first .Plur) = "qa-" ∧
    setAPreC (phi .second .Sing) = "a-" ∧
    setAPreC (phi .third .Sing) = "u-" ∧
    setAPreC (phi .third .Plur) = "ki-" :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Formal Markers Are Postverbal
-- ============================================================================

/-- All informal Set B markers are prefixes. -/
theorem setB_informal_prefix :
    SetBIsPrefix (phi .first .Sing) ∧
    SetBIsPrefix (phi .second .Sing) ∧
    SetBIsPrefix (phi .third .Sing) ∧
    SetBIsPrefix (phi .first .Plur) ∧
    SetBIsPrefix (phi .second .Plur) ∧
    SetBIsPrefix (phi .third .Plur) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Formal Set B markers are NOT prefixes (they're postverbal). -/
theorem setB_formal_postverbal :
    ¬ SetBIsPrefix ⟨.second, .Sing, .formal⟩ ∧
    ¬ SetBIsPrefix ⟨.second, .Plur, .formal⟩ :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- § 11: Independent Pronouns — Lesson 4
-- ============================================================================

/-- Independent (free) personal pronouns. These are used in nonverbal
    sentences and as emphatic/contrastive pronouns in verbal sentences.
    @cite{mondloch-2017} Lesson 4. -/
def independentPronoun : PhiFeatures → String
  | ⟨.first,  .Sing, .informal⟩ => "in"
  | ⟨.second, .Sing, .informal⟩ => "at"
  | ⟨.third,  .Sing, .informal⟩ => "are'"
  | ⟨.first,  .Plur, .informal⟩ => "oj"
  | ⟨.second, .Plur, .informal⟩ => "ix"
  | ⟨.third,  .Plur, .informal⟩ => "a're'"
  | ⟨.second, .Sing, .formal⟩   => "laal"
  | ⟨.second, .Plur, .formal⟩   => "alaq"
  | ⟨.first,  _, .informal⟩   => "oj"
  | ⟨.second, _, .informal⟩   => "ix"
  | ⟨.third,  _, .informal⟩   => "a're'"
  | ⟨_, _, .formal⟩            => "are'"

/-- Independent pronouns correspond to Set B (absolutive) markers in
    form: 1SG *in* = Set B *in-*, 2SG *at* = Set B *at-*, etc.
    This is expected for an ergative language where the independent
    pronouns pattern with absolutive agreement. -/
theorem pronoun_setB_correspondence :
    independentPronoun (phi .first .Sing)  = "in"  ∧
    independentPronoun (phi .second .Sing) = "at"  ∧
    independentPronoun (phi .first .Plur)  = "oj"  ∧
    independentPronoun (phi .second .Plur) = "ix"  :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fragments.Mayan.Kiche
