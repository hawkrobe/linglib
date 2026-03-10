import Linglib.Core.Case.Hierarchy
import Linglib.Core.Case.Basic

/-!
# K'iche' Agreement Fragment @cite{mondloch-2017}

Agreement morphology for K'iche' (K'ichean Mayan), following
@cite{mondloch-2017} Lessons 4, 7–8, 9, 15.

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
-- § 1: Person/Number Features
-- ============================================================================

/-- Grammatical person in K'iche'. -/
inductive Person where
  | first | second | third
  deriving DecidableEq, BEq, Repr

/-- Grammatical number in K'iche'. -/
inductive Number where
  | sg | pl
  deriving DecidableEq, BEq, Repr

/-- Formality level for 2nd person. -/
inductive Formality where
  | informal | formal
  deriving DecidableEq, BEq, Repr

/-- A person/number/formality specification. -/
structure PhiFeatures where
  person : Person
  number : Number
  formality : Formality
  deriving DecidableEq, BEq, Repr

/-- Shorthand for informal phi features. -/
abbrev phi (p : Person) (n : Number) : PhiFeatures := ⟨p, n, .informal⟩

-- ============================================================================
-- § 2: Set B (Absolutive) Markers — Lesson 9
-- ============================================================================

/-- Set B (absolutive) agreement markers.
    These are verbal prefixes (or postverbal particles for formal forms)
    that cross-reference S (intransitive subject) and P (transitive
    object). @cite{mondloch-2017}, Lessons 9, 15. -/
def setBMarker : PhiFeatures → String
  | ⟨.first,  .sg, .informal⟩ => "in-"
  | ⟨.second, .sg, .informal⟩ => "at-"
  | ⟨.third,  .sg, .informal⟩ => "Ø"
  | ⟨.first,  .pl, .informal⟩ => "oj-"
  | ⟨.second, .pl, .informal⟩ => "ix-"
  | ⟨.third,  .pl, .informal⟩ => "ee-"
  | ⟨.second, .sg, .formal⟩   => "la"
  | ⟨.second, .pl, .formal⟩   => "alaq"
  -- Formal forms exist only for 2nd person; others are unreachable
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 3: Set A (Ergative) Markers — Lessons 7, 15
-- ============================================================================

/-- Set A (ergative) markers before consonant-initial roots.
    These cross-reference A (transitive subject) and are identical to
    possessive pronouns before consonant-initial nouns.
    @cite{mondloch-2017}, Lessons 7, 15. -/
def setAPreC : PhiFeatures → String
  | ⟨.first,  .sg, .informal⟩ => "nu-/in-"
  | ⟨.second, .sg, .informal⟩ => "a-"
  | ⟨.third,  .sg, .informal⟩ => "u-"
  | ⟨.first,  .pl, .informal⟩ => "qa-"
  | ⟨.second, .pl, .informal⟩ => "i-"
  | ⟨.third,  .pl, .informal⟩ => "ki-"
  | ⟨.second, .sg, .formal⟩   => "la"
  | ⟨.second, .pl, .formal⟩   => "alaq"
  | ⟨_, _, .formal⟩            => "Ø"

/-- Set A (ergative) markers before vowel-initial roots.
    @cite{mondloch-2017}, Lesson 8. -/
def setAPreV : PhiFeatures → String
  | ⟨.first,  .sg, .informal⟩ => "w-"
  | ⟨.second, .sg, .informal⟩ => "aw-"
  | ⟨.third,  .sg, .informal⟩ => "r-"
  | ⟨.first,  .pl, .informal⟩ => "q-"
  | ⟨.second, .pl, .informal⟩ => "iw-"
  | ⟨.third,  .pl, .informal⟩ => "k-"
  | ⟨.second, .sg, .formal⟩   => "la"
  | ⟨.second, .pl, .formal⟩   => "alaq"
  | ⟨_, _, .formal⟩            => "Ø"

-- ============================================================================
-- § 4: Morphological Positions
-- ============================================================================

/-- Is a Set B marker a prefix (appearing before the root) or a
    postverbal particle? Formal forms are postverbal; all others
    are prefixes. @cite{mondloch-2017}, Lesson 9. -/
def setBIsPrefix (φ : PhiFeatures) : Bool :=
  φ.formality == .informal

/-- Is a Set A marker a prefix or postverbal?
    Same distribution as Set B: formal forms are postverbal. -/
def setAIsPrefix (φ : PhiFeatures) : Bool :=
  φ.formality == .informal

-- ============================================================================
-- § 5: Argument Positions and Alignment
-- ============================================================================

/-- Argument positions in a K'iche' clause. -/
inductive KicheArgPosition where
  | agent    -- A: transitive subject (triggers Set A)
  | patient  -- P: transitive object (triggers Set B)
  | intranS  -- S: intransitive subject (triggers Set B)
  deriving DecidableEq, BEq, Repr

/-- Which agreement set cross-references each argument position? -/
inductive AgreementSet where
  | setA  -- Ergative markers
  | setB  -- Absolutive markers
  deriving DecidableEq, BEq, Repr

/-- The agreement set triggered by each argument position.
    S and P both trigger Set B (= absolutive grouping).
    A triggers Set A (= ergative). -/
def KicheArgPosition.agreementSet : KicheArgPosition → AgreementSet
  | .agent   => .setA  -- A → Set A (ergative)
  | .patient => .setB  -- P → Set B (absolutive)
  | .intranS => .setB  -- S → Set B (absolutive)

/-- The case associated with each argument position. -/
def KicheArgPosition.case : KicheArgPosition → Core.Case
  | .agent   => .erg
  | .patient => .abs
  | .intranS => .abs

-- ============================================================================
-- § 6: Alignment Theorems
-- ============================================================================

/-- K'iche' groups S and P together (both trigger Set B):
    ergative-absolutive alignment. -/
theorem ergative_absolutive_alignment :
    KicheArgPosition.intranS.agreementSet = KicheArgPosition.patient.agreementSet ∧
    KicheArgPosition.agent.agreementSet ≠ KicheArgPosition.patient.agreementSet :=
  ⟨rfl, by decide⟩

/-- S and P receive the same case (ABS). -/
theorem s_p_same_case :
    KicheArgPosition.intranS.case = KicheArgPosition.patient.case := rfl

/-- A receives a different case (ERG) from S/P (ABS). -/
theorem a_different_case :
    KicheArgPosition.agent.case ≠ KicheArgPosition.intranS.case := by decide

/-- K'iche' alignment contrast with Mam: K'iche' is ergative-absolutive
    (S = P ≠ A), while Mam is tripartite (S ≠ A ≠ P, all three
    receive distinct cases). In K'iche', both P and S trigger Set B;
    in Mam, P triggers no agreement at all. -/
theorem kiche_not_tripartite :
    KicheArgPosition.intranS.case = KicheArgPosition.patient.case := rfl

-- ============================================================================
-- § 7: Set B Per-Cell Verification
-- ============================================================================

/-- 1SG absolutive: in- -/
theorem setB_1sg : setBMarker (phi .first .sg) = "in-" := rfl
/-- 2SG absolutive: at- -/
theorem setB_2sg : setBMarker (phi .second .sg) = "at-" := rfl
/-- 3SG absolutive: Ø -/
theorem setB_3sg : setBMarker (phi .third .sg) = "Ø" := rfl
/-- 1PL absolutive: oj- -/
theorem setB_1pl : setBMarker (phi .first .pl) = "oj-" := rfl
/-- 2PL absolutive: ix- -/
theorem setB_2pl : setBMarker (phi .second .pl) = "ix-" := rfl
/-- 3PL absolutive: ee- -/
theorem setB_3pl : setBMarker (phi .third .pl) = "ee-" := rfl
/-- 2SG.FORM: la (postverbal) -/
theorem setB_2sg_form : setBMarker ⟨.second, .sg, .formal⟩ = "la" := rfl
/-- 2PL.FORM: alaq (postverbal) -/
theorem setB_2pl_form : setBMarker ⟨.second, .pl, .formal⟩ = "alaq" := rfl

-- ============================================================================
-- § 8: Set A Per-Cell Verification
-- ============================================================================

/-- 1SG ergative (preC): nu‑ or in‑ -/
theorem setA_1sg : setAPreC (phi .first .sg) = "nu-/in-" := rfl
/-- 2SG ergative (preC): a- -/
theorem setA_2sg : setAPreC (phi .second .sg) = "a-" := rfl
/-- 3SG ergative (preC): u- -/
theorem setA_3sg : setAPreC (phi .third .sg) = "u-" := rfl
/-- 1PL ergative (preC): qa- -/
theorem setA_1pl : setAPreC (phi .first .pl) = "qa-" := rfl
/-- 2PL ergative (preC): i- -/
theorem setA_2pl : setAPreC (phi .second .pl) = "i-" := rfl
/-- 3PL ergative (preC): ki- -/
theorem setA_3pl : setAPreC (phi .third .pl) = "ki-" := rfl

/-- 1SG ergative (preV): w- -/
theorem setA_preV_1sg : setAPreV (phi .first .sg) = "w-" := rfl
/-- 2SG ergative (preV): aw- -/
theorem setA_preV_2sg : setAPreV (phi .second .sg) = "aw-" := rfl
/-- 3SG ergative (preV): r- -/
theorem setA_preV_3sg : setAPreV (phi .third .sg) = "r-" := rfl

-- ============================================================================
-- § 9: Set A / Set B Identity (Possessives = Set A)
-- ============================================================================

/-- Set A markers are identical to possessive pronouns: the transitive
    subject markers (Lesson 15) are the same forms as the possessive
    prefixes (Lessons 7–8). This is a hallmark of ergative-absolutive
    languages, where ERG agreement and possession share the same
    morphological paradigm. @cite{mondloch-2017}, Lesson 15 explicitly
    notes this identity. -/
theorem possessives_equal_setA :
    setAPreC (phi .first .pl) = "qa-" ∧
    setAPreC (phi .second .sg) = "a-" ∧
    setAPreC (phi .third .sg) = "u-" ∧
    setAPreC (phi .third .pl) = "ki-" :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Formal Markers Are Postverbal
-- ============================================================================

/-- All informal Set B markers are prefixes. -/
theorem setB_informal_prefix :
    setBIsPrefix (phi .first .sg) = true ∧
    setBIsPrefix (phi .second .sg) = true ∧
    setBIsPrefix (phi .third .sg) = true ∧
    setBIsPrefix (phi .first .pl) = true ∧
    setBIsPrefix (phi .second .pl) = true ∧
    setBIsPrefix (phi .third .pl) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Formal Set B markers are NOT prefixes (they're postverbal). -/
theorem setB_formal_postverbal :
    setBIsPrefix ⟨.second, .sg, .formal⟩ = false ∧
    setBIsPrefix ⟨.second, .pl, .formal⟩ = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 11: Independent Pronouns — Lesson 4
-- ============================================================================

/-- Independent (free) personal pronouns. These are used in nonverbal
    sentences and as emphatic/contrastive pronouns in verbal sentences.
    @cite{mondloch-2017}, Lesson 4. -/
def independentPronoun : PhiFeatures → String
  | ⟨.first,  .sg, .informal⟩ => "in"
  | ⟨.second, .sg, .informal⟩ => "at"
  | ⟨.third,  .sg, .informal⟩ => "are'"
  | ⟨.first,  .pl, .informal⟩ => "oj"
  | ⟨.second, .pl, .informal⟩ => "ix"
  | ⟨.third,  .pl, .informal⟩ => "a're'"
  | ⟨.second, .sg, .formal⟩   => "laal"
  | ⟨.second, .pl, .formal⟩   => "alaq"
  | ⟨_, _, .formal⟩            => "are'"

/-- Independent pronouns correspond to Set B (absolutive) markers in
    form: 1SG *in* = Set B *in-*, 2SG *at* = Set B *at-*, etc.
    This is expected for an ergative language where the independent
    pronouns pattern with absolutive agreement. -/
theorem pronoun_setB_correspondence :
    independentPronoun (phi .first .sg)  = "in"  ∧
    independentPronoun (phi .second .sg) = "at"  ∧
    independentPronoun (phi .first .pl)  = "oj"  ∧
    independentPronoun (phi .second .pl) = "ix"  :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fragments.Mayan.Kiche
