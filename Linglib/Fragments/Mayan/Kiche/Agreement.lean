import Linglib.Features.Case.Basic
import Linglib.Data.UD.Basic
import Linglib.Features.Number.Capabilities
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Extraction

/-!
# K'iche' Agreement Fragment

Theory-neutral typological metadata for K'iche' (K'ichean Mayan)
agreement morphology, following [mondloch-2017] Lessons 4, 7–8, 9, 15.
K'iche' has ergative-absolutive alignment realized through two verbal
agreement paradigms: Set B (absolutive) cross-references intransitive S
and transitive P and appears between the aspect marker and the root;
Set A (ergative) cross-references transitive A, appears between the
object marker and the root, and is identical to the possessive prefixes.
Unlike its sister Kaqchikel, K'iche' has no construction-specific
inverted alignment.

## Main declarations

* `Kiche.PhiFeatures`: person/number/formality bundles, with `HasPerson`
  and `HasNumber` instances and the informal shorthand `Kiche.phi`.
* `Kiche.setBMarker`, `Kiche.setAPreC`, `Kiche.setAPreV`: the Set B
  (absolutive) and Set A (ergative, pre-consonantal / pre-vocalic)
  exponents.
* `Kiche.ArgPosition.agreementSet`, `Kiche.ArgPosition.case`: the
  agreement set and case each argument position triggers.
* `Kiche.independentPronoun`: the free personal pronouns.
* `Kiche.setAExponent`, `Kiche.setBExponent`: canonical φ-cell exponent
  tables for cross-Mayan consumption.
* `Kiche.extractionStrategy`: the Agent-Focus extraction profile.

## Implementation notes

The alignment is ergative-absolutive: Set B groups S and P (both trigger
the same paradigm) while A triggers Set A. This contrasts with Mam,
which is morphologically tripartite (S, A, P each distinct;
[scott-2023]). K'iche' has two 2nd-person formality levels; the formal
forms (laal SG, alaq PL) are syntactically postverbal and pattern
outside the prefix paradigm. K'iche' is HIGH-ABS (Set B pre-stem on
Infl), and its case wiring reuses `Mayan.ergCaseKiche` (from
`Alignment.ergative`); the canonical φ-cell exponent tables key on
`Agreement.Cell` for cross-Mayan consumption. Agent-Focus Antipassive
marks A-extraction with the voice marker *-n*, shared with the
Absolutive Antipassive ([mondloch-2017] Lesson 22).
-/


namespace Kiche

/-! ### Person, number, and formality features -/

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

/-! ### Set B (absolutive) markers -/

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

/-! ### Set A (ergative) markers -/

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

/-! ### Morphological positions -/

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

/-! ### Argument positions and alignment -/

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

/-! ### Alignment theorems -/

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

/-! ### Set B per-cell verification -/

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

/-! ### Set A per-cell verification -/

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

/-! ### Possessives equal Set A -/

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

/-! ### Formal markers are postverbal -/

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

/-! ### Independent pronouns -/

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

/-! ### Cross-Mayan canonical wrappers -/

open Mayan (MarkerLinearity ExponentTable)
open Agreement

/-- K'iche' is HIGH-ABS: Set B markers appear pre-stem on Infl. -/
def absPosition : Mayan.ABSPosition := .high

/-- Set A linearity: prefixal ([mondloch-2017] Lessons 7–8). -/
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

/-- K'iche' extraction profile: Agent-Focus Antipassive marks A-extraction
    ([mondloch-2017] Lesson 22; also Lessons 30, 33 for radical transitives
    and perfect aspect). The voice marker *-n* is shared with the
    Absolutive Antipassive (Lesson 21); the two differ syntactically — both
    arguments overt under AF, object suppressed under the antipassive — not
    morphologically. HIGH-ABS K'ichean, structurally analogous to
    Kaqchikel. -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

end Kiche
