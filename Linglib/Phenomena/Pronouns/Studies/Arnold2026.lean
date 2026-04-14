import Linglib.Core.Gender
import Linglib.Core.Lexical.Pronouns
import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.ReferentialForm
import Linglib.Fragments.English.Pronouns

/-!
# @cite{arnold-2026}

Arnold, Jennifer E. 2026. Two kinds of singular *they*: A usage-based model.
*Glossa: a journal of general linguistics* X(X). 1–14.
DOI: https://doi.org/10.16995/glossa.23998

## Core Contribution

English singular *they* is not one phenomenon but two, distinguished by
inversely correlated pragmatic conditions:

1. **Underspecified singular *they*** (the older form, attested since Middle
   English; @cite{balhorn-2004}): licensed when the referent's discourse
   representation is **underspecified** — quantified, indefinite, epicene,
   or not elaborated in the discourse. The key criterion is **discourse
   specificity** (@cite{newman-1992} "solidity", @cite{newman-1998}
   "individuation", @cite{camilliere-etal-2021} "social distance"), not
   gender per se.

2. **Personal singular *they*** (the newer form, emerging ~2018): licensed
   when the referent's personal pronouns are known to be *they/them* and
   this fact is in **common ground**. Co-occurs with highly specific
   discourse representations.

The two uses share phonological form (*they*) and the absence of a
contrastive gender feature, but have opposite pragmatic preconditions:
underspecified *they* requires a thin discourse representation, while
personal *they* requires a thick one.

## Formalization

We model the distinction using three components:

- `DiscourseElaboration`: how developed the referent's discourse
  representation is (underspecified vs. elaborated)
- `Core.Pronouns.PronounSpec`: what personal pronouns the referent uses
  (if known)
- `Core.GenderInfo`: what gender information is available in the discourse

The licensing conditions are predicates over these types, and the central
claim — that the two kinds of singular *they* are licensed by inversely
correlated conditions — is a theorem.

## Connection to Grammatical Accounts

@cite{konnelly-cowper-2020} propose a 3-stage grammatical account where
variation in acceptance of singular *they* reflects changes in the gender
feature system (contrastive → variably marked → fully underspecified).
Arnold's account complements this by centering **pragmatic** conditions
on use, particularly the role of discourse elaboration, which the
grammatical account does not address.
-/

set_option autoImplicit false

namespace Phenomena.Pronouns.Studies.Arnold2026

open Core (GenderInfo SurfaceGender)
open Core.Pronouns (PronounSpec)
open Core.Discourse.ReferentialForm (DiscourseElaboration AccessibilityLevel)
open Fragments.English.Pronouns (GenderParadigm)

-- ============================================================================
-- § 2: The Two-Kinds Taxonomy
-- ============================================================================

/-- The two kinds of singular *they* (@cite{arnold-2026} §1).

    These are distinguished by their pragmatic licensing conditions:
    - Underspecified: discourse representation is thin (§2)
    - Personal: referent's pronouns are known to be *they/them* (§3) -/
inductive SingTheyKind where
  /-- Underspecified singular *they*: the older form, licensed by
      underspecified discourse representation. -/
  | underspecified
  /-- Personal singular *they*: the newer form, licensed by knowledge
      that the referent's personal pronouns are *they/them*. -/
  | personal
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 3: Licensing Conditions
-- ============================================================================

/-- Underspecified singular *they* is licensed when the referent's
    discourse representation is underspecified.

    @cite{arnold-2026} §2: "Singular *they* is preferred when the
    speaker intends to evoke an underspecified mental representation
    for the addressee in the discourse." -/
def licensesUnderspecified (de : DiscourseElaboration) : Bool :=
  match de with
  | .underspecified => true
  | .elaborated => false

/-- Personal singular *they* is licensed when the referent's personal
    pronouns are known to be *they/them*.

    @cite{arnold-2026} §3: "the pragmatic condition for using personal
    *they* is knowing that the referent's personal pronouns are
    *they/them*." This knowledge must be in common ground. -/
def licensesPersonal (spec : Option PronounSpec) : Bool :=
  match spec with
  | some .theyThem => true
  | _ => false

/-- Classify a singular *they* use given the discourse state. -/
def classifyUse (de : DiscourseElaboration) (spec : Option PronounSpec) :
    Option SingTheyKind :=
  if licensesPersonal spec then some .personal
  else if licensesUnderspecified de then some .underspecified
  else none

-- ============================================================================
-- § 4: Inverse Correlation
-- ============================================================================

/-- **Core theorem**: the licensing conditions for the two kinds of
    singular *they* are inversely correlated.

    When the referent has a known *they/them* pronoun specification and
    an elaborated discourse representation (the typical case for personal
    *they*), underspecified *they* is NOT licensed. -/
theorem personal_excludes_underspecified
    (spec : PronounSpec) (hspec : spec = .theyThem)
    (de : DiscourseElaboration) (hde : de = .elaborated) :
    licensesPersonal (some spec) = true ∧
    licensesUnderspecified de = false := by
  subst hspec; subst hde; exact ⟨rfl, rfl⟩

/-- Conversely, when the discourse representation is underspecified
    (the typical case for underspecified *they*), personal *they* is
    NOT licensed — there is not enough information about the referent
    to know their pronouns. -/
theorem underspecified_excludes_personal
    (de : DiscourseElaboration) (hde : de = .underspecified)
    (spec : Option PronounSpec) (hspec : spec = none) :
    licensesUnderspecified de = true ∧
    licensesPersonal spec = false := by
  subst hde; subst hspec; exact ⟨rfl, rfl⟩

/-- The two licensing conditions never simultaneously fire on the
    same discourse state (when elaboration and pronoun knowledge
    are consistent). If a referent has *they/them* pronouns, the
    discourse model is necessarily elaborated (you know enough about
    them to know their pronouns). -/
theorem no_simultaneous_licensing
    (de : DiscourseElaboration) (spec : Option PronounSpec)
    (_h : licensesPersonal spec = true) :
    -- Personal they fires → elaboration must not be underspecified
    -- (a referent whose pronouns you know has a rich representation)
    de = .elaborated →
    licensesUnderspecified de = false := by
  intro hde; subst hde; rfl

-- ============================================================================
-- § 5: Antecedent Types (Table 1 data)
-- ============================================================================

/-- Antecedent type classification for singular *they*.

    @cite{arnold-2026} Table 1 shows that singular *they* occurs with
    quantified, indefinite, and definite antecedents, even when the
    referent has a known gender. What unifies these uses (under the
    underspecified account) is that the discourse representation is
    thin, not that gender is unknown. -/
inductive AntecedentType where
  /-- "There's not a man I meet but doth salute me as if I were their
      well-acquainted friend" (Shakespeare, Comedy of Errors, 1623). -/
  | quantified
  /-- "a single mother and their three children" -/
  | indefinite
  /-- "My son will swing by to pick up my order." / "just have them
      call us when they are here" — definite but not elaborated. -/
  | definiteUnelaborated
  deriving DecidableEq, Repr, BEq

/-- All underspecified-*they* antecedent types have underspecified
    discourse elaboration. This is Arnold's core claim: the unifying
    factor is discourse specificity, not antecedent definiteness. -/
def antecedentElaboration : AntecedentType → DiscourseElaboration
  | .quantified => .underspecified
  | .indefinite => .underspecified
  | .definiteUnelaborated => .underspecified

/-- All Table 1 antecedent types license underspecified singular *they*. -/
theorem table1_all_license_underspecified (a : AntecedentType) :
    licensesUnderspecified (antecedentElaboration a) = true := by
  cases a <;> rfl

-- ============================================================================
-- § 6: Connection to Gender Layer
-- ============================================================================

/-- Singular *they* (both kinds) maps to the epicene gender paradigm
    in the English pronoun system. -/
theorem singThey_is_epicene :
    Fragments.English.Pronouns.genderOf "they" = .epicene ∧
    Fragments.English.Pronouns.genderOf "them" = .epicene ∧
    Fragments.English.Pronouns.genderOf "themself" = .epicene := by
  exact ⟨rfl, rfl, rfl⟩

/-- The epicene paradigm has no single `SurfaceGender` equivalent —
    it is a pronoun-system gender class, not a noun-system agreement
    class. This reflects the asymmetry between pronoun selection
    (which depends on discourse state) and noun agreement (which
    depends on morphosyntactic features). -/
theorem epicene_not_surface :
    GenderParadigm.epicene.toSurfaceGender = none := rfl

/-- Underspecified gender info — where gender is unknown — is the
    discourse-level condition that licenses underspecified *they*. -/
theorem underspecified_gender_licenses_underspecified_they :
    licensesUnderspecified DiscourseElaboration.underspecified = true := rfl

-- ============================================================================
-- § 7: Predictions
-- ============================================================================

/-- @cite{arnold-2026} §4.1: the contexts supporting personal *they*
    are often inconsistent with underspecified *they*. Elaborated
    discourse representations (naming, describing, narrating about a
    person) make underspecified *they* infelicitous because the discourse
    model is no longer thin. -/
theorem elaborated_blocks_underspecified :
    licensesUnderspecified DiscourseElaboration.elaborated = false := rfl

/-- @cite{arnold-2026} §4.3: personal *they* is harder than
    underspecified *they*. This is modeled by the additional requirement:
    personal *they* needs pronoun knowledge in common ground, while
    underspecified *they* only needs a thin discourse model. -/
theorem personal_has_stronger_precondition :
    -- Underspecified they: one condition (thin discourse)
    licensesUnderspecified DiscourseElaboration.underspecified = true ∧
    -- Personal they: requires specific pronoun knowledge
    licensesPersonal none = false ∧
    licensesPersonal (some PronounSpec.heHim) = false ∧
    licensesPersonal (some PronounSpec.sheHer) = false ∧
    licensesPersonal (some PronounSpec.theyThem) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Connection to Accessibility Theory
-- ============================================================================

/-- Pronouns (high accessibility) correlate with elaborated discourse
    representations — you use a pronoun for a referent that is already
    well-established in the discourse. The bridge function
    `AccessibilityLevel.toElaboration` is defined in
    `Core.Discourse.ReferentialForm`. -/
theorem pronoun_implies_elaborated :
    AccessibilityLevel.unstressedPron.toElaboration = .elaborated := rfl

/-- Full names (low accessibility) correlate with underspecified discourse
    representations — the referent is being (re-)introduced. -/
theorem fullName_implies_underspecified :
    AccessibilityLevel.fullName.toElaboration = .underspecified := rfl

/-- Singular and plural *they* share the same gender paradigm — the
    structural `genderParadigm` field agrees across number. -/
theorem structural_gender_consistency :
    Fragments.English.Pronouns.they_sg.genderParadigm =
    Fragments.English.Pronouns.they.genderParadigm := rfl

end Phenomena.Pronouns.Studies.Arnold2026
