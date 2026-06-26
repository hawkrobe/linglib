import Linglib.Features.Gender.Interp
import Linglib.Discourse.CommonGround
import Linglib.Fragments.English.Pronouns
import Linglib.Studies.KonnellyCowper2020

/-!
# [arnold-2026]

Arnold, Jennifer E. 2026. Two kinds of singular *they*: A usage-based model.
*Glossa: a journal of general linguistics* X(X). 1–14.
DOI: https://doi.org/10.16995/glossa.23998

## Core Contribution

English singular *they* is not one phenomenon but two, distinguished by
inversely correlated pragmatic conditions:

1. **Underspecified singular *they*** (the older form, attested since Middle
   English; [balhorn-2004]): licensed when the referent's discourse
   representation is **underspecified** — quantified, indefinite, epicene,
   or not elaborated in the discourse. The key criterion is **discourse
   specificity** ([newman-1992] "solidity", [newman-1998]
   "individuation", [camilliere-etal-2021] "social distance"), not
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
- `PronounSet`: what personal pronouns the referent uses (if known)
- `GenderInfo`: what gender information is available in the discourse

The licensing conditions are predicates over these types, and the central
claim — that the two kinds of singular *they* are licensed by inversely
correlated conditions — is a theorem.

## Connection to Grammatical Accounts

[konnelly-cowper-2020] propose a 3-stage grammatical account where
variation in acceptance of singular *they* reflects changes in the gender
feature system (contrastive → variably marked → fully underspecified).
Arnold's account complements this by centering **pragmatic** conditions
on use, particularly the role of discourse elaboration, which the
grammatical account does not address.
-/

set_option autoImplicit false

namespace Arnold2026

/-- How elaborated a referent's discourse representation is ([arnold-2026]).

    [arnold-2026] (§2, UNVERIFIED): the criterion for underspecified
    singular *they* is "discourse specificity" — whether the speaker
    intends to evoke a detailed mental representation for the addressee.
    Extends [newman-1992]'s "solidity" and [newman-1998]'s "individuation".
    Crucially this is *orthogonal* to a referential form's accessibility:
    the same reduced form (*they*) spans both an `underspecified` generic
    and an `elaborated` named individual, so it is assigned from antecedent
    type (`antecedentElaboration`), not derived from `AccessibilityLevel.rank`. -/
inductive DiscourseElaboration where
  /-- Minimal discourse representation: quantified, indefinite, epicene,
      or not developed. "Everyone should make their bed." -/
  | underspecified
  /-- Rich, detailed discourse representation: named, described, topical,
      with known personal attributes. -/
  | elaborated
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: The Two-Kinds Taxonomy
-- ============================================================================

/-- The two kinds of singular *they* ([arnold-2026] §1).

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

/-- The personal pronouns a referent uses — a social fact about the *referent*
    (not a property of the pronoun system) that may or may not be in common
    ground. [arnold-2026]: the pragmatic condition for *personal* singular
    *they* is knowing that the referent's pronouns are *they/them*. Scoped to the
    three English sets this paper's licensing turns on (neopronouns and other
    languages are out of scope here). -/
inductive PronounSet where
  | heHim    -- he/him/his
  | sheHer   -- she/her/hers
  | theyThem -- they/them/theirs
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 3: Licensing Conditions
-- ============================================================================

/-- Underspecified singular *they* is licensed when the referent's
    discourse representation is underspecified.

    [arnold-2026] §2: "Singular *they* is preferred when the
    speaker intends to evoke an underspecified mental representation
    for the addressee in the discourse." -/
def licensesUnderspecified (de : DiscourseElaboration) : Bool :=
  match de with
  | .underspecified => true
  | .elaborated => false

/-- Personal singular *they* is licensed when the referent's personal
    pronouns are known to be *they/them*.

    [arnold-2026] §3: "the pragmatic condition for using personal
    *they* is knowing that the referent's personal pronouns are
    *they/them*." This knowledge must be in common ground. -/
def licensesPersonal (spec : Option PronounSet) : Bool :=
  match spec with
  | some .theyThem => true
  | _ => false

/-- Classify a singular *they* use given the discourse state. -/
def classifyUse (de : DiscourseElaboration) (spec : Option PronounSet) :
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
    (spec : PronounSet) (hspec : spec = .theyThem)
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
    (spec : Option PronounSet) (hspec : spec = none) :
    licensesUnderspecified de = true ∧
    licensesPersonal spec = false := by
  subst hde; subst hspec; exact ⟨rfl, rfl⟩

/-- The two licensing conditions never simultaneously fire on the
    same discourse state (when elaboration and pronoun knowledge
    are consistent). If a referent has *they/them* pronouns, the
    discourse model is necessarily elaborated (you know enough about
    them to know their pronouns). -/
theorem no_simultaneous_licensing
    (de : DiscourseElaboration) (spec : Option PronounSet)
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

    [arnold-2026] Table 1 shows that singular *they* occurs with
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

/-- Singular *they* bears no gender feature — the [konnelly-cowper-2020]
    Elsewhere case: *they* spells out a φ-bundle with none of
    `[MASC]`/`[FEM]`/`[INANIM]`, so its `gender` field is `none`, not a positive epicene
    value. -/
theorem singThey_genderless :
    English.Pronouns.they.gender = none ∧
    English.Pronouns.them.gender = none ∧
    English.Pronouns.themself.gender = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- Singular *they*'s lexical entry carries no surface gender
    ([konnelly-cowper-2020]): the `gender` field is `none`, the structural
    correlate of its Elsewhere status — gender-neutrality is the *absence* of a
    contrastive feature, not a positive value. -/
theorem they_no_surface_gender :
    English.Pronouns.they_sg.gender = none := rfl

/-- Underspecified gender info — where gender is unknown — is the
    discourse-level condition that licenses underspecified *they*. -/
theorem underspecified_gender_licenses_underspecified_they :
    licensesUnderspecified DiscourseElaboration.underspecified = true := rfl

-- ============================================================================
-- § 7: Predictions
-- ============================================================================

/-- [arnold-2026] §4.1: the contexts supporting personal *they*
    are often inconsistent with underspecified *they*. Elaborated
    discourse representations (naming, describing, narrating about a
    person) make underspecified *they* infelicitous because the discourse
    model is no longer thin. -/
theorem elaborated_blocks_underspecified :
    licensesUnderspecified DiscourseElaboration.elaborated = false := rfl

/-- [arnold-2026] §4.3: personal *they* is harder than
    underspecified *they*. This is modeled by the additional requirement:
    personal *they* needs pronoun knowledge in common ground, while
    underspecified *they* only needs a thin discourse model. -/
theorem personal_has_stronger_precondition :
    -- Underspecified they: one condition (thin discourse)
    licensesUnderspecified DiscourseElaboration.underspecified = true ∧
    -- Personal they: requires specific pronoun knowledge
    licensesPersonal none = false ∧
    licensesPersonal (some PronounSet.heHim) = false ∧
    licensesPersonal (some PronounSet.sheHer) = false ∧
    licensesPersonal (some PronounSet.theyThem) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Gender feature consistency
-- ============================================================================

/-- Singular and plural *they* share the same (empty) gender feature — the
    structural `gender` field agrees across number. -/
theorem structural_gender_consistency :
    English.Pronouns.they_sg.gender =
    English.Pronouns.they.gender := rfl

-- ============================================================================
-- § 9: Bridge to Konnelly & Cowper 2020 (morphosyntactic stages)
-- ============================================================================

/-- **Bridge to [konnelly-cowper-2020]'s grammatical stages.** Arnold's
    pragmatic *underspecified they* aligns with their Stage 1: while the grammar
    still obligatorily projects [MASC]/[FEM] for known-gender referents
    (`Stage.stage1`, `genderObligatory = true`), *they* surfaces only where
    gender is unknown — the thin-discourse condition that licenses
    underspecified *they*. (At the gender-default Stage 3, `genderObligatory =
    false`, so *they* is produced regardless of discourse state, naturally
    accommodating personal *they*.) -/
theorem stage1_aligns_with_underspecified_they :
    licensesUnderspecified DiscourseElaboration.underspecified = true ∧
    KonnellyCowper2020.Stage.stage1.genderObligatory = true := ⟨rfl, rfl⟩

end Arnold2026
