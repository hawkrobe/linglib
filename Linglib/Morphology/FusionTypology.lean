import Linglib.Data.WALS.Features.F20A
import Linglib.Data.WALS.Features.F21A

/-!
# Fusion Typology

The Bickel & Nichols fusion/flexivity typology [bickel-nichols-2007]
[bickel-nichols-2013a]: framework-agnostic classification types (`Fusion`,
`Flexivity`, `CaseExponence`, `ExponenceScope`), the per-language `MorphProfile`
record, WALS grounding functions, and the traditional agglutinating/fusional
predicates with their mutual-exclusion theorems.

The `fusion` and `exponence` fields are derived from WALS Chapters 20 and 21;
the orthogonal `flexivity` and `bnExponence` parameters are not derivable from
WALS and are stipulated per language in the Fragments as textbook-consensus
summary values. [bickel-nichols-2007] themselves type *formatives*, not
languages ("it clearly makes little sense to talk about concatenative or
nonlinear languages per se", p. 183); a profile's value summarizes the
language's dominant formative type.
-/

namespace Morphology

-- ============================================================================
-- §1. Typological Classification Types
-- ============================================================================

/-- WALS Ch 20: How inflectional formatives are attached to stems.

    Note: this captures *fusion* only — the degree of phonological
    boundedness between formative and stem. The traditional labels
    "agglutinating" and "fusional" conflate fusion with *flexivity*
    (see `Flexivity` below). Both `concatenative + nonflexive` (Turkish)
    and `concatenative + flexive` (Russian) map to `.concatenative` here.
    [bickel-nichols-2007] -/
inductive Fusion where
  | isolating
  | concatenative
  | nonlinear
  deriving DecidableEq, Repr

/-- Whether inflectional formatives show item-based allomorphic variation.

    [bickel-nichols-2007] argue this is the crucial parameter that
    the traditional typology conflates with fusion:
    - **nonflexive**: formatives "are invariant across the lexicon"
      (p. 185) or vary by rule (Turkish *-ler* ~ *-lar* is vowel-harmony,
      not item-based allomorphy)
    - **flexive**: formatives "come in sets of variants called allomorphs
      ... selected on lexical, i.e. item-based, principles" (p. 184;
      Latin nominative singular *-s* ~ *-m* ~ zero by declension class).
      Traditionally "(in)ﬂecting" (German *flektierend*); B&N's fn. 9
      (p. 184) rejects Comrie's "fusional" for this parameter as
      conflating flexivity with phonological fusion.

    "Flexivity is orthogonal to fusion, and all possible combinations of
    values on the two parameters are attested" (p. 186) — all SIX cells
    of the 3 × 2 space, including flexive-isolating (Yidiɲ) and
    nonflexive-isolating (Lai Chin, p. 187). A `none` value in
    `MorphProfile.flexivity` therefore means *not coded here*, never
    "inapplicable because isolating". -/
inductive Flexivity where
  | nonflexive   -- formatives phonologically invariant / rule-governed
  | flexive      -- formatives show item-based (class-conditioned) allomorphy
  deriving DecidableEq, Repr

/-- WALS Ch 21: How many grammatical categories a single case formative
    expresses. Specifically about *case* formatives and whether they
    bundle number, TAM, etc.

    Distinct from `ExponenceScope` (B&N's broader cumulative/separative
    parameter which applies to all morphological categories, not just
    case). The mono/polyexponential value labels are WALS Ch 21's
    ([bickel-nichols-2013b]), not the chapter's. -/
inductive CaseExponence where
  | monoexponential
  | polyexponential
  | noCase
  deriving DecidableEq, Repr

/-- Whether a single formative expresses multiple grammatical categories
    simultaneously (cumulative) or each formative expresses exactly one
    category (separative).

    [bickel-nichols-2007]: this is a general morphological parameter
    applying across all category pairs, not limited to case+number (cf.
    WALS Ch 21 `Exponence`). Latin *-ō* (1sg.pres.act.ind) is cumulative;
    Turkish verb suffixes are separative (each suffix = one category). -/
inductive ExponenceScope where
  | cumulative    -- one formative, multiple categories
  | separative    -- one formative per category
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. MorphProfile Structure
-- ============================================================================

/-- A language's morphological profile in the B&N fusion typology. The
    `fusion` and `exponence` fields are derived from WALS where possible;
    the orthogonal `flexivity` and `bnExponence` parameters are populated
    when [bickel-nichols-2007] stipulates them. -/
structure MorphProfile where
  language : String
  iso : String
  /-- Ch 20: Fusion type -/
  fusion : Fusion
  /-- Ch 21: Exponence type -/
  exponence : CaseExponence
  /-- [bickel-nichols-2007]: Flexivity — whether inflectional formatives
      show item-based allomorphic variation (flexive) or are phonologically
      invariant (nonflexive). Orthogonal to `fusion`. Not derivable from WALS. -/
  flexivity : Option Flexivity := none
  /-- [bickel-nichols-2007]: Exponence scope — whether single formatives
      bundle multiple categories (cumulative) or each expresses one (separative).
      Broader than WALS Ch 21 `exponence` (which is case-specific). -/
  bnExponence : Option ExponenceScope := none
  deriving Repr, DecidableEq

-- ============================================================================
-- §3. WALS Converter Functions
-- ============================================================================

/-- Convert WALS 20A fusion type to the local three-way `Fusion`
    classification. Every mixed WALS category (`ablautConcatenative`,
    `tonalIsolating`, `tonalConcatenative`, `isolatingConcatenative`)
    returns `none`: WALS 20A itself refuses a pure whole-language value
    for these, and collapsing a mixture to one pole is a per-language
    analytic judgment that belongs in the Fragment's fallback with its
    own docstring (e.g. Arabic: predominantly nonlinear, though person
    and number inflection is concatenative — [bickel-nichols-2007]
    p. 183). -/
def fromWALS20A : Data.WALS.F20A.FusionType → Option Fusion
  | .exclusivelyConcatenative => some .concatenative
  | .exclusivelyIsolating     => some .isolating
  | .exclusivelyTonal         => some .nonlinear
  | .ablautConcatenative      => none
  | .tonalIsolating           => none
  | .tonalConcatenative       => none
  | .isolatingConcatenative   => none

/-- Convert WALS 21A exponence type to the local `CaseExponence` classification.
    Returns `none` for `noCase` (no information about overall exponence). -/
def fromWALS21A : Data.WALS.F21A.ExponenceType → Option CaseExponence
  | .monoexponentialCase  => some .monoexponential
  | .caseNumber           => some .polyexponential
  | .caseReferentiality   => some .polyexponential
  | .caseTam              => some .polyexponential
  | .noCase               => none

-- ============================================================================
-- §4. WALS Lookup Helpers
-- ============================================================================

/-! WALS lookup helpers derive MorphProfile field values from auto-generated
    WALS data. Each returns `Option`, yielding `none` when the language is
    absent from that chapter or the grounding function is uninformative.
    Profile definitions use `.getD fallback` so the fallback is only reached
    when WALS cannot help. -/

def walsFusion (iso : String) : Option Fusion :=
  (Data.WALS.F20A.lookupISO iso).bind (fromWALS20A ·.value)

def walsExponence (iso : String) : Option CaseExponence :=
  (Data.WALS.F21A.lookupISO iso).bind (fromWALS21A ·.value)

-- ============================================================================
-- §4½. Smart Constructor
-- ============================================================================

/-- Build a `MorphProfile` from an ISO 639-3 code via WALS lookups.

    Required-field fallbacks (`fusionFb`, `exponenceFb`) must be supplied for
    the two WALS chapters where the lookup may return `none` (language absent
    from chapter, or grounding function uninformative — e.g. WALS 20A
    `isolatingConcatenative` does not map cleanly to the local 3-way `Fusion`
    enum and yields `none`). When WALS has data the lookup wins; the fallback
    is exercised only when WALS is silent.

    The `flexivity` and `bnExponence` parameters are NOT derivable from any
    WALS chapter and must be passed explicitly when known. They are
    per-language textbook-consensus summary values supplied by the Fragments
    — [bickel-nichols-2007] themselves type formatives, not languages
    (p. 183), and stipulate no per-language table. -/
def MorphProfile.fromWALS
    (language iso : String)
    (fusionFb : Fusion)
    (exponenceFb : CaseExponence)
    (flexivity : Option Flexivity := none)
    (bnExponence : Option ExponenceScope := none) : MorphProfile :=
  { language, iso
  , fusion := (walsFusion iso).getD fusionFb
  , exponence := (walsExponence iso).getD exponenceFb
  , flexivity, bnExponence
  }

-- ============================================================================
-- §5. Helper Predicates
-- ============================================================================

namespace MorphProfile

/-! Mathlib-style `Prop`-typed predicates with `Decidable` instances and
    `@[simp] _iff` lemmas. Filter sites that need `Bool` should call
    `decide` at the boundary. The `_iff` lemmas are `Iff.rfl` (unfolding-
    only) but make the decomposition visible to `simp` and to mathlib-
    pattern `decidable_of_iff` derivations. -/

def IsConcatenative (p : MorphProfile) : Prop := p.fusion = .concatenative
@[simp] theorem isConcatenative_iff (p : MorphProfile) :
    p.IsConcatenative ↔ p.fusion = .concatenative := Iff.rfl
instance : DecidablePred IsConcatenative :=
  fun p => decidable_of_iff _ (isConcatenative_iff p).symm

def IsIsolating (p : MorphProfile) : Prop := p.fusion = .isolating
@[simp] theorem isIsolating_iff (p : MorphProfile) :
    p.IsIsolating ↔ p.fusion = .isolating := Iff.rfl
instance : DecidablePred IsIsolating :=
  fun p => decidable_of_iff _ (isIsolating_iff p).symm

def IsNonlinear (p : MorphProfile) : Prop := p.fusion = .nonlinear
@[simp] theorem isNonlinear_iff (p : MorphProfile) :
    p.IsNonlinear ↔ p.fusion = .nonlinear := Iff.rfl
instance : DecidablePred IsNonlinear :=
  fun p => decidable_of_iff _ (isNonlinear_iff p).symm

def IsFlexive (p : MorphProfile) : Prop := p.flexivity = some .flexive
@[simp] theorem isFlexive_iff (p : MorphProfile) :
    p.IsFlexive ↔ p.flexivity = some .flexive := Iff.rfl
instance : DecidablePred IsFlexive :=
  fun p => decidable_of_iff _ (isFlexive_iff p).symm

def IsNonflexive (p : MorphProfile) : Prop := p.flexivity = some .nonflexive
@[simp] theorem isNonflexive_iff (p : MorphProfile) :
    p.IsNonflexive ↔ p.flexivity = some .nonflexive := Iff.rfl
instance : DecidablePred IsNonflexive :=
  fun p => decidable_of_iff _ (isNonflexive_iff p).symm

def IsCumulative (p : MorphProfile) : Prop := p.bnExponence = some .cumulative
@[simp] theorem isCumulative_iff (p : MorphProfile) :
    p.IsCumulative ↔ p.bnExponence = some .cumulative := Iff.rfl
instance : DecidablePred IsCumulative :=
  fun p => decidable_of_iff _ (isCumulative_iff p).symm

def IsSeparative (p : MorphProfile) : Prop := p.bnExponence = some .separative
@[simp] theorem isSeparative_iff (p : MorphProfile) :
    p.IsSeparative ↔ p.bnExponence = some .separative := Iff.rfl
instance : DecidablePred IsSeparative :=
  fun p => decidable_of_iff _ (isSeparative_iff p).symm

/-- Traditional "agglutinative" = concatenative + nonflexive: "When
    nonﬂexive formatives are concatenative, they are traditionally called
    agglutinative" ([bickel-nichols-2007] p. 187). Exponence is *not* part
    of the definition — separative exponence is a defeasible tendency of
    this type, not a criterion (p. 189: Turkish 1pl *-k* cumulates person
    and number yet is "clearly nonﬂexive"). -/
def IsAgglutinating (p : MorphProfile) : Prop :=
  p.IsConcatenative ∧ p.IsNonflexive
@[simp] theorem isAgglutinating_iff (p : MorphProfile) :
    p.IsAgglutinating ↔ p.IsConcatenative ∧ p.IsNonflexive :=
  Iff.rfl
instance : DecidablePred IsAgglutinating :=
  fun p => decidable_of_iff _ (isAgglutinating_iff p).symm

/-- Traditional "fusional" (textbook label) = concatenative + flexive:
    "the traditional notion of ﬂexive or '(in)ﬂecting' is often restricted
    to just this combination" ([bickel-nichols-2007] p. 186; the chapter
    itself avoids "fusional" — fn. 9 rejects it as conflating flexivity
    with fusion). Cumulative exponence is a tendency of this type, not a
    criterion (p. 189). -/
def IsFusional (p : MorphProfile) : Prop :=
  p.IsConcatenative ∧ p.IsFlexive
@[simp] theorem isFusional_iff (p : MorphProfile) :
    p.IsFusional ↔ p.IsConcatenative ∧ p.IsFlexive := Iff.rfl
instance : DecidablePred IsFusional :=
  fun p => decidable_of_iff _ (isFusional_iff p).symm

/-- "Introflexive" = nonlinear + flexive: "the label introﬂexive for just
    this combination" ([bickel-nichols-2007] p. 186) — the classic Semitic
    root-and-pattern profile. -/
def IsIntroflexive (p : MorphProfile) : Prop :=
  p.IsNonlinear ∧ p.IsFlexive
@[simp] theorem isIntroflexive_iff (p : MorphProfile) :
    p.IsIntroflexive ↔ p.IsNonlinear ∧ p.IsFlexive := Iff.rfl
instance : DecidablePred IsIntroflexive :=
  fun p => decidable_of_iff _ (isIntroflexive_iff p).symm

end MorphProfile

-- ============================================================================
-- §6. Structural Theorems on the B&N Parameter Space
-- ============================================================================

namespace MorphProfile

/-! ### Mutual exclusion

The traditional types "agglutinating" and "fusional" are mutually exclusive
because they require contradictory values on the flexivity dimension
(nonflexive vs flexive). This follows from the B&N decomposition — it is
not an empirical observation but a structural consequence of the definitions. -/

/-- Nonflexive and flexive are contradictory: a language cannot be both. -/
theorem nonflexive_flexive_exclusive (p : MorphProfile) :
    ¬(p.IsNonflexive ∧ p.IsFlexive) := by
  rintro ⟨h1, h2⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-- Cumulative and separative are contradictory: a language cannot be both. -/
theorem cumulative_separative_exclusive (p : MorphProfile) :
    ¬(p.IsCumulative ∧ p.IsSeparative) := by
  rintro ⟨h1, h2⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-- Agglutinating and fusional are mutually exclusive: they require opposite
    flexivity values (nonflexive vs flexive). Follows from the B&N
    decomposition; not an empirical observation. -/
theorem agglutinating_fusional_exclusive (p : MorphProfile) :
    ¬(p.IsAgglutinating ∧ p.IsFusional) := fun ⟨⟨_, hnf⟩, _, hf⟩ =>
  nonflexive_flexive_exclusive p ⟨hnf, hf⟩

end MorphProfile

end Morphology
