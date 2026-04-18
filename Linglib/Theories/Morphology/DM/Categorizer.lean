import Linglib.Core.Gender
import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Categorizing Heads (Distributed Morphology) @cite{harley-2014}
@cite{embick-2004} @cite{marantz-1997}
@cite{kramer-2015}

@cite{harley-2014} "On the identity of roots" addresses three questions about
roots in DM:

1. **What are roots?** (§2) Root terminal nodes are individuated by arbitrary
   indices, not by phonological or semantic content.
   The **Categorization Assumption** holds: roots must merge with a categorizing
   head (n, v, a) to enter the syntax.

2. **Can roots take complements?** (§3) Yes — roots can Merge directly with
   internal arguments without mediation by a functional head. Evidence:
   *one*-replacement in argument structure nominals, verb-object idioms,
   Hiaki suppletive verbs conditioned by the root's complement.

3. **What delimits the domain of special interpretation?** (§4) VoiceP, not
   the first categorizing head. Idiosyncratic interpretation can extend past
   the first categorizer (evidence: multiply derived words like *editorial*,
   *classifieds*, *nationalize*). Voice is the phase head.

## DM Three-Lists Architecture (@cite{marantz-1997}, @cite{harley-2014} §5)

- **List 1**: Root terminal nodes — syntactic atoms with opaque indices
- **List 2**: Vocabulary Items — phonological realizations competing for insertion
- **List 3**: Encyclopedia entries — interpretations conditioned by context

## Phi-Features on n (@cite{kramer-2015} Ch 3)

@cite{kramer-2015} argues that grammatical gender is a phi-feature located on
the nominalizing head n, not on roots. The feature system is parameterized
across languages by **dimension** (what binary feature is used):

| Language    | Dimension | Four types of n                          |
|-------------|-----------|------------------------------------------|
| Amharic     | [±FEM]    | n i[+FEM], n i[−FEM], n, n u[+FEM]      |
| Spanish     | [±FEM]    | n i[+FEM], n i[−FEM], n, n u[+FEM]      |
| Maa         | [±FEM]    | n i[+FEM], n i[−FEM], n, n u[−FEM]       |
| Algonquian  | [±ANIM]   | n i[+ANIM], n i[−ANIM], n, n u[+ANIM]   |

(@cite{kramer-2015} Chs 3, 5-7; @cite{adamson-2024} extends this to Teop [±ANIM]
and Jarawara [±MASC])

This module formalizes the categorization layer, its phi-feature content,
and its relationship to Voice. List 2 (Vocabulary Insertion) is formalized
in `VocabularyInsertion.lean`.

-/

namespace Morphology.DM

open Minimalism

-- ============================================================================
-- § 1: Categorizer Type
-- ============================================================================

/-- A categorizing head that merges with an acategorial root to project
    syntactic structure. The three options correspond to the functional
    heads n, v, a in Distributed Morphology (@cite{marantz-1997}, @cite{harley-2014} §2). -/
inductive Categorizer where
  | n  -- nominal categorizer
  | v  -- verbal categorizer
  | a  -- adjectival categorizer
  deriving DecidableEq, Repr

/-- Map a categorizer to its syntactic category. -/
def Categorizer.toCategory : Categorizer → Cat
  | .n => .N
  | .v => .V
  | .a => .A

-- ============================================================================
-- § 1b: Phi-Features on Categorizing Heads (@cite{kramer-2015} Ch 3)
-- ============================================================================

/-- Gender feature dimension. Different languages locate different
    binary features on n (@cite{kramer-2015} Chs 3, 5-7):

    - **FEM**: [±FEM] dimension (Amharic, Spanish, Maa, Dieri, Wari', Lavukaleve)
    - **MASC**: [±MASC] dimension (Jarawara; @cite{adamson-2024})
    - **ANIM**: [±ANIM] dimension (Algonquian, Teop, Lealao Chinantec) -/
inductive GenderDimension where
  | fem   -- [FEM] dimension
  | masc  -- [MASC] dimension
  | anim  -- [ANIM] dimension
  deriving DecidableEq, Repr

/-- Polarity of a gender feature value.
    The binary [±VAL] system from @cite{kramer-2015} Ch 3.

    Note: polarity is about the *feature value* (+/−), not about
    markedness. In Set 1 languages, u[+FEM] is the arbitrary gender;
    in Set 2, u[−FEM] is. Neither polarity is inherently "marked." -/
inductive Polarity where
  | pos  -- [+VAL]: positive polarity
  | neg  -- [−VAL]: negative polarity
  deriving DecidableEq, Repr

/-- A gender feature value: a dimension (what kind of feature) combined
    with a polarity (positive or negative).

    Examples:
    - `⟨.fem, .pos⟩` = [+FEM] (female, as in Amharic *innat* 'mother')
    - `⟨.fem, .neg⟩` = [−FEM] (male, as in Amharic *abbat* 'father')
    - `⟨.anim, .pos⟩` = [+ANIM] (animate, as in Teop body-part nouns)
    - `⟨.masc, .pos⟩` = [+MASC] (masculine, as in Jarawara) -/
structure GenderVal where
  dim : GenderDimension
  pol : Polarity
  deriving DecidableEq, Repr

/-- Feature interpretability (@cite{kramer-2015} §3.4.2).

    - **Interpretable** (natural gender): legible at LF, restricts the
      denotation to male/female referents. Licensed by Encyclopedia (List 3).
    - **Uninterpretable** (arbitrary gender): invisible at LF, visible
      only at PF. Licensed by Vocabulary Insertion (List 2). -/
inductive Interpretability where
  | i  -- interpretable (natural gender)
  | u  -- uninterpretable (arbitrary gender)
  deriving DecidableEq, Repr

/-- Feature contrastivity (@cite{konnelly-cowper-2020} §4, following
    @cite{wiltschko-2008}).

    Orthogonal to `Interpretability`. A feature can be both interpretable
    (visible at LF when present) and non-contrastive (its absence carries
    no semantic content).

    - **Contrastive**: absence is meaningful — "not [F]" is distinct from
      having no specification. In a context where [F] could appear, its
      absence is interpreted as ¬F. Gender features at K&C Stage 1.
    - **NonContrastive**: a modifier/adjunct whose presence adds meaning
      but whose absence is vacuous — it simply doesn't restrict the
      denotation. Gender features at K&C Stage 3. -/
inductive Contrastivity where
  | contrastive     -- absence = ¬F (privative but semantically active)
  | nonContrastive  -- absence = vacuous (optional modifier)
  deriving DecidableEq, Repr

/-- Whether a contrastive feature's presence is obligatory for referents
    with known values.

    A contrastive feature whose absence is meaningful (¬F) must be present
    when the referent has a known value — otherwise absence would wrongly
    convey ¬F. A non-contrastive feature is an optional modifier whose
    absence is vacuous, so it need not be present even for known values.

    @cite{wiltschko-2008}; applied to gender by @cite{konnelly-cowper-2020}. -/
def Contrastivity.obligatory : Contrastivity → Bool
  | .contrastive => true
  | .nonContrastive => false

/-- A gender feature annotated for interpretability.

    @cite{kramer-2015} Ch 3 identifies four attested combinations on n
    (per dimension):
    - i[+VAL]: natural gender, positive polarity (e.g. female)
    - i[−VAL]: natural gender, negative polarity (e.g. male)
    - u[+VAL]: arbitrary gender, positive polarity (Set 1: Amharic, Spanish)
    - u[−VAL]: arbitrary gender, negative polarity (Set 2: Maa, Wari')

    A fifth option is plain n with no gender feature at all (the default). -/
structure GenderFeature where
  interp : Interpretability
  val : GenderVal
  deriving DecidableEq, Repr

/-- Whether a gender feature is interpretable (natural). -/
def GenderFeature.isNatural : GenderFeature → Bool
  | ⟨.i, _⟩ => true
  | ⟨.u, _⟩ => false

/-- Whether a gender feature is uninterpretable (arbitrary). -/
def GenderFeature.isArbitrary : GenderFeature → Bool
  | ⟨.i, _⟩ => false
  | ⟨.u, _⟩ => true

/-- Number feature on the n head (@cite{kramer-2015} §3.5).

    **Split plurality**: irregular plurals are marked on n (within the
    categorization domain), while regular plurals are marked on Num
    (outside nP). Only irregular number lives on the categorizer. -/
inductive NumberOnN where
  | sg   -- singular (default/unmarked)
  | pl   -- irregular plural (e.g., Amharic broken plurals)
  deriving DecidableEq, Repr

/-- Phi-features hosted on a categorizing head.

    Following @cite{kramer-2015} Ch 3, the n head is the locus of gender
    features and (for irregular nouns) number features. The v and a heads
    do not host phi-features in the standard analysis. -/
structure PhiBundle where
  gender : Option GenderFeature := none
  number : Option NumberOnN := none
  deriving DecidableEq, Repr

instance : Inhabited PhiBundle := ⟨{}⟩

/-- A categorizing head enriched with phi-features and selectional properties.

    This extends the basic three-way `Categorizer` distinction with the
    feature content that @cite{kramer-2015} argues sits on the categorizer
    head. For n heads, this includes gender and (for irregular nouns) number.
    For v and a heads, the phi-bundle is typically empty.

    The `selectsD` field captures the selectional feature {D} from
    @cite{adamson-2024} (following Myler 2016): when true, the n head
    creates a specifier position for an iPossessor DP in Spec,nP. -/
structure CatHead where
  cat : Categorizer
  phi : PhiBundle := {}
  selectsD : Bool := false
  deriving DecidableEq, Repr

/-- The syntactic category of a phi-enriched categorizer head. -/
def CatHead.toCategory (ch : CatHead) : Cat :=
  ch.cat.toCategory

/-- An iPossessable n head: has {D} (selectsD = true) by construction.
    Use this for any n that licenses an iPossessor in Spec,nP.
    The phi-bundle determines gender; selectsD is not a free parameter.

    Examples:
    - Teop body-part n: `.iPoss { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }`
    - Jarawara iPossessable n: `.iPoss` (no gender feature → feminine)
    - Inherited-gender n: `.iPoss` (gender comes from iPossessor via Agree) -/
def CatHead.iPoss (phi : PhiBundle := {}) : CatHead where
  cat := .n
  phi := phi
  selectsD := true

/-- iPossessable n-heads always have selectsD = true, by construction. -/
theorem CatHead.iPoss_selectsD (phi : PhiBundle) :
    (CatHead.iPoss phi).selectsD = true := rfl

-- ============================================================================
-- § 1c: Kramer's Four Types of n (@cite{kramer-2015} Ch 3)
-- ============================================================================

/-! ### FEM dimension (Amharic, Spanish, Romance; @cite{kramer-2015} Chs 3, 6) -/

/-- n with interpretable [+FEM]: female natural gender.
    Examples: Amharic *-it* suffix on animate female nouns. -/
def CatHead.n_iFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.fem, .pos⟩⟩ }

/-- n with interpretable [−FEM]: male natural gender.
    Examples: Amharic animate male nouns.

    Note: `iMasc` is a mnemonic for the *gender* this n yields (masculine),
    not the feature dimension. The feature is i[−FEM] — negative polarity
    in the FEM dimension. For the separate MASC dimension used in
    Jarawara (@cite{adamson-2024}), see `n_uMasc`. -/
def CatHead.n_iMasc : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.fem, .neg⟩⟩ }

/-- Plain n: no gender feature. Default nominal categorizer.
    Examples: inanimate nouns with no gender marking. -/
def CatHead.n_plain : CatHead where
  cat := .n

/-- n with uninterpretable [+FEM]: feminine arbitrary gender.
    Examples: Amharic nouns arbitrarily assigned to feminine class
    (door, lip, sun, ear, eye).
    In Set 1 languages (@cite{kramer-2015} Chs 5-6), the u-feature
    has positive polarity, making feminine the arbitrary gender and
    masculine the default. Languages: Amharic, Spanish. -/
def CatHead.n_uFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.fem, .pos⟩⟩ }

/-- n with uninterpretable [−FEM]: masculine arbitrary gender in the
    FEM dimension. In Set 2 languages (@cite{kramer-2015} Ch 6), the
    u-feature has negative polarity, making masculine the arbitrary
    gender and feminine the default.
    Languages: Maa, Wari' (@cite{kramer-2015} Chs 6-7). -/
def CatHead.n_uNegFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.fem, .neg⟩⟩ }

/-- u[+FEM] and u[−FEM] are distinct n heads: Set 1 vs Set 2. -/
theorem u_fem_polarity_contrast :
    CatHead.n_uFem ≠ CatHead.n_uNegFem := by decide

/-! ### ANIM dimension (Teop, Algonquian, Lealao Chinantec;
    @cite{kramer-2015} Chs 5-6; @cite{adamson-2024} §3.1) -/

/-- n with interpretable [+ANIM]: animate natural gender.
    Examples: Teop gender I nouns (article *a*). -/
def CatHead.n_iAnim : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.anim, .pos⟩⟩ }

/-- n with interpretable [−ANIM]: inanimate natural gender.
    Examples: Teop gender II nouns (article *o*). -/
def CatHead.n_iInanim : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.anim, .neg⟩⟩ }

/-- n with uninterpretable [+ANIM]: animate arbitrary gender.
    Examples: Teop body-part n when iPossessed (@cite{adamson-2024} §3.1). -/
def CatHead.n_uAnim : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }

/-! ### MASC dimension (Jarawara; @cite{adamson-2024} §3.2)

    Note: Maa uses the FEM dimension (Set 2: u[−FEM]), not the MASC
    dimension. The MASC dimension is used only by Jarawara in our
    current coverage (@cite{adamson-2024} §3.2). -/

/-- n with uninterpretable [+MASC]: masculine arbitrary gender.
    In Jarawara, masculine is the marked gender;
    feminine is unmarked (plain n). -/
def CatHead.n_uMasc : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }

/-- Verbal categorizer (no phi-features). -/
def CatHead.v_plain : CatHead where
  cat := .v

/-- Adjectival categorizer (no phi-features). -/
def CatHead.a_plain : CatHead where
  cat := .a

-- ============================================================================
-- § 1d: Licensing Conditions (@cite{kramer-2015} §3.4)
-- ============================================================================

/-- Two types of root–n licensing condition (@cite{kramer-2015} §3.4.1).

    - **Semantic licensing** (Encyclopedia / List 3): restricts interpretation.
      A root with a female natural gender referent must combine with n i[+FEM]
      because the Encyclopedia entry is only defined in that context.
    - **Arbitrary licensing** (PF / List 2): restricts exponence.
      A root is listed in a VI rule's context as requiring [+FEM] on n,
      even though there is no semantic motivation. -/
inductive LicensingType where
  | semantic   -- Encyclopedia / List 3
  | arbitrary  -- PF / List 2
  deriving DecidableEq, Repr

/-- A root–n licensing condition: specifies that a particular root (identified
    by index) is licensed to combine with an n head bearing specific features,
    and the type of licensing (semantic or arbitrary). -/
structure RootLicense (RootIdx : Type) where
  rootIdx : RootIdx
  requiredGender : Option GenderFeature
  licensingType : LicensingType

/-- Whether a CatHead satisfies a licensing condition's gender requirement. -/
def CatHead.satisfiesLicense (ch : CatHead) (req : Option GenderFeature) : Bool :=
  match req with
  | none => ch.phi.gender.isNone
  | some gf => ch.phi.gender == some gf

/-- Whether a categorizer head licenses templatic [t]-intrusion in the
    sense of @cite{faust-2026} (11). The intruder is the exponent of
    `n[+gen]` (Kramer's `n_uFem` and similar): only nominal categorizers
    bearing a gender feature can host the bound-root /t/ exponent
    (@cite{lowenstamm-2014} sister-bound-root analysis). Verbal stems
    are blocked because gender is realized on the higher Agr head
    (@cite{kramer-2020}; @cite{faust-2026} (11)).

    The predicate is `cat = .n ∧ phi.gender ≠ none`. Used by
    `Phonology.Templates.RootTemplateMatch.intrusionLicensed` to filter
    `RootTemplateMatch` candidates with `intruder`-source associations. -/
def CatHead.licensesIntrusion (ch : CatHead) : Bool :=
  decide (ch.cat = .n) && ch.phi.gender.isSome

/-! #### Which canonical `CatHead`s license intrusion

Per-head verification of `licensesIntrusion` against Kramer's taxonomy.
Each theorem breaks if the corresponding canonical `CatHead`'s `cat` or
`phi.gender` field ever changes — making the licensing predictions of
@cite{faust-2026} (11) sensitive to the upstream Kramer-2015 data. -/

/-- u[+FEM] n licenses intrusion (canonical Set 1 feminine — Hebrew /t/
    exponent of taQTiL nouns, Amharic /t/ exponent of gerunds and INFs). -/
theorem n_uFem_licenses_intrusion :
    CatHead.n_uFem.licensesIntrusion = true := rfl

/-- i[+FEM] n licenses intrusion (interpretable feminine). -/
theorem n_iFem_licenses_intrusion :
    CatHead.n_iFem.licensesIntrusion = true := rfl

/-- i[−FEM] n licenses intrusion (interpretable masculine — Faust's
    argument is feature-symmetric: any [+gen] specification on n
    licenses an inherent exponent). -/
theorem n_iMasc_licenses_intrusion :
    CatHead.n_iMasc.licensesIntrusion = true := rfl

/-- Plain n (no gender feature) does NOT license intrusion. -/
theorem n_plain_blocks_intrusion :
    CatHead.n_plain.licensesIntrusion = false := rfl

/-- Verbal categorizer: never licenses intrusion (gender lives on Agr,
    not on v — @cite{faust-2026} (11)). -/
theorem v_plain_blocks_intrusion :
    CatHead.v_plain.licensesIntrusion = false := rfl

/-- Adjectival categorizer: no inherent gender exponent. -/
theorem a_plain_blocks_intrusion :
    CatHead.a_plain.licensesIntrusion = false := rfl

/-- Faust's central morphological prediction: intrusion is well-formed
    iff the categorizer is `n` AND carries a gender feature. The iff
    reduces to a Boolean computation on `CatHead.cat` and
    `CatHead.phi.gender`. -/
theorem licensesIntrusion_iff_n_and_gen (ch : CatHead) :
    ch.licensesIntrusion = true ↔ ch.cat = .n ∧ ch.phi.gender.isSome = true := by
  simp only [CatHead.licensesIntrusion, Bool.and_eq_true, decide_eq_true_eq]

-- ============================================================================
-- § 1e: Phi-Feature Verification
-- ============================================================================

/-- All four Amharic n types are nominal categorizers. -/
theorem four_n_types_are_nominal :
    CatHead.n_iFem.cat = .n ∧ CatHead.n_iMasc.cat = .n ∧
    CatHead.n_plain.cat = .n ∧ CatHead.n_uFem.cat = .n :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The four Amharic n types are pairwise distinct. -/
theorem four_n_types_distinct :
    CatHead.n_iFem ≠ CatHead.n_iMasc ∧
    CatHead.n_iFem ≠ CatHead.n_plain ∧
    CatHead.n_iFem ≠ CatHead.n_uFem ∧
    CatHead.n_iMasc ≠ CatHead.n_plain ∧
    CatHead.n_iMasc ≠ CatHead.n_uFem ∧
    CatHead.n_plain ≠ CatHead.n_uFem := by decide

/-- Natural gender features are interpretable. -/
theorem natural_gender_interpretable :
    (GenderFeature.mk .i ⟨.fem, .pos⟩).isNatural = true ∧
    (GenderFeature.mk .i ⟨.fem, .neg⟩).isNatural = true :=
  ⟨rfl, rfl⟩

/-- Arbitrary gender features are uninterpretable. -/
theorem arbitrary_gender_uninterpretable :
    (GenderFeature.mk .u ⟨.fem, .pos⟩).isArbitrary = true := rfl

/-- Plain n has no gender feature — it is the default/unmarked case. -/
theorem plain_n_no_gender : CatHead.n_plain.phi.gender = none := rfl

/-- Natural and arbitrary gender are mutually exclusive on any feature. -/
theorem natural_arbitrary_exclusive (gf : GenderFeature) :
    ¬(gf.isNatural = true ∧ gf.isArbitrary = true) := by
  cases gf with | mk interp val => cases interp <;> simp [GenderFeature.isNatural, GenderFeature.isArbitrary]

/-- Interpretable gender is semantically licensed; uninterpretable gender
    is arbitrarily licensed (@cite{kramer-2015} §3.4.1). -/
def GenderFeature.licensingType : GenderFeature → LicensingType
  | ⟨.i, _⟩ => .semantic
  | ⟨.u, _⟩ => .arbitrary

/-- Natural gender → semantic licensing. -/
theorem natural_semantic_licensing (gf : GenderFeature) (h : gf.isNatural = true) :
    gf.licensingType = .semantic := by
  cases gf with | mk interp val => cases interp <;> simp_all [GenderFeature.isNatural, GenderFeature.licensingType]

/-- Arbitrary gender → arbitrary licensing. -/
theorem arbitrary_arbitrary_licensing (gf : GenderFeature) (h : gf.isArbitrary = true) :
    gf.licensingType = .arbitrary := by
  cases gf with | mk interp val => cases interp <;> simp_all [GenderFeature.isArbitrary, GenderFeature.licensingType]

-- ============================================================================
-- § 1e-bridge: DM Gender → Minimalist Feature System
-- ============================================================================

/-- Canonical encoding of gender values as natural numbers for the
    Minimalism `PhiFeature.gender` constructor. Each dimension × polarity
    pair maps to a unique `Nat`. -/
def GenderVal.toNat : GenderVal → Nat
  | ⟨.fem, .pos⟩  => 0  -- [+FEM]
  | ⟨.fem, .neg⟩  => 1  -- [−FEM]
  | ⟨.masc, .pos⟩ => 2  -- [+MASC]
  | ⟨.masc, .neg⟩ => 3  -- [−MASC]
  | ⟨.anim, .pos⟩ => 4  -- [+ANIM]
  | ⟨.anim, .neg⟩ => 5  -- [−ANIM]

/-- The encoding is injective: distinct gender values get distinct `Nat`s. -/
theorem genderVal_toNat_injective (v1 v2 : GenderVal) (h : v1.toNat = v2.toNat) :
    v1 = v2 := by
  cases v1 with | mk d1 p1 => cases v2 with | mk d2 p2 =>
  cases d1 <;> cases p1 <;> cases d2 <;> cases p2 <;> simp_all [GenderVal.toNat]

/-- Map a DM gender feature to a Minimalist phi-feature. -/
def GenderFeature.toPhiFeature (gf : GenderFeature) : PhiFeature :=
  .gender gf.val.toNat

/-- Map a DM gender feature to a valued or unvalued grammatical feature,
    determined by interpretability: interpretable gender is valued
    (legible at LF), uninterpretable gender is unvalued (probe). -/
def GenderFeature.toGramFeature (gf : GenderFeature) : GramFeature :=
  match gf.interp with
  | .i => .valued (.phi gf.toPhiFeature)
  | .u => .unvalued (.phi gf.toPhiFeature)

/-- Interpretable gender maps to a valued feature. -/
theorem interpretable_gender_valued (gf : GenderFeature) (h : gf.interp = .i) :
    gf.toGramFeature = .valued (.phi (.gender gf.val.toNat)) := by
  simp [GenderFeature.toGramFeature, h, GenderFeature.toPhiFeature]

/-- Uninterpretable gender maps to an unvalued feature. -/
theorem uninterpretable_gender_unvalued (gf : GenderFeature) (h : gf.interp = .u) :
    gf.toGramFeature = .unvalued (.phi (.gender gf.val.toNat)) := by
  simp [GenderFeature.toGramFeature, h, GenderFeature.toPhiFeature]

/-- Amharic n i[+FEM] produces a valued gender feature. -/
theorem n_iFem_valued :
    (GenderFeature.mk .i ⟨.fem, .pos⟩).toGramFeature =
    .valued (.phi (.gender 0)) := rfl

/-- Amharic n u[+FEM] produces an unvalued gender feature (probe). -/
theorem n_uFem_unvalued :
    (GenderFeature.mk .u ⟨.fem, .pos⟩).toGramFeature =
    .unvalued (.phi (.gender 0)) := rfl

/-! ### Cross-dimensional verification -/

/-- Animacy-dimension n types are distinct from FEM-dimension types. -/
theorem anim_n_types_distinct :
    CatHead.n_iAnim ≠ CatHead.n_iFem ∧
    CatHead.n_iAnim ≠ CatHead.n_iMasc ∧
    CatHead.n_uAnim ≠ CatHead.n_uFem := by decide

/-- Animacy-dimension n types are distinct from plain n. -/
theorem anim_not_plain :
    CatHead.n_iAnim ≠ CatHead.n_plain ∧
    CatHead.n_uAnim ≠ CatHead.n_plain := by decide

-- ============================================================================
-- § 1f: Impoverishment (@cite{adamson-2024} §3.2; Bonet 1991)
-- ============================================================================

/-- A morphosyntactic context that can trigger impoverishment.

    @cite{adamson-2024} ex. 63: [MASC] → ∅ in context of [PL] or
    [PARTICIPANT]. Each context is a separate impoverishment rule. -/
inductive ImpoverishmentContext where
  | plural       -- [PL]: number feature
  | participant  -- [PARTICIPANT]: 1st/2nd person (speech act participants)
  deriving DecidableEq, Repr

/-- Impoverishment: postsyntactic deletion of morphosyntactic features.

    In DM, impoverishment rules apply after syntax but before Vocabulary
    Insertion, deleting features from terminal nodes. This can neutralize
    gender distinctions in certain contexts.

    @cite{adamson-2024} ex. 63: Jarawara [MASC] → ∅ in the context of
    [PL] or [PARTICIPANT]. -/
structure ImpoverishmentRule where
  /-- The feature to be deleted. -/
  targetGender : GenderVal
  /-- The conditioning context (feature that triggers deletion). -/
  context : ImpoverishmentContext
  deriving DecidableEq, Repr

/-- Apply impoverishment: if the rule matches, delete the gender feature. -/
def ImpoverishmentRule.apply (rule : ImpoverishmentRule)
    (phi : PhiBundle) (contextActive : Bool) : PhiBundle :=
  if contextActive then
    match phi.gender with
    | some gf => if gf.val == rule.targetGender
                 then { phi with gender := none }
                 else phi
    | none => phi
  else phi

-- ============================================================================
-- § 2: CategorizedRoot
-- ============================================================================

/-- A root that has been merged with a categorizing head, yielding a
    syntactically projectable unit (@cite{harley-2014} §2). -/
structure CategorizedRoot where
  /-- The acategorial root (arity, change-type, etc.) -/
  root : Root
  /-- The categorizing head that gives it syntactic category -/
  categorizer : Categorizer
  deriving BEq, Repr

/-- The syntactic category of a categorized root, derived from its categorizer. -/
def CategorizedRoot.category (cr : CategorizedRoot) : Cat :=
  cr.categorizer.toCategory

-- ============================================================================
-- § 3: Cross-Categorial Identity and Root Complement Selection
-- ============================================================================

/-- Same root + different categorizer → different syntactic category.
    This is the formal content of the claim that √HAMMER can surface as
    either a noun (hammer) or a verb (to hammer) — same root, different
    category, determined entirely by the categorizer (@cite{harley-2014} §2). -/
theorem same_root_different_category (r : Root) (c1 c2 : Categorizer)
    (h : c1 ≠ c2) :
    (CategorizedRoot.mk r c1).category ≠ (CategorizedRoot.mk r c2).category := by
  simp only [CategorizedRoot.category, Categorizer.toCategory]
  cases c1 <;> cases c2 <;> simp_all

/-- Complement **arity** (c-selection) is a root-level property, not
    contributed by the categorizer (@cite{harley-2014} §3). The root
    determines *whether* it takes an internal argument (selectsTheme vs
    noTheme); the categorizer does not alter this.

    **Note**: This theorem covers arity, not **l-selection** (which
    specific preposition heads the PP complement). @cite{hewett-2026}
    shows that l-selection in Semitic can vary by verbal template,
    falsifying any theory locating l-selection entirely at the root
    level. See `Hewett2026`.

    Evidence for root-level arity:

    1. *one*-replacement in argument structure nominals: "the proud owner
       of a large dog" → "the proud one" — *one* replaces nP including
       √OWN + complement, showing the root took its complement directly.
    2. Verb-object idioms: *kick the bucket* — √KICK selects *the bucket*
       directly under vP, not via mediation by v.
    3. Hiaki suppletive verbs: suppletive forms are conditioned by the
       root's complement (singular vs. plural object), showing locality
       between root and argument below the categorizer. -/
theorem complement_selection_at_root_level (r : Root) (c1 c2 : Categorizer) :
    (CategorizedRoot.mk r c1).root.arity = (CategorizedRoot.mk r c2).root.arity := rfl

/-- A theme-selecting root maintains its complement requirement regardless
    of whether it surfaces as a noun, verb, or adjective (@cite{harley-2014} §3). -/
theorem theme_selecting_root_always_selects (r : Root) (c : Categorizer)
    (h : r.arity = .selectsTheme) :
    (CategorizedRoot.mk r c).root.arity.hasInternalArg = true := by
  simp [h, RootArity.hasInternalArg]

-- ============================================================================
-- § 4: Layered Derivation (Denominal, Deadjectival, Deverbal)
-- ============================================================================

/-- Layered derivational morphology: a root categorized by one head can be
    further categorized by another, yielding derived forms. For example,
    √SHELF + n → shelf, then + v → to shelve (denominal verb).

    Harley (2014 §4) uses multiply derived words (*editor-ial*,
    *class-ifi-eds*, *national-ize*) to argue that idiosyncratic
    interpretation can extend past the first categorizer — the phase
    boundary is at Voice, not at the inner categorizer. -/
inductive Recategorization where
  | denominal    -- n → v (to hammer, to shelve)
  | deadjectival -- a → v (to flatten, to widen)
  | deverbal_n   -- v → n (a build, a throw)
  | deverbal_a   -- v → a (broken, flattened)
  deriving DecidableEq, Repr

/-- The source categorizer of a re-categorization. -/
def Recategorization.source : Recategorization → Categorizer
  | .denominal    => .n
  | .deadjectival => .a
  | .deverbal_n   => .v
  | .deverbal_a   => .v

/-- The target categorizer of a re-categorization. -/
def Recategorization.target : Recategorization → Categorizer
  | .denominal    => .v
  | .deadjectival => .v
  | .deverbal_n   => .n
  | .deverbal_a   => .a

/-- Apply a re-categorization to a categorized root. Returns `none` if the
    root's current categorizer doesn't match the expected source. -/
def CategorizedRoot.recategorize (cr : CategorizedRoot)
    (rc : Recategorization) : Option CategorizedRoot :=
  if cr.categorizer = rc.source then
    some { root := cr.root, categorizer := rc.target }
  else
    none

/-- Denominal verbs start from n-categorized roots. -/
theorem denominal_requires_n (cr : CategorizedRoot) (cr' : CategorizedRoot)
    (h : cr.recategorize .denominal = some cr') :
    cr.categorizer = .n := by
  unfold CategorizedRoot.recategorize at h
  simp only [Recategorization.source] at h
  split at h <;> simp_all

/-- Re-categorization yields the target categorizer. -/
theorem recategorization_changes_category (cr : CategorizedRoot)
    (rc : Recategorization) (cr' : CategorizedRoot)
    (h : cr.recategorize rc = some cr') :
    cr'.categorizer = rc.target := by
  unfold CategorizedRoot.recategorize at h
  split at h
  case isTrue => simp only [Option.some.injEq] at h; rw [← h]
  case isFalse => simp at h

/-- A denominal verb and a directly verbal root yield the same syntactic
    category (V), but have different internal structure. √HAMMER + v gives
    V directly; √HAMMER + n + v also gives V but via layered derivation.
    This structural ambiguity is invisible at the category level
    (@cite{harley-2014} §2). -/
theorem denominal_yields_verbal (r : Root) :
    ∃ cr, (CategorizedRoot.mk r .n).recategorize .denominal = some cr ∧
          cr.category = Cat.V :=
  ⟨⟨r, .v⟩, rfl, rfl⟩

/-- Deadjectival derivation (a → v) connects to @cite{embick-2004}'s resultStative structure: what RootTypology calls
    `AdjectivalStructure.resultStative` is, in DM terms, a root
    first categorized by a, then further categorized by v. -/
theorem deadjectival_source_target :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: VoiceP as Phase Boundary
-- ============================================================================

/- Harley (2014 §4) argues that the first phase head above the root is
   **Voice**, not the categorizer. Evidence:

   1. Multiply derived words can have idiosyncratic interpretations even
      above the first categorizer (*editorial* = related to editing,
      *classifieds* = classified ads, *nationalize* = make state-owned).
   2. Phrasal idioms (*kick the bucket*) involve idiosyncratic interpretation
      up to VoiceP but the external argument is always compositional.
   3. Agentive Voice introduces the external argument and closes off the
      domain of idiosyncratic interpretation.

   Formal consequence: categorizers are never phase heads,
   while `VoiceHead.phaseHead` can be `true`. -/

/-- Categorizers are never phase heads (@cite{harley-2014} §4). -/
def Categorizer.isPhaseHead : Categorizer → Bool
  | _ => false

/-- No categorizer is a phase head (@cite{harley-2014} §4). -/
theorem categorizer_never_phase (c : Categorizer) :
    c.isPhaseHead = false := by cases c <;> rfl

/-- Agentive Voice IS a phase head — it demarcates the boundary above which
    interpretation must be compositional (@cite{harley-2014} §4). -/
theorem agentive_voice_is_phase : voiceAgent.phaseHead = true := rfl

/-- The phase-boundary asymmetry: Voice can be a phase head while
    categorizers never are. This is why idiosyncratic interpretation
    extends past categorizers but not past Voice (@cite{harley-2014} §4). -/
theorem phase_boundary_at_voice_not_categorizer (c : Categorizer) :
    c.isPhaseHead = false ∧ voiceAgent.phaseHead = true :=
  ⟨by cases c <;> rfl, rfl⟩

/-- Voice introduces the external argument (@cite{harley-2014} §4, following
    @cite{kratzer-1996}). The categorizer does NOT introduce arguments —
    complement selection is a root property (§3). -/
theorem voice_introduces_external_arg :
    voiceAgent.hasD = true ∧ voiceAgent.assignsTheta = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Surface Gender Bridge (@cite{kramer-2020} §3; @cite{kramer-2015} Chs 5-7)
-- ============================================================================

/-! The bridge between DM phi-features on n and descriptive `SurfaceGender`
is mediated by Vocabulary Insertion (VI). Different VI systems yield
different surface genders from the same underlying features.

Three VI patterns are attested (@cite{kramer-2015} Chs 5-7):

- **Set 1** (Amharic, Spanish): [+FEM] → feminine, else → masculine (2 genders)
- **Set 2** (Maa, Wari'): [−FEM] → masculine, else → feminine (2 genders)
- **3-gender** (Russian, Mangarayi, Lavukaleve): [+FEM] → feminine,
  [−FEM] → masculine, no feature → neuter (3 genders)

For animacy-based systems (Teop, Algonquian), [+ANIM] → animate,
[−ANIM]/none → inanimate (2 genders). -/

open Core (SurfaceGender)

/-- Set 1 VI: [+FEM] → feminine, else → masculine.
    Default gender: masculine (plain n has no [+FEM]).
    Languages: Amharic, Spanish. (@cite{kramer-2015} Ch 6) -/
def CatHead.surfaceGenderSet1 (ch : CatHead) : SurfaceGender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .masculine

/-- Set 2 VI: [−FEM] → masculine, else → feminine.
    Default gender: feminine (plain n has no [−FEM]).
    Languages: Maa, Wari'. (@cite{kramer-2015} Ch 6) -/
def CatHead.surfaceGenderSet2 (ch : CatHead) : SurfaceGender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .neg⟩ then .masculine else .feminine
  | none    => .feminine

/-- Three-gender VI: [+FEM] → feminine, [−FEM] → masculine, none → neuter.
    Languages: Russian, Mangarayi, Lavukaleve. (@cite{kramer-2015} Ch 7) -/
def CatHead.surfaceGenderThree (ch : CatHead) : SurfaceGender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .neuter

/-- Animacy VI: [+ANIM] → animate, else → inanimate.
    Languages: Teop, Algonquian, Lealao Chinantec. (@cite{kramer-2015} Ch 5) -/
def CatHead.surfaceGenderAnimacy (ch : CatHead) : SurfaceGender :=
  match ch.phi.gender with
  | some gf => if gf.val.dim == .anim && gf.val.pol == .pos
               then .animate else .inanimate
  | none    => .inanimate

-- Verification: canonical n heads produce expected surface genders

theorem set1_verification :
    CatHead.n_iFem.surfaceGenderSet1 = .feminine ∧
    CatHead.n_iMasc.surfaceGenderSet1 = .masculine ∧
    CatHead.n_uFem.surfaceGenderSet1 = .feminine ∧
    CatHead.n_plain.surfaceGenderSet1 = .masculine := ⟨rfl, rfl, rfl, rfl⟩

theorem set2_verification :
    CatHead.n_iFem.surfaceGenderSet2 = .feminine ∧
    CatHead.n_iMasc.surfaceGenderSet2 = .masculine ∧
    CatHead.n_uNegFem.surfaceGenderSet2 = .masculine ∧
    CatHead.n_plain.surfaceGenderSet2 = .feminine := ⟨rfl, rfl, rfl, rfl⟩

theorem three_gender_verification :
    CatHead.n_iFem.surfaceGenderThree = .feminine ∧
    CatHead.n_iMasc.surfaceGenderThree = .masculine ∧
    CatHead.n_uFem.surfaceGenderThree = .feminine ∧
    CatHead.n_uNegFem.surfaceGenderThree = .masculine ∧
    CatHead.n_plain.surfaceGenderThree = .neuter := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem animacy_verification :
    CatHead.n_iAnim.surfaceGenderAnimacy = .animate ∧
    CatHead.n_iInanim.surfaceGenderAnimacy = .inanimate ∧
    CatHead.n_uAnim.surfaceGenderAnimacy = .animate ∧
    CatHead.n_plain.surfaceGenderAnimacy = .inanimate := ⟨rfl, rfl, rfl, rfl⟩

/-- Set 1 and Set 2 agree on natural gender (i[+FEM] → feminine,
    i[−FEM] → masculine) but differ on the default (plain n).
    @cite{kramer-2015} Ch 6: the polarity of u determines which
    gender is arbitrary vs default. -/
theorem set1_set2_default_contrast :
    CatHead.n_plain.surfaceGenderSet1 ≠ CatHead.n_plain.surfaceGenderSet2 := by
  decide

-- ============================================================================
-- § 7: Composed Morphisms: DM → Discourse
-- ============================================================================

open Core (GenderInfo)

/-- Composed morphism: DM categorizer → discourse-level gender knowledge.

    The chain `CatHead → SurfaceGender → GenderInfo` composes the structural
    mechanism (how gender is encoded on *n*) with the discourse layer (what
    participants know about a referent's gender). A noun whose categorizer head
    determines a surface gender always yields `.known g` at the discourse level.

    This is parameterized over a VI schema (Set 1, Set 2, Three, Animacy)
    because the structural → surface mapping is language-specific. -/
def CatHead.toGenderInfoSet1 (ch : CatHead) : GenderInfo :=
  ch.surfaceGenderSet1.toGenderInfo

def CatHead.toGenderInfoSet2 (ch : CatHead) : GenderInfo :=
  ch.surfaceGenderSet2.toGenderInfo

def CatHead.toGenderInfoThree (ch : CatHead) : GenderInfo :=
  ch.surfaceGenderThree.toGenderInfo

def CatHead.toGenderInfoAnimacy (ch : CatHead) : GenderInfo :=
  ch.surfaceGenderAnimacy.toGenderInfo

/-- The composition always yields `.known _` — a DM categorizer head
    always determines a concrete surface gender, so gender is never
    unspecified at the discourse level when the morphosyntax is fully
    resolved. Gender underspecification (@cite{arnold-2026}) arises
    from the discourse, not from the grammar. -/
theorem catHead_gender_always_known_set1 (ch : CatHead) :
    ∃ g, ch.toGenderInfoSet1 = .known g := by
  exact ⟨ch.surfaceGenderSet1, rfl⟩

theorem catHead_gender_always_known_three (ch : CatHead) :
    ∃ g, ch.toGenderInfoThree = .known g := by
  exact ⟨ch.surfaceGenderThree, rfl⟩

end Morphology.DM
