import Linglib.Features.Gender.Decomposition
import Linglib.Features.Gender.Interp
import Linglib.Morphology.DistributedMorphology.Categorizer.Basic

/-!
# Gender on the nominal categorizer

The nominal categorizer is the locus of grammatical gender: an n may
carry an interpretable (natural) or uninterpretable (arbitrary) gender
feature over a language-particular dimension, and language-particular
Vocabulary Insertion maps the resulting inventory to surface genders.
The apparatus is grounded in the general gender machinery of
`Features/Gender/` — dimensions are poles over `Gender`, DM features are
the non-hybrid fragment of `Gender.SplitFeature`, and the FEM slice of
the head inventory is `Gender.KramerN`.

## Main definitions

* `GenderVal`, `GenderFeature`, `Interpretability`, `Contrastivity` —
  gender features on n and their LF status
* `Categorizer.Head` — a categorizer with phi-features and the selectional feature
  {D}; canonical heads `Categorizer.Head.n_iFem` … `Categorizer.Head.n_uMasc`
* `Categorizer.Head.surfaceGenderSet1`/`Set2`/`Three`/`Animacy` — the attested
  Vocabulary-Insertion maps from features to surface gender
* `RootLicense`, `Categorizer.Head.licensesIntrusion` — root–n licensing and
  gender-conditioned templatic t-intrusion

## Main statements

* `toSplitFeature_not_isHybrid` — the DM calculus generates no hybrid
  features
* `surfaceGenderSet1_eq_surface` (and kin) — each insertion map realizes
  a valued feature at its `GenderVal.surface` pole, differing only in the
  default for plain n

## References

* [R. Kramer, *The morphosyntax of gender*][kramer-2015]
* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
* [L. Konnelly and E. Cowper, *Gender diversity and morphosyntax*][konnelly-cowper-2020]
* [P. W. Smith, *Feature mismatches*][smith-2015]
-/

namespace DistributedMorphology

open Minimalist Minimalist.Voice

/-! ### Phi-features on categorizing heads

Grammatical gender lives on n, as an interpretable (natural) or
uninterpretable (arbitrary) feature over a language-particular dimension
([kramer-2015]; [adamson-2024] for MASC and Teop). -/

/-- The binary feature dimension a language's gender system distinguishes
on n. -/
inductive GenderDimension where
  | fem   -- [±FEM]: Amharic, Spanish, Maa, and kin ([kramer-2015])
  | masc  -- [±MASC]: Jarawara ([adamson-2024] (58))
  | anim  -- [±ANIM]: Lealao Chinantec, Algonquian, Teop
  deriving DecidableEq, Repr

/-- The sign of a binary gender feature value. Neither sign is inherently
marked — which one the uninterpretable feature carries is the Set 1 vs.
Set 2 parameter ([kramer-2015] Ch 6). -/
inductive Polarity where
  | pos  -- [+VAL]: positive polarity
  | neg  -- [−VAL]: negative polarity
  deriving DecidableEq, Repr

/-- A gender feature value pairs a dimension with a sign — [+FEM],
[−FEM], [+ANIM], and so on. -/
structure GenderVal where
  dim : GenderDimension
  pol : Polarity
  deriving DecidableEq, Repr

/-- The descriptive gender at a dimension's positive pole. -/
def GenderDimension.positive : GenderDimension → Gender
  | .fem  => .feminine
  | .masc => .masculine
  | .anim => .animate

/-- The descriptive gender at a dimension's negative pole. -/
def GenderDimension.negative : GenderDimension → Gender
  | .fem  => .masculine
  | .masc => .feminine
  | .anim => .inanimate

/-- The descriptive gender a valued feature denotes — the dimension's pole
picked by the sign. -/
def GenderVal.surface (v : GenderVal) : Gender :=
  match v.pol with
  | .pos => v.dim.positive
  | .neg => v.dim.negative

/-- Surface gender underdetermines the feature: Maa's [−FEM] and
Jarawara's [+MASC] both surface as masculine, and drawing that featural
distinction is what the dimension inventory is for ([kramer-2015] §6.3
vs. [adamson-2024] §3.2). -/
theorem surface_femNeg_eq_mascPos :
    (GenderVal.mk .fem .neg).surface = (GenderVal.mk .masc .pos).surface := rfl

/-- Whether a gender feature is legible at LF ([kramer-2015] §3.4.2).
Interpretable gender is natural gender, restricting the denotation and
licensed through the Encyclopedia, while uninterpretable gender is
arbitrary, visible only at PF through Vocabulary Insertion. -/
inductive Interpretability where
  | i  -- interpretable: natural gender (List 3)
  | u  -- uninterpretable: arbitrary gender (List 2)
  deriving DecidableEq, Repr

/-- Whether the absence of a feature is itself meaningful
([wiltschko-2008]; applied to gender by [konnelly-cowper-2020] §4). A
contrastive feature's absence conveys ¬F, while a non-contrastive feature
is a modifier whose absence is vacuous. Orthogonal to
`Interpretability` — an interpretable feature can be non-contrastive. -/
inductive Contrastivity where
  | contrastive     -- absence = ¬F (K&C Stage 1 gender)
  | nonContrastive  -- absence = vacuous (K&C Stage 3 gender)
  deriving DecidableEq, Repr

/-- A contrastive feature must be present when the referent's value is
known, since its absence would wrongly convey ¬F — a non-contrastive
feature need not be. -/
def Contrastivity.obligatory : Contrastivity → Bool
  | .contrastive => true
  | .nonContrastive => false

/-- A gender feature value annotated for interpretability. Per dimension
this yields the four attested gendered ns of [kramer-2015] Ch 3 —
i[+VAL], i[−VAL], u[+VAL], u[−VAL] — beside plain n with no feature. -/
structure GenderFeature where
  interp : Interpretability
  val : GenderVal
  deriving DecidableEq, Repr

/-- Whether a gender feature is interpretable (natural). -/
def GenderFeature.IsNatural (g : GenderFeature) : Prop :=
  g.interp = .i

instance : DecidablePred GenderFeature.IsNatural :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Whether a gender feature is uninterpretable (arbitrary). -/
def GenderFeature.IsArbitrary (g : GenderFeature) : Prop :=
  g.interp = .u

instance : DecidablePred GenderFeature.IsArbitrary :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Number on the n head. Irregular plurals such as Amharic broken plurals
are marked on n inside the categorization domain, while the regular plural
*-otʃtʃ* realizes Num outside nP ([kramer-2015] §3.3, Ch 8). -/
inductive NumberOnN where
  | sg   -- singular (default/unmarked)
  | pl   -- irregular plural (e.g., Amharic broken plurals)
  deriving DecidableEq, Repr

/-- The phi-features a categorizing head hosts — gender and, for
irregular nouns, number on n, while v and a carry none
([kramer-2015] Ch 3). -/
structure PhiBundle where
  gender : Option GenderFeature := none
  number : Option NumberOnN := none
  deriving DecidableEq, Repr

instance : Inhabited PhiBundle := ⟨{}⟩

/-- A categorizing head with its phi-features and the selectional feature
{D}, which creates a specifier position for an iPossessor DP in Spec,nP
([adamson-2024], following [myler-2016]'s convention). A functional
morpheme is a feature bundle: `Categorizer.Head` is the head-leaf label of
`WordStructure Categorizer.Head`, the φ-enriched instance of word-internal
structure. -/
structure Categorizer.Head where
  /-- The categorizer n, v, or a. -/
  categorizer : Categorizer
  /-- The gender and number content ([kramer-2015]). -/
  phi : PhiBundle := {}
  /-- The selectional feature {D} licensing an iPossessor. -/
  selectsD : Bool := false
  deriving DecidableEq, Repr

/-- The syntactic category of a phi-enriched categorizer head. -/
def Categorizer.Head.toCategory (ch : Categorizer.Head) : Cat :=
  ch.categorizer.toCategory

/-- An iPossessable n head — {D} by construction, with the phi-bundle
supplying any gender (Teop's body-part n carries u[+ANIM], Jarawara's is
bare). -/
def Categorizer.Head.iPoss (phi : PhiBundle := {}) : Categorizer.Head where
  categorizer := .n
  phi := phi
  selectsD := true

/-- iPossessable n-heads always have selectsD = true, by construction. -/
theorem Categorizer.Head.iPoss_selectsD (phi : PhiBundle) :
    (Categorizer.Head.iPoss phi).selectsD = true := rfl

/-! ### Kramer's Four Types of n ([kramer-2015] Ch 3) -/

/-! ### FEM dimension (Amharic, Spanish, Romance; [kramer-2015] Chs 3, 6) -/

/-- The n bearing interpretable [+FEM] — female natural gender. In
Amharic the female member of a same-root pair can carry the suffix *-it*
([kramer-2015] (10)). -/
def Categorizer.Head.n_iFem : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.i, ⟨.fem, .pos⟩⟩ }

/-- The n bearing interpretable [−FEM] — male natural gender. The name
gives the resulting gender: the feature is negative-polarity FEM, not the
MASC dimension of Jarawara (`n_uMasc`). -/
def Categorizer.Head.n_iMasc : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.i, ⟨.fem, .neg⟩⟩ }

/-- The plain n with no gender feature — the default nominal
categorizer. -/
def Categorizer.Head.n_plain : Categorizer.Head where
  categorizer := .n

/-- The n bearing uninterpretable [+FEM] — the arbitrary feminine of
Set 1 languages (Amharic, Spanish), leaving masculine as the default.
Amharic assigns it to a handful of inanimates such as *car*, *earth*,
*sun*, and *church* ([kramer-2015] (9), Ch 6). -/
def Categorizer.Head.n_uFem : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.fem, .pos⟩⟩ }

/-- The n bearing uninterpretable [−FEM] — the arbitrary masculine of
Set 2, leaving feminine as the default (Maa, [kramer-2015] §6.3). -/
def Categorizer.Head.n_uNegFem : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.fem, .neg⟩⟩ }

/-- u[+FEM] and u[−FEM] are distinct n heads: Set 1 vs Set 2. -/
theorem u_fem_polarity_contrast :
    Categorizer.Head.n_uFem ≠ Categorizer.Head.n_uNegFem := by decide

/-! ### ANIM dimension (Teop, Algonquian, Lealao Chinantec;
    [kramer-2015] Chs 5-6; [adamson-2024] §3.1) -/

/-- The n bearing interpretable [+ANIM] — Teop gender I nouns, taking
the article *a*. -/
def Categorizer.Head.n_iAnim : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.i, ⟨.anim, .pos⟩⟩ }

/-- The n bearing interpretable [−ANIM] — Teop gender II nouns, taking
the article *o*. -/
def Categorizer.Head.n_iInanim : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.i, ⟨.anim, .neg⟩⟩ }

/-- The n bearing uninterpretable [+ANIM] — Teop's body-part n when
iPossessed ([adamson-2024] §3.1). -/
def Categorizer.Head.n_uAnim : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }

/-! ### MASC dimension (Jarawara; [adamson-2024] §3.2)

Only Jarawara uses this dimension in the current coverage — Maa's
arbitrary masculine is negative-polarity FEM, not MASC. -/

/-- The n bearing uninterpretable [+MASC] — Jarawara's marked masculine,
with feminine as the unmarked plain n. [adamson-2024] (58) also allows the
interpretable variant, not modeled here. -/
def Categorizer.Head.n_uMasc : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }

/-- The verbal categorizer, with no phi-features. -/
def Categorizer.Head.v_plain : Categorizer.Head where
  categorizer := .v

/-- The adjectival categorizer, with no phi-features. -/
def Categorizer.Head.a_plain : Categorizer.Head where
  categorizer := .a

/-- In the categorization configuration [n √], all φ-content sits on the
single head leaf and the single root leaf carries none: gender enters
nominal structure only through n ([kramer-2015]). -/
theorem heads_roots_categorize_ofRoot (ch : Categorizer.Head) (r : Root) :
    heads (categorize ch (ofRoot r)) = {ch}
      ∧ roots (categorize ch (ofRoot r)) = {r} := by
  constructor
  · rw [heads_categorize, heads_ofRoot, Multiset.cons_zero]
  · rw [roots_categorize, roots_ofRoot]

/-! ### Licensing Conditions ([kramer-2015] §3.4) -/

/-- How a root–n combination is licensed ([kramer-2015] §3.4.1). Semantic
licensing restricts interpretation — the Encyclopedia entry is defined
only under the matching n — while arbitrary licensing lists the root in a
Vocabulary Item's context at PF. -/
inductive LicensingType where
  | semantic   -- Encyclopedia / List 3
  | arbitrary  -- PF / List 2
  deriving DecidableEq, Repr

/-- A root–n licensing condition — which gender the n combining with a
given root must bear, and whether the licensing is semantic or
arbitrary. -/
structure RootLicense (RootIdx : Type) where
  /-- The licensed root. -/
  rootIdx : RootIdx
  /-- The gender requirement on n (`none` = plain n). -/
  requiredGender : Option GenderFeature
  /-- Semantic or arbitrary licensing. -/
  licensingType : LicensingType

/-- Whether a Categorizer.Head satisfies a licensing condition's gender requirement. -/
def Categorizer.Head.satisfiesLicense (ch : Categorizer.Head) (req : Option GenderFeature) : Bool :=
  match req with
  | none => ch.phi.gender.isNone
  | some gf => ch.phi.gender == some gf

/-- Whether the head licenses templatic [t]-intrusion — the head is a
nominal categorizer bearing a gender feature, whose exponent the bound
root hosts ([faust-2026] (11), [lowenstamm-2014]). Verbal stems are
blocked because gender is realized on the higher Agr head
([kramer-2020]). -/
def Categorizer.Head.licensesIntrusion (ch : Categorizer.Head) : Bool :=
  decide (ch.categorizer = .n) && ch.phi.gender.isSome

/-! #### Intrusion licensing across the canonical heads -/

/-- u[+FEM] n licenses intrusion (canonical Set 1 feminine — Hebrew /t/
    exponent of taQTiL nouns, Amharic /t/ exponent of gerunds and INFs). -/
theorem n_uFem_licenses_intrusion :
    Categorizer.Head.n_uFem.licensesIntrusion = true := rfl

/-- i[+FEM] n licenses intrusion (interpretable feminine). -/
theorem n_iFem_licenses_intrusion :
    Categorizer.Head.n_iFem.licensesIntrusion = true := rfl

/-- i[−FEM] n licenses intrusion (interpretable masculine — Faust's
    argument is feature-symmetric: any [+gen] specification on n
    licenses an inherent exponent). -/
theorem n_iMasc_licenses_intrusion :
    Categorizer.Head.n_iMasc.licensesIntrusion = true := rfl

/-- Plain n (no gender feature) does NOT license intrusion. -/
theorem n_plain_blocks_intrusion :
    Categorizer.Head.n_plain.licensesIntrusion = false := rfl

/-- The verbal categorizer never licenses intrusion, since gender is
realized on Agr rather than v ([faust-2026] (11)). -/
theorem v_plain_blocks_intrusion :
    Categorizer.Head.v_plain.licensesIntrusion = false := rfl

/-- The adjectival categorizer has no inherent gender exponent. -/
theorem a_plain_blocks_intrusion :
    Categorizer.Head.a_plain.licensesIntrusion = false := rfl

/-- Intrusion is well-formed iff the categorizer is n and carries a
gender feature ([faust-2026] (11)). -/
theorem licensesIntrusion_iff_n_and_gen (ch : Categorizer.Head) :
    ch.licensesIntrusion = true ↔ ch.categorizer = .n ∧ ch.phi.gender.isSome = true := by
  simp only [Categorizer.Head.licensesIntrusion, Bool.and_eq_true, decide_eq_true_eq]

/-! ### Phi-Feature Verification -/

/-- The four Amharic n types are pairwise distinct. -/
theorem four_n_types_distinct :
    Categorizer.Head.n_iFem ≠ Categorizer.Head.n_iMasc ∧
    Categorizer.Head.n_iFem ≠ Categorizer.Head.n_plain ∧
    Categorizer.Head.n_iFem ≠ Categorizer.Head.n_uFem ∧
    Categorizer.Head.n_iMasc ≠ Categorizer.Head.n_plain ∧
    Categorizer.Head.n_iMasc ≠ Categorizer.Head.n_uFem ∧
    Categorizer.Head.n_plain ≠ Categorizer.Head.n_uFem := by decide

/-- Plain n has no gender feature — it is the default/unmarked case. -/
theorem plain_n_no_gender : Categorizer.Head.n_plain.phi.gender = none := rfl

/-- Natural and arbitrary gender are mutually exclusive on any feature. -/
theorem natural_arbitrary_exclusive (gf : GenderFeature) :
    ¬(gf.IsNatural ∧ gf.IsArbitrary) := by
  cases gf with | mk interp val =>
  cases interp <;> simp [GenderFeature.IsNatural, GenderFeature.IsArbitrary]

/-- Interpretable gender is semantically licensed and uninterpretable
gender arbitrarily ([kramer-2015] §3.4.1). -/
def GenderFeature.licensingType : GenderFeature → LicensingType
  | ⟨.i, _⟩ => .semantic
  | ⟨.u, _⟩ => .arbitrary

/-- Natural gender → semantic licensing. -/
theorem natural_semantic_licensing (gf : GenderFeature) (h : gf.IsNatural) :
    gf.licensingType = .semantic := by
  cases gf with | mk interp val =>
  cases interp <;> simp_all [GenderFeature.IsNatural, GenderFeature.licensingType]

/-- Arbitrary gender → arbitrary licensing. -/
theorem arbitrary_arbitrary_licensing (gf : GenderFeature) (h : gf.IsArbitrary) :
    gf.licensingType = .arbitrary := by
  cases gf with | mk interp val =>
  cases interp <;> simp_all [GenderFeature.IsArbitrary, GenderFeature.licensingType]

/-! ### The split-feature reading

DM's gender features are the non-hybrid fragment of the split-feature
architecture of `Features/Gender/Decomposition.lean`: interpretable gender
values both halves of a `Gender.SplitFeature`, uninterpretable gender only
the morphological one. The FEM slice of the head inventory is
[kramer-2015]'s calculus `Gender.KramerN`. -/

/-- A DM gender feature as a split feature ([smith-2015] via
`Gender.SplitFeature`) — interpretable gender values both halves,
uninterpretable gender only the morphological one. -/
def GenderFeature.toSplitFeature (gf : GenderFeature) :
    Gender.SplitFeature GenderVal :=
  match gf.interp with
  | .i => ⟨some gf.val, some gf.val⟩
  | .u => ⟨some gf.val, none⟩

/-- The gender half of a phi-bundle as a split feature, absent for plain
heads. -/
def PhiBundle.genderSplit (phi : PhiBundle) : Gender.SplitFeature GenderVal :=
  (phi.gender.map GenderFeature.toSplitFeature).getD ⟨none, none⟩

/-- Natural gender in the DM sense is natural gender in the split-feature
sense. -/
theorem toSplitFeature_isNatural_iff (gf : GenderFeature) :
    gf.toSplitFeature.IsNatural ↔ gf.IsNatural := by
  cases gf with | mk interp val =>
  cases interp <;>
    simp [GenderFeature.toSplitFeature, Gender.SplitFeature.IsNatural,
      GenderFeature.IsNatural]

/-- Arbitrary gender in the DM sense is arbitrary gender in the
split-feature sense. -/
theorem toSplitFeature_isArbitrary_iff (gf : GenderFeature) :
    gf.toSplitFeature.IsArbitrary ↔ gf.IsArbitrary := by
  cases gf with | mk interp val =>
  cases interp <;>
    simp [GenderFeature.toSplitFeature, Gender.SplitFeature.IsArbitrary,
      GenderFeature.IsArbitrary]

/-- The DM calculus generates no hybrids — the mismatch zoo of
[smith-2015] lies outside it (cf.
`Gender.KramerN.toSplitFeature_not_isHybrid` for the FEM slice). -/
theorem toSplitFeature_not_isHybrid (gf : GenderFeature) :
    ¬ gf.toSplitFeature.IsHybrid := by
  cases gf with | mk interp val =>
  cases interp <;> rintro ⟨u, i, hu, hi, hne⟩ <;>
    simp_all [GenderFeature.toSplitFeature]

/-- A phi-bundle's split feature is absent exactly when the head is
plain. -/
theorem genderSplit_isAbsent_iff (phi : PhiBundle) :
    phi.genderSplit.IsAbsent ↔ phi.gender = none := by
  cases h : phi.gender with
  | none => simp [PhiBundle.genderSplit, h, Gender.SplitFeature.IsAbsent]
  | some gf =>
    cases gf with | mk interp val =>
    cases interp <;>
      simp [PhiBundle.genderSplit, h, GenderFeature.toSplitFeature,
        Gender.SplitFeature.IsAbsent]

/-- [kramer-2015]'s FEM-dimension calculus embeds into the head
inventory. -/
def Categorizer.Head.ofKramerN : Gender.KramerN → Categorizer.Head
  | .plain => .n_plain
  | .iFem  => .n_iFem
  | .iMasc => .n_iMasc
  | .uFem  => .n_uFem
  | .uMasc => .n_uNegFem

/-! ### DM Gender → Minimalist Feature System -/

/-- The encoding of gender values into the Minimalist
`PhiFeature.gender` numeral. -/
def GenderVal.toNat : GenderVal → Nat
  | ⟨.fem, .pos⟩  => 0  -- [+FEM]
  | ⟨.fem, .neg⟩  => 1  -- [−FEM]
  | ⟨.masc, .pos⟩ => 2  -- [+MASC]
  | ⟨.masc, .neg⟩ => 3  -- [−MASC]
  | ⟨.anim, .pos⟩ => 4  -- [+ANIM]
  | ⟨.anim, .neg⟩ => 5  -- [−ANIM]

/-- The encoding sends distinct gender values to distinct numerals. -/
theorem genderVal_toNat_injective (v1 v2 : GenderVal) (h : v1.toNat = v2.toNat) :
    v1 = v2 := by
  cases v1 with | mk d1 p1 => cases v2 with | mk d2 p2 =>
  cases d1 <;> cases p1 <;> cases d2 <;> cases p2 <;> simp_all [GenderVal.toNat]

/-- A DM gender feature as a Minimalist phi-feature. -/
def GenderFeature.toPhiFeature (gf : GenderFeature) : PhiFeature :=
  .gender gf.val.toNat

/-- A DM gender feature as a grammatical feature — valued when
interpretable, unvalued (a probe) when uninterpretable. -/
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
    Categorizer.Head.n_iAnim ≠ Categorizer.Head.n_iFem ∧
    Categorizer.Head.n_iAnim ≠ Categorizer.Head.n_iMasc ∧
    Categorizer.Head.n_uAnim ≠ Categorizer.Head.n_uFem := by decide

/-- Animacy-dimension n types are distinct from plain n. -/
theorem anim_not_plain :
    Categorizer.Head.n_iAnim ≠ Categorizer.Head.n_plain ∧
    Categorizer.Head.n_uAnim ≠ Categorizer.Head.n_plain := by decide

/-! ### Surface Gender Bridge ([kramer-2020]; [kramer-2015] Chs 5-7) -/

/-! The bridge from phi-features on n to descriptive `Gender` is
Vocabulary Insertion, so the same feature inventory surfaces differently
across languages; the four attested patterns follow
([kramer-2015] Chs 5–7). -/


/-- The Set 1 Vocabulary Insertion of Amharic and Spanish — [+FEM]
realizes feminine and everything else masculine, so the default is
masculine ([kramer-2015] Ch 6). -/
def Categorizer.Head.surfaceGenderSet1 (ch : Categorizer.Head) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .masculine

/-- The Set 2 Vocabulary Insertion of Maa — [−FEM] realizes masculine
and everything else feminine, so the default is feminine
([kramer-2015] §6.3). -/
def Categorizer.Head.surfaceGenderSet2 (ch : Categorizer.Head) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .neg⟩ then .masculine else .feminine
  | none    => .feminine

/-- The three-gender Vocabulary Insertion of Mangarayi — [+FEM] feminine,
[−FEM] masculine, no feature neuter ([kramer-2015] §7.2; the other Ch 7
case studies add uninterpretable features to this inventory). -/
def Categorizer.Head.surfaceGenderThree (ch : Categorizer.Head) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .neuter

/-- The animacy Vocabulary Insertion of Lealao Chinantec
([kramer-2015] §5.3), Algonquian (§6.4), and Teop ([adamson-2024]) —
[+ANIM] realizes animate and everything else inanimate. -/
def Categorizer.Head.surfaceGenderAnimacy (ch : Categorizer.Head) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val.dim == .anim && gf.val.pol == .pos
               then .animate else .inanimate
  | none    => .inanimate

-- Verification: canonical n heads produce expected surface genders

theorem set1_verification :
    Categorizer.Head.n_iFem.surfaceGenderSet1 = .feminine ∧
    Categorizer.Head.n_iMasc.surfaceGenderSet1 = .masculine ∧
    Categorizer.Head.n_uFem.surfaceGenderSet1 = .feminine ∧
    Categorizer.Head.n_plain.surfaceGenderSet1 = .masculine := ⟨rfl, rfl, rfl, rfl⟩

theorem set2_verification :
    Categorizer.Head.n_iFem.surfaceGenderSet2 = .feminine ∧
    Categorizer.Head.n_iMasc.surfaceGenderSet2 = .masculine ∧
    Categorizer.Head.n_uNegFem.surfaceGenderSet2 = .masculine ∧
    Categorizer.Head.n_plain.surfaceGenderSet2 = .feminine := ⟨rfl, rfl, rfl, rfl⟩

theorem three_gender_verification :
    Categorizer.Head.n_iFem.surfaceGenderThree = .feminine ∧
    Categorizer.Head.n_iMasc.surfaceGenderThree = .masculine ∧
    Categorizer.Head.n_uFem.surfaceGenderThree = .feminine ∧
    Categorizer.Head.n_uNegFem.surfaceGenderThree = .masculine ∧
    Categorizer.Head.n_plain.surfaceGenderThree = .neuter := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem animacy_verification :
    Categorizer.Head.n_iAnim.surfaceGenderAnimacy = .animate ∧
    Categorizer.Head.n_iInanim.surfaceGenderAnimacy = .inanimate ∧
    Categorizer.Head.n_uAnim.surfaceGenderAnimacy = .animate ∧
    Categorizer.Head.n_plain.surfaceGenderAnimacy = .inanimate := ⟨rfl, rfl, rfl, rfl⟩

/-! Each insertion map realizes a valued feature of its home dimension at
its `GenderVal.surface` pole — the four patterns differ only in the
default for plain n. -/

/-- On FEM-dimension bundles, Set 1 is surface realization with a
masculine default. -/
theorem surfaceGenderSet1_eq_surface (ch : Categorizer.Head)
    (h : ∀ gf ∈ ch.phi.gender, gf.val.dim = .fem) :
    ch.surfaceGenderSet1 = (ch.phi.gender.map (·.val.surface)).getD .masculine := by
  cases hg : ch.phi.gender with
  | none => simp [Categorizer.Head.surfaceGenderSet1, hg]
  | some gf =>
    obtain ⟨itp, d, pol⟩ := gf
    have hmem : (⟨itp, d, pol⟩ : GenderFeature) ∈ ch.phi.gender := by
      rw [hg]; rfl
    obtain rfl : d = .fem := h _ hmem
    cases pol <;>
      simp [Categorizer.Head.surfaceGenderSet1, hg, GenderVal.surface,
        GenderDimension.positive, GenderDimension.negative]

/-- On FEM-dimension bundles, Set 2 is surface realization with a
feminine default. -/
theorem surfaceGenderSet2_eq_surface (ch : Categorizer.Head)
    (h : ∀ gf ∈ ch.phi.gender, gf.val.dim = .fem) :
    ch.surfaceGenderSet2 = (ch.phi.gender.map (·.val.surface)).getD .feminine := by
  cases hg : ch.phi.gender with
  | none => simp [Categorizer.Head.surfaceGenderSet2, hg]
  | some gf =>
    obtain ⟨itp, d, pol⟩ := gf
    have hmem : (⟨itp, d, pol⟩ : GenderFeature) ∈ ch.phi.gender := by
      rw [hg]; rfl
    obtain rfl : d = .fem := h _ hmem
    cases pol <;>
      simp [Categorizer.Head.surfaceGenderSet2, hg, GenderVal.surface,
        GenderDimension.positive, GenderDimension.negative]

/-- On FEM-dimension bundles, the three-gender pattern is surface
realization with a neuter default. -/
theorem surfaceGenderThree_eq_surface (ch : Categorizer.Head)
    (h : ∀ gf ∈ ch.phi.gender, gf.val.dim = .fem) :
    ch.surfaceGenderThree = (ch.phi.gender.map (·.val.surface)).getD .neuter := by
  cases hg : ch.phi.gender with
  | none => simp [Categorizer.Head.surfaceGenderThree, hg]
  | some gf =>
    obtain ⟨itp, d, pol⟩ := gf
    have hmem : (⟨itp, d, pol⟩ : GenderFeature) ∈ ch.phi.gender := by
      rw [hg]; rfl
    obtain rfl : d = .fem := h _ hmem
    cases pol <;>
      simp [Categorizer.Head.surfaceGenderThree, hg, GenderVal.surface,
        GenderDimension.positive, GenderDimension.negative]

/-- On ANIM-dimension bundles, the animacy pattern is surface realization
with an inanimate default. -/
theorem surfaceGenderAnimacy_eq_surface (ch : Categorizer.Head)
    (h : ∀ gf ∈ ch.phi.gender, gf.val.dim = .anim) :
    ch.surfaceGenderAnimacy =
      (ch.phi.gender.map (·.val.surface)).getD .inanimate := by
  cases hg : ch.phi.gender with
  | none => simp [Categorizer.Head.surfaceGenderAnimacy, hg]
  | some gf =>
    obtain ⟨itp, d, pol⟩ := gf
    have hmem : (⟨itp, d, pol⟩ : GenderFeature) ∈ ch.phi.gender := by
      rw [hg]; rfl
    obtain rfl : d = .anim := h _ hmem
    cases pol <;>
      simp [Categorizer.Head.surfaceGenderAnimacy, hg, GenderVal.surface,
        GenderDimension.positive, GenderDimension.negative]

/-- Set 1 surface gender sees only what `Gender.KramerN.exponence` sees —
interpretability is invisible at PF. -/
theorem surfaceGenderSet1_ofKramerN (k₁ k₂ : Gender.KramerN)
    (h : k₁.exponence = k₂.exponence) :
    (Categorizer.Head.ofKramerN k₁).surfaceGenderSet1 =
      (Categorizer.Head.ofKramerN k₂).surfaceGenderSet1 := by
  cases k₁ <;> cases k₂ <;> first | rfl | exact absurd h (by decide)

/-- Set 1 and Set 2 agree on natural gender but differ on the default
for plain n ([kramer-2015] Ch 6). -/
theorem set1_set2_default_contrast :
    Categorizer.Head.n_plain.surfaceGenderSet1 ≠ Categorizer.Head.n_plain.surfaceGenderSet2 := by
  decide

/-! ### Discourse-level gender

The composites `Categorizer.Head → Gender → GenderInfo` connect the structural
encoding of gender on n with what discourse participants know about a
referent's gender, one composite per Vocabulary-Insertion schema. -/

/-- The discourse-level gender a head determines under Set 1 insertion. -/
def Categorizer.Head.toGenderInfoSet1 (ch : Categorizer.Head) : GenderInfo :=
  ch.surfaceGenderSet1.toGenderInfo

def Categorizer.Head.toGenderInfoSet2 (ch : Categorizer.Head) : GenderInfo :=
  ch.surfaceGenderSet2.toGenderInfo

def Categorizer.Head.toGenderInfoThree (ch : Categorizer.Head) : GenderInfo :=
  ch.surfaceGenderThree.toGenderInfo

def Categorizer.Head.toGenderInfoAnimacy (ch : Categorizer.Head) : GenderInfo :=
  ch.surfaceGenderAnimacy.toGenderInfo

/-- The composition always yields `.known _` — a DM categorizer head
    always determines a concrete surface gender, so gender is never
    unspecified at the discourse level when the morphosyntax is fully
    resolved. Gender underspecification ([arnold-2026]) arises
    from the discourse, not from the grammar. -/
theorem catHead_gender_always_known_set1 (ch : Categorizer.Head) :
    ∃ g, ch.toGenderInfoSet1 = .known g := by
  exact ⟨ch.surfaceGenderSet1, rfl⟩

theorem catHead_gender_always_known_three (ch : Categorizer.Head) :
    ∃ g, ch.toGenderInfoThree = .known g := by
  exact ⟨ch.surfaceGenderThree, rfl⟩

end DistributedMorphology
