import Linglib.Features.Gender.Decomposition
import Linglib.Features.Gender.Interp
import Linglib.Morphology.DistributedMorphology.Defs
import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Categorizing heads

A categorizing head n, v, or a merges with an acategorial root to give it a
syntactic category — the categorization assumption. The nominal categorizer
is also the locus of grammatical gender: an n may carry an interpretable
(natural) or uninterpretable (arbitrary) gender feature, and
language-particular Vocabulary Insertion maps the resulting inventory to
surface genders. Complement selection is a property of the root, and the
domain of idiosyncratic interpretation is bounded by Voice, not by the
categorizer.

## Main definitions

* `GenderVal`, `GenderFeature`, `Interpretability`, `Contrastivity` —
  gender features on n and their LF status
* `CatHead` — a categorizer with phi-features and the selectional feature
  {D}; canonical heads `CatHead.n_iFem` … `CatHead.n_uMasc`
* `CatHead.surfaceGenderSet1`/`Set2`/`Three`/`Animacy` — the attested
  Vocabulary-Insertion maps from features to surface gender
* `RootLicense`, `CatHead.licensesIntrusion` — root–n licensing and
  gender-conditioned templatic t-intrusion
* `CategorizedRoot`, `Recategorization` — roots under a categorizer and
  layered derivation

## Main statements

* `same_root_different_category`, `recategorize_preserves_index` — one
  root index across categories, threaded unchanged through derivation
* `agentive_voice_is_phase` — Voice, not the categorizer, bounds special
  interpretation

## References

* [H. Harley, *On the identity of roots*][harley-2014]
* [D. Embick and A. Marantz, *Architecture and blocking*][embick-marantz-2008]
* [R. Kramer, *The morphosyntax of gender*][kramer-2015]
* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
* [L. Konnelly and E. Cowper, *Gender diversity and morphosyntax*][konnelly-cowper-2020]
-/

namespace DistributedMorphology

open Minimalist Minimalist.Voice
open Verb Verb.Root

/-! ### Categorizer Type -/

/-- The syntactic category of a categorizer. -/
def Categorizer.toCategory : Categorizer → Cat
  | .n => .N
  | .v => .V
  | .a => .A

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
([adamson-2024], following [myler-2016]'s convention). -/
structure CatHead where
  /-- The categorizer n, v, or a. -/
  cat : Categorizer
  /-- The gender and number content ([kramer-2015]). -/
  phi : PhiBundle := {}
  /-- The selectional feature {D} licensing an iPossessor. -/
  selectsD : Bool := false
  deriving DecidableEq, Repr

/-- The syntactic category of a phi-enriched categorizer head. -/
def CatHead.toCategory (ch : CatHead) : Cat :=
  ch.cat.toCategory

/-- An iPossessable n head — {D} by construction, with the phi-bundle
supplying any gender (Teop's body-part n carries u[+ANIM], Jarawara's is
bare). -/
def CatHead.iPoss (phi : PhiBundle := {}) : CatHead where
  cat := .n
  phi := phi
  selectsD := true

/-- iPossessable n-heads always have selectsD = true, by construction. -/
theorem CatHead.iPoss_selectsD (phi : PhiBundle) :
    (CatHead.iPoss phi).selectsD = true := rfl

/-! ### Kramer's Four Types of n ([kramer-2015] Ch 3) -/

/-! ### FEM dimension (Amharic, Spanish, Romance; [kramer-2015] Chs 3, 6) -/

/-- The n bearing interpretable [+FEM] — female natural gender. In
Amharic the female member of a same-root pair can carry the suffix *-it*
([kramer-2015] (10)). -/
def CatHead.n_iFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.fem, .pos⟩⟩ }

/-- The n bearing interpretable [−FEM] — male natural gender. The name
gives the resulting gender: the feature is negative-polarity FEM, not the
MASC dimension of Jarawara (`n_uMasc`). -/
def CatHead.n_iMasc : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.fem, .neg⟩⟩ }

/-- The plain n with no gender feature — the default nominal
categorizer. -/
def CatHead.n_plain : CatHead where
  cat := .n

/-- The n bearing uninterpretable [+FEM] — the arbitrary feminine of
Set 1 languages (Amharic, Spanish), leaving masculine as the default.
Amharic assigns it to a handful of inanimates such as *car*, *earth*,
*sun*, and *church* ([kramer-2015] (9), Ch 6). -/
def CatHead.n_uFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.fem, .pos⟩⟩ }

/-- The n bearing uninterpretable [−FEM] — the arbitrary masculine of
Set 2, leaving feminine as the default (Maa, [kramer-2015] §6.3). -/
def CatHead.n_uNegFem : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.fem, .neg⟩⟩ }

/-- u[+FEM] and u[−FEM] are distinct n heads: Set 1 vs Set 2. -/
theorem u_fem_polarity_contrast :
    CatHead.n_uFem ≠ CatHead.n_uNegFem := by decide

/-! ### ANIM dimension (Teop, Algonquian, Lealao Chinantec;
    [kramer-2015] Chs 5-6; [adamson-2024] §3.1) -/

/-- The n bearing interpretable [+ANIM] — Teop gender I nouns, taking
the article *a*. -/
def CatHead.n_iAnim : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.anim, .pos⟩⟩ }

/-- The n bearing interpretable [−ANIM] — Teop gender II nouns, taking
the article *o*. -/
def CatHead.n_iInanim : CatHead where
  cat := .n
  phi := { gender := some ⟨.i, ⟨.anim, .neg⟩⟩ }

/-- The n bearing uninterpretable [+ANIM] — Teop's body-part n when
iPossessed ([adamson-2024] §3.1). -/
def CatHead.n_uAnim : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }

/-! ### MASC dimension (Jarawara; [adamson-2024] §3.2)

Only Jarawara uses this dimension in the current coverage — Maa's
arbitrary masculine is negative-polarity FEM, not MASC. -/

/-- The n bearing uninterpretable [+MASC] — Jarawara's marked masculine,
with feminine as the unmarked plain n. [adamson-2024] (58) also allows the
interpretable variant, not modeled here. -/
def CatHead.n_uMasc : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }

/-- The verbal categorizer, with no phi-features. -/
def CatHead.v_plain : CatHead where
  cat := .v

/-- The adjectival categorizer, with no phi-features. -/
def CatHead.a_plain : CatHead where
  cat := .a

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

/-- Whether a CatHead satisfies a licensing condition's gender requirement. -/
def CatHead.satisfiesLicense (ch : CatHead) (req : Option GenderFeature) : Bool :=
  match req with
  | none => ch.phi.gender.isNone
  | some gf => ch.phi.gender == some gf

/-- Whether the head licenses templatic [t]-intrusion — the head is a
nominal categorizer bearing a gender feature, whose exponent the bound
root hosts ([faust-2026] (11), [lowenstamm-2014]). Verbal stems are
blocked because gender is realized on the higher Agr head
([kramer-2020]). -/
def CatHead.licensesIntrusion (ch : CatHead) : Bool :=
  decide (ch.cat = .n) && ch.phi.gender.isSome

/-! #### Intrusion licensing across the canonical heads -/

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

/-- The verbal categorizer never licenses intrusion, since gender is
realized on Agr rather than v ([faust-2026] (11)). -/
theorem v_plain_blocks_intrusion :
    CatHead.v_plain.licensesIntrusion = false := rfl

/-- The adjectival categorizer has no inherent gender exponent. -/
theorem a_plain_blocks_intrusion :
    CatHead.a_plain.licensesIntrusion = false := rfl

/-- Intrusion is well-formed iff the categorizer is n and carries a
gender feature ([faust-2026] (11)). -/
theorem licensesIntrusion_iff_n_and_gen (ch : CatHead) :
    ch.licensesIntrusion = true ↔ ch.cat = .n ∧ ch.phi.gender.isSome = true := by
  simp only [CatHead.licensesIntrusion, Bool.and_eq_true, decide_eq_true_eq]

/-! ### Phi-Feature Verification -/

/-- The four Amharic n types are pairwise distinct. -/
theorem four_n_types_distinct :
    CatHead.n_iFem ≠ CatHead.n_iMasc ∧
    CatHead.n_iFem ≠ CatHead.n_plain ∧
    CatHead.n_iFem ≠ CatHead.n_uFem ∧
    CatHead.n_iMasc ≠ CatHead.n_plain ∧
    CatHead.n_iMasc ≠ CatHead.n_uFem ∧
    CatHead.n_plain ≠ CatHead.n_uFem := by decide

/-- Plain n has no gender feature — it is the default/unmarked case. -/
theorem plain_n_no_gender : CatHead.n_plain.phi.gender = none := rfl

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
def CatHead.ofKramerN : Gender.KramerN → CatHead
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
    CatHead.n_iAnim ≠ CatHead.n_iFem ∧
    CatHead.n_iAnim ≠ CatHead.n_iMasc ∧
    CatHead.n_uAnim ≠ CatHead.n_uFem := by decide

/-- Animacy-dimension n types are distinct from plain n. -/
theorem anim_not_plain :
    CatHead.n_iAnim ≠ CatHead.n_plain ∧
    CatHead.n_uAnim ≠ CatHead.n_plain := by decide

/-! ### CategorizedRoot -/

/-- A root that has been merged with a categorizing head, yielding a
    syntactically projectable unit ([harley-2014] §2).

    `index` is DM's List-1 individuator — the acategorial atom `DistributedMorphology.Root`,
    an arbitrary tag carrying no form or meaning. It is what survives
    (re)categorization (`recategorize_preserves_index`), so it, not the
    `root` classification, is what makes √HAMMER *one* root across
    *hammer*/*to hammer*. `root` is the c-selection content (arity,
    change-type) the categorizer apparatus reads ([harley-2014] §3); unrelated roots may
    share it, so it cannot individuate. -/
structure CategorizedRoot where
  /-- The acategorial root index — DM's List-1 individuator (`DistributedMorphology.Root`). -/
  index : DistributedMorphology.Root
  /-- The acategorial root's c-selection content (arity, change-type, etc.) -/
  root : Classification
  /-- The categorizing head that gives it syntactic category -/
  categorizer : Categorizer
  deriving BEq, Repr

/-- The syntactic category of a categorized root, derived from its categorizer. -/
def CategorizedRoot.category (cr : CategorizedRoot) : Cat :=
  cr.categorizer.toCategory

/-! ### Cross-categorial identity and root complement selection

[harley-2014] §3's evidence that roots select their complements directly:
*one*-replacement (§3.1 — *this student of chemistry* rejects *that one of
physics* because the root selects the PP and projects √P, which *one*
targets), verb-object idioms (§3.2, after [kratzer-1996] — special
meanings arise for verb-object pairs while the agentive subject composes
freely), and morphological ergative splits (§3.3). Hiaki suppletion
conditioned by the object's number is the §2.1 sisterhood evidence. -/

/-- Same root + different categorizer → different syntactic category.
    This is the formal content of the claim that √HAMMER can surface as
    either a noun (hammer) or a verb (to hammer) — same root, different
    category, determined entirely by the categorizer ([harley-2014] §2). -/
theorem same_root_different_category (i : DistributedMorphology.Root) (r : Classification)
    (c1 c2 : Categorizer) (h : c1 ≠ c2) :
    (CategorizedRoot.mk i r c1).category ≠ (CategorizedRoot.mk i r c2).category := by
  simp only [CategorizedRoot.category, Categorizer.toCategory]
  cases c1 <;> cases c2 <;> simp_all

/-- Complement valency is a root-level property, unaltered by the
categorizer ([harley-2014] §3). This covers c-selection, not l-selection,
which [hewett-2026] shows can vary by verbal template (`Hewett2026`). -/
theorem complement_selection_at_root_level (i : DistributedMorphology.Root) (r : Classification)
    (c1 c2 : Categorizer) :
    (CategorizedRoot.mk i r c1).root.valency = (CategorizedRoot.mk i r c2).root.valency := rfl

/-! ### Layered Derivation (Denominal, Deadjectival, Deverbal) -/

/-- A re-categorization further categorizes an already categorized root,
as in √SHELF + n (*shelf*) + v (*to shelve*). Idiosyncratic
interpretation can survive the inner categorizer ([harley-2014] §4). -/
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
    some { index := cr.index, root := cr.root, categorizer := rc.target }
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

/-- The acategorial index survives (re)categorization: the individuating
    `DistributedMorphology.Root` atom is invariant under `recategorize`, so *shelf* (n) and
    *to shelve* (v) share one List-1 root ([harley-2014] §2, §4). This is
    the work DM's own individuator does that the `root` classification
    cannot — valency/change-type is shared by unrelated roots, the index is
    not — so it is the index, not the classification, that the derivational
    history threads unchanged. -/
theorem recategorize_preserves_index (cr cr' : CategorizedRoot)
    (rc : Recategorization) (h : cr.recategorize rc = some cr') :
    cr'.index = cr.index := by
  unfold CategorizedRoot.recategorize at h
  split at h
  case isTrue => simp only [Option.some.injEq] at h; rw [← h]
  case isFalse => simp at h

/-- A denominal verb and a directly verbal root yield the same syntactic
    category (V), but have different internal structure. √HAMMER + v gives
    V directly; √HAMMER + n + v also gives V but via layered derivation.
    This structural ambiguity is invisible at the category level
    ([harley-2014] §2). -/
theorem denominal_yields_verbal (i : DistributedMorphology.Root) (r : Classification) :
    ∃ cr, (CategorizedRoot.mk i r .n).recategorize .denominal = some cr ∧
          cr.category = Cat.V :=
  ⟨⟨i, r, .v⟩, rfl, rfl⟩

/-- Deadjectival derivation (a → v) connects to [embick-2004]'s result-stative
    structure ([AspP AspR [vP DP v_become √ROOT]]): in DM terms, a root first
    categorized by a, then further categorized by v. -/
theorem deadjectival_source_target :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

/-! ### VoiceP as phase boundary

[harley-2014] §4: the phase head above the root is Voice, not the
categorizer. Multiply derived words carry idiosyncratic senses above the
first categorizer ((36) *editor-ial*, *classifi-eds*, *national-ize*),
while the external argument that Voice introduces stays compositional. -/

/-- Agentive Voice is a phase head — the boundary above which
    interpretation must be compositional. [harley-2014] §4: "Voice is the
    phase head, not v"; the categorizer inventory here accordingly carries
    no phasal structure at all, so the special-interpretation domain
    extends past n, v, a and closes only at Voice. -/
theorem agentive_voice_is_phase : agentive.IsPhasal := by decide

/-- Voice introduces the external argument ([harley-2014] §4, following
    [kratzer-1996]). The categorizer does NOT introduce arguments —
    complement selection is a root property ([harley-2014] §3). -/
theorem voice_introduces_external_arg :
    agentive.HasD ∧ agentive.AssignsTheta := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Surface Gender Bridge ([kramer-2020]; [kramer-2015] Chs 5-7) -/

/-! The bridge from phi-features on n to descriptive `Gender` is
Vocabulary Insertion, so the same feature inventory surfaces differently
across languages; the four attested patterns follow
([kramer-2015] Chs 5–7). -/


/-- The Set 1 Vocabulary Insertion of Amharic and Spanish — [+FEM]
realizes feminine and everything else masculine, so the default is
masculine ([kramer-2015] Ch 6). -/
def CatHead.surfaceGenderSet1 (ch : CatHead) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .masculine

/-- The Set 2 Vocabulary Insertion of Maa — [−FEM] realizes masculine
and everything else feminine, so the default is feminine
([kramer-2015] §6.3). -/
def CatHead.surfaceGenderSet2 (ch : CatHead) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .neg⟩ then .masculine else .feminine
  | none    => .feminine

/-- The three-gender Vocabulary Insertion of Mangarayi — [+FEM] feminine,
[−FEM] masculine, no feature neuter ([kramer-2015] §7.2; the other Ch 7
case studies add uninterpretable features to this inventory). -/
def CatHead.surfaceGenderThree (ch : CatHead) : Gender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .neuter

/-- The animacy Vocabulary Insertion of Lealao Chinantec
([kramer-2015] §5.3), Algonquian (§6.4), and Teop ([adamson-2024]) —
[+ANIM] realizes animate and everything else inanimate. -/
def CatHead.surfaceGenderAnimacy (ch : CatHead) : Gender :=
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

/-- Set 1 surface gender sees only what `Gender.KramerN.exponence` sees —
interpretability is invisible at PF. -/
theorem surfaceGenderSet1_ofKramerN (k₁ k₂ : Gender.KramerN)
    (h : k₁.exponence = k₂.exponence) :
    (CatHead.ofKramerN k₁).surfaceGenderSet1 =
      (CatHead.ofKramerN k₂).surfaceGenderSet1 := by
  cases k₁ <;> cases k₂ <;> first | rfl | exact absurd h (by decide)

/-- Set 1 and Set 2 agree on natural gender but differ on the default
for plain n ([kramer-2015] Ch 6). -/
theorem set1_set2_default_contrast :
    CatHead.n_plain.surfaceGenderSet1 ≠ CatHead.n_plain.surfaceGenderSet2 := by
  decide

/-! ### Discourse-level gender

The composites `CatHead → Gender → GenderInfo` connect the structural
encoding of gender on n with what discourse participants know about a
referent's gender, one composite per Vocabulary-Insertion schema. -/

/-- The discourse-level gender a head determines under Set 1 insertion. -/
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
    resolved. Gender underspecification ([arnold-2026]) arises
    from the discourse, not from the grammar. -/
theorem catHead_gender_always_known_set1 (ch : CatHead) :
    ∃ g, ch.toGenderInfoSet1 = .known g := by
  exact ⟨ch.surfaceGenderSet1, rfl⟩

theorem catHead_gender_always_known_three (ch : CatHead) :
    ∃ g, ch.toGenderInfoThree = .known g := by
  exact ⟨ch.surfaceGenderThree, rfl⟩

end DistributedMorphology
