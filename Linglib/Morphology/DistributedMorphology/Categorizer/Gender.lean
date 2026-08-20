import Linglib.Features.Gender.Decomposition
import Linglib.Features.Gender.Interp
import Linglib.Morphology.DistributedMorphology.Categorizer.Basic

/-!
# Gender on the nominal categorizer

The nominal categorizer is the locus of grammatical gender: an n may
carry a valued gender feature (`Gender.Signed`), interpretable (natural)
or uninterpretable (arbitrary), and Vocabulary Insertion realizes the
result in the language's own gender system (`Gender.System`), falling
back to the system's morphosyntactic default. The attested realization
patterns — Set 1, Set 2, three-gender, animacy-based — differ only in
their system, and PF is blind to interpretability. DM features are the
non-hybrid fragment of `Gender.SplitFeature`, and the FEM slice of the
head inventory is `Gender.KramerN`.

## Main definitions

* `GenderFeature`, `Interpretability`, `Contrastivity` — gender features
  on n and their LF status
* `Categorizer.Head` — a categorizer with phi-features and the
  selectional feature {D}; `Categorizer.Head.gendered` builds the
  canonical inventory `n_iFem` … `n_uMasc`
* `Categorizer.Head.realizeGender` — Vocabulary Insertion into a
  `Gender.System`; `IsSet1` … `IsAnimacyBased` — the attested patterns
* `Categorizer.Head.LicensesIntrusion` — gender-conditioned templatic
  t-intrusion

## Main statements

* `toSplitFeature_not_isHybrid` — the DM calculus generates no hybrid
  features
* `realizeGender_congr` — PF is blind to interpretability
* `not_isSet1_and_isSet2` — the Set 1 vs Set 2 parameter is exclusive

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

/-- A valued gender feature (`Gender.Signed`) annotated for
interpretability. Per dimension this yields the four attested gendered
ns of [kramer-2015] Ch 3 — i[+VAL], i[−VAL], u[+VAL], u[−VAL] — beside
plain n with no feature. -/
structure GenderFeature where
  interp : Interpretability
  val : Gender.Signed
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

/-! ### The canonical head inventory ([kramer-2015] Ch 3)

FEM dimension: Amharic, Spanish, Romance ([kramer-2015] Chs 3, 6). ANIM:
Teop, Algonquian, Lealao Chinantec (Chs 5–6; [adamson-2024] §3.1). MASC:
Jarawara only ([adamson-2024] §3.2) — Maa's arbitrary masculine is
negative-polarity FEM, not MASC. -/

/-- The gendered nominal categorizer: n bearing the valued feature `v`
with interpretability `interp`. -/
def Categorizer.Head.gendered (interp : Interpretability)
    (v : Gender.Signed) : Categorizer.Head where
  categorizer := .n
  phi := { gender := some ⟨interp, v⟩ }

/-- Distinct feature content gives distinct heads — every pairwise
contrast in the inventory below, in one statement. -/
theorem Categorizer.Head.gendered_inj {i₁ i₂ : Interpretability}
    {v₁ v₂ : Gender.Signed} :
    gendered i₁ v₁ = gendered i₂ v₂ ↔ i₁ = i₂ ∧ v₁ = v₂ := by
  simp [Categorizer.Head.gendered, PhiBundle.mk.injEq]

/-- The n bearing interpretable [+FEM] — female natural gender. In
Amharic the female member of a same-root pair can carry the suffix *-it*
([kramer-2015] (10)). -/
def Categorizer.Head.n_iFem : Categorizer.Head := .gendered .i ⟨.fem, .pos⟩

/-- The n bearing interpretable [−FEM] — male natural gender. The name
gives the resulting gender: the feature is negative-polarity FEM, not the
MASC dimension of Jarawara (`n_uMasc`). -/
def Categorizer.Head.n_iMasc : Categorizer.Head := .gendered .i ⟨.fem, .neg⟩

/-- The plain n with no gender feature — the default nominal
categorizer. -/
def Categorizer.Head.n_plain : Categorizer.Head where
  categorizer := .n

/-- A gendered head is never the plain n. -/
theorem Categorizer.Head.gendered_ne_n_plain (interp : Interpretability)
    (v : Gender.Signed) : gendered interp v ≠ n_plain := by
  simp [Categorizer.Head.gendered, Categorizer.Head.n_plain]

/-- The n bearing uninterpretable [+FEM] — the arbitrary feminine of
Set 1 languages (Amharic, Spanish), leaving masculine as the default.
Amharic assigns it to a handful of inanimates such as *car*, *earth*,
*sun*, and *church* ([kramer-2015] (9), Ch 6). -/
def Categorizer.Head.n_uFem : Categorizer.Head := .gendered .u ⟨.fem, .pos⟩

/-- The n bearing uninterpretable [−FEM] — the arbitrary masculine of
Set 2, leaving feminine as the default (Maa, [kramer-2015] §6.3). -/
def Categorizer.Head.n_uNegFem : Categorizer.Head := .gendered .u ⟨.fem, .neg⟩

/-- The n bearing interpretable [+ANIM] — Teop gender I nouns, taking
the article *a*. -/
def Categorizer.Head.n_iAnim : Categorizer.Head := .gendered .i ⟨.anim, .pos⟩

/-- The n bearing interpretable [−ANIM] — Teop gender II nouns, taking
the article *o*. -/
def Categorizer.Head.n_iInanim : Categorizer.Head := .gendered .i ⟨.anim, .neg⟩

/-- The n bearing uninterpretable [+ANIM] — Teop's body-part n when
iPossessed ([adamson-2024] §3.1). -/
def Categorizer.Head.n_uAnim : Categorizer.Head := .gendered .u ⟨.anim, .pos⟩

/-- The n bearing uninterpretable [+MASC] — Jarawara's marked masculine,
with feminine as the unmarked plain n. [adamson-2024] (58) also allows the
interpretable variant, not modeled here. -/
def Categorizer.Head.n_uMasc : Categorizer.Head := .gendered .u ⟨.masc, .pos⟩

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

/-- The head licenses templatic [t]-intrusion: it is a nominal
categorizer bearing a gender feature, whose exponent the bound root
hosts ([faust-2026] (11), [lowenstamm-2014]) — canonically Set 1
feminine, the Hebrew /t/ of taQTiL nouns and the Amharic /t/ of gerunds
and infinitives. Verbal stems are blocked because gender is realized on
the higher Agr head ([kramer-2020]). -/
def Categorizer.Head.LicensesIntrusion (ch : Categorizer.Head) : Prop :=
  ch.categorizer = .n ∧ ch.phi.gender.isSome

instance : DecidablePred Categorizer.Head.LicensesIntrusion :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Arbitrary gender is exactly the failure of natural gender: the two
interpretability classes partition the features. -/
theorem GenderFeature.isArbitrary_iff_not_isNatural (gf : GenderFeature) :
    gf.IsArbitrary ↔ ¬ gf.IsNatural := by
  cases gf with | mk interp val =>
  cases interp <;> simp [GenderFeature.IsNatural, GenderFeature.IsArbitrary]

/-- Interpretable gender is semantically licensed and uninterpretable
gender arbitrarily ([kramer-2015] §3.4.1). -/
def GenderFeature.licensingType : GenderFeature → LicensingType
  | ⟨.i, _⟩ => .semantic
  | ⟨.u, _⟩ => .arbitrary

@[simp] theorem GenderFeature.licensingType_i (v : Gender.Signed) :
    (GenderFeature.mk .i v).licensingType = .semantic := rfl

@[simp] theorem GenderFeature.licensingType_u (v : Gender.Signed) :
    (GenderFeature.mk .u v).licensingType = .arbitrary := rfl

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
    Gender.SplitFeature Gender.Signed :=
  match gf.interp with
  | .i => ⟨some gf.val, some gf.val⟩
  | .u => ⟨some gf.val, none⟩

/-- The gender half of a phi-bundle as a split feature, absent for plain
heads. -/
def PhiBundle.genderSplit (phi : PhiBundle) : Gender.SplitFeature Gender.Signed :=
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

/-! ### Vocabulary Insertion into a gender system

The bridge from features on n to a language's genders is Vocabulary
Insertion into that language's own `Gender.System` — the carrier
discipline of `Features/Gender/Basic.lean`. One map covers the attested
patterns of [kramer-2015] Chs 5–7, which differ only in their system:
the valued feature is realized by `value`, and a bare n falls back to
the system's morphosyntactic default. -/

variable {G : Type*}

/-- Vocabulary Insertion of gender: realize the head's valued feature in
the language's own system, falling back to the system's default. -/
def Categorizer.Head.realizeGender (sys : Gender.System G)
    (value : Gender.Signed → G) (ch : Categorizer.Head) : G :=
  (ch.phi.gender.map fun gf => value gf.val).getD sys.default

@[simp] theorem realizeGender_gendered (sys : Gender.System G)
    (value : Gender.Signed → G) (interp : Interpretability)
    (v : Gender.Signed) :
    (Categorizer.Head.gendered interp v).realizeGender sys value = value v :=
  rfl

@[simp] theorem realizeGender_n_plain (sys : Gender.System G)
    (value : Gender.Signed → G) :
    Categorizer.Head.n_plain.realizeGender sys value = sys.default := rfl

/-- PF is blind to interpretability: heads carrying the same valued
feature realize alike, whatever their LF status — natural and arbitrary
gender receive the same Vocabulary Item ([kramer-2015]). -/
theorem realizeGender_congr (sys : Gender.System G)
    (value : Gender.Signed → G) {ch₁ ch₂ : Categorizer.Head}
    (h : ch₁.phi.gender.map (·.val) = ch₂.phi.gender.map (·.val)) :
    ch₁.realizeGender sys value = ch₂.realizeGender sys value := by
  have e : ∀ o : Option GenderFeature,
      o.map (fun gf => value gf.val) = (o.map (·.val)).map value := by
    intro o; cases o <;> rfl
  rw [Categorizer.Head.realizeGender, Categorizer.Head.realizeGender, e, e, h]

/-- Realization sees only what `Gender.KramerN.exponence` sees. -/
theorem realizeGender_ofKramerN (sys : Gender.System G)
    (value : Gender.Signed → G) (k₁ k₂ : Gender.KramerN)
    (h : k₁.exponence = k₂.exponence) :
    (Categorizer.Head.ofKramerN k₁).realizeGender sys value =
      (Categorizer.Head.ofKramerN k₂).realizeGender sys value := by
  refine realizeGender_congr sys value ?_
  cases k₁ <;> cases k₂ <;> first | rfl | exact absurd h (by decide)

/-! ### The attested realization patterns ([kramer-2015] Chs 5–7)

Each pattern is a constraint on the system's comparative labels: which
label the valued feature realizes and which label the default carries.
Set 1 and Set 2 share a feature inventory and differ only here. -/

/-- A Set 1 system: [+FEM] realizes the feminine-labeled gender and the
default is masculine-labeled (Amharic, Spanish; [kramer-2015] Ch 6). -/
def IsSet1 (sys : Gender.System G) (value : Gender.Signed → G) : Prop :=
  sys.label (value ⟨.fem, .pos⟩) = some .feminine
    ∧ sys.label sys.default = some .masculine

/-- A Set 2 system: [−FEM] realizes the masculine-labeled gender and the
default is feminine-labeled (Maa; [kramer-2015] §6.3). -/
def IsSet2 (sys : Gender.System G) (value : Gender.Signed → G) : Prop :=
  sys.label (value ⟨.fem, .neg⟩) = some .masculine
    ∧ sys.label sys.default = some .feminine

/-- A three-gender system: both FEM poles are realized and the default
is neuter-labeled (Mangarayi; [kramer-2015] §7.2 — the other Ch 7 case
studies add uninterpretable features to this inventory). -/
def IsThreeGender (sys : Gender.System G) (value : Gender.Signed → G) : Prop :=
  sys.label (value ⟨.fem, .pos⟩) = some .feminine
    ∧ sys.label (value ⟨.fem, .neg⟩) = some .masculine
    ∧ sys.label sys.default = some .neuter

/-- An animacy system: [+ANIM] realizes the animate-labeled gender and
the default is inanimate-labeled (Lealao Chinantec, [kramer-2015] §5.3;
Algonquian, §6.4; Teop, [adamson-2024]). -/
def IsAnimacyBased (sys : Gender.System G) (value : Gender.Signed → G) : Prop :=
  sys.label (value ⟨.anim, .pos⟩) = some .animate
    ∧ sys.label sys.default = some .inanimate

/-- The Set 1 vs Set 2 parameter is exclusive: their defaults carry
different labels. -/
theorem not_isSet1_and_isSet2 (sys : Gender.System G)
    (value : Gender.Signed → G) : ¬ (IsSet1 sys value ∧ IsSet2 sys value) :=
  fun ⟨h₁, h₂⟩ => by have := h₁.2.symm.trans h₂.2; simp at this

/-- In a Set 1 system, arbitrary-feminine n realizes the
feminine-labeled gender and plain n the masculine-labeled default. -/
theorem IsSet1.realize_labels {sys : Gender.System G}
    {value : Gender.Signed → G} (h : IsSet1 sys value) :
    sys.label (Categorizer.Head.n_uFem.realizeGender sys value)
        = some .feminine
      ∧ sys.label (Categorizer.Head.n_plain.realizeGender sys value)
        = some .masculine :=
  ⟨h.1, h.2⟩

/-- In a Set 2 system, arbitrary-masculine n realizes the
masculine-labeled gender and plain n the feminine-labeled default. -/
theorem IsSet2.realize_labels {sys : Gender.System G}
    {value : Gender.Signed → G} (h : IsSet2 sys value) :
    sys.label (Categorizer.Head.n_uNegFem.realizeGender sys value)
        = some .masculine
      ∧ sys.label (Categorizer.Head.n_plain.realizeGender sys value)
        = some .feminine :=
  ⟨h.1, h.2⟩

/-- Set 1 is realizable: the two-gender system over `Bool` with `true`
the feminine-labeled class. -/
example : IsSet1 (G := Bool)
    ⟨fun b => some (if b then .feminine else .masculine), false⟩
    (fun v => v == ⟨.fem, .pos⟩) := by
  constructor <;> rfl

/-! ### Discourse-level gender -/

/-- The discourse-level gender information a head determines: the
comparative label of its realized gender, unspecified where the system
leaves the class unlabeled. -/
def Categorizer.Head.genderInfo (sys : Gender.System G)
    (value : Gender.Signed → G) (ch : Categorizer.Head) : GenderInfo :=
  (sys.label (ch.realizeGender sys value)).elim .unspecified .known

/-- In a fully labeled system the grammar always determines a concrete
discourse gender: underspecification ([arnold-2026]) arises from the
discourse, not from a resolved morphosyntax. -/
theorem genderInfo_known (sys : Gender.System G)
    (value : Gender.Signed → G) (hlab : ∀ g, (sys.label g).isSome)
    (ch : Categorizer.Head) :
    ∃ g, ch.genderInfo sys value = .known g := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (hlab (ch.realizeGender sys value))
  exact ⟨g, by simp [Categorizer.Head.genderInfo, hg]⟩

end DistributedMorphology
