import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Linglib.Fragments.Arabic.ModernStandard.Phonology
import Linglib.Studies.Broe1993
import Linglib.Phonology.Subregular.ForbiddenPairs
import Linglib.Phonology.Subregular.Multitier

/-!
# Frisch, Pierrehumbert & Broe (2004) [frisch-pierrehumbert-broe-2004]

*Similarity avoidance and the OCP* argues that OCP-Place in Arabic verbal
roots is gradient: constraint strength is a quantitative function of the
similarity of the homorganic pair, where similarity is the natural-classes
metric of eq. (7) — shared natural classes over shared plus non-shared,
restricted to classes defined by a place feature. A larger, more
contrastive region of the inventory generates more natural classes, so any
coronal pair is automatically less similar than a comparable labial pair,
deriving the strong-coronal vs weak-dorsal/guttural asymmetry that
categorical class-based analyses ([mccarthy-1986], [mccarthy-1994],
[padgett-1995]) must stipulate.
-/

namespace FrischPierrehumbertBroe2004

open Arabic.ModernStandard

/-- The natural-classes similarity metric of eq. (7) (p. 198): shared
natural classes over shared plus non-shared. -/
def similarity {α : Type*} [DecidableEq α] (xs : List (Finset α)) (x y : α) : ℚ :=
  (xs.countP (λ s => decide (x ∈ s ∧ y ∈ s)) : ℚ) /
    xs.countP (λ s => decide (x ∈ s ∨ y ∈ s))

/-! ### Labial natural classes (p. 199) -/

/-- Labial natural classes for the /f, m/ computation (p. 199): the 2
shared classes, then the 7 non-shared. -/
def labialClasses_fm : List (Finset Consonant) :=
  [{.b, .f, .m, .w}, {.b, .f, .m},
   {.b, .f}, {.f, .w}, {.f}, {.b, .m, .w}, {.b, .m}, {.m, .w}, {.m}]

/-- Labial natural classes for the /b, f/ computation (p. 199): the 3
shared classes, then the 5 non-shared, verbatim from the paper. The
`{b, w}` entry is a substitution typo for `{f}` — matrix (8) generates
`{f}` and cannot generate `{b, w}` (`derived_bf_classes`) — leaving the
count, and the reported 3/8, correct. -/
def labialClasses_bf : List (Finset Consonant) :=
  [{.b, .f, .m, .w}, {.b, .f, .m}, {.b, .f},
   {.f, .w}, {.b, .m, .w}, {.b, .m}, {.b, .w}, {.b}]

/-- Worked example, p. 199. -/
theorem similarity_f_m : similarity labialClasses_fm .f .m = 2/9 := by decide +kernel

/-- Worked example, p. 199. -/
theorem similarity_b_f : similarity labialClasses_bf .b .f = 3/8 := by decide +kernel

/-! ### Deriving the classes from feature matrix (8)

`labialContext` records the labial columns of matrix (8), p. 201: [cons],
[son], [cont], [voice] on all four labials, [nasal] on the stops only
(trivial underspecification). [broe-1993]'s construction over this context
regenerates the /f, m/ enumeration exactly and vindicates the reported
3/8 for /b, f/ despite the printed list's typo. -/

/-- The labial columns of feature matrix (8) (p. 201): the extents on
`{b, f, m, w}` of the feature values the matrix specifies. -/
def labialContext : List (Finset Consonant) :=
  [{.b, .f, .m}, {.w},   -- [±cons]
   {.m, .w}, {.b, .f},   -- [±son]
   {.f, .w}, {.b, .m},   -- [±cont]
   {.m}, {.b},           -- [±nasal], specified for stops only
   {.b, .m, .w}, {.f}]   -- [±voice]

/-- The natural classes matrix (8) generates for the labial subinventory. -/
def derivedLabialClasses : List (Finset Consonant) :=
  Broe1993.naturalClasses {.b, .f, .m, .w} labialContext

/-- The derived classes relevant to /f, m/ are exactly the paper's
enumeration. -/
theorem derived_fm_classes :
    (derivedLabialClasses.filter
      (λ s => decide (Consonant.f ∈ s ∨ Consonant.m ∈ s))).toFinset =
      labialClasses_fm.toFinset := by decide +kernel

/-- The derived classes relevant to /b, f/ are the paper's enumeration with
`{f}` in place of `{b, w}`: no description over matrix (8) has extent
`{b, w}`. -/
theorem derived_bf_classes :
    (derivedLabialClasses.filter
      (λ s => decide (Consonant.b ∈ s ∨ Consonant.f ∈ s))).toFinset =
      insert {.f} (labialClasses_bf.toFinset.erase {.b, .w}) := by decide +kernel

/-- similarity(/f, m/) = 2/9, derived from matrix (8) rather than the
printed enumeration. -/
theorem similarity_derived_f_m : similarity derivedLabialClasses .f .m = 2/9 := by
  decide +kernel

/-- similarity(/b, f/) = 3/8, derived from matrix (8): the paper's reported
value is correct despite its list typo. -/
theorem similarity_derived_b_f : similarity derivedLabialClasses .b .f = 3/8 := by
  decide +kernel

/-! ### Table IV (p. 203): O/E by similarity, adjacent pairs -/

/-- The adjacent-pair column of Table IV: pairs of similarity-bin
representative (bin midpoint) and observed-over-expected co-occurrence
rate. O/E falls from 1.22 at similarity 0 to near zero from similarity 0.4
upward — the gradient pattern no two-valued model can match. -/
def adjacentPairOE : List (ℚ × ℚ) :=
  [(0,        122/100),
   (5/100,    105/100),
   (15/100,    83/100),
   (25/100,    59/100),
   (35/100,    32/100),
   (45/100,     3/100),
   (55/100,     6/100),
   (8/10,            0),
   (1,          1/100)]

/-! ### Gradient vs categorical: no threshold TSL₂ grammar fits Table IV

A TSL₂ grammar forbidding tier-adjacent pairs with `similarity ≥ t`
decides each labial pair by the two-valued step function `similarity < t`,
so as an O/E predictor it realises at most two values — one per side of
the threshold. Table IV has more than two distinct O/E levels, so no such
model fits it exactly. This is the corpus-free core of FPB's quantitative
argument; their own comparison is the R² fit of Table V. -/

variable (xs : List (Finset Consonant)) (t c₁ c₂ : ℚ)

/-- Step-function O/E prediction of a threshold model: `c₁` strictly below
the threshold `t`, `c₂` at or above it. -/
def categoricalAtThreshold (sim : ℚ) : ℚ :=
  if sim < t then c₁ else c₂

/-- The TSL₂ grammar over `Consonant` forbidding tier-adjacent labial pairs of
similarity at least `t` — [heinz-rawal-tanner-2011]'s forbidden-pair schema
instantiated with FPB's metric. -/
def thresholdedTSL : Subregular.TSLGrammar 2 Consonant :=
  Subregular.TSLGrammar.ofForbiddenPairs
    (λ x y => similarity xs x y ≥ t) Consonant.IsLabial

/-- **TSL₂ witness**: the threshold grammar's stringset is tier-based
strictly 2-local. -/
theorem thresholdedTSL_lang_isTSL2 :
    Language.IsTierStrictlyLocal 2 (thresholdedTSL xs t).lang :=
  (thresholdedTSL xs t).isTierStrictlyLocal_lang

/-- **BTSL₂ corollary**: the threshold grammar's stringset is in the
multitier closure of strictly local languages, hence consumed by the
[lambert-2026] BTC framework. -/
theorem thresholdedTSL_lang_isBTSL2 :
    Language.IsBTSL 2 (thresholdedTSL xs t).lang :=
  (thresholdedTSL_lang_isTSL2 xs t).toIsBTSL

/-- The threshold grammar accepts a labial pair iff its similarity is
strictly below the threshold — the precise sense in which any
similarity-threshold TSL₂ grammar collapses to the two-valued
`categoricalAtThreshold` prediction. -/
theorem thresholdedTSL_pair_iff {x y : Consonant} (hx : x.IsLabial) (hy : y.IsLabial) :
    [x, y] ∈ (thresholdedTSL xs t).lang ↔ similarity xs x y < t := by
  unfold thresholdedTSL
  rw [Subregular.mem_ofForbiddenPairs_lang_iff_filter_isChain]
  simp only [List.filter_cons, decide_eq_true hx, decide_eq_true hy, ↓reduceIte,
    List.filter_nil, List.isChain_cons_cons, List.isChain_singleton, and_true, not_le]

/-- **No exact categorical fit to Table IV**: for every threshold `t` and
predicted rates `c₁, c₂`, some Table IV bin is missed. A threshold model
realises at most two O/E values, but Table IV contains at least three
(1.22, 0.59, 0.06). FPB's own argument is the aggregate R² comparison of
Table V (p. 207: categorical 0.70 vs natural classes 0.75), which requires
the [cowan-1979] corpus; the exact-fit impossibility here is its
corpus-free core. -/
theorem categorical_cannot_fit_adjacentPairOE :
    ¬ ∀ p ∈ adjacentPairOE, categoricalAtThreshold t c₁ c₂ p.1 = p.2 := by
  intro hfit
  have h₁ := hfit (0, 122/100) (by norm_num [adjacentPairOE])
  have h₂ := hfit (25/100, 59/100) (by norm_num [adjacentPairOE])
  have h₃ := hfit (55/100, 6/100) (by norm_num [adjacentPairOE])
  simp only [categoricalAtThreshold] at h₁ h₂ h₃
  split_ifs at h₁ h₂ h₃ <;> linarith

end FrischPierrehumbertBroe2004
