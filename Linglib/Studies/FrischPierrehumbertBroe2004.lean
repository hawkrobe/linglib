import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
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

## Main definitions

* `similarity`: the natural-classes metric of eq. (7) (p. 198), relative
  to a list of relevant classes.
* `Arabic`: the paper's 28-consonant inventory (feature matrix (8), p. 201).
* `adjacentPairOE`: the adjacent-pair O/E data of Table IV (p. 203).
* `thresholdedTSL`: the TSL₂ grammar forbidding tier-adjacent labial pairs
  of similarity at least `t`, via `Subregular.TSLGrammar.ofForbiddenPairs`.

## Main results

* `similarity_f_m`, `similarity_b_f`: the paper's worked examples,
  similarity(/f, m/) = 2/9 and similarity(/b, f/) = 3/8 (p. 199).
* `thresholdedTSL_pair_iff`: the threshold grammar accepts a labial pair
  iff its similarity is strictly below the threshold, so its decision is a
  two-valued step function of similarity.
* `categorical_cannot_fit_adjacentPairOE`: no two-valued threshold model
  reproduces Table IV, which has at least three distinct O/E levels — the
  corpus-free core of FPB's model comparison.

## Implementation notes

The paper's own model comparison is an R² fit across the nine Table IV
bins (Table V, p. 207: categorical 0.70 vs natural classes 0.75). It and
the converging §4 evidence — the [frisch-zawaydeh-2001] wordlikeness
experiments, Maltese borrowings from Italian ([mifsud-1995]),
cross-linguistic attestations (Tigrinya [buckley-1997-ocp], English
[berkley-1994], Thai [frisch-2000a]), and the processing-difficulty origin
([berg-1998], [boersma-1998], [frisch-1996]; misordering errors in
[abd-el-jawad-abu-salim-1987]) — require the 2,674-root [cowan-1979]
corpus or experimental data, and are out of scope.
-/

namespace FrischPierrehumbertBroe2004

/-! ### The natural-classes similarity metric (eq. (7), p. 198) -/

variable {α : Type*} [DecidableEq α]

/-- Number of natural classes in `xs` containing both `x` and `y` — the
numerator of eq. (7). -/
def sharedClasses (xs : List (Finset α)) (x y : α) : ℕ :=
  xs.countP (λ s => decide (x ∈ s ∧ y ∈ s))

/-- Number of natural classes in `xs` containing `x` or `y` — shared plus
non-shared, the denominator of eq. (7). -/
def totalRelevantClasses (xs : List (Finset α)) (x y : α) : ℕ :=
  xs.countP (λ s => decide (x ∈ s ∨ y ∈ s))

/-- **Eq. (7)**: similarity as shared over shared-plus-non-shared natural
classes, relative to a list `xs` of relevant classes (for OCP-Place, those
defined by a place feature, per p. 198). Identical segments sharing a class
get similarity 1, segments sharing no relevant class get 0 (`0 / 0 = 0` in
`ℚ` covers pairs contained in no relevant class at all). -/
def similarity (xs : List (Finset α)) (x y : α) : ℚ :=
  (sharedClasses xs x y : ℚ) / totalRelevantClasses xs x y

/-! ### The Arabic consonant inventory (feature matrix (8), p. 201) -/

/-- The 28-consonant Arabic inventory of [frisch-pierrehumbert-broe-2004]'s
feature matrix (8), IPA with `Emph` for the emphatic (superscript ˁ)
series. The worked examples and the thresholded grammars below use only the
labial subinventory `{b, f, m, w}`. -/
inductive Arabic where
  /-- /b/ — voiced labial stop. -/
  | b
  /-- /f/ — voiceless labial fricative. -/
  | f
  /-- /m/ — labial nasal. -/
  | m
  /-- /t/ — voiceless coronal stop. -/
  | t
  /-- /d/ — voiced coronal stop. -/
  | d
  /-- /tˁ/ — emphatic voiceless coronal stop. -/
  | tEmph
  /-- /dˁ/ — emphatic voiced coronal stop. -/
  | dEmph
  /-- /θ/ — voiceless coronal fricative. -/
  | theta
  /-- /ð/ — voiced coronal fricative. -/
  | edh
  /-- /s/ — voiceless coronal sibilant. -/
  | s
  /-- /z/ — voiced coronal sibilant. -/
  | z
  /-- /sˁ/ — emphatic voiceless coronal sibilant. -/
  | sEmph
  /-- /zˁ/ — emphatic voiced coronal sibilant. -/
  | zEmph
  /-- /ʃ/ — voiceless palatoalveolar sibilant. -/
  | esh
  /-- /k/ — voiceless dorsal stop. -/
  | k
  /-- /g/ — voiced dorsal stop. -/
  | g
  /-- /q/ — uvular stop (dorsal+pharyngeal in FPB's analysis). -/
  | q
  /-- /χ/ — voiceless uvular fricative. -/
  | chi
  /-- /ʁ/ — voiced uvular fricative. -/
  | gamma
  /-- /ħ/ — voiceless pharyngeal fricative. -/
  | hbar
  /-- /ʕ/ — voiced pharyngeal fricative. -/
  | ayin
  /-- /h/ — voiceless laryngeal fricative. -/
  | h
  /-- /ʔ/ — laryngeal stop. -/
  | glottal
  /-- /l/ — coronal lateral. -/
  | l
  /-- /r/ — coronal rhotic. -/
  | r
  /-- /n/ — coronal nasal. -/
  | n
  /-- /w/ — labial-velar glide. -/
  | w
  /-- /j/ — palatal glide. -/
  | j
  deriving DecidableEq

/-- Membership in the labial class `{b, f, m, w}` — the tier predicate for
the thresholded TSL₂ grammars below. -/
def Arabic.IsLabial (x : Arabic) : Prop := x ∈ ({.b, .f, .m, .w} : Finset Arabic)

instance : DecidablePred Arabic.IsLabial :=
  λ x => inferInstanceAs (Decidable (x ∈ ({.b, .f, .m, .w} : Finset Arabic)))

/-! ### Labial natural classes (p. 199)

FPB enumerate the labial natural classes separately for their two worked
examples: for /f, m/, 2 shared + 7 non-shared = 9 classes, the non-shared
including the singleton `{f}`; for /b, f/, 3 shared + 5 non-shared = 8, the
non-shared omitting `{f}` even though `{f}` contains /f/ and not /b/. Under
[broe-1993]'s structured specification the class set is fixed by the
inventory, so `{f}` should count in both enumerations, giving 3/9 rather
than the paper's 3/8 for /b, f/ — most likely an enumeration slip in the
paper. Both lists are reproduced verbatim so the worked-example values
match the paper's exact numbers; deriving the classes from feature
matrix (8) is deferred. -/

/-- Labial natural classes for the /f, m/ computation (p. 199): 2 shared
followed by 7 non-shared, with the paper's glosses. -/
def labialClasses_fm : List (Finset Arabic) :=
  [ -- shared between f and m:
    {.b, .f, .m, .w},  -- the labials
    {.b, .f, .m},      -- labial consonants
    -- non-shared (contains f, not m):
    {.b, .f},          -- obstruents
    {.f, .w},          -- continuants
    {.f},              -- voiceless continuants
    -- non-shared (contains m, not f):
    {.b, .m, .w},      -- voiced
    {.b, .m},          -- voiced stops
    {.m, .w},          -- voiced sonorants
    {.m}]              -- nasals

/-- Labial natural classes for the /b, f/ computation (p. 199): 3 shared
followed by 5 non-shared. -/
def labialClasses_bf : List (Finset Arabic) :=
  [ -- shared between b and f:
    {.b, .f, .m, .w},  -- the labials
    {.b, .f, .m},      -- labial consonants
    {.b, .f},          -- obstruents
    -- non-shared (contains f, not b):
    {.f, .w},          -- continuants
    -- non-shared (contains b, not f):
    {.b, .m, .w},      -- voiced
    {.b, .m},          -- voiced stops
    {.b, .w},          -- voiced non-nasals
    {.b}]              -- voiced obstruents

/-! ### Worked examples (p. 199) -/

/-- /f, m/ share 2 labial natural classes: the labials `{b, f, m, w}` and
the labial consonants `{b, f, m}`. -/
theorem fm_shared : sharedClasses labialClasses_fm .f .m = 2 := by decide

/-- /f, m/ have 9 relevant classes in total: 2 shared + 7 non-shared. -/
theorem fm_total : totalRelevantClasses labialClasses_fm .f .m = 9 := by decide

/-- /b, f/ share 3 labial natural classes: `{b, f, m, w}`, `{b, f, m}`,
and `{b, f}`. -/
theorem bf_shared : sharedClasses labialClasses_bf .b .f = 3 := by decide

/-- /b, f/ have 8 relevant classes in total: 3 shared + 5 non-shared. -/
theorem bf_total : totalRelevantClasses labialClasses_bf .b .f = 8 := by decide

/-- Worked example: similarity(/f, m/) = 2/9 ≈ 0.22 (p. 199). -/
theorem similarity_f_m : similarity labialClasses_fm .f .m = 2/9 := by
  norm_num [similarity, fm_shared, fm_total]

/-- Worked example: similarity(/b, f/) = 3/8 ≈ 0.38 (p. 199). -/
theorem similarity_b_f : similarity labialClasses_bf .b .f = 3/8 := by
  norm_num [similarity, bf_shared, bf_total]

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

variable (xs : List (Finset Arabic)) (t c₁ c₂ : ℚ)

/-- Step-function O/E prediction of a threshold model: `c₁` strictly below
the threshold `t`, `c₂` at or above it. -/
def categoricalAtThreshold (sim : ℚ) : ℚ :=
  if sim < t then c₁ else c₂

/-- The TSL₂ grammar over `Arabic` forbidding tier-adjacent labial pairs of
similarity at least `t` — [heinz-rawal-tanner-2011]'s forbidden-pair schema
instantiated with FPB's metric. -/
def thresholdedTSL : Subregular.TSLGrammar 2 Arabic :=
  Subregular.TSLGrammar.ofForbiddenPairs
    (λ x y => similarity xs x y ≥ t) Arabic.IsLabial

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
theorem thresholdedTSL_pair_iff {x y : Arabic} (hx : x.IsLabial) (hy : y.IsLabial) :
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
