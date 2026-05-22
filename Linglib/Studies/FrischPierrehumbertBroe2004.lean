/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Linglib.Core.Computability.Subregular.ForbiddenPairs
import Linglib.Core.Computability.Subregular.Multitier

/-!
# Frisch, Pierrehumbert & Broe (2004) @cite{frisch-pierrehumbert-broe-2004}

Similarity Avoidance and the OCP. *Natural Language & Linguistic Theory*
22(1):179–228.

@cite{frisch-pierrehumbert-broe-2004} (FPB) argue that the OCP-Place
constraint in Arabic verbal roots is a **gradient** constraint whose
strength is a quantitative function of the **similarity** between
homorganic consonants. The categorical OCP-Place analyses of
@cite{mccarthy-1986}, @cite{padgett-1995}, and @cite{mccarthy-1994} all
face the same trade-off: dividing consonants into co-occurrence classes
either ignores robust within-class variation (broad classes — many
exceptions) or fragments the data into ad-hoc sub-classes (narrow
classes — many missing generalisations). FPB resolve the trade-off
with a single gradient constraint based on the
**natural-classes similarity metric** (eq. 7):

  Similarity(a, b) = SharedClasses(a, b) / (SharedClasses + NonShared)

restricted to natural classes containing a place feature. Identical
consonants have similarity 1; non-homorganic consonants have similarity
0. The metric is sensitive to inventory **contrast**: larger, more
divided classes (e.g. coronals) yield lower similarity for any pair
within them than smaller classes (e.g. labials), exactly capturing the
empirical distance between the strong coronal OCP and the weaker
guttural/dorsal OCPs.

## What this file formalises

* **§1** — the 28-segment Arabic consonant inventory from FPB (8) p. 201.
* **§2** — the **labial natural classes** as enumerated by the paper
  itself in its two worked-example computations (p. 199). The
  enumeration is given separately for the /f, m/ and /b, f/ examples
  (matching the paper's text); see the design-boundary comment below
  on why the two enumerations are not identical.
* **§3** — the natural-classes similarity metric (eq. 7), parameterised
  on a list of relevant natural classes.
* **§3 worked examples** — the paper's two explicit computations:
  similarity(/f, m/) = 2/9 and similarity(/b, f/) = 3/8 (p. 199).
* **§4** — the empirical Table IV (p. 203) for adjacent pairs:
  9 (similarity-bin, O/E) data points whose monotonic decrease
  embodies FPB's gradient claim.
* **§5** — the substrate connection (`thresholdedTSL` +
  `thresholdedTSL_pair_iff`) showing that the TSL_2 grammar
  `TSLGrammar.ofForbiddenPairs (similarity ≥ t) Arabic.isLabial`
  makes a binary step-function decision on labial pairs (accept iff
  similarity strictly below threshold), and the **cross-framework
  divergence theorem** `categorical_fails_three_test_points` showing
  that no two-valued model (and hence no similarity-threshold TSL_2
  grammar) can match three specific Table IV bins with three
  pairwise-distinct O/E values. This is the **necessary-consequence**
  formalisation of the design-boundary claim in
  `Core/Computability/Subregular/ForbiddenPairs.lean`. FPB's actual
  argument is stronger — it compares R² fits across nine bins
  (Categorical 0.70 vs Natural Classes 0.75 per Table V p. 207) — but
  full R² formalisation requires the lexical corpus and is deferred.

## What this file does *not* formalise

* The **2,674-root corpus** from @cite{cowan-1979} (the *Hans Wehr*
  Arabic-English dictionary) that anchors FPB's O/E computations is
  not in the paper text. We use the paper's reported O/E values
  (Table IV) as data, not a re-derived corpus.
* The **R² model fits** (Table V: Frequency 0.57, Categorical 0.70,
  Soft 0.73, Feature 0.71, Natural Classes 0.75) require the corpus.
  Reproduction is deferred.
* The **stochastic constraint model** of FPB §3.4 (logistic fit
  with K, S parameters; @cite{frisch-broe-pierrehumbert-1997}, Rutgers
  Optimality Archive) requires the corpus and is deferred.
* **§4.1 Frisch–Zawaydeh nonce-verb judgments**
  (@cite{frisch-zawaydeh-2001}: Arabic speakers rate /baba**θ**a/
  identical < /**θ**ab**a**ma/ similar adjacent < /ba**ʃ**afa/ similar
  nonadjacent < /ba**ʔ**ada/ nonhomorganic in OCP-violation severity)
  — experimental data, summarised in docstring only.
* **§4.2 Maltese borrowings from Italian** (FPB Table VI p. 213:
  identical 0.26, similar homorganic 0.45, coronal stop/fric 0.78
  — gradient OCP applied selectively to incorporated Italian forms;
  @cite{mifsud-1995}) — corpus-based, summarised only.
* **§4.2 cross-linguistic similarity-OCP attestations** (Tigrinya
  @cite{buckley-1997-ocp}, Russian @cite{padgett-1995}, English
  @cite{berkley-1994}, Thai @cite{frisch-2000a}) — referenced in
  docstring.
* **§4.3 phonetic / cognitive origin** (@cite{berg-1998},
  @cite{boersma-1998}, @cite{frisch-1996} processing-difficulty
  argument; speech-error data of @cite{abd-el-jawad-abu-salim-1987}:
  /takriib/ for /takbiir/ 'glorification', /maraaʕiʃ/ for /maʃaaʕir/
  'feelings') — diachronic-functional grounding, summarised only.
* **Full natural-class derivation from a feature matrix** —
  the paper sketches this (eq. 8 lays out the feature matrix;
  @cite{broe-1993}'s specification theory provides the lattice
  machinery), but a faithful Lean implementation requires a substrate
  effort the audit explicitly flagged as a separate next step. This
  file reproduces the paper's worked-example natural-class lists
  (per-pair) rather than deriving them.

## Connection to `ForbiddenPairs.lean`'s design boundary

`Linglib/Core/Computability/Subregular/ForbiddenPairs.lean` (the
substrate file for tier-based strictly 2-local grammars defined by
forbidden-pair relations) cites FPB in its design-boundary section as
the empirical motivation for "single-tier TSL_2 cannot capture gradient
similarity-based OCP." Pre-this-file, that citation lived only in
docstring prose. Two declarations below make the claim Lean-formal:
(1) `thresholdedTSL` instantiates the substrate's
`TSLGrammar.ofForbiddenPairs` with `R := λ x y => similarity xs x y ≥ t`,
giving a real (not metaphorical) TSL_2 grammar over Arabic; and
(2) `thresholdedTSL_pair_iff` proves the grammar's accept/reject
decision on labial pairs is exactly the binary step function
`similarity < t`. The `categorical_fails_three_test_points` divergence
theorem then witnesses that no such two-valued model can match three
specific Table IV bins.

## Connection to `Hansson2010.lean`

@cite{hansson-2010} (`Studies/Hansson2010.lean`)
cites FPB at line 76 in its design-boundary section on
similarity-graded transparency: cases where intervening segments
behave differently depending on similarity to the harmonising pair
cannot be captured by single-tier TSL with a fixed tier predicate.
This file is the load-bearing instance of that observation for
Arabic OCP-Place specifically.

## Why this paper anchors a study file

Per CLAUDE.md's anchoring discipline: every Lean file is anchored to
exactly one of (a) a specific paper, (b) a documented empirical
pattern, or (c) a named theoretical framework. The audit on
`ForbiddenPairs.lean` (committed `0.230.508`, hash `8579b346`) flagged
FPB as one of four "silent divergences" — a paper used as a substrate
file's docstring example without itself being anchored. This file
closes that finding by anchoring FPB to its primary phenomenon
(Phonology) with a Lean-formal divergence theorem connecting back to
the substrate citation.
-/

namespace Phonology.Studies.FrischPierrehumbertBroe2004

/-! ## § 1: The Arabic Consonant Inventory (FPB feature matrix (8), p. 201) -/

/-- The 28-segment Arabic consonant inventory used by
@cite{frisch-pierrehumbert-broe-2004} eq. 8 (p. 201). The labelling
follows the paper's IPA-with-superscript-`ˁ`-for-emphatic convention.

This file's worked examples and divergence theorem use only the labial
sub-inventory `{b, f, m, w}`; the full 28-segment list is included to
keep the inventory anchored to FPB's feature matrix and to make the
file extensible to future enumeration work over the full inventory. -/
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
  deriving DecidableEq, Repr

/-- The labial sub-inventory `{b, f, m, w}`. Used by the worked examples
and the divergence theorem. -/
def Arabic.isLabial : Arabic → Prop
  | .b | .f | .m | .w => True
  | _ => False

instance : DecidablePred Arabic.isLabial
  | .b | .f | .m | .w => isTrue trivial
  | .t | .d | .tEmph | .dEmph | .theta | .edh | .s | .z
  | .sEmph | .zEmph | .esh | .k | .g | .q | .chi | .gamma
  | .hbar | .ayin | .h | .glottal | .l | .r | .n | .j => isFalse not_false

/-! ## § 2: Labial Natural Classes — Per-Pair Enumerations from FPB p. 199 -/

/-! ### Per-pair enumerations vs unified lattice

@cite{frisch-pierrehumbert-broe-2004} p. 199 enumerates the labial
natural classes relevant for two specific worked examples:

* /f, m/: 2 shared classes + 7 non-shared = 9 total. The non-shared
  list explicitly includes `{f}` (voiceless labial continuants).
* /b, f/: 3 shared + 5 non-shared = 8 total. The non-shared list
  does **not** include `{f}` even though `{f}` contains `f` and not
  `b` and would naturally appear in a unified lattice.

This difference is **most likely a paper enumeration error**, not a
principled per-pair-relativised derivation: under @cite{broe-1993}'s
specification-theory lattice the relevant labial natural classes are
inventory-determined (closed under intersection of feature-class
extensions), so once the lattice is fixed the set of classes containing
`f` is fixed too. `{f}` would therefore appear in *both* enumerations
under any consistent application of Broe's machinery, giving total = 9
for /b, f/ and similarity 3/9 ≈ 0.33 (rather than the paper's 3/8 = 0.38).
We reproduce the paper's two enumerations faithfully so the worked-
example similarity values match the paper's *exact* numbers (2/9 and
3/8); a unified-lattice derivation that would give the systematic 3/9
result requires substrate work (Broe 1993 specification theory) and is
deferred.
-/

/-- Labial natural classes relevant for the **/f, m/** similarity
computation, reproducing FPB p. 199 verbatim. The 2 shared classes
appear first; the 7 non-shared follow. Each class is annotated with
the phonological gloss the paper provides. -/
def labialClasses_fm : List (Finset Arabic) :=
  [ -- shared between f and m:
    {Arabic.b, Arabic.f, Arabic.m, Arabic.w},  -- the labials
    {Arabic.b, Arabic.f, Arabic.m},            -- labial consonants
    -- non-shared (contains f, not m):
    {Arabic.b, Arabic.f},                      -- labial obstruents
    {Arabic.f, Arabic.w},                      -- labial continuants
    {Arabic.f},                                -- voiceless labial continuants
    -- non-shared (contains m, not f):
    {Arabic.b, Arabic.m, Arabic.w},            -- voiced labials
    {Arabic.b, Arabic.m},                      -- voiced labial stops
    {Arabic.m, Arabic.w},                      -- voiced labial sonorants
    {Arabic.m}]                                -- labial nasals

/-- Labial natural classes relevant for the **/b, f/** similarity
computation, reproducing FPB p. 199 verbatim. The 3 shared classes
appear first; the 5 non-shared follow. -/
def labialClasses_bf : List (Finset Arabic) :=
  [ -- shared between b and f:
    {Arabic.b, Arabic.f, Arabic.m, Arabic.w},  -- the labials
    {Arabic.b, Arabic.f, Arabic.m},            -- labial consonants
    {Arabic.b, Arabic.f},                      -- labial obstruents
    -- non-shared (contains f, not b):
    {Arabic.f, Arabic.w},                      -- labial continuants
    -- non-shared (contains b, not f):
    {Arabic.b, Arabic.m, Arabic.w},            -- voiced labials
    {Arabic.b, Arabic.m},                      -- voiced labial stops
    {Arabic.b, Arabic.w},                      -- voiced non-nasal labials
    {Arabic.b}]                                -- (the labial "{b}" class)

/-! ## § 3: The Natural-Classes Similarity Metric (FPB eq. 7, p. 198) -/

/-- The Nat-valued count of natural classes in `xs` containing both `a`
and `b`. The numerator of FPB eq. 7. -/
def sharedClasses (xs : List (Finset Arabic)) (x y : Arabic) : Nat :=
  (xs.filter (λ s => decide (x ∈ s ∧ y ∈ s))).length

/-- The Nat-valued count of natural classes in `xs` containing at least
one of `a, b` — equivalently, shared + non-shared. The denominator of
FPB eq. 7. -/
def totalRelevantClasses (xs : List (Finset Arabic)) (x y : Arabic) : Nat :=
  (xs.filter (λ s => decide (x ∈ s ∨ y ∈ s))).length

/-- **FPB eq. 7**: the natural-classes similarity metric.

  Similarity(a, b) = |classes containing both| / |classes containing a or b|

Generic in `xs : List (Finset Arabic)`, the list of relevant natural
classes (containing a place feature, per FPB's stipulation on p. 198).

Identical consonants participating in any class get similarity 1
(every relevant class containing one contains the other). Non-homorganic
consonants get similarity 0 (no relevant labial class contains either,
so total = 0 → return 0 by convention to avoid 0/0). -/
def similarity (xs : List (Finset Arabic)) (x y : Arabic) : ℚ :=
  let t := totalRelevantClasses xs x y
  if t = 0 then 0 else (sharedClasses xs x y : ℚ) / (t : ℚ)

/-! ## § 3 worked examples (FPB p. 199) -/

/-- /f, m/ share 2 labial natural classes (`{b, f, m, w}`, `{b, f, m}`)
per FPB p. 199. -/
theorem fm_shared : sharedClasses labialClasses_fm Arabic.f Arabic.m = 2 := by
  decide

/-- /f, m/ have 9 total relevant classes (2 shared + 7 non-shared) per
FPB p. 199. -/
theorem fm_total : totalRelevantClasses labialClasses_fm Arabic.f Arabic.m = 9 := by
  decide

/-- /b, f/ share 3 labial natural classes (`{b, f, m, w}`, `{b, f, m}`,
`{b, f}`) per FPB p. 199. -/
theorem bf_shared : sharedClasses labialClasses_bf Arabic.b Arabic.f = 3 := by
  decide

/-- /b, f/ have 8 total relevant classes (3 shared + 5 non-shared) per
FPB p. 199. -/
theorem bf_total : totalRelevantClasses labialClasses_bf Arabic.b Arabic.f = 8 := by
  decide

/-- **FPB worked example (p. 199)**: similarity(/f, m/) = 2/9.

  /f, m/ share 2 labial natural classes (the labials, labial consonants)
  and have 7 non-shared (the obstruents `{b, f}`, the continuants `{f, w}`,
  the voiceless continuants `{f}`, the voiced labials `{b, m, w}`, the
  voiced stops `{b, m}`, the voiced sonorants `{m, w}`, the nasals `{m}`).
  Similarity = 2 / (2 + 7) = 2/9 ≈ 0.22. -/
theorem similarity_f_m : similarity labialClasses_fm Arabic.f Arabic.m = 2/9 := by
  unfold similarity
  rw [fm_total, fm_shared]
  norm_num

/-- **FPB worked example (p. 199)**: similarity(/b, f/) = 3/8.

  /b, f/ share 3 labial natural classes (the labials, labial consonants,
  obstruents) and have 5 non-shared (`{f, w}`, `{b, m, w}`, `{b, m}`,
  `{b, w}`, `{b}`). Similarity = 3 / (3 + 5) = 3/8 = 0.375. -/
theorem similarity_b_f : similarity labialClasses_bf Arabic.b Arabic.f = 3/8 := by
  unfold similarity
  rw [bf_total, bf_shared]
  norm_num

/-! ## § 4: Empirical Table IV (FPB p. 203, adjacent pairs) -/

/-- FPB Table IV (p. 203, adjacent column): the gradient O/E pattern as
a function of natural-classes similarity. Each entry is
`(similarity-bin-midpoint, O/E)`. The monotonic decrease from
O/E = 1.22 at similarity 0 (no constraint) down to O/E ≈ 0 at
similarity ≥ 0.4 (categorical avoidance of highly similar pairs)
embodies the gradient OCP claim. -/
def empiricalTableIV : List (ℚ × ℚ) :=
  [(0,        122/100),
   (5/100,    105/100),
   (15/100,    83/100),
   (25/100,    59/100),
   (35/100,    32/100),
   (45/100,     3/100),
   (55/100,     6/100),
   (8/10,            0),
   (1,          1/100)]

/-! ## § 5: Cross-Framework Divergence — Categorical Cannot Fit Table IV -/

/-! ### The categorical-at-threshold model

Any TSL_2 grammar of the form
`Core.Computability.Subregular.TSLGrammar.ofForbiddenPairs
   (fun a b => similarity la b ≥ t) p` makes a **two-valued** prediction
about each consonant pair: forbidden (membership rejected) if similarity
≥ t, permitted (accepted) otherwise. As an O/E predictor, this becomes a
step function: predicted O/E = `c1` for similarity < t (where pairs are
attested at some baseline rate) and `c2` for similarity ≥ t (where pairs
are categorically suppressed). Below we show that no choice of
`t, c1, c2 : ℚ` can fit even three specific Table IV bins. -/

/-- Categorical-at-threshold prediction: O/E = `c1` if similarity < `t`,
otherwise `c2`. Any TSL_2 grammar with `R := (similarity ≥ t)` reduces
to this two-valued form. -/
def categoricalAtThreshold (t c1 c2 : ℚ) (sim : ℚ) : ℚ :=
  if sim < t then c1 else c2

/-- Three Table IV bins exhibit three pairwise-distinct O/E values:
similarity 0 → 1.22, similarity 0.25 → 0.59, similarity 0.55 → 0.06
(see `empiricalTableIV` above). Witnesses that the FPB pattern has at
least three distinct response levels — more than a two-valued model
can produce. -/
theorem fpb_three_distinct_OE_levels :
    (122/100 : ℚ) ≠ 59/100 ∧ (122/100 : ℚ) ≠ 6/100 ∧ (59/100 : ℚ) ≠ 6/100 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **The substrate connection**: a TSL_2 grammar over Arabic whose
forbidden-pair relation is "similarity at or above threshold `t`",
restricted to the labial tier. Instantiates
`Core.Computability.Subregular.TSLGrammar.ofForbiddenPairs` directly,
making the connection from FPB's similarity metric to the substrate
machinery true by construction (rather than docstring-only). -/
def thresholdedTSL (xs : List (Finset Arabic)) (t : ℚ) : Core.Computability.Subregular.TSLGrammar 2 Arabic :=
  Core.Computability.Subregular.TSLGrammar.ofForbiddenPairs
    (λ x y => similarity xs x y ≥ t) Arabic.isLabial

/-- **Every threshold-induced FPB grammar is TSL_2.** Explicit
`IsTierStrictlyLocal 2` typing of the implicit complexity claim made by
the `thresholdedTSL` constructor — the substrate-classification "any
two-valued threshold model is TSL_2" is now a typed theorem rather than
docstring prose. -/
theorem thresholdedTSL_lang_isTSL2 (xs : List (Finset Arabic)) (t : ℚ) :
    Core.Computability.Subregular.IsTierStrictlyLocal 2 (thresholdedTSL xs t).lang :=
  ⟨thresholdedTSL xs t, rfl⟩

/-- **BTSL_2 corollary** (via `IsTierStrictlyLocal.toIsBTSL` in
`Core.Computability.Subregular.Multitier`): every threshold-induced FPB
grammar's stringset is in the multitier closure of strictly local
languages, hence consumed by the @cite{lambert-2026} BTC framework. -/
theorem thresholdedTSL_lang_isBTSL2 (xs : List (Finset Arabic)) (t : ℚ) :
    Core.Computability.Subregular.IsBTSL 2 (thresholdedTSL xs t).lang :=
  (thresholdedTSL_lang_isTSL2 xs t).toIsBTSL

/-- **The TSL_2 grammar makes a binary step-function decision on labial
pairs.** For two labial segments `x, y`, the grammar
`thresholdedTSL xs t` accepts the bigram `[x, y]` iff their similarity
is strictly below `t`. This is the precise sense in which any
similarity-threshold TSL_2 grammar collapses to the `categoricalAtThreshold`
two-valued prediction: the accept/reject decision is a step function of
similarity, not a graded response. -/
theorem thresholdedTSL_pair_iff (xs : List (Finset Arabic)) (t : ℚ)
    (x y : Arabic) (hx : Arabic.isLabial x) (hy : Arabic.isLabial y) :
    [x, y] ∈ (thresholdedTSL xs t).lang ↔ similarity xs x y < t := by
  unfold thresholdedTSL
  rw [Core.Computability.Subregular.mem_ofForbiddenPairs_lang_iff_filter_isChain]
  have hfx : decide (Arabic.isLabial x) = true := decide_eq_true hx
  have hfy : decide (Arabic.isLabial y) = true := decide_eq_true hy
  simp only [List.filter_cons, hfx, hfy, ↓reduceIte, List.filter_nil,
             List.isChain_cons_cons, List.isChain_singleton, and_true,
             not_le]

/-- **Cross-framework divergence theorem**: for ANY threshold `t : ℚ` and
any pair of predicted O/E values `c1, c2 : ℚ`, the categorical-at-threshold
model cannot match all three of FPB Table IV's data points
(sim=0, O/E=1.22), (sim=0.25, O/E=0.59), (sim=0.55, O/E=0.06).

**Significance**: any similarity-threshold TSL_2 grammar (per
`thresholdedTSL`, instantiating @cite{heinz-rawal-tanner-2011}'s
substrate) makes a binary step-function decision on each pair (per
`thresholdedTSL_pair_iff`), so its O/E prediction collapses to two
values: one for permitted (similarity < t) pairs, one for forbidden
(similarity ≥ t) pairs. This theorem proves no such two-valued model
can reproduce three pairwise-distinct Table IV bins exactly. It is a
**necessary consequence** of FPB's gradient claim, not a full R²
comparison: FPB's actual argument is about aggregate fit quality across
9 bins (Categorical R² = 0.70 vs Natural Classes R² = 0.75; FPB Table V
p. 207) and requires the lexical corpus to formalise. The 3-bin
separation captured here is the corpus-free Lean-formal version.

The natural downstream extension of FPB's gradient observation is the
weighted-constraint MaxEnt phonotactic learner of @cite{hayes-wilson-2008},
which uses similarity-relevant features as primitives and reproduces
gradient phonotactic patterns by fitting log-linear weights — a
positive-fit complement to this file's negative-fit (categorical-fails)
result.

**Proof strategy**: case analysis on whether the threshold `t` lies
in each of the four intervals partitioned by 0, 0.25, 0.55. In each
case, the three predictions are some constant pattern over `{c1, c2}`,
and `linarith` discharges the resulting numerical impossibility (the
three required O/E values are pairwise distinct). -/
theorem categorical_fails_three_test_points :
    ∀ (t c1 c2 : ℚ),
    ¬ (categoricalAtThreshold t c1 c2 0 = 122/100 ∧
       categoricalAtThreshold t c1 c2 (25/100) = 59/100 ∧
       categoricalAtThreshold t c1 c2 (55/100) = 6/100) := by
  intro t c1 c2 ⟨h1, h2, h3⟩
  unfold categoricalAtThreshold at h1 h2 h3
  by_cases hLT0 : (0 : ℚ) < t
  · -- 0 < t: pred(0) = c1
    by_cases hLT25 : (25/100 : ℚ) < t
    · -- 0.25 < t: pred(0.25) = c1
      by_cases hLT55 : (55/100 : ℚ) < t
      · -- 0.55 < t: pred(0.55) = c1; all three predictions are c1
        simp only [hLT0, hLT25, hLT55, if_true] at h1 h2 h3
        linarith
      · -- ¬ 0.55 < t: pred(0.55) = c2; preds are (c1, c1, c2)
        simp only [hLT0, hLT25, hLT55, if_false] at h1 h2 h3
        linarith
    · -- ¬ 0.25 < t: also ¬ 0.55 < t
      have hLT55 : ¬ (55/100 : ℚ) < t := λ h => hLT25 (by linarith)
      simp only [hLT0, hLT25, hLT55, if_false] at h1 h2 h3
      linarith
  · -- ¬ 0 < t: also ¬ 0.25 < t and ¬ 0.55 < t; all preds are c2
    have hLT25 : ¬ (25/100 : ℚ) < t := λ h => hLT0 (by linarith)
    have hLT55 : ¬ (55/100 : ℚ) < t := λ h => hLT0 (by linarith)
    simp only [hLT0, hLT25, hLT55, if_false] at h1 h2 h3
    linarith

end Phonology.Studies.FrischPierrehumbertBroe2004
