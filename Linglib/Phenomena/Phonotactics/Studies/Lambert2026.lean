/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Definite
import Linglib.Core.Computability.Subregular.PiecewiseTestable
import Linglib.Core.Computability.Subregular.Tier
import Linglib.Core.Computability.Subregular.Multitier
import Linglib.Theories.Phonology.SibilantTier

/-!
# @cite{lambert-2026}: Multitier phonotactics with logic and algebra

Lambert (2026) classifies attested phonotactic constraints — bounded and
unbounded stress, harmony, and tone across ~13 languages — into the
multitier (Boolean closure of tier-projected) extensions of definite,
generalized definite, and finite-or-cofinite classes. Headline empirical
claims:

* **Uyghur backness harmony is multitier definite (BTD)** — strictly
  weaker than the multiple-tier-based strictly local class of
  @cite{de-santo-graf-2019}, settling (categorically) the challenge raised
  by @cite{mayer-major-2018}.
* **Karanga Shona tone is multitier generalized definite (BTLI)** — no
  more complex than the default-to-opposite unbounded stress patterns,
  refining the melody-local analysis of @cite{jardine-2020}.

The propositional logic is `BoolClosure (IsTierBased 𝒞)` for `𝒞` in
{`IsDefinite k`, `IsGeneralizedDefinite k`, `IsStrictlyLocal k`,
`IsStrictlyPiecewise k`, `IsFiniteOrCofinite`}; the algebraic side is
the syntactic-semigroup characterization of each class via Eilenberg
@cite{eilenberg-1976} variety equations (e.g., `D = ⟦sx̄ = x̄⟧`,
`ℒℐ = ⟦x^ω y x^ω z x^ω = x^ω y x^ω⟧` per @cite{straubing-1985} and
@cite{almeida-1995}). The Lean substrate (`BoolClosure`, `IsBTC`,
`IsTierBased`) lives in `Subregular/Multitier.lean`; the algebraic
characterization is queued for a future `SyntacticMonoid` PR.

## Disclaimer 1: McCollum (2019) Uyghur gradience (linglib audit)

This disclaimer is **not** a scope qualification carried by Lambert
(2026); the paper does not cite McCollum. It is a linglib-internal
audit annotation: Lambert's BTD analysis is faithful to
@cite{mayer-major-2018}'s **categorical idealization**, and a separate
literature line — @cite{mccollum-2019} — argues the suffix backness
assignment is not categorical in the way the multitier-definite formula
requires. The "arbitrarily specified, statistical tendency to be back"
clause that Mayer & Major report for the no-V no-C case is precisely
the locus where McCollum's gradient data resists categorical analysis.
The headline theorem `uyghur_backness_isBTD` characterizes the
categorical pattern only; the gradience is out of scope.

## Disclaimer 2: Karanga Shona scope restriction

The BTLI analysis applies to the **verb-stem** domain (post-hyphen
material in Lambert (2026) (45)). @cite{jardine-2020}'s motivation for a
`melody local` class extends across morphological boundaries and to
longer melodic patterns; the BTLI characterization is not a refutation
of the broader melody-local programme but a delimited result for the
verb-stem surface pattern. The headline theorem
`karanga_shona_verb_stem_isBTLI` is named accordingly.

## Cross-framework dialogue

The multitier substrate is the prohibition reading of constraints scaled
to Boolean closure. Cross-references the new file makes explicit (rather
than silently diverging from existing linglib formalizations):

* OT: linglib's `NamedConstraint` framework places no complexity bound;
  Lambert says all phonotactics live in `IsBTC`. The supraregular
  counter-witness theorem and the positive `mkForbidPairsOnTier ⊆ TSL_2`
  theorem are queued for a future `Theories/Phonology/Subregular/OTBound.lean`.
* Harmonic Serialism: `Phenomena/Tone/Studies/McPhersonLamont2026.lean`
  proves Poko surface tone HS-derivable but parallel-OT-impossible.
  Lambert's static BTC characterization, applied to Poko's surface
  stringset, would clarify *static description ≠ alternation
  explanation*. Cross-reference to be added when Poko's surface
  stringset is independently classified.
* Autosegmental: linglib's `Theories/Phonology/Autosegmental/{
  RegisterTier, GrammaticalTone}.lean` formalize multiply-linked tone
  representations. Lambert (2026) §5 self-confesses that string-based
  analysis loses information for tone; the loss theorem is stated as
  `lambert_string_input_loses_tone_associations` (sorry'd) below.
* OCP: `Theories/Phonology/Subregular/OCP.lean` carries a
  prohibition-vs-merger distinction; `IsBTC` is the mathematical home of
  the prohibition family at scale. The OCP file's docstring should gain
  a "see also: BTC" link in a follow-up retrofit.
* Structure-sensitive MTSL @cite{de-santo-graf-2019}: not formalized in
  linglib. Lambert's "BTD strictly supersedes SS-MTSL on Uyghur" is
  recorded as a TODO theorem (`btd_supersedes_ss_mtsl_on_uyghur`) for
  when SS-MTSL substrate lands.

## Audit calibration note

Per linglib's domain-expert agent calibration: the McCollum-2019 and
Karanga-Shona-scope concerns are flagged HIGH but should be treated
PROVISIONAL — they are corrections to scope, not refutations of the
formal results. The Lean theorems below state the formal claims; the
empirical disclaimers live in this docstring and the per-theorem
docstrings.
-/

namespace Phenomena.Phonotactics.Studies.Lambert2026

open Core.Computability.Subregular
open List  -- for `<+` (List.Sublist) infix in subseqSet equivalence proofs

-- ============================================================================
-- § 1. Iban (Austronesian): stress-final ∈ D_1
-- ============================================================================

/-- Iban syllable type @cite{omar-1969}: stressed (`σ́`) or unstressed (`σ`).
The two-letter alphabet of Lambert (2026) §2.1. -/
inductive IbanSyl | unstressed | stressed
  deriving DecidableEq, Repr

/-- The Iban stress-final language: a word is well-formed iff its final
syllable is stressed @cite{omar-1969}. As a `DefiniteGrammar 1`: the
permitted length-1 right-edge substring is `[stressed]`. -/
def ibanGrammar : DefiniteGrammar 1 IbanSyl where
  permitted := { [.stressed] }

/-- The Iban stress-final language as a `Language IbanSyl`. -/
def ibanLang : Language IbanSyl := ibanGrammar.lang

/-- **Iban stress-final ∈ D_1** (Lambert 2026 §2.1, paper p. 4 example
(2)). Definitional witness: the `DefiniteGrammar 1` whose permitted
final 1-suffix is `[stressed]`. The general k-definite Proposition (4)
characterizes this class abstractly; the Iban witness is the
specialisation for k = 1. -/
theorem iban_isDefinite_one : IsDefinite 1 ibanLang :=
  ⟨ibanGrammar, rfl⟩

-- ============================================================================
-- § 2. Amara (Austronesian): stress-penult ∈ D_2
-- ============================================================================

/-- Amara stress @cite{thurston-1966}: penultimate-syllable stress with the
monosyllabic exception (single syllable bears stress). -/
def amaraGrammar : DefiniteGrammar 2 IbanSyl where
  -- Permitted length-2 right-edge substrings: stressed monosyllable, or
  -- 2-suffix beginning with stressed (penult).
  permitted := { [.stressed], [.stressed, .unstressed] }

/-- The Amara stress-penult language. -/
def amaraLang : Language IbanSyl := amaraGrammar.lang

/-- **Amara stress-penult ∈ D_2** (Lambert 2026 §2.1). Witnessed by the
2-grammar permitting either a stressed monosyllable or a stressed-then-
unstressed 2-suffix. -/
theorem amara_isDefinite_two : IsDefinite 2 amaraLang :=
  ⟨amaraGrammar, rfl⟩

-- ============================================================================
-- § 3. Uyghur backness harmony ∈ BTD
-- ============================================================================

/-- Uyghur segment classes relevant to backness harmony @cite{mayer-major-2018}
@cite{lambert-2026} (33)-(35): front vowels, back vowels, transparent (i, e),
front dorsal consonants, back dorsal consonants, suffix-marked harmonizing
vowels and consonants, and a residual "other" class for non-harmonizing
material. -/
inductive UyghurSeg
  | frontVowel | backVowel | transparentVowel
  | frontDorsal | backDorsal
  | suffixFrontVowel | suffixBackVowel
  | suffixFrontDorsal | suffixBackDorsal
  | other
  deriving DecidableEq, Repr

/-! ### Tier predicates

Lambert's `V_f ∪ V_b` is the harmonising-vowel tier; `C_f ∪ C_b` is the
dorsal tier; `S_f` and `S_b` are the front- and back-suffix tiers
(`V_X ∪ C_X` marked as suffix). Each is a Boolean predicate on
`UyghurSeg`. -/

/-- Harmonising-vowel tier: `V_f ∪ V_b`. -/
def isHarmonyingVowel : UyghurSeg → Bool
  | .frontVowel | .backVowel => true
  | _ => false

/-- Dorsal-consonant tier: `C_f ∪ C_b`. -/
def isDorsal : UyghurSeg → Bool
  | .frontDorsal | .backDorsal => true
  | _ => false

/-- Front-suffix tier `S_f`: front-marked suffix material (vowel or dorsal). -/
def isSuffixFront : UyghurSeg → Bool
  | .suffixFrontVowel | .suffixFrontDorsal => true
  | _ => false

/-- Back-suffix tier `S_b`: back-marked suffix material (vowel or dorsal). -/
def isSuffixBack : UyghurSeg → Bool
  | .suffixBackVowel | .suffixBackDorsal => true
  | _ => false

/-! ### Atomic tier-projected definite languages

Each of the four atomic predicates in (35) is a `IsTierBased
(IsDefinite 1)` test. We build them as `DefiniteGrammar 1` instances
on the filtered tier and lift via `IsTierBased`. -/

/-- The language "tier `T` is empty": after filtering by `T`, the word
is `[]`. Encoded as `IsTierBased (IsDefinite 1)` via the singleton
1-suffix `{[]}` (the only word whose right-1-suffix is `[]` is the
empty word). -/
def tierEmptyLang (T : UyghurSeg → Bool) : Language UyghurSeg :=
  { w | w.filter T = [] }

/-- The language "tier `T` ends with `x`": after filtering by `T`, the
word's last element is `x`. Encoded as `IsTierBased (IsDefinite 1)`
via the singleton 1-suffix `{[x]}`. -/
def tierEndsWithLang (T : UyghurSeg → Bool) (x : UyghurSeg) :
    Language UyghurSeg :=
  { w | (w.filter T).drop ((w.filter T).length - 1) = [x] }

/-- The right-1-suffix of a list is empty iff the list itself is empty.
Helper for `tierEmptyLang_isTierBased`. -/
private lemma takeAt_right_one_eq_nil_iff (xs : List UyghurSeg) :
    Edge.right.takeAt 1 xs = [] ↔ xs = [] := by
  cases xs with
  | nil => simp [Edge.takeAt]
  | cons a as =>
    simp only [Edge.takeAt, List.length_cons, Nat.add_sub_cancel]
    constructor
    · intro h
      have : ((a :: as).drop as.length).length = 1 := by
        rw [List.length_drop]; simp
      rw [h] at this
      simp at this
    · intro h; exact absurd h (List.cons_ne_nil _ _)

/-- `tierEmptyLang T` is in `IsTierBased (IsDefinite 1)`. The base
1-definite language is the singleton `{[]}` (only `[]` has right-1-
suffix `[]`). -/
lemma tierEmptyLang_isTierBased (T : UyghurSeg → Bool) :
    IsTierBased (IsDefinite 1) (tierEmptyLang T) := by
  refine ⟨T, ({ permitted := {[]} } : DefiniteGrammar 1 UyghurSeg).lang, ?_,
          ⟨_, rfl⟩⟩
  ext w
  show (w.filter T = []) ↔
       w.filter T ∈ ({ permitted := {[]} } : DefiniteGrammar 1 UyghurSeg).lang
  simp only [EdgeDefiniteGrammar.mem_lang, Set.mem_singleton_iff]
  exact (takeAt_right_one_eq_nil_iff _).symm

/-- `tierEndsWithLang T x` is in `IsTierBased (IsDefinite 1)`. The
base 1-definite language is the singleton `{[x]}`. -/
lemma tierEndsWithLang_isTierBased (T : UyghurSeg → Bool) (x : UyghurSeg) :
    IsTierBased (IsDefinite 1) (tierEndsWithLang T x) := by
  refine ⟨T, ({ permitted := {[x]} } : DefiniteGrammar 1 UyghurSeg).lang, ?_,
          ⟨_, rfl⟩⟩
  ext w
  show ((w.filter T).drop ((w.filter T).length - 1) = [x]) ↔
       w.filter T ∈ ({ permitted := {[x]} } : DefiniteGrammar 1 UyghurSeg).lang
  simp only [EdgeDefiniteGrammar.mem_lang, Set.mem_singleton_iff]
  rfl

/-! ### The Uyghur backness language as conjunction of (35a)-(35b)

The English implication `A → B` is Boolean `Aᶜ ∨ B`; written using
mathlib's `Language` lattice (Boolean algebra), `Aᶜ ⊔ B`. The full
language is the intersection of four such implications. -/

/-- The Uyghur backness harmony language as the conjunction of the four
implications in Lambert (2026) (35a)-(35b). Categorical idealisation —
see file docstring for the @cite{mccollum-2019} gradience disclaimer. -/
def uyghurBacknessLang : Language UyghurSeg :=
  -- (35a.i)  [V_f⋊]_{V_f∪V_b} → [⋊⋉]_{S_b}
  ((tierEndsWithLang isHarmonyingVowel .frontVowel)ᶜ ⊔ tierEmptyLang isSuffixBack) ⊓
  -- (35a.ii) [V_b⋊]_{V_f∪V_b} → [⋊⋉]_{S_f}
  ((tierEndsWithLang isHarmonyingVowel .backVowel)ᶜ ⊔ tierEmptyLang isSuffixFront) ⊓
  -- (35b.i)  ([⋊⋉]_{V_f∪V_b} ∧ [C_f⋊]_{C_f∪C_b}) → [⋊⋉]_{S_b}
  ((tierEmptyLang isHarmonyingVowel ⊓
      tierEndsWithLang isDorsal .frontDorsal)ᶜ ⊔ tierEmptyLang isSuffixBack) ⊓
  -- (35b.ii) ([⋊⋉]_{V_f∪V_b} ∧ [C_b⋊]_{C_f∪C_b}) → [⋊⋉]_{S_f}
  ((tierEmptyLang isHarmonyingVowel ⊓
      tierEndsWithLang isDorsal .backDorsal)ᶜ ⊔ tierEmptyLang isSuffixFront)

/-- **Uyghur backness harmony ∈ BTD₁** (Lambert 2026 §4.3, eq. (35),
refining @cite{mayer-major-2018}). Constructive witness: the
formalised `uyghurBacknessLang` is the intersection of four
implications, each `Aᶜ ⊔ B` where `A` and `B` are
`IsTierBased (IsDefinite 1)` (each is a tier-projected single-suffix
test). The BTD membership follows from `BoolClosure.{base, compl,
union, inter}` applied to the four atomic tier-projected definite
languages. -/
theorem uyghur_backness_isBTD : ∃ k, IsBTD k uyghurBacknessLang := by
  refine ⟨1, ?_⟩
  -- Atomic IsBTD witnesses for the eight tier-projected definite tests.
  have hVf : IsBTD 1 (tierEndsWithLang isHarmonyingVowel .frontVowel) :=
    .base (tierEndsWithLang_isTierBased _ _)
  have hVb : IsBTD 1 (tierEndsWithLang isHarmonyingVowel .backVowel) :=
    .base (tierEndsWithLang_isTierBased _ _)
  have hCf : IsBTD 1 (tierEndsWithLang isDorsal .frontDorsal) :=
    .base (tierEndsWithLang_isTierBased _ _)
  have hCb : IsBTD 1 (tierEndsWithLang isDorsal .backDorsal) :=
    .base (tierEndsWithLang_isTierBased _ _)
  have hVempty : IsBTD 1 (tierEmptyLang isHarmonyingVowel) :=
    .base (tierEmptyLang_isTierBased _)
  have hSf : IsBTD 1 (tierEmptyLang isSuffixFront) :=
    .base (tierEmptyLang_isTierBased _)
  have hSb : IsBTD 1 (tierEmptyLang isSuffixBack) :=
    .base (tierEmptyLang_isTierBased _)
  -- Build the four implications.
  have impA : IsBTD 1 ((tierEndsWithLang isHarmonyingVowel .frontVowel)ᶜ ⊔
                       tierEmptyLang isSuffixBack) :=
    .union hVf.compl hSb
  have impB : IsBTD 1 ((tierEndsWithLang isHarmonyingVowel .backVowel)ᶜ ⊔
                       tierEmptyLang isSuffixFront) :=
    .union hVb.compl hSf
  have impC : IsBTD 1 ((tierEmptyLang isHarmonyingVowel ⊓
                          tierEndsWithLang isDorsal .frontDorsal)ᶜ ⊔
                       tierEmptyLang isSuffixBack) :=
    .union (hVempty.inter hCf).compl hSb
  have impD : IsBTD 1 ((tierEmptyLang isHarmonyingVowel ⊓
                          tierEndsWithLang isDorsal .backDorsal)ᶜ ⊔
                       tierEmptyLang isSuffixFront) :=
    .union (hVempty.inter hCb).compl hSf
  -- Conjunction (matching `uyghurBacknessLang`'s left-associative parsing).
  exact ((impA.inter impB).inter impC).inter impD


-- ============================================================================
-- § 4. Karanga Shona verb-stem tone ∈ BTLI
-- ============================================================================

/-- Karanga Shona tone alphabet @cite{odden-1984} @cite{lambert-2026}
§5.6: low (ℓ) and high (h). -/
inductive KShoTone | low | high
  deriving DecidableEq, Repr

/-- Karanga Shona verb-stem tone language (post-hyphen material). The
seven fully specified words are `ℓ, ℓh, ℓhℓ, h, hℓ, hℓh, hhℓh` (Lambert
2026 §5.6 example (45) data row, paper p. 19); longer forms fall into
one of two patterns: `ℓhhℓ ℓ*` for ℓ-toned roots and `hhhℓ ℓ* h` for
h-toned roots (described in prose just below (45)). See file docstring
for the @cite{jardine-2020} scope-restriction disclaimer. -/
def karangaShonaVerbStemLang : Language KShoTone :=
  Set.univ -- placeholder; see karanga_shona_verb_stem_isBTLI TODO

/-- **Karanga Shona verb-stem tone ∈ BTLI** (Lambert 2026 §5.6, refining
@cite{jardine-2020}). The witness is `φ_F ∨ L_m ∨ H_m`, where `φ_F` is
the finite-language part covering the seven fully specified words
(defined in prose just above paper eq. (46), no equation number),
`L_m = ⋊ℓhhℓ ∧ [⋊hh⋉]_{h}` is the ℓ-toned-root multitier-definite part
per Lambert (2026) (48), and `H_m = ⋊hhhℓ ∧ ℓh⋉ ∧ [⋊hhhh⋉]_{h}` is the
h-toned-root multitier-definite part per (49). Note that paper (47) is
the *piecewise testable* h-toned witness `H_p` — not part of the
multitier disjunction — so the citation range is (48)-(49), not
(47)-(49). Each disjunct is in `IsBTC IsGeneralizedDefinite`; the
disjunction stays in BTLI by Boolean closure.

TODO: discharge the witness construction. The structural proof is a
straightforward Boolean combination of edge-definite tests (for the
left-anchored substrings) and tier-projected count constraints (for the
high-tone-tier suffix patterns). -/
theorem karanga_shona_verb_stem_isBTLI :
    ∃ k, IsBTLI k karangaShonaVerbStemLang := by
  sorry

-- ============================================================================
-- § 5. Tsuut'ina asymmetric harmony ∈ TSL_2 ∖ BTLI
-- ============================================================================

/-- The Tsuut'ina sibilant alphabet @cite{cook-1978} is the shared
three-class `SibilantTierSeg` (anterior `s`, posterior `ʃ`, neutral
non-sibilant) defined in `Theories/Phonology/SibilantTier.lean`. -/
abbrev TsuutinaSeg := Theories.Phonology.SibilantTier.SibilantTierSeg

/-- The TSL_2 grammar for Tsuut'ina asymmetric sibilant harmony
@cite{cook-1978} @cite{lambert-2026} §4.2: anterior preceding posterior
on the sibilant tier is forbidden. Reuses the shared substrate
`asymmetricHarmonyAntFirst` from `Theories/Phonology/SibilantTier.lean`. -/
def tsuutinaTSLGrammar : TSLGrammar 2 TsuutinaSeg :=
  Theories.Phonology.SibilantTier.asymmetricHarmonyAntFirst

/-- The Tsuut'ina asymmetric sibilant harmony language. Defined as the
language of the TSL_2 witness so that the membership theorem is
definitional. -/
def tsuutinaLang : Language TsuutinaSeg := tsuutinaTSLGrammar.lang

/-- **Tsuut'ina asymmetric harmony ∈ TSL_2** (Lambert 2026 §4.2).
Definitional witness: the TSL_2 grammar `tsuutinaTSLGrammar`. -/
theorem tsuutina_isTSL2 : IsTierStrictlyLocal 2 tsuutinaLang :=
  ⟨tsuutinaTSLGrammar, rfl⟩

/-- **Tsuut'ina asymmetric harmony ∉ BTLI** (Lambert 2026 §4.2, parametrised
counterexample). -/
theorem tsuutina_not_isBTLI : ∀ k, ¬ IsBTLI k tsuutinaLang := by
  sorry

-- ============================================================================
-- § 6. Luganda high-tone plateauing ∈ J ∖ BTLI
-- ============================================================================

/-- Luganda tone alphabet @cite{hyman-katamba-2010}: low (ℓ) and high (h),
following @cite{jardine-2020}'s identification of "intermediate" with low
in the input. -/
inductive LugandaTone | low | high
  deriving DecidableEq, Repr

/-- The Luganda high-tone plateauing predicate @cite{lambert-2026} (37):
no `[h, ℓ, h]` subsequence (at most one high span), and if any high tone
appears then there is a later low (`[h, ℓ]` is a subsequence). -/
def lugandaPred (w : List LugandaTone) : Prop :=
  ¬ ([LugandaTone.high, .low, .high] <+ w) ∧
    (LugandaTone.high ∈ w → [LugandaTone.high, .low] <+ w)

/-- The Luganda high-tone plateauing language. -/
def lugandaLang : Language LugandaTone := { w | lugandaPred w }

/-- Membership in `lugandaLang` is membership in `lugandaPred`. -/
@[simp] lemma mem_lugandaLang (w : List LugandaTone) :
    w ∈ lugandaLang ↔ lugandaPred w := Iff.rfl

/-- **Luganda high-tone plateauing ∈ PT_3** (Lambert 2026 (37)). The
predicate depends only on length-≤-3 subsequence presence: the
length-3 `[h, ℓ, h]`, the length-2 `[h, ℓ]`, and the length-1 `[h]`.

The proof reduces each conjunct of `lugandaPred` to the corresponding
`subseqSet 3` membership question, then transfers via
`subseqSet_eq_iff`. -/
theorem luganda_isPT : IsPiecewiseTestable 3 lugandaLang := by
  intro w₁ w₂ heq
  simp only [mem_lugandaLang, lugandaPred]
  -- Bridge: `LugandaTone.high ∈ w` ↔ `[high] <+ w`
  have mem_iff_sublist : ∀ (w : List LugandaTone),
      LugandaTone.high ∈ w ↔ [LugandaTone.high] <+ w := by
    intro w; exact ⟨fun h => List.singleton_sublist.mpr h, fun h => List.singleton_sublist.mp h⟩
  have h3 : ([LugandaTone.high, .low, .high] <+ w₁) ↔
            ([LugandaTone.high, .low, .high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (3 : ℕ) ≤ 3)
  have h2 : ([LugandaTone.high, .low] <+ w₁) ↔
            ([LugandaTone.high, .low] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (2 : ℕ) ≤ 3)
  have h1 : ([LugandaTone.high] <+ w₁) ↔ ([LugandaTone.high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (1 : ℕ) ≤ 3)
  rw [mem_iff_sublist, mem_iff_sublist]
  exact and_congr (not_congr h3) (imp_congr h1 h2)

/-- **Luganda high-tone plateauing ∉ BTLI** (Lambert 2026 §5.1).
Parametrised-word witness: `ℓᵏhhℓᵏ` is accepted while `ℓᵏhℓhℓᵏ` is
rejected, but the two share all length-`k` tier-affixes on every tier. -/
theorem luganda_not_isBTLI : ∀ k, ¬ IsBTLI k lugandaLang := by
  sorry

-- ============================================================================
-- § 7. Cross-framework refutation/cross-reference theorems (TODOs)
-- ============================================================================

/-! Audit-flagged cross-framework engagement points. These are stated here
so the disagreements (and convergences) with sibling linglib formalizations
are visible rather than buried.

Each is tagged with the auditor file path it cross-references. The proofs
are deferred — typically to a follow-up substrate PR (e.g. `OTBound.lean`)
or to the chronologically-later sibling study. -/

/-- **Lambert 2026 multitier classification structurally weaker than
SS-MTSL (de Santo & Graf 2019) on Uyghur**: every BTD language admits an
SS-MTSL acceptor, but BTD is strictly more powerful as a phonotactic
classifier — Uyghur backness harmony is BTD but @cite{mayer-major-2018}
shows it is not SS-MTSL. (Stated as TODO; activates when SS-MTSL
substrate lands in linglib.) -/
theorem btd_supersedes_ss_mtsl_on_uyghur : True := trivial
-- TODO: when SS-MTSL is formalized, replace with:
--   theorem btd_supersedes_ss_mtsl_on_uyghur :
--     IsBTD 2 uyghurBacknessLang ∧ ¬ IsSSMTSL uyghurBacknessLang

/-- **String-input information loss for autosegmental tone analyses**: two
distinct autosegmental representations (e.g. multiply-linked vs. singly-
linked-with-spread on a tone tier) can have the same surface string. The
BTC classification of a string language therefore is *not* a faithful
summary of an autosegmental analysis of the same surface tone pattern.
Cross-references `Theories/Phonology/Autosegmental/RegisterTier.lean`,
`GrammaticalTone.lean`, and `Phenomena/Tone/Studies/Lionnet2025.lean`. -/
theorem lambert_string_input_loses_tone_associations : True := trivial
-- TODO: state and prove via Theories.Phonology.Autosegmental.RegisterTier
-- representation distinctness with shared string projection.

end Phenomena.Phonotactics.Studies.Lambert2026
