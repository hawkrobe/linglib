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
open Theories.Phonology.SibilantTier  -- for SibilantTierSeg constructors in tsuutina refutation

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
-- § 2b. Finnish (Uralic): stress-initial ∈ K_1
-- ============================================================================

/-- Finnish stress @cite{suomi-toivanen-ylitalo-2008}: primary stress is
fixed to the initial syllable. The reverse-definite dual of Iban
stress-final, witnessing the `IsReverseDefinite 1` class @cite{lambert-2026}
§2.2. -/
def finnishGrammar : ReverseDefiniteGrammar 1 IbanSyl where
  permitted := { [.stressed] }

/-- The Finnish stress-initial language. -/
def finnishLang : Language IbanSyl := finnishGrammar.lang

/-- **Finnish stress-initial ∈ K_1** (Lambert 2026 §2.2, paper p. 5
example (6)). Definitional witness: the `ReverseDefiniteGrammar 1`
whose permitted initial 1-prefix is `[stressed]`. -/
theorem finnish_isReverseDefinite_one : IsReverseDefinite 1 finnishLang :=
  ⟨finnishGrammar, rfl⟩

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

/-! ### Atomic IsGeneralizedDefinite languages (uniform `k = 5`)

Each component of Lambert's `φ_F ∨ L_m ∨ H_m` reduces to a Boolean
combination of edge-anchored substring tests and tier-projected
substring tests. We encode each as a `Language KShoTone` and prove it's
`IsGeneralizedDefinite 5` directly via `List.take_take` /
`List.drop_drop`-style structural arguments. The uniform `k = 5` is
chosen as `1 + max(prefix length, suffix length, tier-projection
length, max φ_F word length) = 1 + 4`. -/

/-- "Word starts with `xs`": the language `{w | w.take xs.length = xs}`. -/
def startsWithLang (xs : List KShoTone) : Language KShoTone :=
  { w | w.take xs.length = xs }

/-- "Word ends with `xs`": the language `{w | w.drop (w.length - xs.length) = xs}`. -/
def endsWithLang (xs : List KShoTone) : Language KShoTone :=
  { w | w.drop (w.length - xs.length) = xs }

/-- "Tier-projection by `T` equals exactly `xs`": the language
`{w | w.filter T = xs}`. -/
def tierEqualLang (T : KShoTone → Bool) (xs : List KShoTone) :
    Language KShoTone :=
  { w | w.filter T = xs }

/-- Boolean tier predicate for `h`-tier (high tones only). -/
def isHigh : KShoTone → Bool
  | .high => true
  | .low => false

/-! ### IsGeneralizedDefinite witnesses at `k = 5`

Unfolding helper: `Edge.left.takeAt k w = w.take k` and
`Edge.right.takeAt k w = w.drop (w.length - k)` by `rfl`. The
hypotheses from `IsGeneralizedDefinite k` come in the `Edge.takeAt`
form; we unfold via `show` at the top of each proof. -/

/-- `startsWithLang xs` is `IsGeneralizedDefinite k` for any `k ≥
xs.length`. Proof: same `k`-prefix on both words determines the
`xs.length`-prefix via `List.take_take`. -/
lemma startsWithLang_isGenDef (xs : List KShoTone) (k : ℕ)
    (hk : xs.length ≤ k) : IsGeneralizedDefinite k (startsWithLang xs) := by
  intro w₁ w₂ hpre _
  -- Unfold Edge.left.takeAt to List.take.
  change w₁.take k = w₂.take k at hpre
  have htake : w₁.take xs.length = w₂.take xs.length := by
    rw [show w₁.take xs.length = (w₁.take k).take xs.length by
          rw [List.take_take, min_eq_left hk],
        hpre, List.take_take, min_eq_left hk]
  exact Iff.intro
    (fun h => show w₂.take xs.length = xs from htake.symm.trans h)
    (fun h => show w₁.take xs.length = xs from htake.trans h)

/-- `endsWithLang xs` is `IsGeneralizedDefinite k` for any `k ≥
xs.length`. Symmetric to `startsWithLang_isGenDef`; the underlying
identity is `w.drop (w.length - xs.length) = (w.drop (w.length - k)).drop
(k - xs.length)` when `xs.length ≤ k ≤ w.length`. The general case
splits on whether `w` is shorter than `k`. -/
lemma endsWithLang_isGenDef (xs : List KShoTone) (k : ℕ)
    (hk : xs.length ≤ k) : IsGeneralizedDefinite k (endsWithLang xs) := by
  intro w₁ w₂ _ hsuf
  -- Unfold Edge.right.takeAt to List.drop.
  change w₁.drop (w₁.length - k) = w₂.drop (w₂.length - k) at hsuf
  -- The k-suffixes have equal length, so word lengths are related.
  have hlen_eq : min k w₁.length = min k w₂.length := by
    have h := congrArg List.length hsuf
    simp [List.length_drop] at h
    omega
  have hdrop : w₁.drop (w₁.length - xs.length) =
               w₂.drop (w₂.length - xs.length) := by
    by_cases hw1 : k ≤ w₁.length
    · -- Case: w₁.length ≥ k. Then min k w₁.length = k, so min k w₂.length = k, so w₂.length ≥ k.
      have hw2 : k ≤ w₂.length := by
        rw [min_eq_left hw1] at hlen_eq
        by_cases h : k ≤ w₂.length
        · exact h
        · push Not at h
          rw [min_eq_right (le_of_lt h)] at hlen_eq
          omega
      -- xs.suffix is inside k-suffix.
      rw [show w₁.length - xs.length = (w₁.length - k) + (k - xs.length) by omega,
          show w₂.length - xs.length = (w₂.length - k) + (k - xs.length) by omega,
          ← List.drop_drop, ← List.drop_drop, hsuf]
    · -- Case: w₁.length < k. Then min k w₁.length = w₁.length.
      push Not at hw1
      rw [min_eq_right (le_of_lt hw1)] at hlen_eq
      have hw1_drop : w₁.length - k = 0 := by omega
      rw [hw1_drop, List.drop_zero] at hsuf
      -- hsuf: w₁ = w₂.drop (w₂.length - k). Lengths: w₁.length = min k w₂.length.
      by_cases hw2 : k ≤ w₂.length
      · -- w₂.length ≥ k, but w₁.length = min k w₂.length = k ≥ w₁.length means w₁.length = k. Contradiction with hw1.
        rw [min_eq_left hw2] at hlen_eq
        omega
      · push Not at hw2
        have hw2_drop : w₂.length - k = 0 := by omega
        rw [hw2_drop, List.drop_zero] at hsuf
        -- hsuf: w₁ = w₂. So both .drop equal.
        rw [hsuf]
  exact Iff.intro
    (fun h => show w₂.drop (w₂.length - xs.length) = xs from hdrop.symm.trans h)
    (fun h => show w₁.drop (w₁.length - xs.length) = xs from hdrop.trans h)

/-- `tierEqualLang T xs` is `IsTierBased (IsGeneralizedDefinite k)` for
any `k > xs.length` (strict — without strictness, e.g. `{[h, h]}` is
not GeneralizedDefinite 2 since `[h, h, h]` and `[h, h]` share both
2-prefix and 2-suffix). -/
lemma tierEqualLang_isTierBased (T : KShoTone → Bool) (xs : List KShoTone)
    (k : ℕ) (hk : xs.length < k) :
    IsTierBased (IsGeneralizedDefinite k) (tierEqualLang T xs) := by
  refine ⟨T, {xs}, ?_, ?_⟩
  · ext w; show (w.filter T = xs) ↔ w.filter T ∈ ({xs} : Set _)
    simp [Set.mem_singleton_iff]
  · -- {xs} is IsGeneralizedDefinite k for k ≥ xs.length.
    -- Helper: a word `v` with `v.take k = xs` and `v.length ≤ k` (which we'll
    -- establish) must equal `xs`.
    have hxs_take : xs.take k = xs := List.take_of_length_le (le_of_lt hk)
    -- The forward direction: if w₁ = xs, derive w₂ = xs from `xs.take k = w₂.take k`.
    -- Since |xs| < k, we have |v.take k| = |xs| < k, forcing |v| < k, so v.take k = v.
    have key : ∀ v : List KShoTone, xs.take k = v.take k → v = xs := by
      intro v hv
      rw [hxs_take] at hv
      have hlen : xs.length = min k v.length := by
        have := congrArg List.length hv
        simpa [List.length_take] using this
      have hv_lt : v.length < k := by
        by_cases h : v.length ≤ k
        · rcases eq_or_lt_of_le h with heq | hlt
          · -- |v| = k. Then min k |v| = k. So |xs| = k, contradicting |xs| < k.
            rw [heq, min_self] at hlen; omega
          · exact hlt
        · -- |v| > k impossible since min k |v| = k = |xs| contradicts |xs| < k.
          push Not at h
          rw [min_eq_left (le_of_lt h)] at hlen; omega
      have hv_take : v.take k = v := List.take_of_length_le (le_of_lt hv_lt)
      rw [hv_take] at hv
      exact hv.symm
    intro w₁ w₂ hpre _
    change w₁.take k = w₂.take k at hpre
    show w₁ ∈ ({xs} : Set _) ↔ w₂ ∈ ({xs} : Set _)
    simp only [Set.mem_singleton_iff]
    constructor
    · intro h; exact key w₂ (h ▸ hpre)
    · intro h; exact key w₁ (h ▸ hpre.symm)

/-- The seven fully specified words from Lambert (2026) §5.6 (just above
eq. (46), paper p. 19). Max length 4 (`hhℓh`). -/
def kshonaSevenWords : List (List KShoTone) :=
  [[.low], [.low, .high], [.low, .high, .low],
   [.high], [.high, .low], [.high, .low, .high],
   [.high, .high, .low, .high]]

/-- The finite-language part `φ_F` of Lambert's witness — the seven
fully specified words. -/
def phi_F : Language KShoTone := { w | w ∈ kshonaSevenWords }

/-- `phi_F` is `IsGeneralizedDefinite 5`. Max word length is 4, so for
`k = 5 > 4`, any word of length ≤ 4 has `k`-prefix = whole word. Two
words with same 5-prefix and length ≤ 4 are equal; any word with
length > 4 has a 5-prefix of length 5 (or whole) which differs from
any short word's 5-prefix. -/
lemma phi_F_isGenDef : IsGeneralizedDefinite 5 phi_F := by
  intro w₁ w₂ hpre _
  change w₁.take 5 = w₂.take 5 at hpre
  show w₁ ∈ phi_F ↔ w₂ ∈ phi_F
  by_cases h1 : w₁.length ≤ 4
  · -- w₁.take 5 = w₁.
    have hw₁ : w₁.take 5 = w₁ := List.take_of_length_le (by omega)
    rw [hw₁] at hpre
    -- hpre : w₁ = w₂.take 5; |w₁| ≤ 4, so |w₂.take 5| ≤ 4, so |w₂| ≤ 4 too.
    have hlen_eq : w₁.length = (w₂.take 5).length := by rw [← hpre]
    rw [List.length_take] at hlen_eq
    have hw₂_le : w₂.length ≤ 4 := by omega
    have hw₂ : w₂.take 5 = w₂ := List.take_of_length_le (by omega)
    rw [hw₂] at hpre
    rw [show w₁ = w₂ from hpre]
  · -- w₁.length > 4, so w₁ ∉ phi_F.
    push Not at h1
    have h2 : 4 < w₂.length := by
      have hw₁_len : (w₁.take 5).length = 5 := by
        rw [List.length_take]; omega
      have hw₂_len : (w₂.take 5).length = 5 := by rw [← hpre]; exact hw₁_len
      rw [List.length_take] at hw₂_len; omega
    have hw₁_notin : w₁ ∉ phi_F := by
      intro hin
      simp [phi_F, kshonaSevenWords] at hin
      rcases hin with h | h | h | h | h | h | h <;>
        (rw [h] at h1; simp at h1)
    have hw₂_notin : w₂ ∉ phi_F := by
      intro hin
      simp [phi_F, kshonaSevenWords] at hin
      rcases hin with h | h | h | h | h | h | h <;>
        (rw [h] at h2; simp at h2)
    exact ⟨fun h => absurd h hw₁_notin, fun h => absurd h hw₂_notin⟩

/-- The Karanga Shona verb-stem tone language as the disjunction `φ_F
∨ L_m ∨ H_m` from Lambert (2026) §5.6 (formula appearing just after
eq. (49), paper p. 19). -/
def karangaShonaVerbStemLang : Language KShoTone :=
  -- φ_F: finite seven words
  phi_F ⊔
  -- L_m: ℓ-toned roots, multitier definite per (48)
  -- L_m = ⋊ℓhhℓ ∧ [⋊hh⋉]_{h}
  (startsWithLang [.low, .high, .high, .low] ⊓
    tierEqualLang isHigh [.high, .high]) ⊔
  -- H_m: h-toned roots, multitier definite per (49)
  -- H_m = ⋊hhhℓ ∧ ℓh⋉ ∧ [⋊hhhh⋉]_{h}
  (startsWithLang [.high, .high, .high, .low] ⊓
    endsWithLang [.low, .high] ⊓
    tierEqualLang isHigh [.high, .high, .high, .high])

/-- **Karanga Shona verb-stem tone ∈ BTLI₅** (Lambert 2026 §5.6,
refining @cite{jardine-2020}). Constructive witness for the disjunction
`φ_F ∨ L_m ∨ H_m` at uniform `k = 5`. Each disjunct lifts to
`IsBTC (IsGeneralizedDefinite 5)` via `IsTierBased.of_class` +
`BoolClosure.base`; the disjunction is closed by `BoolClosure.union`. -/
theorem karanga_shona_verb_stem_isBTLI :
    ∃ k, IsBTLI k karangaShonaVerbStemLang := by
  refine ⟨5, ?_⟩
  -- φ_F via direct IsGeneralizedDefinite + IsTierBased.of_class
  have hPhi : IsBTLI 5 phi_F := .base (.of_class phi_F_isGenDef)
  -- L_m components
  have hLm_pre : IsBTLI 5 (startsWithLang [.low, .high, .high, .low]) :=
    .base (.of_class (startsWithLang_isGenDef _ 5 (by decide)))
  have hLm_tier : IsBTLI 5 (tierEqualLang isHigh [.high, .high]) :=
    .base (tierEqualLang_isTierBased isHigh _ 5 (by decide))
  have hLm : IsBTLI 5
      (startsWithLang [.low, .high, .high, .low] ⊓
        tierEqualLang isHigh [.high, .high]) := .inter hLm_pre hLm_tier
  -- H_m components
  have hHm_pre : IsBTLI 5 (startsWithLang [.high, .high, .high, .low]) :=
    .base (.of_class (startsWithLang_isGenDef _ 5 (by decide)))
  have hHm_suf : IsBTLI 5 (endsWithLang [.low, .high]) :=
    .base (.of_class (endsWithLang_isGenDef _ 5 (by decide)))
  have hHm_tier : IsBTLI 5 (tierEqualLang isHigh [.high, .high, .high, .high]) :=
    .base (tierEqualLang_isTierBased isHigh _ 5 (by decide))
  have hHm : IsBTLI 5
      (startsWithLang [.high, .high, .high, .low] ⊓
        endsWithLang [.low, .high] ⊓
        tierEqualLang isHigh [.high, .high, .high, .high]) :=
    .inter (.inter hHm_pre hHm_suf) hHm_tier
  -- Disjunction
  exact .union (.union hPhi hLm) hHm

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

/-! ### Refutation: Tsuut'ina ∉ BTLI

Lambert (2026) §4.2 parameterised counterexample: for every `k`, the
words `ʃᵏ⁺¹sᵏ⁺¹` (accepted) and `ʃᵏ s ʃ sᵏ` (rejected) share the
length-`k` tier-prefix and length-`k` tier-suffix on every Bool tier.
The 8-tier enumeration (3 alphabet classes × 2 keep/drop choices)
collapses to 4 because both witnesses contain no neutral material; on
the three non-empty Bool combinations of (anterior, posterior), the
tier-projected words are **equal** (cases 2-3) or have **matching**
length-`k` affixes (case 1: both kinds kept, the `s` and `ʃ` swap in
the middle of the rejected word doesn't reach the length-`k` window). -/

/-- The accepted Tsuut'ina parameterised witness `ʃᵏ⁺¹ sᵏ⁺¹`. Sibilant
tier projection: `posterior^(k+1) ++ anterior^(k+1)` — no anterior
precedes any posterior. -/
abbrev tsuutinaAccepted (k : ℕ) : List TsuutinaSeg :=
  List.replicate (k + 1) SibilantTierSeg.posterior ++ List.replicate (k + 1) SibilantTierSeg.anterior

/-- The rejected Tsuut'ina parameterised witness `ʃᵏ s ʃ sᵏ`. The
internal `[anterior, posterior]` is the forbidden adjacency on the
sibilant tier. -/
abbrev tsuutinaRejected (k : ℕ) : List TsuutinaSeg :=
  List.replicate k SibilantTierSeg.posterior ++ [SibilantTierSeg.anterior, SibilantTierSeg.posterior] ++ List.replicate k SibilantTierSeg.anterior

/-! Proof recipe for `tsuutina_not_isBTLI` (TODO):

1. **Tier-affix equality**: prove `tsuutina_tierAffixes (k : ℕ) (T : TsuutinaSeg → Bool)` —
   for every Bool tier, `Edge.left.takeAt k ((tsuutinaAccepted k).filter T) =
   Edge.left.takeAt k ((tsuutinaRejected k).filter T)` and the symmetric for
   `Edge.right.takeAt`. Case-split on `(T anterior, T posterior)` — `T neutral`
   is irrelevant (no neutral material in either witness):
   - `(false, false)`: both filtered = `[]`.
   - `(true, false)`: both filtered = `anterior^(k+1)`.
   - `(false, true)`: both filtered = `posterior^(k+1)`.
   - `(true, true)`: filtered accepted = `posterior^(k+1) ++ anterior^(k+1)`,
     filtered rejected = `posterior^k ++ [anterior, posterior] ++ anterior^k`.
     Both have length `2k+2`. Length-`k` prefix is `posterior^k` for both;
     length-`k` suffix is `anterior^k` for both.

2. **Indistinguishability**: combine via `IsBTC.indist_isGenDef_of_tierAffixes`
   to get `IsBTC.Indist (IsGeneralizedDefinite k) (tsuutinaAccepted k) (tsuutinaRejected k)`.

3. **Membership separation**: prove
   - `tsuutinaAccepted k ∈ tsuutinaLang`: via `mem_ofForbiddenPairs_lang_iff_filter_isChain`;
     filtered = `posterior^(k+1) ++ anterior^(k+1)`, no adjacent (anterior, posterior)
     pair, so `IsChain (¬ antPostForbidden)`.
   - `tsuutinaRejected k ∉ tsuutinaLang`: filtered contains adjacent
     `[anterior, posterior]` (the middle two characters), violating `IsChain`.

4. **Refutation**: `not_isBTC_of_indist` from `IsBTC.Indist` + membership separation
   directly gives `¬ IsBTLI k tsuutinaLang`.

The Lean infrastructure is in place via `IsBTC.Indist`, `IsBTC.mem_iff_of_indist`,
`not_isBTC_of_indist`, `IsBTC.indist_isGenDef_of_tierAffixes` (`Subregular/Multitier.lean`).
The remaining work is the per-witness combinatorial reasoning over `List.replicate`
and `List.filter`. -/

/-- **Tsuut'ina asymmetric harmony ∉ BTLI** (Lambert 2026 §4.2, parametrised
counterexample). The witnesses `tsuutinaAccepted k` and `tsuutinaRejected k`
satisfy the Lambert-style "shared length-`k` tier-affixes on every tier"
property; the framework `not_isBTC_of_indist` then refutes BTLI membership. -/
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
