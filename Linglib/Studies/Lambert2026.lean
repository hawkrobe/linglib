/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Definite
import Linglib.Core.Computability.Subregular.PiecewiseTestable
import Linglib.Core.Computability.Subregular.Sandwich
import Linglib.Core.Computability.Subregular.Tier
import Linglib.Core.Computability.Subregular.Multitier
import Linglib.Core.Computability.Subregular.ForbiddenPairs
import Linglib.Phonology.Subregular.Sibilant
import Linglib.Phonology.Subregular.Agree

/-!
# [lambert-2026]: Multitier phonotactics with logic and algebra

Lambert (2026) classifies attested phonotactic constraints — bounded and
unbounded stress, harmony, and tone across ~13 languages — into the
multitier (Boolean closure of tier-projected) extensions of definite,
generalized definite, and finite-or-cofinite classes. Headline empirical
claims:

* **Uyghur backness harmony is multitier definite (BTD)** — strictly
  weaker than the multiple-tier-based strictly local class of
  [de-santo-graf-2019], settling (categorically) the challenge raised
  by [mayer-major-2018].
* **Karanga Shona tone is multitier generalized definite (BTLI)** — no
  more complex than the default-to-opposite unbounded stress patterns,
  refining the melody-local analysis of [jardine-2020].

The propositional logic is `BoolClosure (IsTierBased 𝒞)` for `𝒞` in
{`IsDefinite k`, `IsGeneralizedDefinite k`, `IsStrictlyLocal k`,
`IsStrictlyPiecewise k`, `IsFiniteOrCofinite`}; the algebraic side is
the syntactic-semigroup characterization of each class via Eilenberg
[eilenberg-1976] variety equations (e.g., `D = ⟦sx̄ = x̄⟧`,
`ℒℐ = ⟦x^ω y x^ω z x^ω = x^ω y x^ω⟧` per [straubing-1985] and
[almeida-1995]). The Lean substrate (`BoolClosure`, `IsBTC`,
`IsTierBased`) lives in `Subregular/Multitier.lean`; the algebraic
characterization is queued for a future `SyntacticMonoid` PR.

## Disclaimer 1: McCollum (2019) Uyghur gradience (linglib audit)

This disclaimer is **not** a scope qualification carried by Lambert
(2026); the paper does not cite McCollum. It is a linglib-internal
audit annotation: Lambert's BTD analysis is faithful to
[mayer-major-2018]'s **categorical idealization**, and a separate
literature line — [mccollum-2019] — argues the suffix backness
assignment is not categorical in the way the multitier-definite formula
requires. The "arbitrarily specified, statistical tendency to be back"
clause that Mayer & Major report for the no-V no-C case is precisely
the locus where McCollum's gradient data resists categorical analysis.
The headline theorem `uyghur_backness_isBTD` characterizes the
categorical pattern only; the gradience is out of scope.

## Disclaimer 2: Karanga Shona scope restriction

The BTLI analysis applies to the **verb-stem** domain (post-hyphen
material in Lambert (2026) (45)). [jardine-2020]'s motivation for a
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
  theorem are queued for a future `Phonology/Subregular/OTBound.lean`.
* Harmonic Serialism: `Studies/McPhersonLamont2026.lean`
  proves Poko surface tone HS-derivable but parallel-OT-impossible.
  Lambert's static BTC characterization, applied to Poko's surface
  stringset, would clarify *static description ≠ alternation
  explanation*. Cross-reference to be added when Poko's surface
  stringset is independently classified.
* Autosegmental: linglib's `Phonology/Autosegmental/{
  RegisterTier, GrammaticalTone}.lean` formalize multiply-linked tone
  representations. Lambert (2026) §5 self-confesses that string-based
  analysis loses information for tone; the loss theorem is stated as
  `lambert_string_input_loses_tone_associations` (sorry'd) below.
* OCP: `Phonology/Subregular/OCP.lean` carries a
  prohibition-vs-merger distinction; `IsBTC` is the mathematical home of
  the prohibition family at scale. The OCP file's docstring should gain
  a "see also: BTC" link in a follow-up retrofit.
* Structure-sensitive MTSL [de-santo-graf-2019]: not formalized in
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

namespace Lambert2026

open Core.Computability.Subregular
open List  -- for `<+` (List.Sublist) infix in subseqSet equivalence proofs
open Phonology (Sibilant)
open Phonology.Subregular  -- for `TSLGrammar.agree`

-- ============================================================================
-- § 1. Iban (Austronesian): stress-final ∈ D_1
-- ============================================================================

/-- Iban syllable type [omar-1969]: stressed (`σ́`) or unstressed (`σ`).
The two-letter alphabet of Lambert (2026) §2.1. -/
inductive IbanSyl | unstressed | stressed
  deriving DecidableEq, Repr

/-- The Iban stress-final language: a word is well-formed iff its final
syllable is stressed [omar-1969]. As a `DefiniteGrammar 1`: the
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

/-- Amara stress [thurston-1966]: penultimate-syllable stress with the
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

/-- Finnish stress [suomi-toivanen-ylitalo-2008]: primary stress is
fixed to the initial syllable. The reverse-definite dual of Iban
stress-final, witnessing the `IsReverseDefinite 1` class [lambert-2026]
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

/-- Uyghur segment classes relevant to backness harmony [mayer-major-2018]
[lambert-2026] (33)-(35): front vowels, back vowels, transparent (i, e),
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
see file docstring for the [mccollum-2019] gradience disclaimer. -/
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
refining [mayer-major-2018]). Constructive witness: the
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

/-- Karanga Shona tone alphabet [odden-1984] [lambert-2026]
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

/-- "Word starts with `xs`": the language `{w | w.take xs.length = xs}`.
Originally introduced for `KShoTone` but α-generic; also reused for
`LugandaTone` in §10 Kagoshima Japanese. -/
def startsWithLang {α : Type*} (xs : List α) : Language α :=
  { w | w.take xs.length = xs }

/-- "Word ends with `xs`": the language `{w | w.drop (w.length - xs.length) = xs}`.
α-generic, reused for `LugandaTone` in §10 Kagoshima Japanese. -/
def endsWithLang {α : Type*} (xs : List α) : Language α :=
  { w | w.drop (w.length - xs.length) = xs }

/-- "Tier-projection by `T` equals exactly `xs`": the language
`{w | w.filter T = xs}`. α-generic, reused for `LugandaTone` in §10
Kagoshima Japanese. -/
def tierEqualLang {α : Type*} (T : α → Bool) (xs : List α) :
    Language α :=
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
`xs.length`-prefix via `List.take_take`. α-generic. -/
lemma startsWithLang_isGenDef {α : Type*} (xs : List α) (k : ℕ)
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
lemma endsWithLang_isGenDef {α : Type*} (xs : List α) (k : ℕ)
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
lemma tierEqualLang_isTierBased {α : Type*} (T : α → Bool) (xs : List α)
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
    have key : ∀ v : List α, xs.take k = v.take k → v = xs := by
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
  (startsWithLang ([.low, .high, .high, .low] : List KShoTone) ⊓
    tierEqualLang isHigh [.high, .high]) ⊔
  -- H_m: h-toned roots, multitier definite per (49)
  -- H_m = ⋊hhhℓ ∧ ℓh⋉ ∧ [⋊hhhh⋉]_{h}
  (startsWithLang ([.high, .high, .high, .low] : List KShoTone) ⊓
    endsWithLang ([.low, .high] : List KShoTone) ⊓
    tierEqualLang isHigh [.high, .high, .high, .high])

/-- **Karanga Shona verb-stem tone ∈ BTLI₅** (Lambert 2026 §5.6,
refining [jardine-2020]). Constructive witness for the disjunction
`φ_F ∨ L_m ∨ H_m` at uniform `k = 5`. Each disjunct lifts to
`IsBTC (IsGeneralizedDefinite 5)` via `IsTierBased.of_class` +
`BoolClosure.base`; the disjunction is closed by `BoolClosure.union`. -/
theorem karanga_shona_verb_stem_isBTLI :
    ∃ k, IsBTLI k karangaShonaVerbStemLang := by
  refine ⟨5, ?_⟩
  -- φ_F via direct IsGeneralizedDefinite + IsTierBased.of_class
  have hPhi : IsBTLI 5 phi_F := .base (.of_class phi_F_isGenDef)
  -- L_m components
  have hLm_pre : IsBTLI 5 (startsWithLang ([.low, .high, .high, .low] : List KShoTone)) :=
    .base (.of_class (startsWithLang_isGenDef _ 5 (by decide)))
  have hLm_tier : IsBTLI 5 (tierEqualLang isHigh [.high, .high]) :=
    .base (tierEqualLang_isTierBased isHigh _ 5 (by decide))
  have hLm : IsBTLI 5
      (startsWithLang ([.low, .high, .high, .low] : List KShoTone) ⊓
        tierEqualLang isHigh [.high, .high]) := .inter hLm_pre hLm_tier
  -- H_m components
  have hHm_pre : IsBTLI 5 (startsWithLang ([.high, .high, .high, .low] : List KShoTone)) :=
    .base (.of_class (startsWithLang_isGenDef _ 5 (by decide)))
  have hHm_suf : IsBTLI 5 (endsWithLang ([.low, .high] : List KShoTone)) :=
    .base (.of_class (endsWithLang_isGenDef _ 5 (by decide)))
  have hHm_tier : IsBTLI 5 (tierEqualLang isHigh [.high, .high, .high, .high]) :=
    .base (tierEqualLang_isTierBased isHigh _ 5 (by decide))
  have hHm : IsBTLI 5
      (startsWithLang ([.high, .high, .high, .low] : List KShoTone) ⊓
        endsWithLang ([.low, .high] : List KShoTone) ⊓
        tierEqualLang isHigh [.high, .high, .high, .high]) :=
    .inter (.inter hHm_pre hHm_suf) hHm_tier
  -- Disjunction
  exact .union (.union hPhi hLm) hHm

-- ============================================================================
-- § 5. Tsuut'ina asymmetric harmony ∈ TSL_2 ∖ BTLI
-- ============================================================================

/-! ### Sibilant-harmony grammars over the shared `Sibilant` alphabet

Both asymmetric directions plus the symmetric foil, over the shared
`Phonology.Sibilant` substrate. Lambert's classification draws the
symmetric-vs-asymmetric comparison: the symmetric grammar is the [hansson-2010]
Navajo profile (`TSLGrammar.agree`, disagreement forbidden in both directions),
the anterior-first asymmetric grammar the [cook-1978] Tsuut'ina profile. -/

/-- Forbidden-pair relation: anterior immediately preceding posterior on the tier
(the [cook-1978] Tsuut'ina adjacency). -/
def antPostForbidden : Sibilant → Sibilant → Prop
  | .anterior, .posterior => True
  | _, _ => False

instance : DecidableRel antPostForbidden
  | .anterior, .posterior => isTrue trivial
  | .anterior, .anterior => isFalse not_false
  | .anterior, .neutral => isFalse not_false
  | .posterior, _ => isFalse not_false
  | .neutral, _ => isFalse not_false

/-- Tsuut'ina-style asymmetric harmony: anterior-before-posterior forbidden on the
tier, the reverse permitted. -/
def asymmetricHarmonyAntFirst : TSLGrammar 2 Sibilant :=
  TSLGrammar.ofForbiddenPairs antPostForbidden Sibilant.onTier

/-- Dual forbidden-pair relation: posterior immediately preceding anterior. -/
def postAntForbidden : Sibilant → Sibilant → Prop
  | .posterior, .anterior => True
  | _, _ => False

instance : DecidableRel postAntForbidden
  | .posterior, .anterior => isTrue trivial
  | .posterior, .posterior => isFalse not_false
  | .posterior, .neutral => isFalse not_false
  | .anterior, _ => isFalse not_false
  | .neutral, _ => isFalse not_false

/-- Posterior-first asymmetric harmony grammar (the mirror of
`asymmetricHarmonyAntFirst`). -/
def asymmetricHarmonyPostFirst : TSLGrammar 2 Sibilant :=
  TSLGrammar.ofForbiddenPairs postAntForbidden Sibilant.onTier

/-- Symmetric sibilant harmony: any tier-adjacent disagreement forbidden — the
[hansson-2010] Navajo profile, the foil for the asymmetric comparison. -/
def symmetricHarmony : TSLGrammar 2 Sibilant :=
  TSLGrammar.agree Sibilant.onTier

/-- The symmetric language is contained in the anterior-first asymmetric language:
forbidding disagreement in both directions rules out everything the one-direction
constraint does, and more. -/
theorem symmetricHarmony_lang_subset_asymAntFirst :
    symmetricHarmony.lang ≤ asymmetricHarmonyAntFirst.lang :=
  lang_antitone_R (R := antPostForbidden) (R' := (· ≠ ·))
    (fun a b h => by cases a <;> cases b <;> simp_all [antPostForbidden])
    Sibilant.onTier

/-- Dual inclusion against the posterior-first asymmetric language. -/
theorem symmetricHarmony_lang_subset_asymPostFirst :
    symmetricHarmony.lang ≤ asymmetricHarmonyPostFirst.lang :=
  lang_antitone_R (R := postAntForbidden) (R' := (· ≠ ·))
    (fun a b h => by cases a <;> cases b <;> simp_all [postAntForbidden])
    Sibilant.onTier

/-- The Tsuut'ina sibilant alphabet ([cook-1978]) is the shared three-class
`Phonology.Sibilant` (anterior `s`, posterior `ʃ`, neutral non-sibilant). -/
abbrev TsuutinaSeg := Sibilant

/-- The TSL_2 grammar for Tsuut'ina asymmetric sibilant harmony ([cook-1978];
Lambert's asymmetric classification): anterior preceding posterior on the
sibilant tier is forbidden, the reverse permitted. -/
def tsuutinaTSLGrammar : TSLGrammar 2 TsuutinaSeg :=
  asymmetricHarmonyAntFirst

/-- The Tsuut'ina asymmetric sibilant harmony language. Defined as the
language of the TSL_2 witness so that the membership theorem is
definitional. -/
def tsuutinaLang : Language TsuutinaSeg := tsuutinaTSLGrammar.lang

/-- **Tsuut'ina asymmetric harmony ∈ TSL_2**. Definitional witness: the
TSL_2 grammar `tsuutinaTSLGrammar`. -/
theorem tsuutina_isTSL2 : IsTierStrictlyLocal 2 tsuutinaLang :=
  ⟨tsuutinaTSLGrammar, rfl⟩

/-! ### Refutation: Tsuut'ina ∉ BTLI

Lambert's parameterised counterexample: for every `k`, the
words `ʃᵏ⁺¹sᵏ⁺¹` (accepted) and `ʃᵏ s ʃ sᵏ` (rejected) share the
length-`k` tier-prefix and length-`k` tier-suffix on every Bool tier.
Both witnesses are sandwiches with **asymmetric** bookends `posterior`
on the left and `anterior` on the right; widths differ between
witnesses (`k+1` for accepted, `k` for rejected). The 8-tier
enumeration (3 alphabet classes × 2 keep/drop) collapses to 4 since the
witnesses contain no neutrals.

The substrate `Sandwich` (in `Core/Computability/Subregular/Sandwich.lean`)
handles the (true, true) case directly via `takeAt_*_sandwich` (the
bookends are wide enough); the other three cases reduce to filtered
words being equal (after a `replicate_succ` rewrite to merge the middle
contribution into the bookend). -/

/-- The accepted Tsuut'ina parameterised witness `ʃᵏ⁺¹ sᵏ⁺¹`. Sibilant
tier projection: `posterior^(k+1) ++ anterior^(k+1)` — no anterior
precedes any posterior. -/
abbrev tsuutinaAccepted (k : ℕ) : List TsuutinaSeg :=
  sandwich (k + 1) Sibilant.posterior [] (k + 1) Sibilant.anterior

/-- The rejected Tsuut'ina parameterised witness `ʃᵏ s ʃ sᵏ`. The
internal `[anterior, posterior]` is the forbidden adjacency on the
sibilant tier. -/
abbrev tsuutinaRejected (k : ℕ) : List TsuutinaSeg :=
  sandwich k Sibilant.posterior [.anterior, .posterior] k Sibilant.anterior

/-- Tier-affix equality on every Bool tier. Case-split on
`(T posterior, T anterior)`. The (true, true) case applies the
substrate's `takeAt_*_sandwich` directly (bookends wide enough). The
other three cases collapse the filtered witnesses to a single replicate
(with `replicate_succ` to merge bookend + middle contribution). -/
private lemma tsuutina_tierAffixes (k : ℕ) (T : TsuutinaSeg → Bool) :
    Edge.left.takeAt k ((tsuutinaAccepted k).filter T) =
      Edge.left.takeAt k ((tsuutinaRejected k).filter T) ∧
    Edge.right.takeAt k ((tsuutinaAccepted k).filter T) =
      Edge.right.takeAt k ((tsuutinaRejected k).filter T) := by
  unfold tsuutinaAccepted tsuutinaRejected
  match h_post : T Sibilant.posterior, h_ant : T Sibilant.anterior with
  | false, false =>
    have h_post' : ¬ T Sibilant.posterior = true := by simp [h_post]
    have h_ant' : ¬ T Sibilant.anterior = true := by simp [h_ant]
    rw [filter_sandwich_of_neg_neg h_post' h_ant',
        filter_sandwich_of_neg_neg h_post' h_ant']
    have h_rej : ([Sibilant.anterior, .posterior] : List _).filter T = [] := by
      simp [List.filter_cons_of_neg h_ant', List.filter_cons_of_neg h_post']
    simp [h_rej]
  | true, false =>
    have h_ant' : ¬ T Sibilant.anterior = true := by simp [h_ant]
    rw [filter_sandwich_of_pos_neg h_post h_ant',
        filter_sandwich_of_pos_neg h_post h_ant']
    -- accepted: replicate (k+1) post ++ [].filter T = replicate (k+1) post
    -- rejected: replicate k post ++ [post] = replicate (k+1) post
    have h_rej : ([Sibilant.anterior, .posterior] : List _).filter T =
                 [Sibilant.posterior] := by
      simp [List.filter_cons_of_neg h_ant', List.filter_cons_of_pos h_post]
    rw [List.filter_nil, List.append_nil, h_rej, ← List.replicate_succ']
    exact ⟨rfl, rfl⟩
  | false, true =>
    have h_post' : ¬ T Sibilant.posterior = true := by simp [h_post]
    rw [filter_sandwich_of_neg_pos h_post' h_ant,
        filter_sandwich_of_neg_pos h_post' h_ant]
    -- accepted: [].filter T ++ replicate (k+1) ant = replicate (k+1) ant
    -- rejected: [ant] ++ replicate k ant = replicate (k+1) ant
    have h_rej : ([Sibilant.anterior, .posterior] : List _).filter T =
                 [Sibilant.anterior] := by
      simp [List.filter_cons_of_pos h_ant, List.filter_cons_of_neg h_post']
    rw [List.filter_nil, List.nil_append, h_rej]
    show (Sibilant.anterior :: List.replicate k Sibilant.anterior).take k =
         (List.replicate (k + 1) Sibilant.anterior).take k ∧
         (Sibilant.anterior :: List.replicate k Sibilant.anterior).drop _ =
         (List.replicate (k + 1) Sibilant.anterior).drop _
    rw [← List.replicate_succ]
    exact ⟨rfl, rfl⟩
  | true, true =>
    rw [filter_sandwich_of_pos_pos h_post h_ant,
        filter_sandwich_of_pos_pos h_post h_ant,
        takeAt_left_sandwich (Nat.le_succ k), takeAt_left_sandwich (le_refl k),
        takeAt_right_sandwich (Nat.le_succ k), takeAt_right_sandwich (le_refl k)]
    exact ⟨rfl, rfl⟩

/-- The accepted Tsuut'ina witness lies in `tsuutinaLang`. The sibilant
tier projection is the witness itself (no neutral material), and on
that string the only adjacency types are `(posterior, posterior)`,
`(posterior, anterior)` (the boundary), and `(anterior, anterior)` —
none of which equal the forbidden `(anterior, posterior)`. -/
private lemma tsuutinaAccepted_mem (k : ℕ) :
    tsuutinaAccepted k ∈ tsuutinaLang := by
  show tsuutinaAccepted k ∈ (TSLGrammar.ofForbiddenPairs antPostForbidden
                              Sibilant.onTier).lang
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  -- Filter to sibilants: identity since no neutrals in the witness.
  have h_filter : (tsuutinaAccepted k).filter
                    (fun x => decide (Sibilant.onTier x)) =
                  tsuutinaAccepted k := by
    unfold tsuutinaAccepted sandwich
    simp
  rw [h_filter]
  -- IsChain (¬ antPostForbidden) on sandwich (k+1) post [] (k+1) ant
  -- = post^(k+1) ++ [] ++ ant^(k+1) = post^(k+1) ++ ant^(k+1).
  show (sandwich (k + 1) Sibilant.posterior []
          (k + 1) Sibilant.anterior).IsChain
        (fun a b => ¬ antPostForbidden a b)
  unfold sandwich
  rw [List.append_nil, List.isChain_append]
  refine ⟨?_, ?_, ?_⟩
  · exact List.isChain_replicate_of_rel _ (by decide)
  · exact List.isChain_replicate_of_rel _ (by decide)
  · intro x hx y hy
    rw [List.getLast?_replicate] at hx
    rw [List.head?_replicate] at hy
    simp at hx hy
    obtain ⟨_, rfl⟩ := hx
    obtain ⟨_, rfl⟩ := hy
    decide

/-- The rejected Tsuut'ina witness is **not** in `tsuutinaLang`. The
internal `[anterior, posterior]` is precisely the forbidden adjacency
on the sibilant tier. -/
private lemma tsuutinaRejected_notMem (k : ℕ) :
    tsuutinaRejected k ∉ tsuutinaLang := by
  show ¬ (tsuutinaRejected k ∈ (TSLGrammar.ofForbiddenPairs antPostForbidden
                                  Sibilant.onTier).lang)
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  -- Filter is identity (no neutrals).
  have h_filter : (tsuutinaRejected k).filter
                    (fun x => decide (Sibilant.onTier x)) =
                  tsuutinaRejected k := by
    unfold tsuutinaRejected sandwich
    simp
  rw [h_filter]
  -- The witness contains the adjacent pair (anterior, posterior).
  -- Unfold sandwich, then use isChain_append_cons_cons to expose the pair.
  show ¬ (sandwich k Sibilant.posterior
            [Sibilant.anterior, .posterior] k Sibilant.anterior).IsChain
        (fun a b => ¬ antPostForbidden a b)
  unfold sandwich
  intro hchain
  -- Reassociate: post^k ++ [ant, post] ++ ant^k = post^k ++ (ant :: post :: ant^k).
  rw [show List.replicate k Sibilant.posterior ++
          [Sibilant.anterior, Sibilant.posterior] ++
          List.replicate k Sibilant.anterior =
          List.replicate k Sibilant.posterior ++
          (Sibilant.anterior :: Sibilant.posterior ::
            List.replicate k Sibilant.anterior) by
        simp [List.append_assoc]] at hchain
  rw [List.isChain_append_cons_cons] at hchain
  exact hchain.2.1 (by decide : antPostForbidden Sibilant.anterior
                                              Sibilant.posterior)

/-- **Tsuut'ina asymmetric harmony ∉ BTLI** (Lambert's parametrised
counterexample). -/
theorem tsuutina_not_isBTLI : ∀ k, ¬ IsBTLI k tsuutinaLang := by
  intro k
  apply not_isBTC_of_indist (w₁ := tsuutinaAccepted k) (w₂ := tsuutinaRejected k)
  · exact IsBTC.indist_isGenDef_of_tierAffixes (tsuutina_tierAffixes k)
  · exact tsuutinaAccepted_mem k
  · exact tsuutinaRejected_notMem k

-- ============================================================================
-- § 6. Luganda high-tone plateauing ∈ J ∖ BTLI
-- ============================================================================

/-- Luganda tone alphabet [hyman-katamba-2010]: low (ℓ) and high (h),
following [jardine-2020]'s identification of "intermediate" with low
in the input. -/
inductive LugandaTone | low | high
  deriving DecidableEq, Repr

/-- The Luganda high-tone plateauing predicate [lambert-2026] (37):
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

/-! ### Refutation: Luganda ∉ BTLI

Lambert (2026) §5.1 parameterised counterexample: for every `k`, the words
`ℓᵏ ℓ h h ℓ ℓᵏ` (accepted) and `ℓᵏ ℓ h ℓ h ℓ ℓᵏ` (rejected) share the
length-`k` tier-prefix and length-`k` tier-suffix on every Bool tier.
Both witnesses are sandwiches with bookend `low` and width `k`; the
substrate `Sandwich` (in `Core/Computability/Subregular/Sandwich.lean`)
handles the bookend-keeps-tier-affix case directly, leaving only the
small filtered-middle equality as per-witness work.

Membership separation is **predicate-level** (not TSL-grammar level):
`lugandaPred` requires no `[h, ℓ, h]` subsequence and (if any high
appears) a `[h, ℓ]` subsequence. Accepted satisfies both; rejected fails
the first because its explicit middle `[ℓ, h, ℓ, h, ℓ]` contains
`[h, ℓ, h]` as a subsequence. -/

/-- The accepted Luganda parameterised witness `ℓᵏ ℓ h h ℓ ℓᵏ`. The two
high tones are adjacent inside the middle, so no `[h, ℓ, h]` subsequence
can be formed (no low position lies strictly between them). -/
abbrev lugandaAccepted (k : ℕ) : List LugandaTone :=
  sandwich k LugandaTone.low [LugandaTone.low, .high, .high, .low] k LugandaTone.low

/-- The rejected Luganda parameterised witness `ℓᵏ ℓ h ℓ h ℓ ℓᵏ`. The
explicit middle `[ℓ, h, ℓ, h, ℓ]` contains `[h, ℓ, h]` as a
subsequence — exactly the structural pattern `lugandaPred` forbids. -/
abbrev lugandaRejected (k : ℕ) : List LugandaTone :=
  sandwich k LugandaTone.low [LugandaTone.low, .high, .low, .high, .low] k LugandaTone.low

/-- Tier-affix equality on every Bool tier. Case-split on `T low`:
when low is kept, the bookends survive and `takeAt_*_sandwich` gives
the affix `replicate k low` on both sides; when low is dropped, the
filtered word collapses to the middle and the two middles project to
the same filtered list (either `[h, h]` or `[]` depending on `T high`). -/
private lemma luganda_tierAffixes (k : ℕ) (T : LugandaTone → Bool) :
    Edge.left.takeAt k ((lugandaAccepted k).filter T) =
      Edge.left.takeAt k ((lugandaRejected k).filter T) ∧
    Edge.right.takeAt k ((lugandaAccepted k).filter T) =
      Edge.right.takeAt k ((lugandaRejected k).filter T) := by
  unfold lugandaAccepted lugandaRejected
  match h_low : T LugandaTone.low with
  | true =>
    -- Bookends kept; filtered words remain sandwiches with bookend `low`.
    -- `takeAt_*_sandwich` projects to `replicate k low` on both sides.
    rw [filter_sandwich_of_pos_pos h_low h_low,
        filter_sandwich_of_pos_pos h_low h_low,
        takeAt_left_sandwich (le_refl k), takeAt_left_sandwich (le_refl k),
        takeAt_right_sandwich (le_refl k), takeAt_right_sandwich (le_refl k)]
    exact ⟨rfl, rfl⟩
  | false =>
    have h_low' : ¬ T LugandaTone.low = true := by simp [h_low]
    -- Bookends dropped; both filtered words equal `mid.filter T`.
    rw [filter_sandwich_of_neg_neg h_low' h_low',
        filter_sandwich_of_neg_neg h_low' h_low']
    -- Sub-case on `T high`; both middles' filtered forms agree.
    match h_high : T LugandaTone.high with
    | true =>
      have h_acc : ([LugandaTone.low, .high, .high, .low] : List LugandaTone).filter T =
                   [LugandaTone.high, .high] := by
        simp [List.filter_cons_of_neg h_low', List.filter_cons_of_pos h_high]
      have h_rej : ([LugandaTone.low, .high, .low, .high, .low] : List LugandaTone).filter T =
                   [LugandaTone.high, .high] := by
        simp [List.filter_cons_of_neg h_low', List.filter_cons_of_pos h_high]
      rw [h_acc, h_rej]
      exact ⟨rfl, rfl⟩
    | false =>
      have h_high' : ¬ T LugandaTone.high = true := by simp [h_high]
      have h_acc : ([LugandaTone.low, .high, .high, .low] : List LugandaTone).filter T = [] := by
        simp [List.filter_cons_of_neg h_low', List.filter_cons_of_neg h_high']
      have h_rej : ([LugandaTone.low, .high, .low, .high, .low] : List LugandaTone).filter T = [] := by
        simp [List.filter_cons_of_neg h_low', List.filter_cons_of_neg h_high']
      rw [h_acc, h_rej]
      exact ⟨rfl, rfl⟩

/-- The accepted Luganda witness lies in `lugandaLang`. The first
predicate conjunct `¬ [h, ℓ, h] <+ ·` follows from `not_sublist_sandwich`
(pat = `[h, ℓ, h]` doesn't start or end with `low`, and the explicit
middle doesn't contain `[h, ℓ, h]` as a subsequence). The second
`high ∈ · → [h, ℓ] <+ ·` lifts a decidable check on the middle through
`sublist_sandwich_of_sublist_mid`. -/
private lemma lugandaAccepted_mem (k : ℕ) :
    lugandaAccepted k ∈ lugandaLang := by
  show lugandaPred (lugandaAccepted k)
  refine ⟨?_, fun _ => ?_⟩
  · exact not_sublist_sandwich (by decide) (by decide) (by decide) k k
  · exact sublist_sandwich_of_sublist_mid (by decide) k _ k _

/-- The rejected Luganda witness fails `lugandaPred` because its explicit
middle `[low, high, low, high, low]` contains `[high, low, high]` as a
subsequence (positions 1, 2, 3). Lifted via `sublist_sandwich_of_sublist_mid`. -/
private lemma lugandaRejected_notMem (k : ℕ) :
    lugandaRejected k ∉ lugandaLang := by
  intro h_mem
  exact h_mem.1 (sublist_sandwich_of_sublist_mid (by decide) k _ k _)

/-- **Luganda high-tone plateauing ∉ BTLI** (Lambert 2026 §5.1).
Parametrised-word witness: `ℓᵏ ℓ h h ℓ ℓᵏ` is accepted while
`ℓᵏ ℓ h ℓ h ℓ ℓᵏ` is rejected, but the two share all length-`k`
tier-affixes on every tier. -/
theorem luganda_not_isBTLI : ∀ k, ¬ IsBTLI k lugandaLang := by
  intro k
  apply not_isBTC_of_indist (w₁ := lugandaAccepted k) (w₂ := lugandaRejected k)
  · exact IsBTC.indist_isGenDef_of_tierAffixes (luganda_tierAffixes k)
  · exact lugandaAccepted_mem k
  · exact lugandaRejected_notMem k

-- ============================================================================
-- § 7. Prinmi pitch-accent ∈ PT_3 ∖ BTLI
-- ============================================================================

/-! Lambert 2026 §5.2 ([ding-2006]): Prinmi pitch-accent lexically
selects a high-tone position within a domain (morpheme or span of
adjacent morphemes); high may spread progressively to the next syllable.
The resulting pattern enforces:

1. **Obligatoriness**: at least one high tone (`h`).
2. **At most one high span**: no `[h, ℓ, h]` subsequence (same as
   Luganda §5.1).
3. **Span length ≤ 2**: no `[h, h, h]` subsequence (new conjunct
   not present in Luganda).

Lambert: "the same words witness this nonmembership as for high-tone
plateauing: `ℓᵏ h h ℓᵏ` is valid but `ℓᵏ h ℓ h ℓᵏ` is not, despite
the two having the same k-affixes on every tier." So we **reuse**
`lugandaAccepted` / `lugandaRejected` as witnesses and `luganda_tierAffixes`
as the indistinguishability proof — the substrate `Sandwich`'s
`not_sublist_sandwich` discharges both the `[h, ℓ, h]` and the new
`[h, h, h]` non-subsequence claims uniformly.

Alphabet: `LugandaTone` reused per Lambert's unified `ℓ`/`h` notation
across §5.

Disclaimer (Lambert §5.2): [ding-2006] assumes maximally
quadrisyllabic domains with significant compounding; that finite-domain
restriction would make Prinmi *co/finite* (a stronger classification).
The PT_3-and-not-BTLI result formalised here applies to the *unbounded*
analysis Lambert presents; the bounded analysis is out of scope. -/

/-- The Prinmi pitch-accent predicate [lambert-2026] (39):
* `[h] <+ w` — at least one high tone (obligatoriness).
* `¬ [h, ℓ, h] <+ w` — at most one high span.
* `¬ [h, h, h] <+ w` — high span length ≤ 2 syllables. -/
def prinmiPred (w : List LugandaTone) : Prop :=
  ([LugandaTone.high] <+ w) ∧
    (¬ ([LugandaTone.high, .low, .high] <+ w)) ∧
    (¬ ([LugandaTone.high, .high, .high] <+ w))

/-- The Prinmi pitch-accent language. -/
def prinmiLang : Language LugandaTone := { w | prinmiPred w }

/-- Membership in `prinmiLang` is membership in `prinmiPred`. -/
@[simp] lemma mem_prinmiLang (w : List LugandaTone) :
    w ∈ prinmiLang ↔ prinmiPred w := Iff.rfl

/-- **Prinmi pitch-accent ∈ PT_3** (Lambert 2026 (39)). All three
conjuncts depend only on length-≤-3 subsequence presence: the length-1
`[h]` and the two length-3 patterns. -/
theorem prinmi_isPT : IsPiecewiseTestable 3 prinmiLang := by
  intro w₁ w₂ heq
  simp only [mem_prinmiLang, prinmiPred]
  have h1 : ([LugandaTone.high] <+ w₁) ↔ ([LugandaTone.high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (1 : ℕ) ≤ 3)
  have h_hlh : ([LugandaTone.high, .low, .high] <+ w₁) ↔
               ([LugandaTone.high, .low, .high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (3 : ℕ) ≤ 3)
  have h_hhh : ([LugandaTone.high, .high, .high] <+ w₁) ↔
               ([LugandaTone.high, .high, .high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (3 : ℕ) ≤ 3)
  exact and_congr h1 (and_congr (not_congr h_hlh) (not_congr h_hhh))

/-- The accepted Luganda witness also satisfies `prinmiPred`. The first
two conjuncts mirror Luganda; the third (no `[h, h, h]` subseq) follows
from `not_sublist_sandwich` since the explicit middle `[low, high, high,
low]` contains no three highs. -/
private lemma prinmiAccepted_mem (k : ℕ) :
    lugandaAccepted k ∈ prinmiLang := by
  show prinmiPred (lugandaAccepted k)
  refine ⟨?_, ?_, ?_⟩
  · exact sublist_sandwich_of_sublist_mid (by decide) k _ k _
  · exact not_sublist_sandwich (by decide) (by decide) (by decide) k k
  · exact not_sublist_sandwich (by decide) (by decide) (by decide) k k

/-- The rejected Luganda witness fails `prinmiPred` because its explicit
middle `[low, high, low, high, low]` contains `[high, low, high]` as a
subsequence — exactly the second conjunct of `prinmiPred`. -/
private lemma prinmiRejected_notMem (k : ℕ) :
    lugandaRejected k ∉ prinmiLang := by
  intro h_mem
  exact h_mem.2.1 (sublist_sandwich_of_sublist_mid (by decide) k _ k _)

/-- **Prinmi pitch-accent ∉ BTLI** (Lambert 2026 §5.2). Same witnesses
and tier-affix proof as Luganda §5.1 — Lambert: "The same words witness
this nonmembership as for high-tone plateauing." -/
theorem prinmi_not_isBTLI : ∀ k, ¬ IsBTLI k prinmiLang := by
  intro k
  apply not_isBTC_of_indist (w₁ := lugandaAccepted k) (w₂ := lugandaRejected k)
  · exact IsBTC.indist_isGenDef_of_tierAffixes (luganda_tierAffixes k)
  · exact prinmiAccepted_mem k
  · exact prinmiRejected_notMem k

-- ============================================================================
-- § 8. Arigibi pitch-accent ∈ PT_2 ∩ BTN
-- ============================================================================

/-! Lambert 2026 §5.3 ([donohue-1997]): Arigibi (Trans-New Guinea)
allows at most one mora with high tone (position lexically specified;
words with no high tone are allowed). The phonotactic constraint is
`¬h..h` — no `[high, high]` subsequence anywhere.

Lambert: "exactly analogous to culminativity in isolation, and as such
it is piecewise testable and tier-based co/finite, as demonstrated in
§2.3" (Lambert's §2.3 is unbounded culminativity). -/

/-- Boolean tier predicate selecting `LugandaTone.high`. Shared by §8
Arigibi and §9 Chuave. -/
def isLugHigh : LugandaTone → Bool
  | .high => true
  | .low => false

/-- The Arigibi pitch-accent language: at most one high mora. -/
def arigibiLang : Language LugandaTone :=
  { w | ¬ ([LugandaTone.high, .high] <+ w) }

/-- Membership in `arigibiLang` is `¬ [h, h] <+ w`. -/
@[simp] lemma mem_arigibiLang (w : List LugandaTone) :
    w ∈ arigibiLang ↔ ¬ ([LugandaTone.high, .high] <+ w) := Iff.rfl

/-- **Arigibi pitch-accent ∈ PT_2** (Lambert 2026 §5.3, formula `¬h..h`).
The constraint depends only on length-2 subseq `[h, h]`. -/
theorem arigibi_isPT : IsPiecewiseTestable 2 arigibiLang := by
  intro w₁ w₂ heq
  show ¬ ([LugandaTone.high, .high] <+ w₁) ↔ ¬ ([LugandaTone.high, .high] <+ w₂)
  exact not_congr (subseqSet_eq_iff heq (le_refl 2))

/-- The high-tier projection of any LugandaTone word is a `replicate`
list of `high`s (since `isLugHigh` only keeps highs). -/
private lemma lugFilterHigh_eq_replicate (w : List LugandaTone) :
    w.filter isLugHigh = List.replicate (w.filter isLugHigh).length .high := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro x hx
  rw [List.mem_filter] at hx
  rcases x with _ | _
  · exact absurd hx.2 (by decide)
  · rfl

/-- `[h, h] <+ w` iff `[h, h]` is a sublist of the high-tier projection.
Forward: `Sublist.filter` + reduction of `[h, h].filter isLugHigh = [h, h]`.
Backward: transitivity through `List.filter_sublist`. -/
private lemma hh_sublist_iff_filter (w : List LugandaTone) :
    ([LugandaTone.high, .high] <+ w) ↔
      ([LugandaTone.high, .high] <+ w.filter isLugHigh) := by
  constructor
  · intro h
    have := h.filter isLugHigh
    simpa only [List.filter_cons_of_pos (by decide : isLugHigh .high = true),
                List.filter_nil] using this
  · intro h
    exact h.trans List.filter_sublist

/-- **Arigibi pitch-accent ∈ BTN** (Lambert 2026 §5.3). On the high
tier, the projection has length ≤ 1, i.e., is either `[]` or `[high]` —
a finite set, hence co/finite. -/
theorem arigibi_isBTN : IsBTN arigibiLang := by
  apply IsBTC.of_tierBased
  refine ⟨isLugHigh, { xs | xs = [] ∨ xs = [LugandaTone.high] }, ?_, ?_⟩
  · -- arigibiLang = preimage of {[], [high]} under tier projection.
    ext w
    show ¬ ([LugandaTone.high, .high] <+ w) ↔
         (w.filter isLugHigh = [] ∨ w.filter isLugHigh = [.high])
    rw [hh_sublist_iff_filter]
    rw [show ([LugandaTone.high, .high] : List _) = List.replicate 2 .high from rfl]
    rw [lugFilterHigh_eq_replicate w]
    rw [List.replicate_sublist_replicate]
    -- Goal: ¬ 2 ≤ (w.filter isLugHigh).length ↔
    --       replicate _ .high = [] ∨ replicate _ .high = [.high]
    constructor
    · intro h_lt
      have h_le_one : (w.filter isLugHigh).length ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h_le_one with hn | hn
      · left; rw [hn]; rfl
      · right; rw [hn]; rfl
    · rintro (h | h)
      · -- h : replicate (w.filter isLugHigh).length .high = []
        have h_len : (w.filter isLugHigh).length = 0 := by
          have := congrArg List.length h
          simpa [List.length_replicate] using this
        omega
      · -- h : replicate (w.filter isLugHigh).length .high = [.high]
        have h_len : (w.filter isLugHigh).length = 1 := by
          have := congrArg List.length h
          simpa [List.length_replicate] using this
        omega
  · -- {xs | xs = [] ∨ xs = [high]} is {[], [high]}, finite.
    left
    have h_eq : ({xs : List LugandaTone | xs = [] ∨ xs = [.high]}) =
                ({([] : List LugandaTone)} ∪ {[LugandaTone.high]}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    rw [h_eq]
    exact (Set.finite_singleton _).union (Set.finite_singleton _)

-- ============================================================================
-- § 9. Chuave obligatoriness ∈ PT_1 ∩ BTN
-- ============================================================================

/-! Lambert 2026 §5.5 ([donohue-1997]): Chuave (Trans-New Guinea)
exhibits **obligatoriness** — every word must contain at least one
high-tone mora. There is no restriction on placement; multiple high
spans are allowed. The phonotactic constraint is the simplest possible:
the formula `h` (at least one high). This is both:

* **PT_1**: the constraint depends only on the length-1 subsequence
  `[h]`.
* **BTN** (multitier finite-or-cofinite): on the high tier, the
  projection must be non-empty. The non-empty list set is co/finite
  (its complement is the singleton `{[]}`). -/

/-- The Chuave obligatoriness language: at least one mora has high tone. -/
def chuaveLang : Language LugandaTone := { w | LugandaTone.high ∈ w }

/-- Membership in `chuaveLang` is `high ∈ w`. -/
@[simp] lemma mem_chuaveLang (w : List LugandaTone) :
    w ∈ chuaveLang ↔ LugandaTone.high ∈ w := Iff.rfl

/-- **Chuave obligatoriness ∈ PT_1** (Lambert 2026 §5.5). The constraint
`high ∈ w` is the singleton subseq presence `[high] <+ w`. -/
theorem chuave_isPT : IsPiecewiseTestable 1 chuaveLang := by
  intro w₁ w₂ heq
  show LugandaTone.high ∈ w₁ ↔ LugandaTone.high ∈ w₂
  rw [← List.singleton_sublist, ← List.singleton_sublist]
  exact subseqSet_eq_iff heq (le_refl 1)

/-- **Chuave obligatoriness ∈ BTN** (Lambert 2026 §5.5, formula
`¬ [⋊⋉]_{h}`). On the high tier `isLugHigh`, the projection
`w.filter isLugHigh` is non-empty iff `high ∈ w`. The non-empty set
`{xs | xs ≠ []}` is co/finite (complement is `{[]}`). -/
theorem chuave_isBTN : IsBTN chuaveLang := by
  apply IsBTC.of_tierBased
  refine ⟨isLugHigh, { xs | xs ≠ [] }, ?_, ?_⟩
  · -- chuaveLang = preimage of {xs | xs ≠ []} under tier projection.
    ext w
    show LugandaTone.high ∈ w ↔ w.filter isLugHigh ∈ ({xs | xs ≠ []} : Set _)
    simp only [Set.mem_setOf_eq, ne_eq]
    rw [List.filter_eq_nil_iff]
    constructor
    · intro hmem hall
      exact (hall LugandaTone.high hmem) (by decide : isLugHigh .high = true)
    · intro hne
      by_contra hno
      apply hne
      intro x hx hisHigh
      apply hno
      rcases x with _ | _
      · exact absurd hisHigh (by decide)
      · exact hx
  · -- IsFiniteOrCofinite { xs | xs ≠ [] }: complement is {[]}, finite.
    right
    show ({xs : List LugandaTone | xs ≠ []}ᶜ).Finite
    have h_compl : ({xs : List LugandaTone | xs ≠ []}ᶜ) = {([] : List LugandaTone)} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
                 ne_eq, not_not]
    rw [h_compl]
    exact Set.finite_singleton _

-- ============================================================================
-- § 10. Kagoshima Japanese pitch-accent ∈ PT_3
-- ============================================================================

/-! Lambert 2026 §5.4 ([kawahara-2015], [haraguchi-1977]):
Kagoshima Japanese has a pitch-accent system with exactly one high tone
per word, appearing on the final or penultimate mora.

Lambert formula (42), order-based PT_3:
* `h`        — at least one high tone (obligatoriness)
* `¬h..h`    — no two highs (culminativity)
* `¬h..ℓ..ℓ` — high doesn't have two lows after (forces final/penult position)

Lambert formula (43), tier-based multitier definite:
* `[⋊h⋉]_{h}`   — high tier projection equals exactly `[h]`
* `(hℓ⋉ ∨ h⋉)`  — word ends with `[h, ℓ]` or `[h]`

The PT_3 result is direct from `subseqSet_eq_iff`. The multitier
characterization uses `tierEqualLang isLugHigh [.high]` (high tier =
singleton `[h]`) intersected with the disjunction of two `endsWithLang`
cases. The §4 helpers (`startsWithLang`, `endsWithLang`,
`tierEqualLang`) were generalized to `α : Type*` for this section so
they apply at type `LugandaTone` without duplication.

We prove `kagoshima_multitier_isBTLI` (multitier generalized definite, k = 2).
Lambert states the stronger BTD₂ classification (multitier definite —
right-edge-only); BTD substrate for `endsWithLang` is queued for
follow-up. The order/tier formulation equivalence (formulas 42 ↔ 43)
is stated as a TODO theorem `kagoshima_lang_eq_mt`.

Alphabet: `LugandaTone` reused per Lambert's unified `ℓ`/`h` notation
across §5. -/

/-- The Kagoshima Japanese pitch-accent predicate [lambert-2026]
(42): at least one high, no two highs, no `[h, ℓ, ℓ]` subseq. -/
def kagoshimaPred (w : List LugandaTone) : Prop :=
  ([LugandaTone.high] <+ w) ∧
    ¬ ([LugandaTone.high, .high] <+ w) ∧
    ¬ ([LugandaTone.high, .low, .low] <+ w)

/-- The Kagoshima Japanese pitch-accent language. -/
def kagoshimaLang : Language LugandaTone := { w | kagoshimaPred w }

/-- Membership in `kagoshimaLang` is membership in `kagoshimaPred`. -/
@[simp] lemma mem_kagoshimaLang (w : List LugandaTone) :
    w ∈ kagoshimaLang ↔ kagoshimaPred w := Iff.rfl

/-- **Kagoshima Japanese pitch-accent ∈ PT_3** (Lambert 2026 (42)).
All three conjuncts depend only on length-≤-3 subseq presence:
length-1 `[h]`, length-2 `[h, h]`, length-3 `[h, ℓ, ℓ]`. -/
theorem kagoshima_isPT : IsPiecewiseTestable 3 kagoshimaLang := by
  intro w₁ w₂ heq
  simp only [mem_kagoshimaLang, kagoshimaPred]
  have h1 : ([LugandaTone.high] <+ w₁) ↔ ([LugandaTone.high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (1 : ℕ) ≤ 3)
  have h_hh : ([LugandaTone.high, .high] <+ w₁) ↔
              ([LugandaTone.high, .high] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (2 : ℕ) ≤ 3)
  have h_hll : ([LugandaTone.high, .low, .low] <+ w₁) ↔
               ([LugandaTone.high, .low, .low] <+ w₂) :=
    subseqSet_eq_iff heq (by decide : (3 : ℕ) ≤ 3)
  exact and_congr h1 (and_congr (not_congr h_hh) (not_congr h_hll))

/-- The Kagoshima multitier-encoded language: high-tier-projection
equals exactly `[h]` AND word ends with `[h, ℓ]` or `[h]`. Lambert
2026 (43). -/
def kagoshimaMTLang : Language LugandaTone :=
  tierEqualLang isLugHigh [LugandaTone.high] ⊓
    (endsWithLang ([LugandaTone.high, .low] : List LugandaTone) ⊔
     endsWithLang ([LugandaTone.high] : List LugandaTone))

/-- **Kagoshima multitier characterization ∈ BTLI₂** (Lambert 2026
(43)). Each component lifts to `IsBTLI 2`:
* `tierEqualLang isLugHigh [.high]` via `tierEqualLang_isTierBased` (k = 2 > 1 = |xs|);
* `endsWithLang [.high, .low]` via `endsWithLang_isGenDef` (k = 2 ≥ 2);
* `endsWithLang [.high]` via `endsWithLang_isGenDef` (k = 2 ≥ 1).
The conjunction/disjunction are closed by `BoolClosure.inter` /
`BoolClosure.union`. Lambert's stronger BTD₂ classification is queued
for follow-up. -/
theorem kagoshima_multitier_isBTLI : IsBTLI 2 kagoshimaMTLang := by
  -- Tier component: high tier = [.high]
  have hTier : IsBTLI 2 (tierEqualLang isLugHigh [LugandaTone.high]) :=
    .base (tierEqualLang_isTierBased isLugHigh _ 2 (by decide))
  -- Suffix components
  have hSufHL : IsBTLI 2 (endsWithLang ([LugandaTone.high, .low] : List LugandaTone)) :=
    .base (.of_class (endsWithLang_isGenDef _ 2 (by decide)))
  have hSufH : IsBTLI 2 (endsWithLang ([LugandaTone.high] : List LugandaTone)) :=
    .base (.of_class (endsWithLang_isGenDef _ 2 (by decide)))
  -- Disjunction of suffixes
  have hSuf : IsBTLI 2
      (endsWithLang ([LugandaTone.high, .low] : List LugandaTone) ⊔
       endsWithLang ([LugandaTone.high] : List LugandaTone)) := .union hSufHL hSufH
  -- Intersection
  exact .inter hTier hSuf

/-! **Equivalence (formula 42 ↔ 43) is queued for follow-up.** Lambert
states the order-based predicate `kagoshimaLang` and the multitier
predicate `kagoshimaMTLang` describe the same language, but the proof
requires structural reasoning about how "no `[h, ℓ, ℓ]` subseq"
combined with "exactly one high" forces the unique high to lie in the
final two positions. Both formulations are independently classified
above (PT_3 and BTLI_2 respectively). -/

-- ============================================================================
-- § 11. Cross-framework refutation/cross-reference theorems (TODOs)
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
classifier — Uyghur backness harmony is BTD but [mayer-major-2018]
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
Cross-references `Phonology/Autosegmental/RegisterTier.lean`,
`GrammaticalTone.lean`, and `Studies/Lionnet2025.lean`. -/
theorem lambert_string_input_loses_tone_associations : True := trivial
-- TODO: state and prove via Phonology.Autosegmental.RegisterTier
-- representation distinctness with shared string projection.

end Lambert2026
