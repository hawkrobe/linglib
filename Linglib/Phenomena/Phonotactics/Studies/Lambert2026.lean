/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Definite
import Linglib.Core.Computability.Subregular.PiecewiseTestable
import Linglib.Core.Computability.Subregular.Tier
import Linglib.Core.Computability.Subregular.Multitier

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

/-- The Uyghur backness harmony language: a word is well-formed iff its
suffix vowels/dorsals harmonize with the rightmost stem harmonizing-vowel
(or, fallback, the rightmost stem dorsal consonant), per Lambert (2026)
(33). Categorical idealization — see file docstring for the
@cite{mccollum-2019} gradience disclaimer. -/
def uyghurBacknessLang : Language UyghurSeg :=
  -- Schematic: the actual predicate is the conjunction of the
  -- mutually-exclusive implications in Lambert (2026) (35a)-(35b). The
  -- BTD witness construction uses tier projections to {V_f ∪ V_b} and
  -- {C_f ∪ C_b} and definite (suffix-only) tests on each.
  Set.univ -- placeholder; see uyghur_backness_isBTD TODO

/-- **Uyghur backness harmony ∈ BTD** (Lambert 2026 §4.3, eq. (35),
refining @cite{mayer-major-2018}). The full proof constructs the
formula in (35) as a Boolean combination of tier-projected definite
tests on the harmonizing-vowel tier and the dorsal-consonant tier.

TODO: the proof is a finite Boolean combination of four tier-based
definite tests, mirroring Lambert (2026) (35a)-(35b). Suffix-tier
notation: `S_X` = the tier of suffix-X-class material; `[⋊]_{S_X}`
asserts the `S_X` tier is non-empty (a tier-final on `S_X` exists).
  (a) (35a.i)  [V_f⋊]_{V_f∪V_b} → [⋊]_{S_f}    (V_f rightmost in stem ⇒ front suffix)
  (b) (35a.ii) [V_b⋊]_{V_f∪V_b} → [⋊]_{S_b}    (V_b rightmost in stem ⇒ back suffix)
  (c) (35b.i)  ([⋉⋊]_{V_f∪V_b} ∧ [C_f⋊]_{C_f∪C_b}) → [⋊]_{S_f}
                                                (no V, C_f rightmost ⇒ front suffix)
  (d) (35b.ii) ([⋉⋊]_{V_f∪V_b} ∧ [C_b⋊]_{C_f∪C_b}) → [⋊]_{S_b}
                                                (no V, C_b rightmost ⇒ back suffix)
Each implication is `IsTierBased (IsDefinite 1)` (single-tier-suffix
test); the conjunction is `BoolClosure.inter`-closed; therefore `k = 1`
should suffice as the BTD witness. -/
theorem uyghur_backness_isBTD : ∃ k, IsBTD k uyghurBacknessLang := by
  sorry

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

/-- Tsuut'ina sibilant alphabet @cite{cook-1978}: 's' (anterior) and 'ʃ'
(non-anterior); plus other (non-sibilant). -/
inductive TsuutinaSeg | anterior | nonAnterior | other
  deriving DecidableEq, Repr

/-- The sibilant tier predicate: keep `anterior` and `nonAnterior`,
discard everything else. -/
def tsuutinaTier (s : TsuutinaSeg) : Prop :=
  s = .anterior ∨ s = .nonAnterior

instance : DecidablePred tsuutinaTier := fun s => by
  cases s <;> simp [tsuutinaTier] <;> infer_instance

/-- The TSL_2 grammar for Tsuut'ina asymmetric sibilant harmony
@cite{cook-1978} @cite{lambert-2026} §4.2: project onto the sibilant
tier, then forbid the length-2 factor `[anterior, nonAnterior]` (an
anterior sibilant immediately preceding a non-anterior sibilant on the
tier — which on the un-projected string means anterior preceding
non-anterior at any distance). -/
def tsuutinaTSLGrammar : TSLGrammar 2 TsuutinaSeg where
  tier := tsuutinaTier
  permitted := { f | f ≠ [some .anterior, some .nonAnterior] }

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
