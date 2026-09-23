module

public import Linglib.Core.Computability.Definite
public import Linglib.Core.Data.List.Sublist
public import Linglib.Phonology.Subregular.Multitier
public import Linglib.Phonology.Subregular.ForbiddenPairs
public import Linglib.Phonology.Subregular.Sibilant
public import Linglib.Phonology.Subregular.Agree

/-!
# Lambert (2026): Multitier phonotactics with logic and algebra

This file formalizes the classifications of [lambert-2026]: attested constraints on stress,
harmony, and tone are placed in the multitier extensions of the definite, reverse definite,
generalized definite, and co/finite classes, the Boolean closures of the tier-projected classes,
by writing each constraint as a propositional formula over tier affixes, and are refuted from a
class by a pair of words the class cannot separate. With the tier literals `Language.tierWord`,
`tierPrefix`, and `tierSuffix`, a membership proof has the shape of its formula: the bounded
stress patterns with culminativity are multitier definite or reverse definite, the four
unbounded patterns of Hayes's typology are multitier reverse definite, definite, or generalized
definite as their defaults demand, Uyghur backness harmony is multitier definite
(`uyghur_isBTD`), and the Karanga Shona verb stem is multitier generalized definite
(`karangaShona_isBTLI`). The refutations follow the paper's parameterized witnesses:
culminativity alone is not generalized definite, culminative stress-final is not definite, and
Tsuut'ina sibilant harmony, Luganda plateauing, and Prinmi are not multitier generalized
definite (`tsuutina_not_isBTLI`, `luganda_not_isBTLI`).

## Implementation notes

Patterns are string languages over the paper's alphabets: syllables by stress, and by weight
and stress for unbounded stress; the sibilant classes; segment classes for Uyghur, with suffix
material marked as such following the paper; and two tones, without tone associations. A
pattern is defined by one of the paper's formulae, and where the paper gives an order-based and
a tier-based formula for the same pattern both are classified but their equivalence is proved
only for Navajo and Chuave. Windows are the paper's: the length of the longest affix, and one
more for a whole tier word, whose boundary markers count. The Uyghur pattern is the categorical
one of Mayer and Major that the paper analyzes.

## TODO

Prove the equivalence of the order-based and tier-based formulae for Kagoshima Japanese ((42),
(43)) and for Karanga Shona ((46)–(49)), and the piecewise testability of the Tsuut'ina
grammar. The algebraic characterizations of §6 by equations on the syntactic semigroup are not
formalized.

## References

* [lambert-2026]
* [omar-1969], [thurston-1966], [suomi-toivanen-ylitalo-2008]
* [hayes-1995], [roberts-1987], [bunn-bunn-1970], [grubb-1969], [krueger-1961]
* [heinz-2010], [sapir-hoijer-1967], [cook-1978], [mayer-major-2018]
* [hyman-katamba-2010], [ding-2006], [donohue-1997], [odden-1984], [jardine-2020]
-/

@[expose] public section

namespace Lambert2026

open Language Subregular List

/-! ### Bookended witnesses

The paper's parameterized witnesses are words `aᵏ ++ mid ++ bᵏ`. -/

section Sandwich

variable {α : Type*}

/-- A bookended word: `kL` copies of `aL`, then `mid`, then `kR` copies of `aR`. -/
private abbrev sandwich (kL : ℕ) (aL : α) (mid : List α) (kR : ℕ) (aR : α) : List α :=
  replicate kL aL ++ mid ++ replicate kR aR

/-- A pattern that can borrow neither bookend's symbol for its head or its last element is a
sublist of the bookended word exactly when it is a sublist of the middle. -/
private lemma sublist_sandwich_iff {pat mid : List α} {aL aR : α}
    (h_first : pat.head? ≠ some aL) (h_last : pat.getLast? ≠ some aR) {kL kR : ℕ} :
    pat <+ sandwich kL aL mid kR aR ↔ pat <+ mid := by
  unfold sandwich
  rw [append_assoc, sublist_replicate_append_iff_of_head?_ne h_first,
    sublist_append_replicate_iff_of_getLast?_ne h_last]

/-- Two members of a list occur in one order or the other as a subsequence, unless equal. -/
private lemma sublist_pair_of_mem {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    x = y ∨ [x, y] <+ l ∨ [y, x] <+ l := by
  induction l with
  | nil => nomatch hx
  | cons a t ih =>
    rcases mem_cons.mp hx with rfl | hx'
    · rcases mem_cons.mp hy with rfl | hy'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ((singleton_sublist.mpr hy').cons_cons x))
    · rcases mem_cons.mp hy with rfl | hy'
      · exact Or.inr (Or.inr ((singleton_sublist.mpr hx').cons_cons y))
      · exact (ih hx' hy').imp_right λ h => h.imp (·.cons a) (·.cons a)

end Sandwich

/-! ### Bounded stress (§2)

Stress-final, stress-penult, and stress-initial are definite, definite, and reverse definite
((2), (5), (6)). Culminativity, at most one primary stress, is tier-based co/finite on the
stress tier but not generalized definite, so it lifts each bounded pattern out of the affix
classes to the multitier ones ((13)); with it stress-final is no longer definite (§2.3). -/

/-- A syllable, unstressed or bearing primary stress. -/
inductive Syl
  | unstressed
  | stressed
  deriving DecidableEq, Repr

/-- The stress tier. -/
def Syl.isStressed : Syl → Bool
  | .stressed => true
  | .unstressed => false

/-- Iban stress-final ((2), [omar-1969]): `σ́⋉`. -/
def iban : Language Syl := ofSuffix [.stressed]

theorem iban_isDefinite : iban.IsDefinite 1 := isDefinite_ofSuffix _

/-- Amara stress-penult ((5), [thurston-1966]): `σ́Σ⋉ ∨ ⋊σ́⋉`. -/
def amara : Language Syl :=
  {w | Edge.right.takeAt 2 w ∈
    ({[.stressed], [.stressed, .unstressed], [.stressed, .stressed]} : Set (List Syl))}

theorem amara_isDefinite : amara.IsDefinite 2 := isDefinite_setOf_right 2 _

/-- Finnish stress-initial ((6), [suomi-toivanen-ylitalo-2008]): `⋊σ́`. -/
def finnish : Language Syl := ofPrefix [.stressed]

theorem finnish_isReverseDefinite : finnish.IsReverseDefinite 1 := isReverseDefinite_ofPrefix _

/-- Culminativity (§2.3): at most one stressed syllable, `[⋊⋉ ∨ ⋊σ́⋉]_{σ́}`. -/
def culminativity : Language Syl :=
  {w | w.filter Syl.isStressed = [] ∨ w.filter Syl.isStressed = [.stressed]}

/-- Culminativity is tier-based co/finite: on the stress tier the word is empty or a single
stressed syllable. -/
theorem culminativity_isTierBased : IsTierBased IsFiniteOrCofinite culminativity :=
  ⟨_, _, rfl, Or.inl ((Set.finite_singleton _).insert _)⟩

/-- Culminativity is not generalized definite: `σᵏσ́σᵏ` is in and `σᵏσ́σ́σᵏ` is out, with the
same prefix and suffix of length `k`. -/
theorem culminativity_not_isGeneralizedDefinite (k : ℕ) :
    ¬ culminativity.IsGeneralizedDefinite k := by
  intro h
  have key : sandwich k Syl.unstressed [Syl.stressed] k Syl.unstressed ∈ culminativity ↔
      sandwich k Syl.unstressed [Syl.stressed, Syl.stressed] k Syl.unstressed ∈ culminativity :=
    isGeneralizedDefinite_iff_edges.mp h (by simp) (by simp [rtake_eq_reverse_take_reverse])
  refine absurd (key.mp ?_) ?_
  · show filter Syl.isStressed _ = [] ∨ filter Syl.isStressed _ = [Syl.stressed]
    simp [Syl.isStressed]
  · show ¬ (filter Syl.isStressed _ = [] ∨ filter Syl.isStressed _ = [Syl.stressed])
    simp [Syl.isStressed]

/-- Culminative stress-final ((13a)): `σ́⋉ ∧ [⋊σ́⋉]_{σ́}`. -/
def stressFinalCulminative : Language Syl := iban ⊓ tierWord Syl.isStressed [.stressed]

theorem stressFinalCulminative_isBTD : IsBTD 2 stressFinalCulminative :=
  IsBTC.inter (isBTD_ofSuffix _ (by decide)) (isBTD_tierWord _ _ (by decide))

/-- Culminative stress-penult ((13b)): `(σ́σ⋉ ∨ ⋊σ́⋉) ∧ [⋊σ́⋉]_{σ́}`. -/
def stressPenultCulminative : Language Syl := amara ⊓ tierWord Syl.isStressed [.stressed]

theorem stressPenultCulminative_isBTD : IsBTD 2 stressPenultCulminative :=
  IsBTC.inter (IsBTC.of_class amara_isDefinite) (isBTD_tierWord _ _ (by decide))

/-- Culminative stress-initial ((13c)): `⋊σ́ ∧ [⋊σ́⋉]_{σ́}`. -/
def stressInitialCulminative : Language Syl := finnish ⊓ tierWord Syl.isStressed [.stressed]

theorem stressInitialCulminative_isBTK : IsBTK 2 stressInitialCulminative :=
  IsBTC.inter (isBTK_ofPrefix _ (by decide)) (isBTK_tierWord _ _ (by decide))

/-- Culminative stress-final is not definite (§2.3): `σσᵏσ́` is in and `σ́σᵏσ́` is out, with the
same suffix of length `k`; strict locality is more powerful than definiteness. -/
theorem stressFinalCulminative_not_isDefinite (k : ℕ) :
    ¬ stressFinalCulminative.IsDefinite k := by
  intro h
  have hlen : k ≤ (replicate k Syl.unstressed ++ [Syl.stressed]).length := by
    rw [length_append, length_replicate, length_singleton]; omega
  have key : [Syl.unstressed] ++ (replicate k Syl.unstressed ++ [Syl.stressed]) ∈
      stressFinalCulminative ↔
      [Syl.stressed] ++ (replicate k Syl.unstressed ++ [Syl.stressed]) ∈ stressFinalCulminative :=
    iff_of_eq (h (by rw [Edge.takeAt_right_append_of_le_length _ _ hlen,
      Edge.takeAt_right_append_of_le_length _ _ hlen]))
  have ha : [Syl.unstressed] ++ (replicate k Syl.unstressed ++ [Syl.stressed]) ∈
      stressFinalCulminative :=
    ⟨(suffix_append (replicate k Syl.unstressed) [Syl.stressed]).trans
      (suffix_append [Syl.unstressed] _), by
      show filter Syl.isStressed _ = [Syl.stressed]
      simp [Syl.isStressed]⟩
  refine absurd (key.mp ha).2 ?_
  show ¬ filter Syl.isStressed _ = [Syl.stressed]
  simp [Syl.isStressed]

/-! ### Unbounded stress (§3)

The four patterns of Hayes's typology ([hayes-1995]) over syllables distinguished by weight:
the default-to-same patterns are multitier reverse definite or definite, the default-to-opposite
ones multitier generalized definite ((20), (23), (26), (29)). -/

/-- A syllable by weight and stress. -/
inductive QSyl
  | light
  | heavy
  | lightStressed
  | heavyStressed
  deriving DecidableEq, Repr

/-- The stress tier. -/
def QSyl.isStressed : QSyl → Bool
  | .lightStressed | .heavyStressed => true
  | _ => false

/-- The heavy tier. -/
def QSyl.isHeavy : QSyl → Bool
  | .heavy | .heavyStressed => true
  | _ => false

/-- Exactly one primary stress: `[⋊σ́⋉]_{σ́}`. -/
def oneStress : Language QSyl :=
  tierWord QSyl.isStressed [.lightStressed] ⊔ tierWord QSyl.isStressed [.heavyStressed]

theorem oneStress_isBTD : IsBTD 2 oneStress :=
  IsBTC.union (isBTD_tierWord _ _ (by decide)) (isBTD_tierWord _ _ (by decide))

theorem oneStress_isBTK : IsBTK 2 oneStress :=
  IsBTC.union (isBTK_tierWord _ _ (by decide)) (isBTK_tierWord _ _ (by decide))

/-- Amele ((20), [roberts-1987]): stress the leftmost heavy syllable, else the leftmost. -/
def amele : Language QSyl :=
  oneStress ⊓ (tierPrefix QSyl.isHeavy [.heavyStressed] ⊔
    (tierWord QSyl.isHeavy [] ⊓ ofPrefix [.lightStressed]))

theorem amele_isBTK : IsBTK 2 amele :=
  IsBTC.inter oneStress_isBTK (IsBTC.union (isBTK_tierPrefix _ _ (by decide))
    (IsBTC.inter (isBTK_tierWord _ _ (by decide)) (isBTK_ofPrefix _ (by decide))))

/-- Golin ((23), [bunn-bunn-1970]): stress the rightmost heavy syllable, else the rightmost. -/
def golin : Language QSyl :=
  oneStress ⊓ (tierSuffix QSyl.isHeavy [.heavyStressed] ⊔
    (tierWord QSyl.isHeavy [] ⊓ ofSuffix [.lightStressed]))

theorem golin_isBTD : IsBTD 2 golin :=
  IsBTC.inter oneStress_isBTD (IsBTC.union (isBTD_tierSuffix _ _ (by decide))
    (IsBTC.inter (isBTD_tierWord _ _ (by decide)) (isBTD_ofSuffix _ (by decide))))

/-- Kwak'wala ((26), [grubb-1969]): stress the leftmost heavy syllable, else the rightmost. -/
def kwakwala : Language QSyl :=
  oneStress ⊓ (tierPrefix QSyl.isHeavy [.heavyStressed] ⊔
    (tierWord QSyl.isHeavy [] ⊓ ofSuffix [.lightStressed]))

theorem kwakwala_isBTLI : IsBTLI 2 kwakwala :=
  IsBTC.inter oneStress_isBTD.toIsBTLI
    (IsBTC.union (IsBTK.toIsBTLI (isBTK_tierPrefix _ _ (by decide)))
      (IsBTC.inter (IsBTD.toIsBTLI (isBTD_tierWord _ _ (by decide)))
        (IsBTD.toIsBTLI (isBTD_ofSuffix _ (by decide)))))

/-- Chuvash ((29), [krueger-1961]): stress the rightmost heavy syllable, else the leftmost. -/
def chuvash : Language QSyl :=
  oneStress ⊓ (tierSuffix QSyl.isHeavy [.heavyStressed] ⊔
    (tierWord QSyl.isHeavy [] ⊓ ofPrefix [.lightStressed]))

theorem chuvash_isBTLI : IsBTLI 2 chuvash :=
  IsBTC.inter oneStress_isBTD.toIsBTLI
    (IsBTC.union (IsBTD.toIsBTLI (isBTD_tierSuffix _ _ (by decide)))
      (IsBTC.inter (IsBTD.toIsBTLI (isBTD_tierWord _ _ (by decide)))
        (IsBTK.toIsBTLI (isBTK_ofPrefix _ (by decide)))))

/-! ### Harmony (§4)

Navajo's symmetric sibilant harmony ([sapir-hoijer-1967]) is multitier co/finite, one of the
two sibilant tiers being empty, and coincides with the tier-based agreement grammar, which the
library already identifies with [heinz-2010]'s forbidden subsequences. Tsuut'ina's asymmetric
harmony ([cook-1978]) is tier-based strictly local but not multitier generalized definite: an
internal factor is needed. Uyghur backness harmony ([mayer-major-2018]) is multitier definite,
lying between the two. -/

/-- The anterior tier. -/
def Sibilant.isAnterior : Sibilant → Bool
  | .anterior => true
  | _ => false

/-- The posterior tier. -/
def Sibilant.isPosterior : Sibilant → Bool
  | .posterior => true
  | _ => false

/-- Navajo ((30)): the sibilants agree, `[⋊⋉]_s ∨ [⋊⋉]_ʃ`. -/
def navajo : Language Sibilant :=
  tierWord Sibilant.isAnterior [] ⊔ tierWord Sibilant.isPosterior []

theorem navajo_isBTN : IsBTN navajo := IsBTC.union (isBTN_tierWord _ _) (isBTN_tierWord _ _)

/-- The tier formula for Navajo describes the agreement grammar on the sibilant tier, which is
tier-based strictly local and strictly piecewise. -/
theorem navajo_eq_agree :
    navajo = (TierStrictlyLocalGrammar.agree Sibilant.onTier).language := by
  ext w
  rw [mem_agree_lang_iff_forall_sublist_pair]
  show (w.filter Sibilant.isAnterior = [] ∨ w.filter Sibilant.isPosterior = []) ↔ _
  simp only [filter_eq_nil_iff]
  constructor
  · rintro (h | h) a b hab ha hb
    · have ha' := h a (hab.subset (mem_cons_self))
      have hb' := h b (hab.subset (mem_cons_of_mem _ mem_cons_self))
      cases a <;> cases b <;> simp_all [Sibilant.isAnterior, Sibilant.onTier]
    · have ha' := h a (hab.subset (mem_cons_self))
      have hb' := h b (hab.subset (mem_cons_of_mem _ mem_cons_self))
      cases a <;> cases b <;> simp_all [Sibilant.isPosterior, Sibilant.onTier]
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := hne
    have hx : x = .anterior := by cases x <;> simp_all [Sibilant.isAnterior]
    have hy : y = .posterior := by cases y <;> simp_all [Sibilant.isPosterior]
    subst hx hy
    rcases sublist_pair_of_mem ‹Sibilant.anterior ∈ w› ‹Sibilant.posterior ∈ w› with
      h' | h' | h'
    · exact Sibilant.noConfusion h'
    · exact Sibilant.noConfusion (h _ _ h' trivial trivial)
    · exact Sibilant.noConfusion (h _ _ h' trivial trivial)

/-- Anterior immediately before posterior on the sibilant tier, the adjacency Tsuut'ina
forbids ((31)). -/
def antPostForbidden : Sibilant → Sibilant → Prop
  | .anterior, .posterior => True
  | _, _ => False

instance : DecidableRel antPostForbidden
  | .anterior, .posterior => isTrue trivial
  | .anterior, .anterior => isFalse not_false
  | .anterior, .neutral => isFalse not_false
  | .posterior, _ => isFalse not_false
  | .neutral, _ => isFalse not_false

/-- Tsuut'ina asymmetric harmony ([cook-1978]): `¬[sʃ]_{s,ʃ}`, an anterior sibilant is not
followed on the tier by a posterior one. -/
def tsuutinaGrammar : TierStrictlyLocalGrammar 2 Sibilant :=
  TierStrictlyLocalGrammar.ofForbiddenPairs antPostForbidden Sibilant.onTier

/-- The Tsuut'ina language. -/
def tsuutina : Language Sibilant := tsuutinaGrammar.language

theorem tsuutina_isTierStrictlyLocal : IsTierStrictlyLocal 2 tsuutina := ⟨tsuutinaGrammar, rfl⟩

/-- The accepted witness `ʃᵏ⁺¹sᵏ⁺¹`. -/
private abbrev tsuutinaIn (k : ℕ) : List Sibilant :=
  sandwich (k + 1) .posterior [] (k + 1) .anterior

/-- The rejected witness `ʃᵏsʃsᵏ`. -/
private abbrev tsuutinaOut (k : ℕ) : List Sibilant :=
  sandwich k .posterior [.anterior, .posterior] k .anterior

/-- The two witnesses share their affixes of length `k` on every tier. -/
private lemma tsuutina_tierAffixes (k : ℕ) (T : Sibilant → Bool) :
    Edge.left.takeAt k ((tsuutinaIn k).filter T) = Edge.left.takeAt k ((tsuutinaOut k).filter T) ∧
    Edge.right.takeAt k ((tsuutinaIn k).filter T) =
      Edge.right.takeAt k ((tsuutinaOut k).filter T) := by
  cases h_post : T .posterior <;> cases h_ant : T .anterior <;>
    simp [rtake_eq_reverse_take_reverse, h_post, h_ant, ← replicate_succ, take_append_of_le_length]

private lemma tsuutinaIn_mem (k : ℕ) : tsuutinaIn k ∈ tsuutina := by
  show tsuutinaIn k ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs antPostForbidden
    Sibilant.onTier).language
  rw [mem_ofForbiddenPairs_language_iff_filter_isChain]
  have h_filter : (tsuutinaIn k).filter (λ x => decide (Sibilant.onTier x)) = tsuutinaIn k := by
    unfold tsuutinaIn sandwich
    simp
  rw [h_filter]
  show (sandwich (k + 1) Sibilant.posterior [] (k + 1) Sibilant.anterior).IsChain
    (λ a b => ¬ antPostForbidden a b)
  unfold sandwich
  rw [append_nil, isChain_append]
  refine ⟨isChain_replicate_of_rel _ (by decide), isChain_replicate_of_rel _ (by decide), ?_⟩
  intro x hx y hy
  rw [getLast?_replicate] at hx
  rw [head?_replicate] at hy
  simp at hx hy
  obtain ⟨_, rfl⟩ := hx
  obtain ⟨_, rfl⟩ := hy
  decide

private lemma tsuutinaOut_notMem (k : ℕ) : tsuutinaOut k ∉ tsuutina := by
  show ¬ (tsuutinaOut k ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs antPostForbidden
    Sibilant.onTier).language)
  rw [mem_ofForbiddenPairs_language_iff_filter_isChain]
  have h_filter : (tsuutinaOut k).filter (λ x => decide (Sibilant.onTier x)) = tsuutinaOut k := by
    unfold tsuutinaOut sandwich
    simp
  rw [h_filter]
  show ¬ (sandwich k Sibilant.posterior [Sibilant.anterior, .posterior] k Sibilant.anterior).IsChain
    (λ a b => ¬ antPostForbidden a b)
  unfold sandwich
  intro hchain
  rw [show replicate k Sibilant.posterior ++ [Sibilant.anterior, Sibilant.posterior] ++
      replicate k Sibilant.anterior =
      replicate k Sibilant.posterior ++
        (Sibilant.anterior :: Sibilant.posterior :: replicate k Sibilant.anterior) by
      simp [append_assoc]] at hchain
  rw [isChain_append_cons_cons] at hchain
  exact hchain.2.1 (by decide : antPostForbidden Sibilant.anterior Sibilant.posterior)

/-- Tsuut'ina is not multitier generalized definite (§4.2): `ʃᵏ⁺¹sᵏ⁺¹` is in and `ʃᵏsʃsᵏ` is
out, with the same affixes of length `k` on every tier. -/
theorem tsuutina_not_isBTLI (k : ℕ) : ¬ IsBTLI k tsuutina :=
  not_isBTC_of_indist (IsBTC.indist_isGenDef_of_tierAffixes (tsuutina_tierAffixes k))
    (tsuutinaIn_mem k) (tsuutinaOut_notMem k)

/-- The segment classes of Uyghur backness harmony ((34)): harmonizing vowels and dorsal
consonants, front or back, the same marked as suffix material, and the rest. -/
inductive UyghurSeg
  | frontVowel
  | backVowel
  | frontDorsal
  | backDorsal
  | suffixFrontVowel
  | suffixBackVowel
  | suffixFrontDorsal
  | suffixBackDorsal
  | other
  deriving DecidableEq, Repr

/-- The harmonizing-vowel tier `V_f ∪ V_b`. -/
def UyghurSeg.isHarmonizingVowel : UyghurSeg → Bool
  | .frontVowel | .backVowel => true
  | _ => false

/-- The dorsal tier `C_f ∪ C_b`. -/
def UyghurSeg.isDorsal : UyghurSeg → Bool
  | .frontDorsal | .backDorsal => true
  | _ => false

/-- The front-suffix tier `S_f`. -/
def UyghurSeg.isSuffixFront : UyghurSeg → Bool
  | .suffixFrontVowel | .suffixFrontDorsal => true
  | _ => false

/-- The back-suffix tier `S_b`. -/
def UyghurSeg.isSuffixBack : UyghurSeg → Bool
  | .suffixBackVowel | .suffixBackDorsal => true
  | _ => false

/-- Uyghur backness harmony ((35)): the suffix agrees with the rightmost harmonizing vowel, or
failing that with the rightmost dorsal, each implication `φ → ψ` written `φᶜ ⊔ ψ`. -/
def uyghur : Language UyghurSeg :=
  ((tierSuffix UyghurSeg.isHarmonizingVowel [.frontVowel])ᶜ ⊔
      tierWord UyghurSeg.isSuffixBack []) ⊓
    ((tierSuffix UyghurSeg.isHarmonizingVowel [.backVowel])ᶜ ⊔
      tierWord UyghurSeg.isSuffixFront []) ⊓
    ((tierWord UyghurSeg.isHarmonizingVowel [] ⊓ tierSuffix UyghurSeg.isDorsal [.frontDorsal])ᶜ ⊔
      tierWord UyghurSeg.isSuffixBack []) ⊓
    ((tierWord UyghurSeg.isHarmonizingVowel [] ⊓ tierSuffix UyghurSeg.isDorsal [.backDorsal])ᶜ ⊔
      tierWord UyghurSeg.isSuffixFront [])

/-- Uyghur backness harmony is multitier definite (§4.3): every literal is a tier suffix. -/
theorem uyghur_isBTD : IsBTD 1 uyghur :=
  IsBTC.inter (IsBTC.inter (IsBTC.inter
    (IsBTC.union (IsBTC.compl (isBTD_tierSuffix _ _ (by decide))) (isBTD_tierWord _ _ (by decide)))
    (IsBTC.union (IsBTC.compl (isBTD_tierSuffix _ _ (by decide))) (isBTD_tierWord _ _ (by decide))))
    (IsBTC.union (IsBTC.compl (IsBTC.inter (isBTD_tierWord _ _ (by decide))
      (isBTD_tierSuffix _ _ (by decide)))) (isBTD_tierWord _ _ (by decide))))
    (IsBTC.union (IsBTC.compl (IsBTC.inter (isBTD_tierWord _ _ (by decide))
      (isBTD_tierSuffix _ _ (by decide)))) (isBTD_tierWord _ _ (by decide)))

/-! ### Tone (§5)

Tone strings over low and high, without their associations to segments. Luganda plateauing and
Prinmi are piecewise testable but not multitier generalized definite; Arigibi, Chuave, and
Kagoshima Japanese are piecewise testable and multitier co/finite or definite; the Karanga Shona
verb stem is multitier generalized definite. Order-based formulae are Boolean combinations of
shuffle ideals. -/

/-- A tone. -/
inductive Tone
  | low
  | high
  deriving DecidableEq, Repr

/-- The high-tone tier. -/
def Tone.isHigh : Tone → Bool
  | .high => true
  | .low => false

/-- Luganda high-tone plateauing ((37), [hyman-katamba-2010]): `¬h..ℓ..h ∧ (h → h..ℓ)`. -/
def luganda : Language Tone :=
  (shuffleIdeal [.high, .low, .high])ᶜ ⊓ ((shuffleIdeal [.high])ᶜ ⊔ shuffleIdeal [.high, .low])

theorem luganda_isPiecewiseTestable : luganda.IsPiecewiseTestable 3 :=
  (isPiecewiseTestable_compl_shuffleIdeal (by decide)).inter
    ((isPiecewiseTestable_compl_shuffleIdeal (by decide)).union
      (isPiecewiseTestable_shuffleIdeal (by decide)))

/-- The accepted witness `ℓᵏℓhhℓℓᵏ`. -/
private abbrev toneIn (k : ℕ) : List Tone := sandwich k .low [.low, .high, .high, .low] k .low

/-- The rejected witness `ℓᵏℓhℓhℓℓᵏ`. -/
private abbrev toneOut (k : ℕ) : List Tone :=
  sandwich k .low [.low, .high, .low, .high, .low] k .low

/-- The two witnesses share their affixes of length `k` on every tier. -/
private lemma tone_tierAffixes (k : ℕ) (T : Tone → Bool) :
    Edge.left.takeAt k ((toneIn k).filter T) = Edge.left.takeAt k ((toneOut k).filter T) ∧
    Edge.right.takeAt k ((toneIn k).filter T) = Edge.right.takeAt k ((toneOut k).filter T) := by
  cases h_low : T .low <;> cases h_high : T .high <;>
    simp [rtake_eq_reverse_take_reverse, h_low, h_high]

/-- The tone witnesses are not separated by any multitier generalized definite language. -/
private lemma tone_indist (k : ℕ) :
    IsBTC.Indist (IsGeneralizedDefinite · k) (toneIn k) (toneOut k) :=
  IsBTC.indist_isGenDef_of_tierAffixes (tone_tierAffixes k)

/-- Luganda plateauing is not multitier generalized definite (§5.1). -/
theorem luganda_not_isBTLI (k : ℕ) : ¬ IsBTLI k luganda :=
  not_isBTC_of_indist (tone_indist k)
    ⟨(sublist_sandwich_iff (by decide) (by decide)).not.mpr (by decide),
      Or.inr (sublist_append_of_sublist_left (sublist_append_of_sublist_right (by decide)))⟩
    fun h ↦ h.1 (sublist_append_of_sublist_left (sublist_append_of_sublist_right (by decide)))

/-- Prinmi ((39), [ding-2006]): one high span of at most two syllables,
`h ∧ ¬h..ℓ..h ∧ ¬h..h..h`. -/
def prinmi : Language Tone :=
  shuffleIdeal [.high] ⊓ (shuffleIdeal [.high, .low, .high])ᶜ ⊓
    (shuffleIdeal [.high, .high, .high])ᶜ

theorem prinmi_isPiecewiseTestable : prinmi.IsPiecewiseTestable 3 :=
  ((isPiecewiseTestable_shuffleIdeal (by decide)).inter
    (isPiecewiseTestable_compl_shuffleIdeal (by decide))).inter
    (isPiecewiseTestable_compl_shuffleIdeal (by decide))

/-- Prinmi is not multitier generalized definite (§5.2), by the Luganda witnesses. -/
theorem prinmi_not_isBTLI (k : ℕ) : ¬ IsBTLI k prinmi :=
  not_isBTC_of_indist (tone_indist k)
    ⟨⟨sublist_append_of_sublist_left (sublist_append_of_sublist_right (by decide)),
      (sublist_sandwich_iff (by decide) (by decide)).not.mpr (by decide)⟩,
      (sublist_sandwich_iff (by decide) (by decide)).not.mpr (by decide)⟩
    fun h ↦ h.1.2 (sublist_append_of_sublist_left (sublist_append_of_sublist_right (by decide)))

/-- Arigibi ((40), [donohue-1997]): at most one high mora, `¬h..h`. -/
def arigibi : Language Tone := (shuffleIdeal [.high, .high])ᶜ

theorem arigibi_isPiecewiseTestable : arigibi.IsPiecewiseTestable 2 :=
  isPiecewiseTestable_compl_shuffleIdeal (by decide)

/-- The high tier of a tone string is a run of highs. -/
private lemma filter_isHigh_eq_replicate (w : List Tone) :
    w.filter Tone.isHigh = replicate (w.filter Tone.isHigh).length .high :=
  eq_replicate_iff.mpr ⟨rfl, λ x hx => by
    rcases x with _ | _
    · exact absurd (mem_filter.mp hx).2 (by decide)
    · rfl⟩

/-- Two highs occur in a tone string iff they occur on its high tier. -/
private lemma high_high_sublist_iff (w : List Tone) :
    [Tone.high, .high] <+ w ↔ [Tone.high, .high] <+ w.filter Tone.isHigh :=
  ⟨λ h => by simpa only [filter_cons_of_pos (by decide : Tone.isHigh .high = true), filter_nil]
    using h.filter Tone.isHigh, λ h => h.trans filter_sublist⟩

/-- Arigibi is tier-based co/finite (§5.3): on the high tier the word is empty or a single
high, culminativity on tone. -/
theorem arigibi_isTierBased : IsTierBased IsFiniteOrCofinite arigibi := by
  refine ⟨Tone.isHigh, {xs | xs = [] ∨ xs = [.high]}, ?_,
    Or.inl ((Set.finite_singleton _).insert _)⟩
  ext w
  show ¬ [Tone.high, .high] <+ w ↔ w.filter Tone.isHigh = [] ∨ w.filter Tone.isHigh = [.high]
  rw [high_high_sublist_iff, show ([Tone.high, .high] : List Tone) = replicate 2 .high from rfl,
    filter_isHigh_eq_replicate w, replicate_sublist_replicate]
  generalize (w.filter Tone.isHigh).length = n
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [replicate_succ]

/-- Kagoshima Japanese ((42), [ding-2006]): one high tone, on the final or the penultimate
mora, `h ∧ ¬h..h ∧ ¬h..ℓ..ℓ`. -/
def kagoshima : Language Tone :=
  shuffleIdeal [.high] ⊓ (shuffleIdeal [.high, .high])ᶜ ⊓ (shuffleIdeal [.high, .low, .low])ᶜ

theorem kagoshima_isPiecewiseTestable : kagoshima.IsPiecewiseTestable 3 :=
  ((isPiecewiseTestable_shuffleIdeal (by decide)).inter
    (isPiecewiseTestable_compl_shuffleIdeal (by decide))).inter
    (isPiecewiseTestable_compl_shuffleIdeal (by decide))

/-- Kagoshima Japanese by tiers ((43)): `[⋊h⋉]_{h} ∧ (hℓ⋉ ∨ h⋉)`. -/
def kagoshimaTier : Language Tone :=
  tierWord Tone.isHigh [.high] ⊓ (ofSuffix [.high, .low] ⊔ ofSuffix [.high])

theorem kagoshimaTier_isBTD : IsBTD 2 kagoshimaTier :=
  IsBTC.inter (isBTD_tierWord _ _ (by decide))
    (IsBTC.union (isBTD_ofSuffix _ (by decide)) (isBTD_ofSuffix _ (by decide)))

/-- Chuave ((44), [donohue-1997]): obligatoriness, at least one high mora, `h`. -/
def chuave : Language Tone := shuffleIdeal [.high]

theorem chuave_isPiecewiseTestable : chuave.IsPiecewiseTestable 1 :=
  isPiecewiseTestable_shuffleIdeal (by decide)

/-- Chuave is the complement of an empty high tier, `¬[⋊⋉]_{h}`. -/
theorem chuave_eq_compl_tierWord : chuave = (tierWord Tone.isHigh [])ᶜ := by
  ext w
  show [Tone.high] <+ w ↔ ¬ w.filter Tone.isHigh = []
  rw [singleton_sublist, filter_eq_nil_iff]
  push Not
  constructor
  · exact λ h => ⟨.high, h, rfl⟩
  · rintro ⟨a, ha, hh⟩
    cases a
    · exact absurd hh (by decide)
    · exact ha

theorem chuave_isBTN : IsBTN chuave :=
  chuave_eq_compl_tierWord ▸ IsBTC.compl (isBTN_tierWord Tone.isHigh [])

/-- The seven fully specified Karanga Shona stems (§5.6, [odden-1984]). -/
def karangaShort : Language Tone :=
  {w | w ∈ [[.low], [.low, .high], [.low, .high, .low], [.high], [.high, .low],
    [.high, .low, .high], [.high, .high, .low, .high]]}

/-- The Karanga Shona verb stem ((48), (49)): a short stem, a low-toned root `⋊ℓhhℓ ∧ [⋊hh⋉]_{h}`,
or a high-toned root `⋊hhhℓ ∧ ℓh⋉ ∧ [⋊hhhh⋉]_{h}`. -/
def karangaShona : Language Tone :=
  karangaShort ⊔
    (ofPrefix [.low, .high, .high, .low] ⊓ tierWord Tone.isHigh [.high, .high]) ⊔
    (ofPrefix [.high, .high, .high, .low] ⊓ ofSuffix [.low, .high] ⊓
      tierWord Tone.isHigh [.high, .high, .high, .high])

/-- The Karanga Shona verb stem is multitier generalized definite (§5.6, refining
[jardine-2020]): tier prefixes and tier suffixes are both needed. -/
theorem karangaShona_isBTLI : IsBTLI 5 karangaShona :=
  IsBTC.union (IsBTC.union
    (IsBTC.of_class (isDefinite_succ_of_forall_length_le (N := 4)
      λ w hw => (by decide : ∀ w ∈ [[Tone.low], [.low, .high], [.low, .high, .low], [.high],
        [.high, .low], [.high, .low, .high], [.high, .high, .low, .high]], w.length ≤ 4)
        w hw).toIsGeneralizedDefinite)
    (IsBTC.inter (IsBTK.toIsBTLI (isBTK_ofPrefix _ (by decide)))
      (IsBTD.toIsBTLI (isBTD_tierWord _ _ (by decide)))))
    (IsBTC.inter (IsBTC.inter (IsBTK.toIsBTLI (isBTK_ofPrefix _ (by decide)))
      (IsBTD.toIsBTLI (isBTD_ofSuffix _ (by decide))))
      (IsBTD.toIsBTLI (isBTD_tierWord _ _ (by decide))))

end Lambert2026
