import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Data.Forms.UchiharaMendozaRuiz2021

/-!
# Uchihara and Mendoza Ruiz (2021): Minimality, Maximality and Perfect Prosodic Word in Alcozauca Mixtec

This file formalizes [uchihara-mendozaruiz-2021], on the size of the prosodic word in
Alcozauca Mixtec. The word is at least bimoraic: monosyllabic stems lengthen, (15), loans acquire
a mora, and syncope is accompanied by prothesis. Especially in casual speech it is also at most
bimoraic: loans truncate, (45), the perfective prefix is realized by tone alone where a segmental
prefix would leave a mora unfooted, (64), and the vowel-initial allomorphs of the enclitics fuse
with the stem. The paper's reductionist claim is that both effects follow from the three
prosodic-word size restrictor constraints of [mccarthy-prince-1994], FOOT-BINARITY, PARSE(µ) and
ALL-FEET-RIGHT, `ftBin`, `parseMora`, `allFeetRight`, so that the ideal word is the perfect
prosodic word of [ito-mester-2015], coextensive with one binary foot, `IsPerfect`: the perfect
words are exactly the non-empty words the three restrictors accept, `isPerfect_iff`, hence a
perfect candidate wins under every ranking of the restrictors, `isPerfect_mem_optimal`, and
nothing else does, `isPerfect_of_mem_optimal`; (15) and (45) are the instances `lengthening` and
`truncation`. Two asymmetries between the effects follow. PARSE(µ) is gradient in the unfooted
moras where FOOT-BINARITY is categorical in each foot, `parseMora_cons_inr` and
`ftBin_singleton_le`, so [ndi(kiʔĩ)] beats [nindi(kiʔĩ)], and the factorial typology of the
restrictors with a general
faithfulness constraint yields maximality only together with minimality, (110), while a ranking
with ALL-FEET-RIGHT below faithfulness yields minimality and foot alignment without maximality,
(111): `minimality_of_maximality` and `exists_minimality_not_maximality`.

## Implementation notes

Candidates are `Prosody.Footing`s over mora weights, flat parses into feet and stray syllables,
and the constraints read them as in [kager-2007]; ALL-FEET-RIGHT is categorical, one violation
per foot not at the right edge however much intervenes. Faithfulness constraints relate input to
output, so the tableaux of the paper are formalized over the restrictors alone, where the
paper's optimum is the sole violation-free candidate; the register difference, PARSE(µ) and
ALL-FEET-RIGHT dominated by MAXroot, MAX(µ) and NOHIATUS in careful speech and dominating them
in casual speech, is not represented. The factorial typology uses the paper's single general
faithfulness constraint F, read as the number of moras added to or removed from an input of
`n` moras, `faith`, over a candidate space of light-syllable footings of up to four moras. The
tree-level `Prosody.PerfectWord` is the headed counterpart of `IsPerfect`. The forms are the
rows of `Data.Forms.UchiharaMendozaRuiz2021`.

## References

* [uchihara-mendozaruiz-2021]
* [mccarthy-prince-1994]
* [ito-mester-2015]
* [kager-2007]
* [de-lacy-2003]
-/

namespace UchiharaMendozaRuiz2021

open Prosody Constraints OptimalityTheory

/-- A syllable is its mora count. -/
abbrev Word := Footing Syllable.Weight

/-! ### The prosodic-word size restrictor constraints -/

/-- FOOT-BINARITY: one violation per foot that is not bimoraic. -/
def ftBin : Constraint Word := λ fc => (fc.nonBimoraicFeet id).length

/-- PARSE(µ): one violation per mora parsed into no foot. -/
def parseMora : Constraint Word := λ fc => fc.strays.sum

/-- ALL-FEET-RIGHT: one violation per foot not at the right edge of the word, whatever
intervenes. -/
def allFeetRight : Constraint Word := λ fc => (Footing.feet fc.dropLast).length

/-- The three prosodic-word size restrictor constraints. -/
def restrictors : List (Constraint Word) := [ftBin, parseMora, allFeetRight]

/-- The perfect prosodic word: a single bimoraic foot and nothing else. -/
def IsPerfect (fc : Word) : Prop :=
  fc.strays = [] ∧ fc.feet.length = 1 ∧ ∀ f ∈ fc.feet, f.moraCount id = 2

instance (fc : Word) : Decidable (IsPerfect fc) := by unfold IsPerfect; infer_instance

theorem IsPerfect.ftBin {fc : Word} (h : IsPerfect fc) : ftBin fc = 0 := by
  simp only [UchiharaMendozaRuiz2021.ftBin, Footing.nonBimoraicFeet, List.length_eq_zero_iff,
    List.filter_eq_nil_iff, decide_eq_true_eq, not_not]
  exact h.2.2

theorem IsPerfect.parseMora {fc : Word} (h : IsPerfect fc) : parseMora fc = 0 := by
  simp only [UchiharaMendozaRuiz2021.parseMora, h.1, List.sum_nil]

theorem IsPerfect.allFeetRight {fc : Word} (h : IsPerfect fc) : allFeetRight fc = 0 := by
  obtain ⟨hs, hf, _⟩ := h
  rcases fc with _ | ⟨x, _ | ⟨y, fc⟩⟩
  · rfl
  · rfl
  · exfalso
    rcases x with f | s <;> rcases y with g | s'
    · simp [Footing.feet] at hf
    · simp [Footing.strays] at hs
    · simp [Footing.strays] at hs
    · simp [Footing.strays] at hs

/-- The perfect words are exactly the non-empty words the three restrictors accept, given
that every stray syllable weighs a mora. -/
theorem isPerfect_iff {fc : Word} (hpos : ∀ s ∈ fc.strays, s ≠ 0) :
    IsPerfect fc ↔ fc ≠ [] ∧ ftBin fc = 0 ∧ parseMora fc = 0 ∧ allFeetRight fc = 0 := by
  refine ⟨λ h => ⟨?_, h.ftBin, h.parseMora, h.allFeetRight⟩, ?_⟩
  · rintro rfl
    simp [IsPerfect, Footing.feet] at h
  · rintro ⟨hne, hb, hp, ha⟩
    have hs : fc.strays = [] := by
      rcases hstr : fc.strays with _ | ⟨s, rest⟩
      · rfl
      · have h1 := hpos s (hstr ▸ List.mem_cons_self)
        have h2 : parseMora fc = s + rest.sum := by simp [parseMora, hstr]
        exact absurd (Nat.eq_zero_of_add_eq_zero_right (h2 ▸ hp)) h1
    simp only [ftBin, Footing.nonBimoraicFeet, List.length_eq_zero_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_not] at hb
    refine ⟨hs, ?_, hb⟩
    rcases fc with _ | ⟨x, _ | ⟨y, fc⟩⟩
    · exact absurd rfl hne
    · rcases x with f | s
      · rfl
      · simp [Footing.strays] at hs
    · exfalso
      rcases x with f | s
      · simp [allFeetRight, Footing.feet] at ha
      · simp [Footing.strays] at hs

/-- A perfect candidate is optimal under every ranking of the restrictors. -/
theorem isPerfect_mem_optimal {cands : List Word} {fc : Word} (hc : fc ∈ cands)
    (h : IsPerfect fc) {rk : List (Constraint Word)} (hrk : rk ∈ restrictors.permutations')
    (hne : cands ≠ []) : fc ∈ (Tableau.ofRanking cands rk hne).optimal :=
  Tableau.ofRanking_zero_mem_optimal_allRankings hc
    (λ con hcon => by
      simp only [restrictors, List.mem_cons, List.not_mem_nil, or_false] at hcon
      rcases hcon with rfl | rfl | rfl
      · exact h.ftBin
      · exact h.parseMora
      · exact h.allFeetRight)
    hrk

/-- When some candidate is perfect, only perfect candidates are optimal under the restrictors,
whatever their ranking. -/
theorem isPerfect_of_mem_optimal {cands : List Word} {fc₀ fc : Word} (hc₀ : fc₀ ∈ cands)
    (h₀ : IsPerfect fc₀) (hfc : fc ≠ []) (hpos : ∀ s ∈ fc.strays, s ≠ 0)
    {rk : List (Constraint Word)} (hrk : rk ∈ restrictors.permutations') (hne : cands ≠ [])
    (hc : fc ∈ (Tableau.ofRanking cands rk hne).optimal) : IsPerfect fc := by
  have hperm := List.mem_permutations'.mp hrk
  have hzero : ∀ con ∈ restrictors, con fc = 0 := by
    have hle := Tableau.le_of_mem_optimal hc (List.mem_toFinset.mpr hc₀)
    have h0 : (Tableau.ofRanking cands rk hne).profile fc₀ = 0 := by
      funext i
      have hi : rk.get i ∈ restrictors := hperm.subset (rk.get_mem i)
      simp only [restrictors, List.mem_cons, List.not_mem_nil, or_false] at hi
      show rk.get i fc₀ = 0
      rcases hi with hi | hi | hi <;> rw [hi]
      · exact h₀.ftBin
      · exact h₀.parseMora
      · exact h₀.allFeetRight
    rw [h0] at hle
    have hbot : (Tableau.ofRanking cands rk hne).profile fc = 0 :=
      le_antisymm hle (ViolationProfile.zero_le _)
    intro con hcon
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hperm.symm.subset hcon)
    exact congrFun hbot i
  exact (isPerfect_iff hpos).2 ⟨hfc, hzero _ (by simp [restrictors]),
    hzero _ (by simp [restrictors]), hzero _ (by simp [restrictors])⟩

/-! ### Lengthening and truncation -/

/-- A light syllable. -/
abbrev light : Syllable.Weight := 1

/-- A heavy syllable. -/
abbrev heavy : Syllable.Weight := 2

/-- (15): the candidates for /ja/ 'white', the lengthened bimoraic foot (jaa), the degenerate
foot (ja) and the unfooted syllable ja. -/
def lengtheningCandidates : List Word :=
  [[.inl (Foot.monosyllable heavy)], [.inl (Foot.monosyllable light)], [.inr light]]

/-- (15): the lengthened bimoraic foot is the sole optimum. -/
theorem lengthening :
    (Tableau.ofRanking lengtheningCandidates restrictors).optimal =
      {[.inl (Foot.monosyllable heavy)]} := by
  decide +kernel

/-- (45): the candidates for Spanish *hamaca* 'hammock', the truncated bimoraic foot (ma.ka),
a(ma.ka) with an unfooted mora, (a.ma)ka with a foot off the right edge, and the trimoraic
foot (a.ma.ka). -/
def truncationCandidates : List Word :=
  [[.inl (Foot.trochee light light)], [.inr light, .inl (Foot.trochee light light)],
    [.inl (Foot.trochee light light), .inr light], [.inl ⟨[light, light, light], 0⟩]]

/-- (45): the truncated bimoraic foot is the sole optimum. -/
theorem truncation :
    (Tableau.ofRanking truncationCandidates restrictors).optimal =
      {[.inl (Foot.trochee light light)]} := by
  decide +kernel

/-! ### Two asymmetries between maximality and minimality -/

/-- PARSE(µ) is gradient: each unfooted syllable adds its moras. -/
theorem parseMora_cons_inr (s : Syllable.Weight) (fc : Word) :
    parseMora (.inr s :: fc) = s + parseMora fc := by
  simp [parseMora, Footing.strays]

/-- FOOT-BINARITY is categorical in each foot: a single foot violates it at most once, however
far from binary it is. -/
theorem ftBin_singleton_le (f : Foot Syllable.Weight) : ftBin [.inl f] ≤ 1 := by
  simp only [ftBin, Footing.nonBimoraicFeet, Footing.feet, List.filterMap_cons, Sum.getLeft?,
    List.filterMap_nil]
  exact List.length_filter_le _ _

/-- The general faithfulness constraint F of the factorial typology: the moras added to or
removed from an input of `n` moras. -/
def faith (n : ℕ) : Constraint Word := λ fc =>
  Int.natAbs ((fc.feet.map (·.moraCount id)).sum + fc.strays.sum - n)

/-- The restrictors with F, for an input of `n` moras, in the order indexed by a ranking. -/
def constraintsF (n : ℕ) : Fin 4 → Constraint Word := ![ftBin, parseMora, allFeetRight, faith n]

/-- The light-syllable candidates of up to four moras of the tableaux (110) and (111). -/
def typologyCandidates : List Word :=
  [[.inr light], [.inl (Foot.monosyllable light)], [.inl (Foot.trochee light light)],
    [.inl (Foot.trochee light light), .inr light], [.inr light, .inl (Foot.trochee light light)],
    [.inl ⟨[light, light, light], 0⟩],
    [.inl (Foot.trochee light light), .inl (Foot.trochee light light)],
    [.inr light, .inr light, .inl (Foot.trochee light light)],
    [.inl (Foot.trochee light light), .inr light, .inr light],
    [.inr light, .inl (Foot.trochee light light), .inr light], [.inr light, .inr light]]

/-- The optima for an input of `n` moras under the ranking `r` of the four constraints. -/
def typologyOptimal (n : ℕ) (r : List (Fin 4)) : Finset Word :=
  (Tableau.ofRanking typologyCandidates (r.map (constraintsF n))).optimal

/-- The rankings of the four constraints. -/
def rankings : List (List (Fin 4)) := ([0, 1, 2, 3] : List (Fin 4)).permutations'

/-- (110): every ranking that truncates trimoraic and quadrimoraic inputs to the bimoraic foot
lengthens the monomoraic input to it: maximality entails minimality. -/
theorem minimality_of_maximality :
    ∀ r ∈ rankings, (∀ fc ∈ typologyOptimal 3 r, IsPerfect fc) →
      (∀ fc ∈ typologyOptimal 4 r, IsPerfect fc) → ∀ fc ∈ typologyOptimal 1 r, IsPerfect fc := by
  decide +kernel

/-- (111): a ranking with ALL-FEET-RIGHT below faithfulness lengthens the monomoraic input but
keeps a quadrimoraic input as two feet: minimality without maximality. -/
theorem exists_minimality_not_maximality :
    ∃ r ∈ rankings, (∀ fc ∈ typologyOptimal 1 r, IsPerfect fc) ∧
      ¬ ∀ fc ∈ typologyOptimal 4 r, IsPerfect fc :=
  ⟨[0, 1, 3, 2], by decide, by decide +kernel, by decide +kernel⟩

end UchiharaMendozaRuiz2021
