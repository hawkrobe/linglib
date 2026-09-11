import Linglib.Phonology.Subregular.Sibilant
import Linglib.Phonology.Subregular.Agree
import Linglib.Phonology.Subregular.Multitier
import Linglib.Phonology.Subregular.Harmony
import Linglib.Data.Examples.Hansson2010

/-!
# Hansson (2010): Consonant Harmony: Long-Distance Interaction in Phonology

This file formalizes the Navajo sibilant harmony with which [hansson-2010] opens its survey of
consonant harmony (section 1.1, and the case study of section 2.4.1.1): the alveolar and
postalveolar sibilant series cannot co-occur, and when morpheme concatenation juxtaposes them
the rightmost sibilant determines the anteriority of every sibilant before it, across any
vowels and non-sibilant consonants in between (3), (4), (6). The harmony is the map
`anticipatory` over the substrate's sibilant tier alphabet, whose fixed points are exactly the
words of the tier-based strictly 2-local agree language, `mem_language_iff_anticipatory_eq`;
it leaves the trigger and everything off the tier in place and neutralizes the contrast in the
sibilants it targets, the three characteristics the book draws from (4). It is the substrate's
harmony `System`, [rose-walker-2011]'s decomposition shared with the vowel harmonies of the
fragments, run from the right, `anticipatory_eq_transduceWord`. The book's own qualification
(section 3.1.2) is the perseveratory assimilation of the first-person subject prefix after the
s-perfective and s-destruct prefixes (12), (14), which the anticipatory map mispredicts,
`perseveratory_rows`, while harmony from the root still overrides it (15). The examples are
the rows of `Data.Examples.Hansson2010`, whose tier strings the theorems read off the
transcriptions.

## Implementation notes

An affricate contributes its fricative release as its tier symbol, and voicing and
glottalization are not read, so the [ʒ] of (4c), voiced under a condition the book sets aside,
is the postalveolar class. The book's correspondence-theoretic analysis (chapters 4 and 5), its
typological survey (chapter 2), and its speech-error account (chapter 6) are not formalized;
[rose-walker-2004]'s Agreement by Correspondence is in `Studies/RoseWalker2004.lean`.

## References

* [hansson-2010]
* [rose-walker-2011]
* [rose-walker-2004]
* [mcdonough-1991]
* [sapir-hoijer-1967]
-/

namespace Hansson2010

open Subregular Subregular.Harmony Phonology.Harmony Data.Examples

/-! ### Transcriptions and the tier alphabet -/

/-- The sibilant class of a transcription symbol: the alveolar series by its *s* or *z*, the
postalveolar by its *ʃ* or *ʒ*, everything else off the tier. -/
def classify (c : Char) : Sibilant :=
  if c = 's' ∨ c = 'z' then .anterior else if c = 'ʃ' ∨ c = 'ʒ' then .posterior else .neutral

/-- The tier string of a transcription. -/
def tierOf (s : String) : List Sibilant := s.toList.map classify

/-- The underlying form of a row, from its `underlying` feature. -/
def ur (e : LinguisticExample) : List Sibilant := tierOf ((e.feature? "underlying").getD "")

/-- The surface form of a row. -/
def sr (e : LinguisticExample) : List Sibilant := tierOf e.primaryText

/-- The sibilants of a word, in order. -/
abbrev sibilants (w : List Sibilant) : List Sibilant := tierProject Sibilant.onTier w

theorem mem_sibilants_onTier {w : List Sibilant} {s : Sibilant} (h : s ∈ sibilants w) :
    s.onTier := by
  rw [sibilants, tierProject_eq_filter, List.mem_filter] at h
  exact of_decide_eq_true h.2

theorem mem_sibilants {w : List Sibilant} {s : Sibilant} (hs : s ∈ w) (h : s.onTier) :
    s ∈ sibilants w := by
  rw [sibilants, tierProject_eq_filter, List.mem_filter]
  exact ⟨hs, decide_eq_true h⟩

/-! ### The surface language -/

/-- The surface phonotactic (section 2.4.1.1): on the sibilant tier, adjacent sibilants agree
in class, the tier-based strictly 2-local agree language. -/
abbrev navajoSibilantHarmony : TierStrictlyLocalGrammar 2 Sibilant :=
  TierStrictlyLocalGrammar.agree Sibilant.onTier

theorem isTierStrictlyLocal : Language.IsTierStrictlyLocal 2 navajoSibilantHarmony.language :=
  ⟨_, rfl⟩

theorem isBTSL : Language.IsBTSL 2 navajoSibilantHarmony.language :=
  isTierStrictlyLocal.toIsBTSL

/-- A word is harmonic iff its sibilants are all of one class. -/
theorem mem_language_iff (w : List Sibilant) :
    w ∈ navajoSibilantHarmony.language ↔ (sibilants w).IsChain (· = ·) := by
  rw [navajoSibilantHarmony, TierStrictlyLocalGrammar.agree,
    mem_ofForbiddenPairs_language_iff_filter_isChain, sibilants, tierProject_eq_filter]
  simp only [ne_eq, not_not]

/-! ### Anticipatory harmony, section 1.1 -/

/-- The trigger: the rightmost sibilant of a word. -/
def trigger (w : List Sibilant) : Option Sibilant := (sibilants w).getLast?

/-- A sibilant takes the trigger's class; anything off the tier is untouched. -/
def harmonize (t : Option Sibilant) (s : Sibilant) : Sibilant :=
  if s.onTier then t.getD s else s

/-- Anticipatory sibilant harmony: every sibilant takes the class of the rightmost one. -/
def anticipatory (w : List Sibilant) : List Sibilant := w.map (harmonize (trigger w))

theorem harmonize_of_not_onTier {t : Option Sibilant} {s : Sibilant} (h : ¬ s.onTier) :
    harmonize t s = s :=
  if_neg h

theorem harmonize_some_of_onTier {t s : Sibilant} (h : s.onTier) : harmonize (some t) s = t :=
  if_pos h

theorem trigger_onTier {w : List Sibilant} {t : Sibilant} (h : trigger w = some t) :
    t.onTier := by
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp h
  exact mem_sibilants_onTier (hl ▸ List.mem_append_right l (List.mem_singleton_self t))

theorem onTier_harmonize {t : Option Sibilant} (ht : ∀ s ∈ t, s.onTier) (s : Sibilant) :
    (harmonize t s).onTier ↔ s.onTier := by
  cases t with
  | none => simp [harmonize]
  | some t =>
    by_cases hs : s.onTier
    · simp [harmonize, hs, ht t rfl]
    · simp [harmonize, hs]

theorem sibilants_map_harmonize {t : Option Sibilant} (ht : ∀ s ∈ t, s.onTier)
    (w : List Sibilant) : sibilants (w.map (harmonize t)) = (sibilants w).map (harmonize t) := by
  simp only [sibilants, tierProject_eq_filter, List.filter_map]
  congr 1
  exact List.filter_congr λ s _ => by simp [onTier_harmonize ht]

theorem sibilants_anticipatory (w : List Sibilant) :
    sibilants (anticipatory w) = (sibilants w).map (harmonize (trigger w)) :=
  sibilants_map_harmonize (λ _ h => trigger_onTier h) w

/-- A word is harmonic iff each of its sibilants is of the trigger's class. -/
theorem mem_language_iff_trigger (w : List Sibilant) :
    w ∈ navajoSibilantHarmony.language ↔ ∀ s ∈ sibilants w, trigger w = some s := by
  rw [mem_language_iff]
  constructor
  · intro h s hs
    rw [List.isChain_eq_iff_eq_replicate] at h
    rcases hh : (sibilants w).head? with _ | a
    · exact absurd hs (by simp [List.head?_eq_none_iff.mp hh])
    · have hrep := h a hh
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (List.length_pos_of_mem hs).ne'
      rw [hn] at hrep
      have hsa : s = a := List.eq_of_mem_replicate (n := n + 1) (by rwa [hrep] at hs)
      rw [hsa, trigger, hrep, List.replicate_succ']
      simp
  · intro h
    exact List.Pairwise.isChain (List.pairwise_of_forall_mem_list λ a ha b hb =>
      Option.some_inj.mp ((h a ha).symm.trans (h b hb)))

/-- The trigger is left in place: the rightmost sibilant determines the rest. -/
theorem trigger_anticipatory (w : List Sibilant) : trigger (anticipatory w) = trigger w := by
  rw [trigger, sibilants_anticipatory, List.getLast?_map, ← trigger]
  rcases ht : trigger w with _ | t
  · rfl
  · simp [harmonize_some_of_onTier (trigger_onTier ht)]

/-- The harmonized word is harmonic. -/
theorem anticipatory_mem_language (w : List Sibilant) :
    anticipatory w ∈ navajoSibilantHarmony.language := by
  rw [mem_language_iff_trigger, trigger_anticipatory, sibilants_anticipatory]
  intro s hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
  rcases ht : trigger w with _ | t
  · have : sibilants w = [] := List.getLast?_eq_none_iff.mp (by simpa [trigger] using ht)
    simp [this] at hu
  · rw [harmonize_some_of_onTier (mem_sibilants_onTier hu)]

/-- A harmonic word is a fixed point of the harmony. -/
theorem anticipatory_eq_self_of_mem {w : List Sibilant}
    (h : w ∈ navajoSibilantHarmony.language) : anticipatory w = w := by
  rw [mem_language_iff_trigger] at h
  refine (List.map_congr_left λ s hs => ?_).trans (List.map_id w)
  by_cases hon : s.onTier
  · rw [h s (mem_sibilants hs hon)]
    exact harmonize_some_of_onTier hon
  · exact harmonize_of_not_onTier hon

/-- The surface language is exactly the set of fixed points of anticipatory harmony: the
stringset the tier-based grammar recognizes and the map the harmony computes are one object. -/
theorem mem_language_iff_anticipatory_eq (w : List Sibilant) :
    w ∈ navajoSibilantHarmony.language ↔ anticipatory w = w :=
  ⟨anticipatory_eq_self_of_mem, λ h => h ▸ anticipatory_mem_language w⟩

/-- Neutralization (4): prefixes differing only in the class of a sibilant surface alike once a
sibilant follows. -/
theorem anticipatory_cons_eq {a b : Sibilant} {w : List Sibilant} (ha : a.onTier)
    (hb : b.onTier) {t : Sibilant} (ht : trigger w = some t) :
    anticipatory (a :: w) = anticipatory (b :: w) := by
  have htr : ∀ c : Sibilant, c.onTier → trigger (c :: w) = some t := λ c hc => by
    have hc' : sibilants (c :: w) = c :: sibilants w := by
      simp [sibilants, tierProject_eq_filter, hc]
    rw [trigger, hc', List.getLast?_cons, ← trigger, ht]
    rfl
  simp only [anticipatory, List.map_cons, htr a ha, htr b hb, harmonize_some_of_onTier ha,
    harmonize_some_of_onTier hb]

/-! ### The examples -/

/-- The anticipatory examples of (3), (4), (6), (11), (13), and (15): the map takes each
underlying form to its surface sibilants. -/
theorem anticipatory_rows :
    ∀ e ∈ Examples.all, e.feature? "directionality" = some "anticipatory" →
      sibilants (anticipatory (ur e)) = sibilants (sr e) := by
  decide

/-- The book's qualification (section 3.1.2): the s-perfective (12) and s-destruct (14)
prefixes assimilate the following first-person prefix perseveratively, which the anticipatory
map mispredicts. -/
theorem perseveratory_rows :
    ∀ e ∈ Examples.all, e.feature? "directionality" = some "perseveratory" →
      sibilants (anticipatory (ur e)) ≠ sibilants (sr e) := by
  decide

/-- The underlying form of (6a) is disharmonic. -/
theorem ur_ex6a_ii_violates : ur Examples.ex6a_ii ∉ navajoSibilantHarmony.language := by
  rw [mem_language_iff_anticipatory_eq]
  decide

/-- Its surface form is harmonic. -/
theorem sr_ex6a_ii_legal : sr Examples.ex6a_ii ∈ navajoSibilantHarmony.language := by
  rw [mem_language_iff_anticipatory_eq]
  decide

/-! ### The harmony system -/

/-- Anteriority as the harmonic value. -/
def value : Sibilant → Option Bool
  | .anterior => some true
  | .posterior => some false
  | .neutral => none

/-- Write an anteriority value. -/
def write (v : Bool) (_ : Sibilant) : Sibilant := if v then .anterior else .posterior

/-- Navajo sibilant harmony as a harmony `System`: both sibilant series participate, all
else is transparent, nothing blocks, and the direction is leftward. -/
def navajo : System Sibilant where
  pattern :=
    { value := value
      participation := λ s => if s.onTier then .participating else .transparent
      direction := .leftward }
  targetIsContext := Sibilant.onTier
  isTarget := Sibilant.onTier
  write := write
  value_write := λ v _ => by cases v <;> rfl

theorem pattern_onTier_iff (s : Sibilant) : navajo.pattern.OnTier s ↔ s.onTier := by
  cases s <;> simp [navajo, Pattern.OnTier]

/-- The leftmost sibilant of a word. -/
def first (w : List Sibilant) : Option Sibilant := (sibilants w).head?

theorem windowOutput_nil (x : Sibilant) : navajo.spreadRule.windowOutput [] x = [x] := by
  simp [System.spreadRule, System.isBlocker, navajo]

theorem windowOutput_singleton {t : Sibilant} (ht : t.onTier) {x : Sibilant} (hx : x.onTier) :
    navajo.spreadRule.windowOutput [t] x = [t] := by
  cases t <;> cases x <;> simp_all [System.spreadRule, System.isBlocker, navajo, value, write]

theorem applyOnTierAux_eq (t : Option Sibilant) (ht : ∀ s ∈ t, s.onTier) (xs : List Sibilant) :
    navajo.spreadRule.applyOnTierAux navajo.pattern.OnTier t.toList xs =
      xs.map (harmonize (t.or (first xs))) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.onTier
    · rw [OSLRule.applyOnTierAux, if_pos ((pattern_onTier_iff x).mpr hx)]
      have hfirst : first (x :: xs) = some x := by
        simp [first, sibilants, tierProject_eq_filter, List.filter_cons_of_pos, hx]
      cases t with
      | none =>
        have := ih (some x) (λ s hs => Option.mem_some_iff.mp hs ▸ hx)
        simp only [Option.toList] at this
        simp only [Option.toList, List.nil_append, windowOutput_nil, List.rtake,
          List.length_singleton, Nat.reduceSub, Nat.sub_self, List.drop_zero, this, hfirst]
        simp [Option.or, harmonize_some_of_onTier hx]
      | some t =>
        have := ih (some t) ht
        simp only [Option.toList] at this
        simp only [Option.toList, windowOutput_singleton (ht t rfl) hx, List.rtake,
          List.singleton_append, List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.drop_succ_cons, List.drop_zero, this]
        simp [Option.or, harmonize_some_of_onTier hx]
    · rw [OSLRule.applyOnTierAux, if_neg ((pattern_onTier_iff x).not.mpr hx), ih t ht]
      simp [first, sibilants, tierProject_eq_filter, List.filter_cons_of_neg, hx,
        harmonize_of_not_onTier hx]

/-- The substrate's progressive harmony over the Navajo system: every sibilant takes the
class of the leftmost one. -/
theorem transduceWord_eq (w : List Sibilant) :
    navajo.transduceWord w = w.map (harmonize (first w)) := by
  simpa [System.transduceWord, OSLRule.applyOnTier, Option.or] using
    applyOnTierAux_eq none (by simp) w

/-- Anticipatory harmony is the substrate's harmony system run from the right. -/
theorem anticipatory_eq_transduceWord (w : List Sibilant) :
    anticipatory w = (navajo.transduceWord w.reverse).reverse := by
  rw [transduceWord_eq, List.map_reverse, List.reverse_reverse, anticipatory]
  congr 1
  simp [first, trigger, sibilants, tierProject_eq_filter, List.filter_reverse,
    List.head?_reverse]

end Hansson2010
