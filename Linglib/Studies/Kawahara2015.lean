import Linglib.Phonology.Prosody.Syllable
import Linglib.Phonology.Constraints.Defs
import Linglib.Fragments.Japanese.Prosody

/-!
# Kawahara (2015) [kawahara-2015]

Tokyo Japanese pitch accent, after the survey *The phonology of Japanese
accent*. The antepenultimate accent rule ([mccawley-1968]) and the Latin
Stress Rule ([hayes-1995]) agree on six of Table 1's eight trisyllabic
weight conditions and diverge exactly on HLH and LLH; the accent-to-tone
derivation (accentual HL, initial rise, spreading) determines surface tones
and is culminative — at most one HL fall per word, for every accent
location and length (`accentToTones_culminative`); the eight-way affix
accent typology projects onto the coarse dominant/recessive split; and both
compound-accent rules satisfy NonFinality ([prince-smolensky-1993]).
-/

namespace Kawahara2015

open Prosody Japanese.Prosody Constraints

/-! ### Default accent: the AAR vs the Latin Stress Rule

Language-neutral accent-placement rules over a syllable-weight profile,
compared on loanword default accentuation (§2). -/

private def findSyllable (weights : List Syllable.Weight) (targetMora : ℕ) : Option ℕ :=
  go weights targetMora 0
where
  go : List Syllable.Weight → ℕ → ℕ → Option ℕ
    | [], _, _ => none
    | w :: ws, target, idx => if target < w then some idx else go ws (target - w) (idx + 1)

/-- The antepenultimate accent rule, which accents the syllable containing
    the antepenultimate mora and the initial syllable of shorter words
    ([mccawley-1968]). Returns the 0-indexed syllable. -/
def defaultAccentAAR (weights : List Syllable.Weight) : Option ℕ :=
  match weights with
  | [] => none
  | _ =>
    let totalMorae := weights.foldl (· + ·) 0
    let targetMora := if totalMorae ≥ 3 then totalMorae - 3 else 0
    findSyllable weights targetMora

/-- The Latin Stress Rule, which accents a heavy (≥ 2μ) penult and the
    antepenult otherwise, with mono- and disyllables accented initially
    ([hayes-1995]). §2.3 reviews arguments that LSR-conforming variants
    occur even where the two rules diverge, making the LSR arguably the
    better characterization of the Japanese default. -/
def latinStressRule (weights : List Syllable.Weight) : Option ℕ :=
  match weights with
  | [] => none
  | _ =>
    if weights.length ≤ 2 then some 0
    else if Syllable.Weight.heavy ≤ weights.getD (weights.length - 2) 0 then
      some (weights.length - 2)
    else some (weights.length - 3)

/-- The eight trisyllabic weight conditions of Table 1. -/
def trisyllabicConditions : List (List Syllable.Weight) :=
  [[.heavy, .heavy, .heavy], [.heavy, .heavy, .light],
   [.heavy, .light, .heavy], [.heavy, .light, .light],
   [.light, .heavy, .heavy], [.light, .heavy, .light],
   [.light, .light, .heavy], [.light, .light, .light]]

/-- The AAR and the LSR agree on six of the eight trisyllabic weight
    conditions and diverge exactly on HLH and LLH (Table 1). -/
theorem aar_lsr_mismatches :
    trisyllabicConditions.filter (fun w => defaultAccentAAR w != latinStressRule w) =
      [[.heavy, .light, .heavy], [.light, .light, .heavy]] := by decide

/-- On HLH the AAR accents σ₂, the syllable containing the antepenultimate
    mora, while the LSR accents the antepenult σ₁ since the penult is light
    (Table 1c: `HL'H` vs `H'LH`). -/
theorem aar_lsr_mismatch_hlh :
    defaultAccentAAR [.heavy, .light, .heavy] = some 1 ∧
      latinStressRule [.heavy, .light, .heavy] = some 0 := by decide

/-- On LLH the AAR accents σ₂ and the LSR σ₁ (Table 1g: `LL'H` vs
    `L'LH`). -/
theorem aar_lsr_mismatch_llh :
    defaultAccentAAR [.light, .light, .heavy] = some 1 ∧
      latinStressRule [.light, .light, .heavy] = some 0 := by decide

/-! ### Loanword accent (§2)

Loanwords lack lexical accent specifications, so their accentuation reveals
the default pattern (§2.1; [kubozono-2006]). -/

/-- A loanword entry paired with its syllable-weight profile. -/
structure LoanwordEntry where
  entry : ProsodicEntry
  /-- Syllable weight profile (left to right) -/
  weights : List Syllable.Weight
  deriving Repr

/-- *ku-ri-su'-ma-su* 'Christmas', accented on the antepenultimate mora
    ((10a)). -/
def kurisumasu : LoanwordEntry :=
  { entry := { form := "kurisumasu", gloss := "Christmas"
               accentMora := some 2, nMorae := 5 }
    weights := [.light, .light, .light, .light, .light] }

/-- *a-su-fa'-ru-to* 'asphalt', accented on the antepenultimate mora
    ((10g)). -/
def asufaruto : LoanwordEntry :=
  { entry := { form := "asufaruto", gloss := "asphalt"
               accentMora := some 2, nMorae := 5 }
    weights := [.light, .light, .light, .light, .light] }

/-- *ma-ku-do-na'-ru-do* 'McDonald', accented on the antepenultimate mora
    ((10h)). -/
def makudonarudo : LoanwordEntry :=
  { entry := { form := "makudonarudo", gloss := "McDonald's"
               accentMora := some 3, nMorae := 6 }
    weights := [.light, .light, .light, .light, .light, .light] }

/-- *a.me.ri.ka* 'America', unaccented as a four-mora word with two final
    light non-epenthetic syllables ((16a)). -/
def amerika : LoanwordEntry :=
  { entry := { form := "amerika", gloss := "America"
               accentMora := none, nMorae := 4 }
    weights := [.light, .light, .light, .light] }

/-- The accented loanwords of (10) carry the accent the AAR assigns. -/
theorem loanwords_match_aar :
    defaultAccentAAR kurisumasu.weights = kurisumasu.entry.accentMora ∧
      defaultAccentAAR asufaruto.weights = asufaruto.entry.accentMora ∧
      defaultAccentAAR makudonarudo.weights = makudonarudo.entry.accentMora := by decide

/-- On all-light profiles the LSR agrees with the AAR, so the (10)
    loanwords match it as well (§2.3). -/
theorem loanwords_match_lsr :
    latinStressRule kurisumasu.weights = kurisumasu.entry.accentMora ∧
      latinStressRule asufaruto.weights = asufaruto.entry.accentMora ∧
      latinStressRule makudonarudo.weights = makudonarudo.entry.accentMora := by decide

/-- Neither default rule derives *amerika*'s unaccentedness, as neither
    produces unaccented outputs (§2.3 n. 10). Four-mora light-final
    unaccentedness is §2.4's separate generalization. -/
theorem amerika_beyond_default_rules :
    defaultAccentAAR amerika.weights ≠ amerika.entry.accentMora ∧
      latinStressRule amerika.weights ≠ amerika.entry.accentMora := by decide

/-! ### From accent to surface tones (§1.4)

Tones are specified by the accentual HL and the initial rise, then spread
rightward ((7)–(9)). -/

/-- A level tone. Japanese distinguishes only H and L at the lexical level
    (§1.3). -/
inductive LevelTone where
  | H
  | L
  deriving DecidableEq, Repr

/-- The tonal specification of mora `i` (0-indexed) before spreading
    ((4)–(5)). The accented mora is H and its successor L (accentual HL),
    while mora 0 is L and mora 1 H (initial rise) unless the accentual
    tones win, and other moras are unspecified. -/
def toneSpec (accentMora : Option ℕ) (i : ℕ) : Option LevelTone :=
  if accentMora = some i then some .H
  else if 1 ≤ i ∧ accentMora = some (i - 1) then some .L
  else if i = 0 then some .L
  else if i = 1 then some .H
  else none

/-- The surface tones of an `nMorae`-word from its accent position, by
    specification (`toneSpec`) followed by spreading — a left scan copying
    the most recent specified tone rightward ((7)–(9)). The seed is never
    consulted, since mora 0 is always specified. -/
def accentToTones (accentMora : Option ℕ) (nMorae : ℕ) : List LevelTone :=
  ((((List.range nMorae).map (toneSpec accentMora)).scanl (fun t o => o.getD t)) .H).tail

/-- Unaccented *ame(+ga)* 'candy' surfaces LHH by initial rise and
    spreading ((6b)). -/
theorem ameCandy_ga_tones : accentToTones ameCandy.accentMora 3 = [.L, .H, .H] := by
  decide

/-- Initially-accented *a'me(+ga)* 'rain' surfaces HLL, since the accentual
    HL blocks the initial rise ((5b), (8)). -/
theorem ameRain_ga_tones : accentToTones ameRain.accentMora 3 = [.H, .L, .L] := by
  decide

/-- Of the n+1 accent patterns of a trisyllable ((3)), the unaccented,
    initial, and medial ones are pairwise distinct, while final accent
    neutralizes with unaccentedness word-internally because the post-accent
    L falls off the word edge (§1.4). -/
theorem trisyllabic_tone_patterns :
    accentToTones none 3 ≠ accentToTones (some 0) 3 ∧
      accentToTones none 3 ≠ accentToTones (some 1) 3 ∧
      accentToTones (some 0) 3 ≠ accentToTones (some 1) 3 ∧
      accentToTones none 3 = accentToTones (some 2) 3 := by decide

/-! ### Culminativity

"Japanese allows only one HL pitch fall within a word" (§1.4) —
`accentToTones_culminative` derives this for every accent location and word
length. -/

/-- The number of H-to-L falls in a tone string. -/
def hlFallCount : List LevelTone → ℕ
  | .H :: .L :: rest => hlFallCount (.L :: rest) + 1
  | _ :: rest => hlFallCount rest
  | [] => 0

theorem count_L_tail_le : ∀ l : List LevelTone, l.tail.count .L ≤ l.count .L
  | [] => Nat.le_refl _
  | .H :: _ => by rw [List.tail_cons, List.count_cons_of_ne (by decide)]
  | .L :: _ => by rw [List.tail_cons, List.count_cons_self]; exact Nat.le_succ _

/-- An L head opens no fall. -/
theorem hlFallCount_L_cons (l : List LevelTone) :
    hlFallCount (.L :: l) = hlFallCount l := by
  cases l with
  | nil => rfl
  | cons b rest => cases b <;> rfl

/-- Every fall consumes an L strictly after the first position. -/
theorem hlFallCount_le_count_tail :
    ∀ l : List LevelTone, hlFallCount l ≤ l.tail.count .L
  | [] => Nat.le_refl _
  | [t] => by cases t <;> simp [hlFallCount]
  | .H :: .L :: rest => by
      have ih := hlFallCount_le_count_tail (.L :: rest)
      rw [show hlFallCount (.H :: .L :: rest) = hlFallCount (.L :: rest) + 1 from rfl,
        List.tail_cons, List.count_cons_self]
      rw [List.tail_cons] at ih
      omega
  | .H :: .H :: rest => by
      have ih := hlFallCount_le_count_tail (.H :: rest)
      rw [show hlFallCount (.H :: .H :: rest) = hlFallCount (.H :: rest) from rfl,
        List.tail_cons, List.count_cons_of_ne (by decide)]
      rw [List.tail_cons] at ih
      exact ih
  | .L :: b :: rest => by
      have ih := hlFallCount_le_count_tail (b :: rest)
      rw [hlFallCount_L_cons, List.tail_cons]
      exact ih.trans (count_L_tail_le _)

theorem hlFallCount_cons_cons (t u : LevelTone) (l : List LevelTone) :
    hlFallCount (t :: u :: l) =
      hlFallCount (u :: l) + if t = .H ∧ u = .L then 1 else 0 := by
  cases t <;> cases u <;> simp [hlFallCount]

/-- Spreading is fall-invariant, since copying a tone neither creates nor
    destroys an HL fall. -/
theorem hlFallCount_cons_scanl (spec : List (Option LevelTone)) (x t : LevelTone) :
    hlFallCount (x :: spec.scanl (fun t o => o.getD t) t) =
      hlFallCount (x :: t :: spec.filterMap id) := by
  induction spec generalizing x t with
  | nil => cases x <;> cases t <;> rfl
  | cons o rest ih =>
    cases o with
    | some u =>
      simp only [List.scanl_cons, Option.getD_some,
        show (some u :: rest).filterMap id = u :: rest.filterMap id from rfl]
      rw [hlFallCount_cons_cons, hlFallCount_cons_cons, ih t u]
    | none =>
      have hδ : (if t = LevelTone.H ∧ t = LevelTone.L then 1 else 0) = 0 := by
        cases t <;> simp
      simp only [List.scanl_cons, Option.getD_none,
        show (none :: rest).filterMap id = rest.filterMap id from rfl]
      rw [hlFallCount_cons_cons, hlFallCount_cons_cons, ih t t,
        hlFallCount_cons_cons, hδ, Nat.add_zero]

/-- Mora 0 is always specified, as H under initial accent and otherwise as
    the initial-rise L. -/
theorem toneSpec_zero (a : Option ℕ) :
    toneSpec a 0 = some (if a = some 0 then .H else .L) := by
  by_cases h : a = some 0 <;> simp [toneSpec, h]

/-- After mora 0, the only source of a specified L is the post-accent L,
    which pins the accent location. -/
theorem toneSpec_eq_L {a : Option ℕ} {j : ℕ} (hj : 1 ≤ j) :
    toneSpec a j = some .L ↔ a = some (j - 1) := by
  unfold toneSpec
  split_ifs with h1 h2 <;> simp_all
  omega

/-- The specified tones after mora 0 contain at most one L, since the
    post-accent L pins the accent location and positions are distinct. -/
theorem count_L_toneSpec_dense (a : Option ℕ) :
    ∀ l : List ℕ, l.Nodup → (∀ j ∈ l, 1 ≤ j) →
      (l.filterMap (toneSpec a)).count .L ≤ 1 := by
  intro l
  induction l with
  | nil => simp
  | cons j rest ih =>
    intro hnd hpos
    rw [List.filterMap_cons]
    rcases hj : toneSpec a j with _ | t
    · exact ih hnd.of_cons fun k hk => hpos k (.tail _ hk)
    rcases t with _ | _
    · simpa [List.count_cons] using ih hnd.of_cons fun k hk => hpos k (.tail _ hk)
    · have ha : a = some (j - 1) := (toneSpec_eq_L (hpos j (.head _))).mp hj
      have hrest : (rest.filterMap (toneSpec a)).count .L = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨k, hk, hspec⟩ := List.mem_filterMap.mp hmem
        have hk1 := hpos k (.tail _ hk)
        have hak : a = some (k - 1) := (toneSpec_eq_L hk1).mp hspec
        have hj1 := hpos j (.head _)
        have hkj : k = j := by
          rw [ha] at hak
          simp only [Option.some.injEq] at hak
          omega
        exact (List.nodup_cons.mp hnd).1 (hkj ▸ hk)
      simp [hrest]

/-- A word carries at most one HL fall, whatever its accent location and
    length (culminativity, §1.4). -/
theorem accentToTones_culminative (a : Option ℕ) (n : ℕ) :
    hlFallCount (accentToTones a n) ≤ 1 := by
  obtain _ | m := n
  · exact Nat.zero_le _
  · have hpeel : accentToTones a (m + 1) =
        (((List.range m).map Nat.succ).map (toneSpec a)).scanl (fun t o => o.getD t)
          (if a = some 0 then LevelTone.H else .L) := by
      simp only [accentToTones, List.range_succ_eq_map, List.map_cons, toneSpec_zero,
        List.scanl_cons, List.tail_cons, Option.getD_some]
    rw [hpeel, ← hlFallCount_L_cons, hlFallCount_cons_scanl, hlFallCount_L_cons]
    refine (hlFallCount_le_count_tail _).trans ?_
    rw [List.tail_cons, List.filterMap_map, Function.id_comp]
    exact count_L_toneSpec_dense a _
      (List.nodup_range.map Nat.succ_injective)
      (fun j hj => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hj
        exact Nat.succ_le_succ k.zero_le)

/-! ### Affix accent typology (§6)

The eight affix accent types and their projection to the coarse
dominant/recessive split. -/

/-- The eight affix types project onto the coarse dominant/recessive
    distinction, with three preserving root accent when present (recessive,
    recessive pre-accenting, accent-shifting) and five overriding it
    (§6). -/
theorem affix_typology_coarse_partition :
    taraSuffix.accentType.toProsodicDominance = .recessive ∧
      siSuffix.accentType.toProsodicDominance = .recessive ∧
      monoSuffix.accentType.toProsodicDominance = .recessive ∧
      ppoiSuffix.accentType.toProsodicDominance = .dominant ∧
      keSuffix.accentType.toProsodicDominance = .dominant ∧
      oPrefix.accentType.toProsodicDominance = .dominant ∧
      tekiSuffix.accentType.toProsodicDominance = .dominant ∧
      zuSuffix.accentType.toProsodicDominance = .dominant :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Compound accent (§4)

The traditional dichotomy by N2 length: short N2s (≤ 2μ) either retain
accent or pre-accent the N1-final position; long N2s (≥ 3μ) take N2-initial
accent unless their own accent is nonfinal. Both rules are stated over mora
counts; the paper's rules target syllables, and the two coincide on the
light-syllable data of (22)–(24) formalized below. -/

/-- The compound accent under a short (≤ 2μ) N2, which either pre-accents
    the N1-final position, its own accent lost to NonFinality, or retains
    its accent shifted by N1's length (§4.1). -/
def shortN2CompoundAccent (n1Morae : ℕ) (n2Accent : Option ℕ)
    (preAccenting : Bool) : Option ℕ :=
  if preAccenting then
    match n1Morae with
    | 0 => none
    | n + 1 => some n
  else
    n2Accent.map (· + n1Morae)

/-- The compound accent under a long (≥ 3μ) N2, which receives N2-initial
    accent when unaccented or finally-accented and otherwise retains its
    own accent (§4.2). -/
def longN2CompoundAccent (n1Morae : ℕ) (n2Accent : Option ℕ)
    (n2Morae : ℕ) : Option ℕ :=
  some (n1Morae + (n2Accent.filter (· + 1 != n2Morae)).getD 0)

/-- The NonFinality constraint over an (accent, mora count) pair, violated
    once when the accent sits on the final mora ([prince-smolensky-1993];
    §4.1 invokes it for the loss of final accent in compounds). -/
def nonFinality : Constraint (Option ℕ × ℕ) :=
  Constraint.binary fun an => an.1 = some (an.2 - 1) ∧ 1 ≤ an.2

/-- In *ka'buto+musi → kabuto'+musi* 'beetle', the pre-accenting short N2
    puts the accent on N1-final *to* ((22a)). -/
theorem kabuto_musi_compound :
    shortN2CompoundAccent 3 (some 0) true = some 2 := by decide

/-- In *si'n+yokohama → sin+yo'kohama* 'Shin-Yokohama', the unaccented long
    N2 receives N2-initial accent ((23a)). -/
theorem sin_yokohama_compound :
    longN2CompoundAccent 2 none 4 = some 2 := by decide

/-- In *si'n+tamane'gi → sin+tamane'gi* 'new onion', the long N2 retains
    its nonfinal accent ((24a)). -/
theorem sin_tamanegi_compound :
    longN2CompoundAccent 2 (some 2) 4 = some 4 := by decide

/-- A nonfinal (or absent) accent satisfies `nonFinality`. -/
theorem nonFinality_eq_zero {acc : Option ℕ} {n : ℕ} (h : ∀ p ∈ acc, p + 1 ≠ n) :
    nonFinality (acc, n) = 0 := by
  rcases acc with _ | p
  · simp [nonFinality, Constraint.binary]
  · have hp := h p rfl
    simp only [nonFinality, Constraint.binary_apply]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    simp only [Option.some.injEq] at h1
    omega

/-- Short-N2 pre-accenting never yields final accent, since the new accent
    lands on the N1-final position and N2 intervenes (§4.1). -/
theorem shortN2_preaccent_nonfinal (n1Morae n2Morae : ℕ) (n2Accent : Option ℕ)
    (h : 1 ≤ n2Morae) :
    nonFinality (shortN2CompoundAccent n1Morae n2Accent true, n1Morae + n2Morae) = 0 := by
  refine nonFinality_eq_zero fun p hp => ?_
  rcases n1Morae with _ | k
  · exact absurd (show p ∈ (none : Option ℕ) from hp) (by simp)
  · have hp' : p ∈ (some k : Option ℕ) := hp
    rw [Option.mem_some_iff] at hp'
    omega

/-- Long-N2 compound accent never yields final accent, since unaccented and
    finally-accented N2s take N2-initial accent and retained accents are
    nonfinal within N2 (§4.2). -/
theorem longN2_nonfinal (n1Morae n2Morae : ℕ) (n2Accent : Option ℕ)
    (h2 : 3 ≤ n2Morae) (hacc : ∀ p ∈ n2Accent, p < n2Morae) :
    nonFinality (longN2CompoundAccent n1Morae n2Accent n2Morae, n1Morae + n2Morae) = 0 := by
  refine nonFinality_eq_zero fun p hp => ?_
  unfold longN2CompoundAccent at hp
  rw [Option.mem_some_iff] at hp
  rcases n2Accent with _ | pos
  · simp only [Option.filter_none, Option.getD_none] at hp
    omega
  · have hlt := hacc pos rfl
    simp only [Option.filter_some] at hp
    split_ifs at hp with hfin
    · rw [bne_iff_ne] at hfin
      simp only [Option.getD_some] at hp
      omega
    · simp only [Option.getD_none] at hp
      omega

/-! ### Weight sensitivity (§2.3)

Japanese moraic structure: coda nasals, geminate first halves, long vowels,
and diphthongs are moraic, so closed syllables are heavy — the weight
sensitivity the LSR analysis rests on. -/

/-- With Weight-by-Position active, a CVC syllable is heavy regardless of
    its segments, e.g. /tan/ = 2μ (§2.3). -/
theorem japanese_wbp_active (o n c : Phonology.Segment) :
    (Syllable.ofCV [o] [n] [c] true).weight = .heavy := rfl

end Kawahara2015
