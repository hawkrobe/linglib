import Linglib.Phonology.Prosody.Syllable
import Linglib.Phonology.Constraints.Defs
import Linglib.Fragments.Japanese.Prosody

/-!
# Kawahara (2015) [kawahara-2015]

*The phonology of Japanese accent* surveys Tokyo Japanese pitch accent: a
single lexical accent per word determines the surface tone contour, and its
location is predictable in loanwords, compounds, and affixed words. This
file formalizes the survey's core generalizations — the Table 1 comparison
of the antepenultimate accent rule ([mccawley-1968]) with the Latin Stress
Rule ([hayes-1995]), the accent-to-tone derivation and its culminativity
(`accentToTones_culminative`), the eight-way affix accent typology, and
NonFinality ([prince-smolensky-1993]) in compound accent.
-/

namespace Kawahara2015

open Prosody Japanese.Prosody Constraints

/-! ### Default accent: the AAR vs the Latin Stress Rule

Language-neutral accent-placement rules over a syllable-weight profile,
compared on loanword default accentuation (§2). -/

/-- The antepenultimate accent rule, which accents the syllable containing
    the antepenultimate mora and the initial syllable of shorter words
    ([mccawley-1968]). Returns the 0-indexed syllable. -/
def defaultAccentAAR (weights : List Syllable.Weight) : Option ℕ :=
  match weights with
  | [] => none
  | _ => some ((weights.scanl (· + ·) 0).tail.findIdx (weights.sum - 3 < ·))

/-- The Latin Stress Rule, which accents a heavy (≥ 2μ) penult and the
    antepenult otherwise, with mono- and disyllables accented initially
    ([hayes-1995]). §2.3 reviews arguments that LSR-conforming variants
    occur even where the two rules diverge, making the LSR arguably the
    better characterization of the Japanese default. -/
def latinStressRule (weights : List Syllable.Weight) : Option ℕ :=
  match weights with
  | [] => none
  | _ =>
    some (weights.length - if Syllable.Weight.heavy ≤ weights.reverse.getD 1 0 then 2 else 3)

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
    specification (`toneSpec`) followed by spreading ((7)–(9)). -/
def accentToTones (accentMora : Option ℕ) (nMorae : ℕ) : List LevelTone :=
  spread ((List.range nMorae).map (toneSpec accentMora)) .H
where
  /-- Rightward spreading into unspecified positions. The seed is never
      consulted on well-formed input, since mora 0 is always specified. -/
  spread : List (Option LevelTone) → LevelTone → List LevelTone
    | [], _ => []
    | some t :: rest, _ => t :: spread rest t
    | none :: rest, last => last :: spread rest last

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
      have e : hlFallCount (.L :: b :: rest) = hlFallCount (b :: rest) := by
        cases b <;> rfl
      rw [e, List.tail_cons]
      exact ih.trans (count_L_tail_le _)

theorem hlFallCount_cons_cons (t u : LevelTone) (l : List LevelTone) :
    hlFallCount (t :: u :: l) =
      hlFallCount (u :: l) + if t = .H ∧ u = .L then 1 else 0 := by
  cases t <;> cases u <;> simp [hlFallCount]

/-- Spreading is fall-invariant, since copying a tone neither creates nor
    destroys an HL fall. -/
theorem hlFallCount_spread (spec : List (Option LevelTone)) (t : LevelTone) :
    hlFallCount (t :: accentToTones.spread spec t) =
      hlFallCount (t :: spec.filterMap id) := by
  induction spec generalizing t with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | some u =>
      rw [show accentToTones.spread (some u :: rest) t =
            u :: accentToTones.spread rest u from rfl,
        show (some u :: rest).filterMap id = u :: rest.filterMap id from rfl,
        hlFallCount_cons_cons, hlFallCount_cons_cons, ih u]
    | none =>
      rw [show accentToTones.spread (none :: rest) t =
            t :: accentToTones.spread rest t from rfl,
        show (none :: rest).filterMap id = rest.filterMap id from rfl,
        hlFallCount_cons_cons, ih t]
      have hδ : (if t = .H ∧ t = .L then 1 else 0) = 0 := by cases t <;> simp
      rw [hδ, Nat.add_zero]

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
        (if a = some 0 then LevelTone.H else .L) ::
          accentToTones.spread (((List.range m).map Nat.succ).map (toneSpec a))
            (if a = some 0 then LevelTone.H else .L) := by
      rw [accentToTones, List.range_succ_eq_map, List.map_cons, toneSpec_zero]
      rfl
    rw [hpeel, hlFallCount_spread]
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
    if n1Morae > 0 then some (n1Morae - 1) else none
  else
    n2Accent.map (· + n1Morae)

/-- The compound accent under a long (≥ 3μ) N2, which receives N2-initial
    accent when unaccented or finally-accented and otherwise retains its
    own accent (§4.2). -/
def longN2CompoundAccent (n1Morae : ℕ) (n2Accent : Option ℕ)
    (n2Morae : ℕ) : Option ℕ :=
  match n2Accent with
  | none => some n1Morae
  | some pos =>
    if pos + 1 = n2Morae then some n1Morae
    else some (pos + n1Morae)

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
  have hp' : p ∈ (if n1Morae > 0 then some (n1Morae - 1) else none) := hp
  split_ifs at hp' with h1
  · rw [Option.mem_some_iff] at hp'
    omega
  · exact absurd hp' (by simp)

/-- Long-N2 compound accent never yields final accent, since unaccented and
    finally-accented N2s take N2-initial accent and retained accents are
    nonfinal within N2 (§4.2). -/
theorem longN2_nonfinal (n1Morae n2Morae : ℕ) (n2Accent : Option ℕ)
    (h2 : 3 ≤ n2Morae) (hacc : ∀ p ∈ n2Accent, p < n2Morae) :
    nonFinality (longN2CompoundAccent n1Morae n2Accent n2Morae, n1Morae + n2Morae) = 0 := by
  refine nonFinality_eq_zero fun p hp => ?_
  rcases n2Accent with _ | pos
  · have hp' : p ∈ (some n1Morae : Option ℕ) := hp
    rw [Option.mem_some_iff] at hp'
    omega
  · have hlt := hacc pos rfl
    have hp' : p ∈ (if pos + 1 = n2Morae then some n1Morae else some (pos + n1Morae)) := hp
    split_ifs at hp' with hfin <;> rw [Option.mem_some_iff] at hp' <;> omega

/-! ### Weight sensitivity (§2.3)

Japanese moraic structure: coda nasals, geminate first halves, long vowels,
and diphthongs are moraic, so closed syllables are heavy — the weight
sensitivity the LSR analysis rests on. -/

/-- With Weight-by-Position active, a CVC syllable is heavy regardless of
    its segments, e.g. /tan/ = 2μ (§2.3). -/
theorem japanese_wbp_active (o n c : Phonology.Segment) :
    (Syllable.ofCV [o] [n] [c] true).weight = .heavy := rfl

end Kawahara2015
