import Linglib.Phonology.Prosody.Syllable
import Mathlib.Data.Nat.PSub
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
(`accentToTones_culminative`), and NonFinality ([prince-smolensky-1993]) in
compound accent. The §6 affix accent lexicon lives in
`Fragments/Japanese/Prosody.lean`.
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

/-- The weight profile of an all-light loanword — one light syllable per
    mora. -/
def lightProfile (e : ProsodicEntry) : List Syllable.Weight :=
  List.replicate e.nMorae .light

/-- *ku-ri-su'-ma-su* 'Christmas', accented on the antepenultimate mora
    ((10a)). -/
def kurisumasu : ProsodicEntry :=
  { form := "kurisumasu", gloss := "Christmas", accentMora := some 2, nMorae := 5 }

/-- *a-su-fa'-ru-to* 'asphalt', accented on the antepenultimate mora
    ((10g)). -/
def asufaruto : ProsodicEntry :=
  { form := "asufaruto", gloss := "asphalt", accentMora := some 2, nMorae := 5 }

/-- *ma-ku-do-na'-ru-do* 'McDonald', accented on the antepenultimate mora
    ((10h)). -/
def makudonarudo : ProsodicEntry :=
  { form := "makudonarudo", gloss := "McDonald's", accentMora := some 3, nMorae := 6 }

/-- *a.me.ri.ka* 'America', unaccented as a four-mora word with two final
    light non-epenthetic syllables ((16a)). -/
def amerika : ProsodicEntry :=
  { form := "amerika", gloss := "America", accentMora := none, nMorae := 4 }

/-- The accented loanwords of (10) carry the accent the AAR assigns. -/
theorem loanwords_match_aar :
    defaultAccentAAR (lightProfile kurisumasu) = kurisumasu.accentMora ∧
      defaultAccentAAR (lightProfile asufaruto) = asufaruto.accentMora ∧
      defaultAccentAAR (lightProfile makudonarudo) = makudonarudo.accentMora := by decide

/-- On all-light profiles the LSR agrees with the AAR, so the (10)
    loanwords match it as well (§2.3). -/
theorem loanwords_match_lsr :
    latinStressRule (lightProfile kurisumasu) = kurisumasu.accentMora ∧
      latinStressRule (lightProfile asufaruto) = asufaruto.accentMora ∧
      latinStressRule (lightProfile makudonarudo) = makudonarudo.accentMora := by decide

/-- Neither default rule derives *amerika*'s unaccentedness, as neither
    produces unaccented outputs (§2.3 n. 10). Four-mora light-final
    unaccentedness is §2.4's separate generalization. -/
theorem amerika_beyond_default_rules :
    defaultAccentAAR (lightProfile amerika) ≠ amerika.accentMora ∧
      latinStressRule (lightProfile amerika) ≠ amerika.accentMora := by decide

/-! ### From accent to surface tones (§1.4)

Tones are specified by the accentual HL and the initial rise, then spread
rightward ((7)–(9)). -/

/-- A level tone. Japanese distinguishes only H and L at the lexical level
    (§1.3). -/
inductive LevelTone where
  | H
  | L
  deriving DecidableEq, Repr

/-- The accentual HL — H on the accented mora, L on its successor ((4)). -/
def accentualHL (accentMora : Option ℕ) (i : ℕ) : Option LevelTone :=
  if accentMora = some i then some .H
  else if accentMora.map (· + 1) = some i then some .L
  else none

/-- The initial rise — L on mora 0, H on mora 1 ((5)). -/
def initialRise (i : ℕ) : Option LevelTone :=
  if i = 0 then some .L else if i = 1 then some .H else none

/-- The tonal specification of mora `i` before spreading, with the
    accentual HL taking precedence over the initial rise ((5b)). -/
def toneSpec (accentMora : Option ℕ) (i : ℕ) : Option LevelTone :=
  (accentualHL accentMora i).or (initialRise i)

/-- The surface tones of an `nMorae`-word from its accent position, by
    specification (`toneSpec`) followed by spreading — a left scan copying
    the most recent specified tone rightward ((7)–(9)). The seed is never
    consulted, since mora 0 is always specified. -/
def accentToTones (accentMora : Option ℕ) (nMorae : ℕ) : List LevelTone :=
  (((List.range nMorae).map (toneSpec accentMora)).scanl (fun t o => o.getD t) .H).tail

/-- Unaccented *ame(+ga)* 'candy' surfaces LHH by initial rise and
    spreading ((6b)). -/
theorem ameCandy_ga_tones : accentToTones ameCandy.accentMora 3 = [.L, .H, .H] := by
  decide

/-- Initially-accented *a'me(+ga)* 'rain' surfaces HLL, since the accentual
    HL blocks the initial rise ((5b), (8)). -/
theorem ameRain_ga_tones : accentToTones ameRain.accentMora 3 = [.H, .L, .L] := by
  decide

/-- Of the n+1 accent patterns of a trisyllable ((3)), the unaccented,
    initial, and medial contours are distinct, while final accent
    neutralizes with unaccentedness word-internally because the post-accent
    L falls off the word edge (§1.4). -/
theorem trisyllabic_tone_patterns :
    [accentToTones none 3, accentToTones (some 0) 3, accentToTones (some 1) 3].Nodup ∧
      accentToTones none 3 = accentToTones (some 2) 3 := by decide

/-! ### Culminativity

"Japanese allows only one HL pitch fall within a word" (§1.4) —
`accentToTones_culminative` derives this for every accent location and word
length. -/

/-- The number of H-to-L falls in a tone string — the occurrences of
    `(H, L)` among adjacent pairs. -/
def hlFallCount (l : List LevelTone) : ℕ := (l.zip l.tail).count (.H, .L)

/-- An L head opens no fall. -/
theorem hlFallCount_L_cons (l : List LevelTone) :
    hlFallCount (.L :: l) = hlFallCount l := by
  cases l <;> simp [hlFallCount]

theorem hlFallCount_cons_cons (t u : LevelTone) (l : List LevelTone) :
    hlFallCount (t :: u :: l) =
      hlFallCount (u :: l) + if t = .H ∧ u = .L then 1 else 0 := by
  cases t <;> cases u <;> simp [hlFallCount]

/-- Every fall consumes an L strictly after the first position. -/
theorem hlFallCount_le_count_tail :
    ∀ l : List LevelTone, hlFallCount l ≤ l.tail.count .L
  | [] => Nat.le_refl _
  | [_] => by simp [hlFallCount]
  | t :: u :: rest => by
      have ih := hlFallCount_le_count_tail (u :: rest)
      rw [hlFallCount_cons_cons, List.tail_cons]
      rw [List.tail_cons] at ih
      cases t <;> cases u <;> simp_all
      omega

/-- Spreading is fall-invariant, since copying a tone neither creates nor
    destroys an HL fall. -/
theorem hlFallCount_cons_scanl (spec : List (Option LevelTone)) (x t : LevelTone) :
    hlFallCount (x :: spec.scanl (fun t o => o.getD t) t) =
      hlFallCount (x :: t :: spec.filterMap id) := by
  induction spec generalizing x t with
  | nil => rfl
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
  by_cases h : a = some 0 <;> simp [toneSpec, accentualHL, initialRise, h]

/-- After mora 0, the only source of a specified L is the post-accent L,
    which pins the accent location. -/
theorem toneSpec_eq_L {a : Option ℕ} {j : ℕ} (hj : 1 ≤ j) :
    toneSpec a j = some .L ↔ a.map (· + 1) = some j := by
  unfold toneSpec accentualHL initialRise
  split_ifs with h1 h2 <;> simp_all [Option.or]

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
    · have ha : a.map (· + 1) = some j := (toneSpec_eq_L (hpos j (.head _))).mp hj
      have hrest : (rest.filterMap (toneSpec a)).count .L = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨k, hk, hspec⟩ := List.mem_filterMap.mp hmem
        have hak : a.map (· + 1) = some k := (toneSpec_eq_L (hpos k (.tail _ hk))).mp hspec
        rw [ha] at hak
        exact (List.nodup_cons.mp hnd).1 ((Option.some_inj.mp hak) ▸ hk)
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

/-! ### Compound accent (§4)

The traditional dichotomy by N2 length: short N2s (≤ 2μ) either retain
accent or pre-accent the N1-final position; long N2s (≥ 3μ) take N2-initial
accent unless their own accent is nonfinal. Both rules are stated over mora
counts; the paper's rules target syllables, and the two coincide on the
light-syllable data of (21)–(24) formalized below. -/

/-- A retaining short N2 keeps its own accent, shifted into the compound
    (§4.1, (21)). -/
def shortN2Retain (n1Morae : ℕ) (n2Accent : Option ℕ) : Option ℕ :=
  n2Accent.map (n1Morae + ·)

/-- A pre-accenting short N2 accents the N1-final mora — the partial
    predecessor of N1's length — its own accent lost to NonFinality
    (§4.1, (22)). -/
def shortN2PreAccent (n1Morae : ℕ) : Option ℕ :=
  n1Morae.ppred

/-- The compound accent under a long (≥ 3μ) N2, which receives N2-initial
    accent when unaccented or finally-accented and otherwise retains its
    own accent (§4.2). -/
def longN2CompoundAccent (n1Morae n2Morae : ℕ) (n2Accent : Option ℕ) : Option ℕ :=
  some (n1Morae + (n2Accent.filter (· + 1 != n2Morae)).getD 0)

/-- The NonFinality constraint over an (accent, mora count) pair, violated
    once when the accent sits on the final mora ([prince-smolensky-1993];
    §4.1 invokes it for the loss of final accent in compounds). -/
def nonFinality : Constraint (Option ℕ × ℕ) :=
  Constraint.binary fun an => an.1.map (· + 1) = some an.2

/-- In *fa'asuto+ki'su → faasuto+ki'su* 'first kiss', the short N2 retains
    its accent on *ki* ((21a)). -/
theorem faasuto_kisu_compound : shortN2Retain 4 (some 0) = some 4 := rfl

/-- In *ka'buto+musi → kabuto'+musi* 'beetle', the pre-accenting short N2
    puts the accent on N1-final *to* ((22a)). -/
theorem kabuto_musi_compound : shortN2PreAccent 3 = some 2 := rfl

/-- In *si'n+yokohama → sin+yo'kohama* 'Shin-Yokohama', the unaccented long
    N2 receives N2-initial accent ((23a)). -/
theorem sin_yokohama_compound : longN2CompoundAccent 2 4 none = some 2 := rfl

/-- In *si'n+tamane'gi → sin+tamane'gi* 'new onion', the long N2 retains
    its nonfinal accent ((24a)). -/
theorem sin_tamanegi_compound : longN2CompoundAccent 2 4 (some 2) = some 4 := rfl

/-- `nonFinality` is satisfied exactly when the accent's successor is not
    the mora count. -/
@[simp] theorem nonFinality_eq_zero {acc : Option ℕ} {n : ℕ} :
    nonFinality (acc, n) = 0 ↔ acc.map (· + 1) ≠ some n := by
  simp [nonFinality, Constraint.binary]

/-- Short-N2 pre-accenting never yields final accent, since the new accent
    lands on the N1-final position and N2 intervenes (§4.1). -/
theorem shortN2_preaccent_nonfinal (n1Morae n2Morae : ℕ) (h : 1 ≤ n2Morae) :
    nonFinality (shortN2PreAccent n1Morae, n1Morae + n2Morae) = 0 := by
  rcases n1Morae with _ | k
  · simp [shortN2PreAccent, Nat.ppred_zero]
  · simp [shortN2PreAccent, Nat.ppred_succ]
    omega

/-- Long-N2 compound accent never yields final accent, since retention is
    filtered to N2-nonfinal accents and the N2-initial default is nonfinal
    in a trimoraic-or-longer N2 (§4.2). -/
theorem longN2_nonfinal (n1Morae n2Morae : ℕ) (n2Accent : Option ℕ) (h2 : 3 ≤ n2Morae) :
    nonFinality (longN2CompoundAccent n1Morae n2Morae n2Accent, n1Morae + n2Morae) = 0 := by
  rcases hX : n2Accent.filter (· + 1 != n2Morae) with _ | pos
  · simp [longN2CompoundAccent, hX]
    omega
  · have hpos := (Option.filter_eq_some_iff.mp hX).2
    rw [bne_iff_ne] at hpos
    simp [longN2CompoundAccent, hX]
    omega

end Kawahara2015
