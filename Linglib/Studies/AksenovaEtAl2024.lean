import Mathlib.Tactic.DeriveFintype
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Subregular.Harmony
import Linglib.Data.Examples.AksenovaEtAl2024

/-!
# Aksënova, Rawski, Graf & Heinz 2024: the computational power of harmonic forms

Vowel-harmony phonotactics are tier-based strictly 2-local: project the harmonizing
segments on a tier and ban the disagreeing bigrams. Lokaa ATR harmony needs the tier
because no strictly local window bounds the transparent material; Kirghiz, Buryat, and Yakut
double harmonies each fit on a single tier, with blocking (Buryat's high vowels) and
configuration-dependent blocking (Yakut's low vowels) both mere bigram bans; Kikongo's
vowel and nasal harmonies need two tiers, which are disjoint. Of the four relations two
tier alphabets can stand in, only same, embedded, and disjoint are attested.

This file states each printed grammar (Tables 34.2–34.7) as a `TSLGrammar.ofForbiddenPairs`
over the paper's tier alphabet, reads the paper's forms into that alphabet, and checks the
forms and their starred counterparts against it (`lokaa_rows`, `kirghiz_rows`, `buryat_rows`,
`yakut_rows`, `kikongo_rows`). The `Pattern`
theorems say which grammars segment-level participation reproduces: Kirghiz and Buryat are
conjunctions of two patterns (`kirghiz_two_patterns`, `buryat_expressible`), Buryat's blocking
is asymmetric (`buryat_not_symmetric`), and Yakut's is left open. `tierRelation` computes the
§34.3.4 typology (`kikongo_disjoint_tiers`).

## References

* [aksenova-rawski-graf-heinz-2024]
-/

namespace AksenovaEtAl2024

open Phonology.Harmony Subregular

/-- The tier of a printed form: its symbols read into the tier alphabet, everything else —
consonants, transparent vowels, length and tone marks — dropped. -/
def tierOf {V : Type} (ofChar : Char → Option V) (s : String) : List V := s.toList.filterMap ofChar

/-! ### Lokaa (Table 34.2): ATR agreement on the tier of non-high vowels -/

/-- The Lokaa tier `T = {ɛ, e, o, ə, ɔ, a}`; `eh` = ɛ, `oh` = ɔ. -/
inductive LokaaV where
  | eh | e | o | schwa | oh | a
  deriving DecidableEq, Fintype, Repr

def LokaaV.tense : LokaaV → Bool
  | .e | .o | .schwa => true
  | .eh | .oh | .a => false

/-- Akinlabi's transcription: tone is a precomposed accent on e, o, a and a combining mark
after ɛ, ɔ, ə; high vowels are off the tier. -/
def LokaaV.ofChar : Char → Option LokaaV
  | 'ɛ' => some .eh | 'ɔ' => some .oh | 'ə' => some .schwa
  | 'e' | 'è' | 'é' => some .e | 'o' | 'ò' | 'ó' => some .o | 'a' | 'à' | 'á' => some .a
  | _ => none

/-- `H_ATR`: tier-adjacent vowels disagreeing in tenseness. -/
def lokaaBanned (x y : LokaaV) : Prop := x.tense ≠ y.tense

instance : DecidableRel lokaaBanned := fun x y => by unfold lokaaBanned; infer_instance

def lokaa : TSLGrammar 2 LokaaV := TSLGrammar.ofForbiddenPairs lokaaBanned fun _ => True

/-- The (3) forms are accepted and their starred counterparts rejected. -/
theorem lokaa_rows :
    ∀ row ∈ Examples.all, row.language = "loka1252" →
      tierOf LokaaV.ofChar row.primaryText ∈ lokaa.lang ∧
        ∀ alt ∈ row.alternatives, tierOf LokaaV.ofChar alt.1 ∉ lokaa.lang := by
  simp only [lokaa, mem_ofForbiddenPairs_lang_iff_filter_isChain]; decide

/-! ### Kirghiz ((5), Table 34.3): fronting and rounding on one tier -/

/-- The Kirghiz tier `T = {a, ɨ, e, i, o, ö, u, ü}`; `ih` = ɨ, `oe` = ö, `ue` = ü. -/
inductive KirghizV where
  | a | ih | e | i | o | oe | u | ue
  deriving DecidableEq, Fintype, Repr

namespace KirghizV

def front : KirghizV → Bool
  | .e | .i | .oe | .ue => true
  | .a | .ih | .o | .u => false

def round : KirghizV → Bool
  | .o | .oe | .u | .ue => true
  | .a | .ih | .e | .i => false

def ofChar : Char → Option KirghizV
  | 'a' => some .a | 'ɨ' => some .ih | 'e' => some .e | 'i' => some .i | 'o' => some .o
  | 'ö' => some .oe | 'u' => some .u | 'ü' => some .ue | _ => none

end KirghizV

/-- `H_front ∪ H_round`: the bigram disagrees in fronting or in rounding. -/
def kirghizBanned (x y : KirghizV) : Prop := x.front ≠ y.front ∨ x.round ≠ y.round

instance : DecidableRel kirghizBanned := fun x y => by unfold kirghizBanned; infer_instance

def kirghiz : TSLGrammar 2 KirghizV := TSLGrammar.ofForbiddenPairs kirghizBanned fun _ => True

theorem kirghiz_rows :
    ∀ row ∈ Examples.all, row.language = "kirg1245" →
      tierOf KirghizV.ofChar row.primaryText ∈ kirghiz.lang ∧
        ∀ alt ∈ row.alternatives, tierOf KirghizV.ofChar alt.1 ∉ kirghiz.lang := by
  simp only [kirghiz, mem_ofForbiddenPairs_lang_iff_filter_isChain]; decide

/-- Kirghiz frontness harmony: every vowel participates. -/
def kirghizFront : Pattern KirghizV Bool :=
  { value := fun v => some v.front, participation := fun _ => .participating }

/-- Kirghiz rounding harmony, on the same tier. -/
def kirghizRound : Pattern KirghizV Bool :=
  { value := fun v => some v.round, participation := fun _ => .participating }

/-- The printed grammar is the conjunction of the two patterns' compatibilities. -/
theorem kirghiz_two_patterns (x y : KirghizV) :
    kirghizBanned x y ↔ ¬ (kirghizFront.Compatible x y ∧ kirghizRound.Compatible x y) := by
  revert x y; decide

/-! ### Buryat ((9), Table 34.4): high vowels block rounding -/

/-- The Buryat tier `T = {a, e, ɔ, o, ʊ, u}` (transparent /i/ excluded); `oh` = ɔ, `uh` = ʊ. -/
inductive BuryatV where
  | a | e | oh | o | uh | u
  deriving DecidableEq, Fintype, Repr

namespace BuryatV

def tense : BuryatV → Bool
  | .e | .o | .u => true
  | .a | .oh | .uh => false

def high : BuryatV → Bool
  | .uh | .u => true
  | .a | .e | .oh | .o => false

def round : BuryatV → Bool
  | .oh | .o | .uh | .u => true
  | .a | .e => false

def ofChar : Char → Option BuryatV
  | 'a' => some .a | 'e' => some .e | 'ɔ' => some .oh | 'o' => some .o | 'ʊ' => some .uh
  | 'u' => some .u | _ => none

end BuryatV

/-- `H_ATR ∪ H_r1 ∪ H_r2`: the bigram disagrees in ATR; or its non-high vowels disagree in
rounding; or a rounded non-high vowel follows a high vowel. -/
def buryatBanned (x y : BuryatV) : Prop :=
  x.tense ≠ y.tense ∨ (¬ x.high ∧ ¬ y.high ∧ x.round ≠ y.round) ∨ (x.high ∧ ¬ y.high ∧ y.round)

instance : DecidableRel buryatBanned := fun x y => by unfold buryatBanned; infer_instance

def buryat : TSLGrammar 2 BuryatV := TSLGrammar.ofForbiddenPairs buryatBanned fun _ => True

/-- The (9) forms are accepted — `ɔr-ʊːl-aːd` because the high causative blocks rounding —
and their starred counterparts rejected. -/
theorem buryat_rows :
    ∀ row ∈ Examples.all, row.language = "russ1264" →
      tierOf BuryatV.ofChar row.primaryText ∈ buryat.lang ∧
        ∀ alt ∈ row.alternatives, tierOf BuryatV.ofChar alt.1 ∉ buryat.lang := by
  simp only [buryat, mem_ofForbiddenPairs_lang_iff_filter_isChain]; decide

/-- Blocking is directional: `*ʊɔ` is banned but `ɔʊ` licensed. -/
theorem buryat_asymmetric : buryatBanned .uh .oh ∧ ¬ buryatBanned .oh .uh := by decide

/-- No symmetric adjacency relation renders Buryat's grammar. -/
theorem buryat_not_symmetric (R : BuryatV → BuryatV → Prop) (hsymm : ∀ x y, R x y ↔ R y x) :
    ¬ ∀ x y, R x y ↔ buryatBanned x y := fun h =>
  buryat_asymmetric.2 ((h _ _).mp ((hsymm _ _).mp ((h _ _).mpr buryat_asymmetric.1)))

/-- Buryat ATR harmony: every tier vowel participates. -/
def buryatATR : Pattern BuryatV Bool :=
  { value := fun v => some v.tense, participation := fun _ => .participating }

/-- Buryat rounding harmony: high vowels are opaque, imposing unroundedness on what follows. -/
def buryatRound : Pattern BuryatV Bool :=
  { value := fun v => some (if v.high then false else v.round)
    participation := fun v => if v.high then .opaque else .participating }

/-- With opaque blockers the printed grammar is the conjunction of the two patterns. -/
theorem buryat_expressible (x y : BuryatV) :
    buryatBanned x y ↔ ¬ (buryatATR.Compatible x y ∧ buryatRound.Compatible x y) := by
  revert x y; decide

/-! ### Yakut ((14), Table 34.5): harmonizing blockers -/

/-- The Yakut tier `T = {a, ɨ, e, i, o, ö, u, ü}`. -/
inductive YakutV where
  | a | ih | e | i | o | oe | u | ue
  deriving DecidableEq, Fintype, Repr

namespace YakutV

def front : YakutV → Bool
  | .e | .i | .oe | .ue => true
  | .a | .ih | .o | .u => false

def round : YakutV → Bool
  | .o | .oe | .u | .ue => true
  | .a | .ih | .e | .i => false

def high : YakutV → Bool
  | .ih | .i | .u | .ue => true
  | .a | .e | .o | .oe => false

def ofChar : Char → Option YakutV
  | 'a' => some .a | 'ɨ' => some .ih | 'e' => some .e | 'i' => some .i | 'o' => some .o
  | 'ö' => some .oe | 'u' => some .u | 'ü' => some .ue | _ => none

end YakutV

/-- `H_front ∪ H_r1 ∪ H_r2 ∪ H_r3`: the bigram disagrees in fronting; or its high vowels
disagree in rounding; or a rounded non-high vowel follows a high vowel; or a non-high vowel
is followed by a vowel disagreeing in rounding. (The printed `H_r2` lists `*üö` twice and
omits `*üo`, which `H_front` bans anyway.) -/
def yakutBanned (x y : YakutV) : Prop :=
  x.front ≠ y.front ∨ (x.high ∧ y.high ∧ x.round ≠ y.round) ∨ (x.high ∧ ¬ y.high ∧ y.round) ∨
    (¬ x.high ∧ x.round ≠ y.round)

instance : DecidableRel yakutBanned := fun x y => by unfold yakutBanned; infer_instance

def yakut : TSLGrammar 2 YakutV := TSLGrammar.ofForbiddenPairs yakutBanned fun _ => True

theorem yakut_rows :
    ∀ row ∈ Examples.all, row.language = "yaku1245" →
      tierOf YakutV.ofChar row.primaryText ∈ yakut.lang ∧
        ∀ alt ∈ row.alternatives, tierOf YakutV.ofChar alt.1 ∉ yakut.lang := by
  simp only [yakut, mem_ofForbiddenPairs_lang_iff_filter_isChain]; decide

/-- Low vowels harmonize but block: rounding passes from `o` to `u`, not from `u` to `o`. -/
theorem yakut_asymmetric : yakutBanned .u .o ∧ ¬ yakutBanned .o .u := by decide

/-! ### Kikongo ((16), (18), Tables 34.6–34.7): two disjoint tiers -/

/-- The Kikongo tier symbols: the vowels `T_v = {e, o, i, u}` and `T_n = {n, m, d, l}`. -/
inductive KikongoSeg where
  | e | o | i | u | n | m | d | l
  deriving DecidableEq, Fintype, Repr

namespace KikongoSeg

def isVowel : KikongoSeg → Bool
  | .e | .o | .i | .u => true
  | _ => false

def high : KikongoSeg → Bool
  | .i | .u => true
  | _ => false

def isNasal : KikongoSeg → Bool
  | .n | .m => true
  | _ => false

def ofChar : Char → Option KikongoSeg
  | 'e' => some .e | 'o' => some .o | 'i' => some .i | 'u' => some .u | 'n' => some .n
  | 'm' => some .m | 'd' => some .d | 'l' => some .l | _ => none

/-- A printed form read into the tier symbols. A nasal before a stop is the prenasalized
onset of that stop, not a tier nasal: read with `m` projected, Table 34.7 would ban the
paper's own `-somp-el-`, `-tomb-ol-`, and `-lemb-ol-` (`*ml`). -/
def parse : List Char → List KikongoSeg
  | 'm' :: 'p' :: rest | 'm' :: 'b' :: rest | 'n' :: 'g' :: rest => parse rest
  | c :: rest => (ofChar c).toList ++ parse rest
  | [] => []

end KikongoSeg

/-- The vowel tier `T_v` and the nasal tier `T_n`. -/
abbrev kikongoVowelTier (s : KikongoSeg) : Prop := s.isVowel = true
abbrev kikongoNasalTier (s : KikongoSeg) : Prop := s.isVowel = false

/-- `H_v`: tier-adjacent vowels disagreeing in height. -/
def kikongoVowel : TSLGrammar 2 KikongoSeg :=
  TSLGrammar.ofForbiddenPairs (fun x y => x.high ≠ y.high) kikongoVowelTier

/-- `H_n`: `d` or `l` after a nasal. -/
def kikongoNasal : TSLGrammar 2 KikongoSeg :=
  TSLGrammar.ofForbiddenPairs (fun x y => x.isNasal ∧ ¬ y.isNasal) kikongoNasalTier

/-- Every (16) and (18) form passes both grammars on its own tier. -/
theorem kikongo_rows :
    ∀ row ∈ Examples.all, row.language = "koon1247" →
      KikongoSeg.parse row.primaryText.toList ∈ kikongoVowel.lang ∧
        KikongoSeg.parse row.primaryText.toList ∈ kikongoNasal.lang := by
  simp only [kikongoVowel, kikongoNasal, mem_ofForbiddenPairs_lang_iff_filter_isChain]; decide

/-! ### The tier-relation typology (§34.3.4, Table 34.8)

Two tier alphabets are the same, embedded, disjoint, or partially overlapping; the last is
unattested, a tendency the chapter reports would exclude 95% of the possible tier
organizations of a ten-element alphabet. -/

/-- The four logical relations between two tier alphabets (Figure 34.2). -/
inductive TierRelation where
  | same
  | embedded
  | disjoint
  | overlapping
  deriving DecidableEq, Repr

/-- The relation between two tiers over a finite alphabet. -/
def tierRelation {α : Type} [Fintype α] [DecidableEq α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] : TierRelation :=
  let T₁ := Finset.univ.filter fun s => decide (p s)
  let T₂ := Finset.univ.filter fun s => decide (q s)
  if T₁ = T₂ then .same
  else if T₁ ⊆ T₂ ∨ T₂ ⊆ T₁ then .embedded
  else if Disjoint T₁ T₂ then .disjoint
  else .overlapping

/-- Kirghiz and Buryat double harmonies are single-tier — Table 34.8's S rows. -/
theorem kirghiz_same_tier : tierRelation kirghizFront.OnTier kirghizRound.OnTier = .same := by
  decide

theorem buryat_same_tier : tierRelation buryatATR.OnTier buryatRound.OnTier = .same := by decide

/-- Kikongo's vowel and nasal tiers are disjoint — Table 34.8's D row. -/
theorem kikongo_disjoint_tiers : tierRelation kikongoVowelTier kikongoNasalTier = .disjoint := by
  decide

end AksenovaEtAl2024
