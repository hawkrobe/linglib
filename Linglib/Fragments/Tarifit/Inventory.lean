import Linglib.Theories.Phonology.Syllable.NaturalClass

/-!
# Tarifit Consonant Inventory
@cite{afkir-zellou-2025}

Consonantal root data for Tarifit Berber (Amazigh, Afro-Asiatic;
Glottocode: tari1263). Target words are CCəC triconsonantal verbs in
the simple imperative form, from the production experiment in
@cite{afkir-zellou-2025}.

Each word is specified by its three consonant natural classes on the
Parker 8-level sonority scale (@cite{parker-2002}), enabling MaxEnt
constraint evaluation based on cluster sonority profiles.

## Prosodic template

Tarifit has non-concatenative morphology with consonantal roots and
prosodic templates. The CCəC template places a "prosodic template"
schwa between C2 and C3. The C1–C2 cluster may receive an **intrusive
schwa** (articulatory in origin) or the word may surface **vowelless**
(no schwa at all).

## Spirantization

Singleton stops /b, d, t/ surface as fricatives [β, ð, θ] in all
non-geminate environments (@cite{afkir-zellou-2025}). Natural class
assignments below reflect surface realization.

## Word list sourcing

Words are from the paper's 38-item CCəC target word list. Glosses
marked with (p. 20) are verified from the paper's main text; others
are from the paper's word list / online appendix.
-/

namespace Fragments.Tarifit.Inventory

open Theories.Phonology.Syllable

-- ============================================================================
-- § 1: Word Type
-- ============================================================================

/-- A CCəC target word from the Tarifit production experiment.
    The template schwa sits between C2 and C3. -/
structure TriconWord where
  ipa   : String
  gloss : String
  c1    : NatClass
  c2    : NatClass
  c3    : NatClass
  deriving DecidableEq, BEq, Repr

/-- C1–C2 sonority profile: rising (C1 less sonorous than C2). -/
def TriconWord.isRising (w : TriconWord) : Bool :=
  w.c1.parkerSonority < w.c2.parkerSonority

/-- C1–C2 sonority profile: falling (C1 more sonorous than C2). -/
def TriconWord.isFalling (w : TriconWord) : Bool :=
  w.c1.parkerSonority > w.c2.parkerSonority

/-- C1–C2 sonority profile: plateauing (equal sonority). -/
def TriconWord.isPlateauing (w : TriconWord) : Bool :=
  w.c1.parkerSonority == w.c2.parkerSonority

-- ============================================================================
-- § 2: Target Words
-- ============================================================================

-- Rising onset (C1 < C2 sonority): environment for intrusive schwa

/-- /qrəβ/ : VLS(1)–liquid(6)–VDF(4), rise = 5.
    Table 9 "almost exclusively" C1ǎC2 (@cite{afkir-zellou-2025}).
    -- UNVERIFIED: gloss inferred from Berber root Q-R-B; paper does not
    -- gloss this word (distinct from /qrəʕ/ 'rip!' on p. 20). -/
def w_qreb : TriconWord := ⟨"qrəβ", "approach!", .vls, .liquid, .vdf⟩

/-- /qməʕ/ 'suppress!' (p. 20): VLS(1)–nasal(5)–VDF(4), rise = 4.
    Table 9 "variably" C1ǎC2 (@cite{afkir-zellou-2025}). -/
def w_qmes : TriconWord := ⟨"qməʕ", "suppress!", .vls, .nasal, .vdf⟩

/-- /srəm/ : VLF(3)–liquid(6)–nasal(5), rise = 3.
    Table 9 "almost exclusively" C1ǎC2 (@cite{afkir-zellou-2025}).
    -- UNVERIFIED: gloss inferred from Berber root S-R-M; paper does not
    -- gloss this word explicitly. -/
def w_srem : TriconWord := ⟨"srəm", "be ashamed!", .vlf, .liquid, .nasal⟩

-- Falling onset (C1 > C2 sonority): no intrusive schwa

/-- /ntəf/ 'pluck!' (p. 20): nasal(5)–VLS(1)–VLF(3), fall = 4.
    Table 7 "often vowelless" (>30%); Table 9 "never" C1ǎC2
    (@cite{afkir-zellou-2025}). -/
def w_ntef : TriconWord := ⟨"ntəf", "pluck!", .nasal, .vls, .vlf⟩

/-- /nqəβ/ 'pick!' (p. 20): nasal(5)–VLS(1)–VDF(4), fall = 4.
    Table 9 "variably" C1ǎC2 (@cite{afkir-zellou-2025}). -/
def w_nqeb : TriconWord := ⟨"nqəβ", "pick!", .nasal, .vls, .vdf⟩

/-- /ħkəm/ 'judge!' (p. 20): VLF(3)–VLS(1)–nasal(5), fall = 2.
    Table 9 "never" C1ǎC2 (@cite{afkir-zellou-2025}). -/
def w_hkem : TriconWord := ⟨"ħkəm", "judge!", .vlf, .vls, .nasal⟩

-- Plateauing onset (C1 ≈ C2 sonority): no intrusive schwa

/-- /sχəf/ 'pass out!' (p. 20): VLF(3)–VLF(3)–VLF(3), plateau.
    Table 7 "often vowelless" (13–20%); Table 9 "never" C1ǎC2
    (@cite{afkir-zellou-2025}). -/
def w_skhef : TriconWord := ⟨"sχəf", "pass out!", .vlf, .vlf, .vlf⟩

/-- /sfən/ 'show!' (p. 20): VLF(3)–VLF(3)–nasal(5), plateau.
    Table 9 "never" C1ǎC2 (@cite{afkir-zellou-2025}). -/
def w_sfen : TriconWord := ⟨"sfən", "show!", .vlf, .vlf, .nasal⟩

/-- All target words from the production experiment used in our model. -/
def targetWords : List TriconWord :=
  [w_qreb, w_qmes, w_srem, w_ntef, w_nqeb, w_hkem, w_skhef, w_sfen]

-- ============================================================================
-- § 3: Sonority Profile Verification
-- ============================================================================

theorem qreb_rising : w_qreb.isRising = true := by native_decide
theorem qmes_rising : w_qmes.isRising = true := by native_decide
theorem srem_rising : w_srem.isRising = true := by native_decide
theorem ntef_falling : w_ntef.isFalling = true := by native_decide
theorem nqeb_falling : w_nqeb.isFalling = true := by native_decide
theorem hkem_falling : w_hkem.isFalling = true := by native_decide
theorem skhef_plateauing : w_skhef.isPlateauing = true := by native_decide
theorem sfen_plateauing : w_sfen.isPlateauing = true := by native_decide

end Fragments.Tarifit.Inventory
