import Linglib.Core.Basic
import Linglib.Fragments.English.Determiners

/-! # Japanese Quantifier Fragment

Japanese quantifiers differ from English in three key ways:
1. Floating quantifiers: gakusei-ga san-nin kita (students-NOM three-CL came)
2. Wh-indeterminates: dare-ka (who-Q = someone), dare-mo (who-∀ = everyone)
3. No articles — bare nouns are ambiguous (generic/definite/indefinite)

Key typological properties:
- Particle-based force: -ka (existential), -mo (universal), -demo (free choice)
- Floating quantifiers interact with case marking for scope
- Conservativity expected to hold (universal)
- Negative concord via -mo...nai: dare-mo...nai = nobody

## References
- Shimoyama, J. (2006). Indeterminate phrase quantification in Japanese.
- Nakanishi, K. (2007). Formal properties of measurement constructions.
-/

namespace Fragments.Japanese.Determiners

open Fragments.English.Determiners (QForce Monotonicity Strength)

/-- Japanese quantifier entry. Extends the English pattern with
    indeterminate/particle morphology and floating quantifier properties. -/
structure JapaneseQuantEntry where
  /-- Kana/kanji form -/
  form : String
  /-- Rōmaji romanization -/
  romaji : String
  /-- English gloss -/
  gloss : String
  /-- Quantificational force -/
  qforce : QForce
  /-- Monotonicity -/
  monotonicity : Monotonicity := .increasing
  /-- Weak/strong -/
  strength : Strength := .weak
  /-- Quantificational particle (ka/mo/demo) if built from indeterminate -/
  particle : Option String := none
  /-- Whether this quantifier can float (appear separated from its NP) -/
  floats : Bool := false
  /-- Whether this quantifier requires clausemate negation (negative concord) -/
  requiresNegation : Bool := false
  /-- The wh-indeterminate base (e.g., "dare" for dare-ka/dare-mo) -/
  indeterminate : Option String := none
  deriving Repr, BEq

-- ============================================================================
-- Entries
-- ============================================================================

/-- すべて subete "all" — universal, increasing, strong.
    すべての学生 subete-no gakusei "all students" -/
def subete : JapaneseQuantEntry :=
  { form := "すべて"
  , romaji := "subete"
  , gloss := "all"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong }

/-- どのNも dono_N_mo "every N" — universal, increasing, strong.
    Built from wh-indeterminate dono + particle mo.
    どの学生も dono gakusei mo "every student" -/
def dono_N_mo : JapaneseQuantEntry :=
  { form := "どの…も"
  , romaji := "dono-N-mo"
  , gloss := "every"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , particle := some "mo"
  , indeterminate := some "dono" }

/-- 誰か dare_ka "someone" — existential, increasing, weak.
    Built from wh-indeterminate dare + particle ka. -/
def dare_ka : JapaneseQuantEntry :=
  { form := "誰か"
  , romaji := "dare-ka"
  , gloss := "someone"
  , qforce := .existential
  , monotonicity := .increasing
  , strength := .weak
  , particle := some "ka"
  , indeterminate := some "dare" }

/-- 誰も dare_mo "everyone / nobody" — universal (affirmative) or
    negative universal (with clausemate negation: dare-mo...nai).
    Shimoyama (2006): -mo is Hamblin universal over indeterminate set. -/
def dare_mo : JapaneseQuantEntry :=
  { form := "誰も"
  , romaji := "dare-mo"
  , gloss := "everyone / nobody (with negation)"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , particle := some "mo"
  , requiresNegation := false  -- affirmative use exists
  , indeterminate := some "dare" }

/-- 何人か nan_nin_ka "several people" — existential numeral+CL+ka.
    Floating quantifier: 学生が何人か来た gakusei-ga nan-nin-ka kita. -/
def nan_nin_ka : JapaneseQuantEntry :=
  { form := "何人か"
  , romaji := "nan-nin-ka"
  , gloss := "several (people)"
  , qforce := .existential
  , monotonicity := .increasing
  , strength := .weak
  , particle := some "ka"
  , floats := true
  , indeterminate := some "nan" }

/-- ほとんど hotondo "most/almost all" — proportional, increasing, strong. -/
def hotondo : JapaneseQuantEntry :=
  { form := "ほとんど"
  , romaji := "hotondo"
  , gloss := "most"
  , qforce := .proportional
  , monotonicity := .increasing
  , strength := .strong }

/-- 両方 ryōhō "both" — universal dual, strong.
    両方の学生 ryōhō-no gakusei "both students".
    Presupposes exactly two referents (like English "both").
    K&S: both = every restricted to dual sets. -/
def ryoho : JapaneseQuantEntry :=
  { form := "両方"
  , romaji := "ryōhō"
  , gloss := "both"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong }

-- ============================================================================
-- Lexicon
-- ============================================================================

def allQuantifiers : List JapaneseQuantEntry :=
  [subete, dono_N_mo, dare_ka, dare_mo, nan_nin_ka, hotondo, ryoho]

def lookup (romaji : String) : Option JapaneseQuantEntry :=
  allQuantifiers.find? λ e => e.romaji == romaji

-- ============================================================================
-- Verification
-- ============================================================================

/-- dare-ka is built from indeterminate dare + particle ka. -/
theorem dare_ka_indeterminate :
    dare_ka.indeterminate = some "dare" ∧ dare_ka.particle = some "ka" :=
  ⟨rfl, rfl⟩

/-- dare-mo is built from indeterminate dare + particle mo. -/
theorem dare_mo_indeterminate :
    dare_mo.indeterminate = some "dare" ∧ dare_mo.particle = some "mo" :=
  ⟨rfl, rfl⟩

/-- Particle shift: same indeterminate base, different force.
    ka → existential, mo → universal (Shimoyama 2006). -/
theorem particle_force_shift :
    dare_ka.qforce = .existential ∧ dare_mo.qforce = .universal :=
  ⟨rfl, rfl⟩

/-- nan-nin-ka floats. -/
theorem nan_nin_ka_floats : nan_nin_ka.floats = true := rfl

/-- ryōhō is universal and strong (like English "both"). -/
theorem ryoho_universal_strong :
    ryoho.qforce = .universal ∧ ryoho.strength = .strong :=
  ⟨rfl, rfl⟩

/-- Fragment has 7 entries. -/
theorem fragment_size : allQuantifiers.length = 7 := rfl

end Fragments.Japanese.Determiners
