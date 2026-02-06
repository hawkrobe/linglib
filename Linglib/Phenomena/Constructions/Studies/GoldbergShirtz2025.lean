import Mathlib.Data.Rat.Defs

/-!
# Goldberg & Shirtz (2025): PAL Constructions — Empirical Data

Experimental results from five studies on Phrasal Adjective-Like (PAL)
constructions, plus cross-linguistic attestation data.

PALs are phrases that fill word-level syntactic slots:
- "a must-see movie" (must-see is a phrase in modifier position)
- "a real wink-wink situation" (wink-wink is a phrase acting as adjective)
- "a simple meet-and-greet"

## Key findings

1. PALs are preferred when the situation type is **common knowledge** (Study 1a)
2. PALs are preferred when interlocutors have **shared background** (Study 1b)
3. PALs are judged as **wittier** than paraphrases (Study 2)
4. PALs are judged as **more sarcastic** than paraphrases (Study 3)
5. **Conventional subtypes** (must-VERB, a simple ⟨PAL⟩, etc.) behave similarly (Study 5)
6. PALs are attested in **unrelated language families** (German, Dutch, Turkish, Hebrew, ...)

## Reference

Goldberg, A. E., & Shirtz, S. (2025). PAL constructions: How phrases can act
like words. To appear in Language.
-/

namespace Phenomena.Constructions.Studies.GoldbergShirtz2025

/-! ## Study result structure -/

/-- A single experimental result from one of Studies 1–5. -/
structure PALStudyResult where
  /-- Study identifier (e.g. "1a", "2") -/
  study : String
  /-- Research question tested -/
  question : String
  /-- Number of participants -/
  nParticipants : Nat
  /-- Mean % choosing PAL over paraphrase -/
  meanPALChosen : ℚ
  /-- Regression coefficient (β) -/
  beta : ℚ
  /-- z-statistic -/
  zStat : ℚ
  /-- p-value description -/
  pValue : String
  deriving Repr

/-! ## Studies 1–5: Experimental results -/

/-- Study 1a: Common knowledge increases PAL use.
Participants preferred PALs when the situation type (e.g., "grab-and-go")
was common knowledge vs. not. -/
def study1a : PALStudyResult :=
  { study := "1a"
  , question := "Does common knowledge of the situation type increase PAL use?"
  , nParticipants := 80
  , meanPALChosen := 773 / 10   -- 77.3%
  , beta := 169 / 100           -- 1.69
  , zStat := 480 / 100          -- 4.80
  , pValue := "< 0.0001" }

/-- Study 1b: Shared background increases PAL use.
Same design as 1a but manipulates shared background knowledge
between speaker and addressee. -/
def study1b : PALStudyResult :=
  { study := "1b"
  , question := "Does shared background increase PAL use?"
  , nParticipants := 80
  , meanPALChosen := 743 / 10   -- 74.3%
  , beta := 178 / 100           -- 1.78
  , zStat := 462 / 100          -- 4.62
  , pValue := "< 0.001" }

/-- Study 2: PALs are judged wittier than paraphrases. -/
def study2 : PALStudyResult :=
  { study := "2"
  , question := "Are PALs judged as wittier than paraphrases?"
  , nParticipants := 100
  , meanPALChosen := 822 / 10   -- 82.2%
  , beta := 258 / 100           -- 2.58
  , zStat := 848 / 100          -- 8.48
  , pValue := "< 0.001" }

/-- Study 3: PALs are judged more sarcastic than paraphrases. -/
def study3 : PALStudyResult :=
  { study := "3"
  , question := "Are PALs judged as more sarcastic than paraphrases?"
  , nParticipants := 100
  , meanPALChosen := 845 / 10   -- 84.5%
  , beta := 271 / 100           -- 2.71
  , zStat := 854 / 100          -- 8.54
  , pValue := "< 0.001" }

/-- Study 5: Conventional PAL subtypes behave like novel PALs.
Tests must-VERB, a simple ⟨PAL⟩, Don't PAL me, the old ⟨PAL⟩ N. -/
def study5 : PALStudyResult :=
  { study := "5"
  , question := "Do conventional PAL subtypes show the same familiarity sensitivity?"
  , nParticipants := 100
  , meanPALChosen := 8609 / 100  -- 86.09%
  , beta := 228 / 100            -- 2.28
  , zStat := 610 / 100           -- 6.10
  , pValue := "< 0.0001" }

/-- All study results. -/
def allStudies : List PALStudyResult :=
  [study1a, study1b, study2, study3, study5]

/-! ## Cross-linguistic data -/

/-- Attestation of PAL-like constructions across languages. -/
structure CrossLinguisticPAL where
  language : String
  family : String
  exemplar : String
  gloss : String
  resemblesCompound : Bool
  deriving Repr

/-- German PAL attestation. -/
def german : CrossLinguisticPAL :=
  { language := "German"
  , family := "Indo-European (Germanic)"
  , exemplar :="ein Hau-drauf Typ"
  , gloss := "a hit-on-it type (= a reckless type)"
  , resemblesCompound := true }

/-- Dutch PAL attestation. -/
def dutch : CrossLinguisticPAL :=
  { language := "Dutch"
  , family := "Indo-European (Germanic)"
  , exemplar :="een trek-je-niks-aan houding"
  , gloss := "a pull-you-nothing-on attitude (= a couldn't-care-less attitude)"
  , resemblesCompound := true }

/-- Afrikaans PAL attestation. -/
def afrikaans : CrossLinguisticPAL :=
  { language := "Afrikaans"
  , family := "Indo-European (Germanic)"
  , exemplar :="'n sommer-net-so ding"
  , gloss := "a just-like-that thing"
  , resemblesCompound := true }

/-- Turkish PAL attestation. -/
def turkish : CrossLinguisticPAL :=
  { language := "Turkish"
  , family := "Turkic"
  , exemplar :="gel-git politikası"
  , gloss := "come-go policy (= wishy-washy policy)"
  , resemblesCompound := true }

/-- Hebrew PAL attestation. -/
def hebrew : CrossLinguisticPAL :=
  { language := "Hebrew"
  , family := "Afro-Asiatic (Semitic)"
  , exemplar :="yaldá al-tidrexí-alái"
  , gloss := "girl don't-step-on-me (= a don't-mess-with-me girl)"
  , resemblesCompound := false }

/-- Brazilian Portuguese PAL attestation. -/
def brazilianPortuguese : CrossLinguisticPAL :=
  { language := "Brazilian Portuguese"
  , family := "Indo-European (Romance)"
  , exemplar :="um papo cabeça"
  , gloss := "a talk head (= an intellectual conversation)"
  , resemblesCompound := true }

/-- All cross-linguistic attestations. -/
def crossLinguisticData : List CrossLinguisticPAL :=
  [german, dutch, afrikaans, turkish, hebrew, brazilianPortuguese]

/-! ## Distributional properties -/

/-- Syntactic positions where PALs are attested. -/
inductive PALPosition where
  | prenominalModifier  -- "a grab-and-go lunch"
  | headNoun            -- "a real wink-wink"
  | predicateAdj        -- "The vibe was very wink-wink"
  | verb                -- "Don't wink-wink me"
  deriving Repr, DecidableEq, BEq

/-- An attested PAL example with its syntactic position. -/
structure PALExample where
  pal : String
  position : PALPosition
  sentence : String
  deriving Repr

/-- Key examples showing PAL distributional flexibility. -/
def palExamples : List PALExample :=
  [ { pal := "grab-and-go"
    , position := .prenominalModifier
    , sentence := "a grab-and-go lunch" }
  , { pal := "wink-wink"
    , position := .headNoun
    , sentence := "a real wink-wink" }
  , { pal := "wink-wink"
    , position := .predicateAdj
    , sentence := "The vibe was very wink-wink" }
  , { pal := "wink-wink"
    , position := .verb
    , sentence := "Don't wink-wink me" }
  , { pal := "meet-and-greet"
    , position := .prenominalModifier
    , sentence := "a simple meet-and-greet event" }
  , { pal := "must-see"
    , position := .prenominalModifier
    , sentence := "a must-see movie" } ]

/-! ## Stress pattern -/

/-- PALs receive compound-like stress: primary stress falls on the PAL
(modifier), not on the head noun. This mirrors NN compound stress
(e.g., BLACKbird vs. black BIRD). -/
def palStressIsCompoundLike : Bool := true

end Phenomena.Constructions.Studies.GoldbergShirtz2025
