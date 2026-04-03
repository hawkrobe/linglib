/-!
# Narrog (2010, 2012) Deontic Necessity Typology
@cite{narrog-2012} @cite{narrog-2010}

Cross-linguistic survey data on deontic necessity from a genealogically
diverse sample of 200 languages (@cite{narrog-2010} appendix;
@cite{narrog-2012} Table 6.6).

## Data sources

- **Table 3 / Table 6.5**: Area-level counts of whether each language has
  grammaticalized obligation (NEC) and/or ability/situational possibility
  (POT) markers, split by 6 geographic areas.

- **Table 4 / Table 6.6**: Aggregate counts of deontic necessity type
  (strong, weak, neutral, indeterminate). These are the finest-grained
  published data — per-language type assignments are not available.

- **Appendix**: The 200 languages in the sample, listed by phylum.

## Notes

- The total of Table 4 (60 + 62 + 22 + 32 = 176) exceeds 131 (languages
  with any NEC marker) because 44 languages had markers of multiple types
  (@cite{narrog-2010} fn. 17).
- Per-language deontic necessity type assignments are not published;
  only aggregate counts are available.
-/

namespace Core.Modality.DeonticNecessity

-- ============================================================================
-- §1. Deontic Necessity Type Classification
-- ============================================================================

/-- How a language grammaticalizes deontic necessity.
    From @cite{narrog-2010} Table 4 / @cite{narrog-2012} Table 6.6. -/
inductive DeonticNecessityType where
  | strong          -- grammaticalized strong deontic necessity (*must*-type)
  | weak            -- grammaticalized weak deontic necessity (*should*-type)
  | neutral         -- grammaticalized but unspecified for strength
  | indeterminate   -- unclear from available descriptions
  deriving DecidableEq, Repr

/-- Language counts by deontic necessity type.
    Source: @cite{narrog-2010} Table 4, reproduced in @cite{narrog-2012}
    Table 6.6 (p. 251).

    Total exceeds 200 because 44 languages have markers of multiple types
    (@cite{narrog-2010} fn. 17). -/
def deonticNecessityCounts : List (DeonticNecessityType × Nat) :=
  [ (.strong, 60), (.weak, 62), (.neutral, 22), (.indeterminate, 32) ]

/-- The sample size: 200 genealogically diverse languages. -/
def sampleSize : Nat := 200

-- ============================================================================
-- §2. Area-Level NEC/POT Presence (Table 3 / Table 6.5)
-- ============================================================================

/-- Geographic area classification used in the sample. -/
inductive Area where
  | africa
  | americas
  | australia
  | eurasia
  | pacific      -- Austronesian and Papuan
  | southSoutheastAsia
  deriving DecidableEq, Repr

/-- Per-area counts of obligation (NEC) and ability/possibility (POT) marking.
    Source: @cite{narrog-2010} Table 3 / @cite{narrog-2012} Table 6.5 (p. 250). -/
structure AreaModalPresence where
  area : Area
  bothNecPot : Nat   -- languages with both NEC and POT markers
  onlyNec : Nat      -- languages with only NEC markers
  onlyPot : Nat      -- languages with only POT markers
  neither : Nat      -- languages with neither
  deriving Repr, BEq

def AreaModalPresence.total (a : AreaModalPresence) : Nat :=
  a.bothNecPot + a.onlyNec + a.onlyPot + a.neither

def areaData : List AreaModalPresence :=
  [ ⟨.africa,             27, 3,  9, 7,  ⟩
  , ⟨.americas,           32, 4,  7, 4,  ⟩
  , ⟨.australia,           1, 2,  1, 12, ⟩
  , ⟨.eurasia,            15, 0,  0, 0,  ⟩
  , ⟨.pacific,            27, 1, 17, 11, ⟩
  , ⟨.southSoutheastAsia, 19, 0,  1, 0,  ⟩
  ]

-- ============================================================================
-- §3. Derived Counts
-- ============================================================================

/-- Count of a specific deontic necessity type. -/
def countOf (t : DeonticNecessityType) : Nat :=
  match deonticNecessityCounts.find? (·.1 == t) with
  | some (_, n) => n
  | none => 0

/-- Total languages across all areas. -/
def areaSampleTotal : Nat := areaData.foldl (· + ·.total) 0

/-- Total languages with any NEC marker (both + onlyNec). -/
def languagesWithNec : Nat :=
  areaData.foldl (fun acc a => acc + a.bothNecPot + a.onlyNec) 0

/-- Total languages with any POT marker (both + onlyPot). -/
def languagesWithPot : Nat :=
  areaData.foldl (fun acc a => acc + a.bothNecPot + a.onlyPot) 0

-- ============================================================================
-- §4. Consistency Checks
-- ============================================================================

/-- Area totals sum to the sample size. -/
theorem area_totals_sum_to_200 : areaSampleTotal = sampleSize := by native_decide

/-- Languages with any NEC marker: 121 + 10 = 131. -/
theorem nec_count : languagesWithNec = 131 := by native_decide

/-- Languages with any POT marker: 121 + 35 = 156.
    (Paper says 157 = 121 + 35 + 1; the discrepancy is in the original.) -/
theorem pot_count : languagesWithPot = 156 := by native_decide

/-- Strong deontic necessity: 60 languages. -/
theorem strong_count : countOf .strong = 60 := by native_decide

/-- Weak deontic necessity: 62 languages. -/
theorem weak_count : countOf .weak = 62 := by native_decide

/-- Neutral: 22 languages. -/
theorem neutral_count : countOf .neutral = 22 := by native_decide

/-- Indeterminate: 32 languages. -/
theorem indeterminate_count : countOf .indeterminate = 32 := by native_decide

/-- POT markers are more common than NEC markers cross-linguistically.
    @cite{narrog-2010} p. 406: 156 vs 131. -/
theorem pot_more_common_than_nec : languagesWithPot > languagesWithNec := by native_decide

end Core.Modality.DeonticNecessity
