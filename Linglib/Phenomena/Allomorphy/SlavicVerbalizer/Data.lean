/-!
# Slavic Verbalizer (VBLZ) — Empirical Data @cite{stojkovic-2026}

Theory-neutral empirical data for the Slavic verbalizer suffix used in
secondary imperfectivisation. Stojković (2026) documents a three-way
surface alternation across Slavic:

| Group        | INF stem VC | Languages                                  |
|--------------|-------------|--------------------------------------------|
| [ov] group   | [ov]        | Polish, Czech, Slovak, U/L Sorbian,...    |
| [ov]/[ev]    | [ov]∼[ev]   | BCMS, Slovenian, Russian,...              |
| [uv] group   | [uv]        | Ukrainian, Lemko Rusyn, Bulgarian, Maced.  |

All groups share the present-stem vowel [u] (before /-je-/). The
variation is confined to the infinitive stem (before /-a-/).
-/

namespace Phenomena.Allomorphy.SlavicVerbalizer.Data

-- ============================================================================
-- § 1: Languages and Groups
-- ============================================================================

/-- Representative Slavic languages exhibiting secondary imperfectivisation. -/
inductive SlavicLang where
  | russian
  | polish
  | czech
  | upperSorbian
  | bcms              -- Bosnian/Croatian/Montenegrin/Serbian
  | slovenian
  | slovak
  | lowerSorbian
  | ukrainian
  | lemkoRusyn
  | bulgarian
  | macedonian
  deriving DecidableEq, BEq, Repr

/-- The three surface-form groups for the VBLZ in the infinitive stem.
    Stojković (2026), Table 3. -/
inductive VBLZGroup where
  /-- Always [ov], regardless of preceding consonant. -/
  | ovGroup
  /-- [ov] after non-palatals, [ev] after palatals. -/
  | ovEvGroup
  /-- Always [uv], regardless of preceding consonant. -/
  | uvGroup
  deriving DecidableEq, BEq, Repr

/-- Surface VC forms attested in the infinitive stem for each group. -/
def VBLZGroup.forms : VBLZGroup → List String
  | .ovGroup   => ["ov"]
  | .ovEvGroup => ["ov", "ev"]
  | .uvGroup   => ["uv"]

/-- Group membership for each language. -/
def SlavicLang.vblzGroup : SlavicLang → VBLZGroup
  | .polish | .czech | .slovak | .upperSorbian | .lowerSorbian => .ovGroup
  | .russian | .bcms | .slovenian                              => .ovEvGroup
  | .ukrainian | .lemkoRusyn | .bulgarian | .macedonian        => .uvGroup

-- ============================================================================
-- § 2: Concrete Data
-- ============================================================================

/-- A VBLZ datum: language, infinitive-stem VC, present-stem V.
    The present stem V is the vowel that surfaces before the present-tense
    suffix /-je-/; the infinitive stem VC is before /-a-/ (thematic). -/
structure VBLZDatum where
  lang : SlavicLang
  infStem : String    -- infinitive-stem VC (e.g. "ov", "ev", "uv")
  presStem : String   -- present-stem V (always "u")
  deriving DecidableEq, BEq, Repr

/-- Polish: kup-ov-a-ć / kup-uj-e 'buy'. -/
def polishVBLZ : VBLZDatum := ⟨.polish, "ov", "u"⟩

/-- Czech: kup-ov-a-t / kup-uj-e 'buy'. -/
def czechVBLZ : VBLZDatum := ⟨.czech, "ov", "u"⟩

/-- Slovak: kup-ov-a-ť / kup-uj-e 'buy'. -/
def slovakVBLZ : VBLZDatum := ⟨.slovak, "ov", "u"⟩

/-- Upper Sorbian: kup-ov-a-ć / kup-uj-e 'buy'. -/
def upperSorbianVBLZ : VBLZDatum := ⟨.upperSorbian, "ov", "u"⟩

/-- Lower Sorbian: kup-ov-a-ś / kup-uj-o 'buy'. -/
def lowerSorbianVBLZ : VBLZDatum := ⟨.lowerSorbian, "ov", "u"⟩

/-- Russian: kup-ov-a-t' / kup-uj-et 'buy' (non-palatal base).
    After palatals: torg-ev-a-t' / torg-uj-et 'trade'. -/
def russianVBLZ : VBLZDatum := ⟨.russian, "ov", "u"⟩

/-- BCMS: kup-ov-a-ti / kup-uj-e 'buy' (non-palatal).
    After palatals: poštov-ev-a-ti (palatal assimilation). -/
def bcmsVBLZ : VBLZDatum := ⟨.bcms, "ov", "u"⟩

/-- Slovenian: kup-ov-a-ti / kup-uj-e 'buy' (non-palatal).
    After palatals: dež-ev-a-ti 'rain'. -/
def slovenianVBLZ : VBLZDatum := ⟨.slovenian, "ov", "u"⟩

/-- Ukrainian: kup-uv-a-ty / kup-uj-e 'buy'. -/
def ukrainianVBLZ : VBLZDatum := ⟨.ukrainian, "uv", "u"⟩

/-- Lemko Rusyn: ris-uv-a-ty / ris-uj-e 'draw'. -/
def lemkoRusynVBLZ : VBLZDatum := ⟨.lemkoRusyn, "uv", "u"⟩

/-- Bulgarian: kup-uv-a-m / kup-uv-a-m 'buy'. -/
def bulgarianVBLZ : VBLZDatum := ⟨.bulgarian, "uv", "u"⟩

/-- Macedonian: kup-uv-a / kup-uv-a 'buy'. -/
def macedonianVBLZ : VBLZDatum := ⟨.macedonian, "uv", "u"⟩

/-- All VBLZ data points. -/
def allData : List VBLZDatum :=
  [polishVBLZ, czechVBLZ, slovakVBLZ, upperSorbianVBLZ, lowerSorbianVBLZ,
   russianVBLZ, bcmsVBLZ, slovenianVBLZ,
   ukrainianVBLZ, lemkoRusynVBLZ, bulgarianVBLZ, macedonianVBLZ]

theorem allData_length : allData.length = 12 := rfl

-- ============================================================================
-- § 3: Universals
-- ============================================================================

/-- The present-stem vowel is universally [u] across all three groups
    (before the present-tense suffix /-je-/). This uniformity is the
    starting point of Stojković's analysis: the variation is confined
    to the infinitive stem. -/
theorem presentStemUniversal :
    allData.all (fun d => d.presStem == "u") = true := rfl

/-- Each datum's infinitive stem is consistent with its language's group. -/
theorem infStem_matches_group :
    allData.all (fun d => d.lang.vblzGroup.forms.contains d.infStem) = true := rfl

end Phenomena.Allomorphy.SlavicVerbalizer.Data
