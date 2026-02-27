import Linglib.Core.Interfaces.ExtractionMorphology

/-!
# Voice System Interface

Theory-neutral interface for cross-linguistic voice system typology —
how languages map argument roles to a privileged syntactic position
(the "pivot") via voice alternation.

Languages vary in:
- **How many voices** they have (2 in Toba Batak, 4+ in Tagalog)
- **Which roles can be promoted** to pivot (agent/patient only, or also
  locative, instrumental, benefactive, circumstantial)
- **Whether the system is symmetrical** — in symmetrical systems (Toba
  Batak, Tagalog), no voice is morphologically or syntactically basic;
  in asymmetrical systems (English active/passive), one voice is marked

This interface captures the *alignment* dimension of voice systems:
which argument roles can be promoted, and is the system symmetrical?
It complements `ExtractionMorphology` (which captures *how* extraction
is marked) and `Minimalism.VoiceFlavor` (which captures the *semantic
contribution* of the voice head).

## References

- Erlewine, M. Y. (2018). Extraction and licensing in Toba Batak.
  Language 94(3): 662–697.
- Foley, W. A. (2008). The place of Philippine languages in a
  typology of voice systems. In P. K. Austin & S. Musgrave (eds.),
  Voice and Grammatical Relations in Austronesian Languages.
-/

namespace Interfaces

-- ============================================================================
-- § 1: Pivot Target
-- ============================================================================

/-- Which argument role can be promoted to pivot in a given voice.

    Finer-grained than `ArgumentRole`: Philippine-type systems
    distinguish locative, instrumental, benefactive, and circumstantial
    pivots, all of which collapse to `ArgumentRole.oblique`. -/
inductive PivotTarget where
  | agent
  | patient
  | locative
  | instrumental
  | benefactive
  | circumstantial
  deriving DecidableEq, BEq, Repr

/-- Coercion from `PivotTarget` to `ArgumentRole`.

    Locative, instrumental, benefactive, and circumstantial all
    collapse to `oblique` — the distinction among obliques is a
    voice-system concern, not an extraction-morphology concern. -/
def PivotTarget.toArgumentRole : PivotTarget → ArgumentRole
  | .agent => .agent
  | .patient => .patient
  | .locative => .oblique
  | .instrumental => .oblique
  | .benefactive => .oblique
  | .circumstantial => .oblique

-- ============================================================================
-- § 2: Voice Entry
-- ============================================================================

/-- A single voice in a voice system: a name and the role it promotes. -/
structure VoiceEntry where
  /-- Name of the voice (e.g., "Actor Voice", "Patient Voice") -/
  name : String
  /-- Which argument role this voice promotes to pivot -/
  promotes : PivotTarget
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: Voice System Symmetry
-- ============================================================================

/-- Whether a voice system is symmetrical or asymmetrical.

    - **Symmetrical**: no voice is morphologically or syntactically
      basic; all voices have equal status (e.g., Tagalog, Toba Batak)
    - **Asymmetrical**: one voice (typically active) is basic/unmarked
      and the other(s) are derived (e.g., English active/passive) -/
inductive VoiceSystemSymmetry where
  | symmetrical
  | asymmetrical
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: Voice System Profile
-- ============================================================================

/-- A language's voice system profile: its inventory of voices,
    symmetry type, and descriptive notes. -/
structure VoiceSystemProfile where
  /-- Language name -/
  language : String
  /-- The voices in the system -/
  voices : List VoiceEntry
  /-- Symmetrical or asymmetrical -/
  symmetry : VoiceSystemSymmetry
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- § 5: Helpers
-- ============================================================================

/-- How many voices does this system have? -/
def VoiceSystemProfile.voiceCount (p : VoiceSystemProfile) : Nat :=
  p.voices.length

/-- Does any voice in this system promote a given role? -/
def VoiceSystemProfile.promotesRole (p : VoiceSystemProfile) (r : PivotTarget) : Bool :=
  p.voices.any (·.promotes == r)

/-- Does this system distinguish among oblique pivots (locative,
    instrumental, benefactive, circumstantial)? -/
def VoiceSystemProfile.distinguishesObliques (p : VoiceSystemProfile) : Bool :=
  p.voices.any (λ v => match v.promotes with
    | .locative | .instrumental | .benefactive | .circumstantial => true
    | _ => false)

/-- Is this a simple active/passive system (exactly agent + patient)? -/
def VoiceSystemProfile.isActivePassive (p : VoiceSystemProfile) : Bool :=
  p.voiceCount == 2 &&
  p.promotesRole .agent &&
  p.promotesRole .patient

/-- The set of roles promotable to pivot in this system. -/
def VoiceSystemProfile.promotableRoles (p : VoiceSystemProfile) : List PivotTarget :=
  p.voices.map (·.promotes) |>.eraseDups

end Interfaces
