import Linglib.Theories.Interfaces.Morphosyntax.Extraction

/-!
# Voice System
@cite{erlewine-2018}

Theory-neutral types for cross-linguistic voice system typology ---
how languages map argument roles to a privileged syntactic position
(the "pivot") via voice alternation.

Languages vary in:
- **How many voices** they have (2 in Toba Batak, 4+ in Tagalog)
- **Which roles can be promoted** to pivot (agent/patient only, or also
  locative, instrumental, benefactive, circumstantial)
- **Whether the system is symmetrical** --- in symmetrical systems (Toba
  Batak, Tagalog), no voice is morphologically or syntactically basic;
  in asymmetrical systems (English active/passive), one voice is marked

-/

namespace Interfaces

-- ============================================================================
-- S 1: Pivot Target
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
  deriving DecidableEq, Repr

/-- Coercion from `PivotTarget` to `ArgumentRole`.

    Locative, instrumental, benefactive, and circumstantial all
    collapse to `oblique` --- the distinction among obliques is a
    voice-system concern, not an extraction-morphology concern. -/
def PivotTarget.toArgumentRole : PivotTarget → ArgumentRole
  | .agent => .agent
  | .patient => .patient
  | .locative => .oblique
  | .instrumental => .oblique
  | .benefactive => .oblique
  | .circumstantial => .oblique

-- ============================================================================
-- S 2: Voice Entry
-- ============================================================================

/-- A single voice in a voice system: a name and the role it promotes. -/
structure VoiceEntry where
  /-- Name of the voice (e.g., "Actor Voice", "Patient Voice") -/
  name : String
  /-- Which argument role this voice promotes to pivot -/
  promotes : PivotTarget
  deriving DecidableEq, Repr

-- ============================================================================
-- S 3: Voice System Symmetry
-- ============================================================================

/-- Whether a voice system is symmetrical or asymmetrical.

    - **Symmetrical**: no voice is morphologically or syntactically
      basic; all voices have equal status (e.g., Tagalog, Toba Batak)
    - **Asymmetrical**: one voice (typically active) is basic/unmarked
      and the other(s) are derived (e.g., English active/passive) -/
inductive VoiceSystemSymmetry where
  | symmetrical
  | asymmetrical
  deriving DecidableEq, Repr

-- ============================================================================
-- S 4: Voice System Profile
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
-- S 5: Helpers
-- ============================================================================

/-- How many voices does this system have? -/
def VoiceSystemProfile.voiceCount (p : VoiceSystemProfile) : Nat :=
  p.voices.length

/-- Does any voice in this system promote a given role? -/
def VoiceSystemProfile.promotesRole (p : VoiceSystemProfile) (r : PivotTarget) : Prop :=
  ∃ v ∈ p.voices, v.promotes = r

instance (p : VoiceSystemProfile) (r : PivotTarget) :
    Decidable (p.promotesRole r) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Does this system distinguish among oblique pivots (locative,
    instrumental, benefactive, circumstantial)? -/
def VoiceSystemProfile.distinguishesObliques (p : VoiceSystemProfile) : Prop :=
  ∃ v ∈ p.voices,
    v.promotes = .locative ∨ v.promotes = .instrumental ∨
    v.promotes = .benefactive ∨ v.promotes = .circumstantial

instance (p : VoiceSystemProfile) : Decidable p.distinguishesObliques :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Is this a simple active/passive system (exactly agent + patient)? -/
def VoiceSystemProfile.isActivePassive (p : VoiceSystemProfile) : Prop :=
  p.voiceCount = 2 ∧
  p.promotesRole .agent ∧
  p.promotesRole .patient

instance (p : VoiceSystemProfile) : Decidable p.isActivePassive :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set of roles promotable to pivot in this system. -/
def VoiceSystemProfile.promotableRoles (p : VoiceSystemProfile) : List PivotTarget :=
  p.voices.map (·.promotes) |>.eraseDups

end Interfaces
