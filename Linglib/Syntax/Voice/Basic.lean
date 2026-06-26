import Linglib.Syntax.Extraction

/-!
# Voice system typology

[erlewine-2018]

Theory-neutral types for cross-linguistic voice-system typology — how languages
map argument roles to a privileged syntactic position (the "pivot") via voice
alternation. Per-language data are bare `def voices : List VoiceEntry` and
`def symmetry : VoiceSystemSymmetry` in `Fragments/<Lang>/…`; the queries below
operate on the voice list.

## Main definitions

* `PivotTarget` : the role a voice promotes to pivot (finer than `ArgumentRole`).
* `VoiceEntry`, `VoiceSystemSymmetry` : one voice (name + promoted role); system symmetry.
* `Voice.voiceCount` / `promotesRole` / `distinguishesObliques` / `isActivePassive`
  / `promotableRoles` : queries over a language's `List VoiceEntry`.
-/

namespace Voice

/-! ### Pivot target -/

/-- Which argument role a voice promotes to pivot. Finer-grained than
    `Extraction.ArgumentRole`: Philippine-type systems distinguish locative,
    instrumental, benefactive, and circumstantial pivots, all collapsing to oblique. -/
inductive PivotTarget where
  | agent
  | patient
  | locative
  | instrumental
  | benefactive
  | circumstantial
  deriving DecidableEq, Repr

/-- Coarsen a `PivotTarget` to a `Extraction.ArgumentRole` (obliques collapse). -/
def PivotTarget.toArgumentRole : PivotTarget → Extraction.ArgumentRole
  | .agent => .agent
  | .patient => .patient
  | .locative => .oblique
  | .instrumental => .oblique
  | .benefactive => .oblique
  | .circumstantial => .oblique

/-! ### Voice entry and symmetry -/

/-- A single voice in a voice system: a name and the role it promotes. -/
structure VoiceEntry where
  /-- Name of the voice (e.g., "Actor Voice", "Patient Voice"). -/
  name : String
  /-- Which argument role this voice promotes to pivot. -/
  promotes : PivotTarget
  deriving DecidableEq, Repr

/-- Whether a voice system is symmetrical (no basic voice, e.g. Tagalog) or
    asymmetrical (one basic voice, e.g. English active/passive). -/
inductive VoiceSystemSymmetry where
  | symmetrical
  | asymmetrical
  deriving DecidableEq, Repr

/-! ### Queries over a voice inventory -/

/-- How many voices a system has. -/
def voiceCount (voices : List VoiceEntry) : Nat := voices.length

/-- Does any voice promote a given role? -/
def promotesRole (voices : List VoiceEntry) (r : PivotTarget) : Prop :=
  ∃ v ∈ voices, v.promotes = r

instance (voices : List VoiceEntry) (r : PivotTarget) :
    Decidable (promotesRole voices r) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Does the system distinguish among oblique pivots
    (locative, instrumental, benefactive, circumstantial)? -/
def distinguishesObliques (voices : List VoiceEntry) : Prop :=
  ∃ v ∈ voices,
    v.promotes = .locative ∨ v.promotes = .instrumental ∨
    v.promotes = .benefactive ∨ v.promotes = .circumstantial

instance (voices : List VoiceEntry) : Decidable (distinguishesObliques voices) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A simple active/passive system: exactly agent + patient. -/
def isActivePassive (voices : List VoiceEntry) : Prop :=
  voiceCount voices = 2 ∧ promotesRole voices .agent ∧ promotesRole voices .patient

instance (voices : List VoiceEntry) : Decidable (isActivePassive voices) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The roles promotable to pivot in a system. -/
def promotableRoles (voices : List VoiceEntry) : List PivotTarget :=
  voices.map (·.promotes) |>.eraseDups

end Voice
