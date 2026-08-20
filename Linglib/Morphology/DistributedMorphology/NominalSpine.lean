import Mathlib.Order.WithBot
import Mathlib.Tactic.DeriveFintype

/-!
# The nominal spine

The extended nominal projection as a spine order — √ROOT < n < Poss <
Num < D — with the positions of the nominal domain classified by where
they attach. Locality to n is then geometry: a position is within nP
exactly when its attachment site is at or below n, which is what
[adamson-2024]'s Gender Locality Hypothesis (gender features on n are
valued only within nP) quantifies over. The inalienable/alienable
possession contrast is a contrast of attachment sites — Spec,nP versus
Spec,PossP ([alexiadou-2003]; [myler-2016]) — and low versus high
number likewise ([adamson-2024]).

## Main definitions

* `SpineHead` — the heads of the extended nominal projection, linearly
  ordered by height
* `NominalPosition`, `NominalPosition.attachmentSite`, `isWithinNP` —
  the positions of the nominal domain and their spine geometry
* `PossessionType`, `NumberPosition` — the possession and number
  contrasts as attachment contrasts
* `ExternalFeature` — features attached above nP, clausal ones outside
  the nominal spine altogether (`⊤`)
* `PossessionGenderMechanism` — possessee gender vs inherited gender

## Main statements

* `ExternalFeature.not_withinNP` — no external feature attaches within
  nP

## Implementation notes

`PossessionType.possessorPosition .inalienable = .specN` is a
contemporary DM gloss: [alexiadou-2003] (and
[kampanarou-alexiadou-2026]'s rendering of it) places the inalienable
possessor as the complement of NP rather than Spec,nP. Downstream
consumers (Tseltalan possessor extraction in [aissen-polian-2025],
Icelandic *hafa*/*eiga* in [myler-2016]) recover the right empirical
predictions either way, but not every formulation carves the contrast
at exactly Spec,nP vs Spec,PossP — Michelioudakis et al. collapse both
possessor types into Spec,nP (as [kampanarou-alexiadou-2026] notes),
which this substrate does not represent.

## References

* [A. Alexiadou, *Some notes on the structure of alienable and
  inalienable possessors*][alexiadou-2003]
* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
* [N. Myler, *Building and interpreting possession sentences*][myler-2016]
-/

namespace DistributedMorphology

/-! ### The nominal spine -/

/-- The heads of the extended nominal projection, in spine order:
√ROOT < n < Poss < Num < D ([adamson-2024]; the Poss layer after
[alexiadou-2003], [myler-2016]). -/
inductive SpineHead where
  | root
  | n
  | poss
  | num
  | d
  deriving DecidableEq, Repr, Fintype

/-- The height of a head on the spine. -/
def SpineHead.height : SpineHead → Nat
  | .root => 0
  | .n    => 1
  | .poss => 2
  | .num  => 3
  | .d    => 4

instance : LinearOrder SpineHead :=
  LinearOrder.lift' SpineHead.height (by decide)

/-! ### Positions and their attachment sites -/

/-- Structural positions within and around the nominal phrase:

    [DP D [NumP Num [PossP DP Poss [nP DP [n √ROOT n]]]]]

heads of the spine together with the two possessor specifiers. -/
inductive NominalPosition where
  | root         -- √ROOT: the acategorial root itself
  | nHead        -- n: the categorizing head bearing gender features
  | specN        -- Spec,nP: inalienable possessor position
  | poss         -- Poss head: alienable possession head
  | specPoss     -- Spec,PossP: alienable possessor position
  | num          -- Num head: number (high/inflectional)
  | d            -- D head: definiteness
  deriving DecidableEq, Repr, Fintype

/-- Where each position attaches on the spine: a specifier attaches at
its head's projection. -/
def NominalPosition.attachmentSite : NominalPosition → SpineHead
  | .root     => .root
  | .nHead    => .n
  | .specN    => .n
  | .poss     => .poss
  | .specPoss => .poss
  | .num      => .num
  | .d        => .d

/-- Within-nP is spine geometry: the position attaches at or below n. -/
def NominalPosition.isWithinNP (p : NominalPosition) : Bool :=
  decide (p.attachmentSite ≤ SpineHead.n)

/-- The Gender Locality Hypothesis ([adamson-2024]): gender features on
n are valued only within nP, so a position can condition gender exactly
when its attachment site is at or below n. -/
def genderLocalityHypothesis (pos : NominalPosition) : Bool :=
  pos.isWithinNP

/-! ### Possession -/

/-- Two types of possession, distinguished by the possessor's
attachment site ([adamson-2024], following [myler-2016];
[alexiadou-2003]). The inalienable possessor sits in Spec,nP, licensed
by an n bearing the selectional feature {D} (`Categorizer.Head.selectsD`)
and interpreted by a part-whole relation; the alienable possessor sits
in Spec,PossP, mediated by a Poss head and often extra morphology
(Teop *te*). -/
inductive PossessionType where
  | inalienable  -- possessor in Spec,nP (local to n)
  | alienable    -- possessor in Spec,PossP (nonlocal to n)
  deriving DecidableEq, Repr, Fintype

/-- The possessor's position. -/
def PossessionType.possessorPosition : PossessionType → NominalPosition
  | .inalienable => .specN
  | .alienable   => .specPoss

/-- Whether this possession type can affect gender assignment: the GLH
applied to the possessor's attachment site. -/
def PossessionType.canAffectGender (pt : PossessionType) : Bool :=
  genderLocalityHypothesis pt.possessorPosition

/-! ### Number -/

/-- Number features appear in two positions ([adamson-2024]): low
number on n is derivational and can interact with gender (Standard
Italian *-a* plurals, Tunisian Arabic collectives); high number on Num
is inflectional and cannot. -/
inductive NumberPosition where
  | onN    -- low/derivational number (within nP)
  | onNum  -- high/inflectional number (on Num, outside nP)
  deriving DecidableEq, Repr, Fintype

/-- The position a number feature occupies. -/
def NumberPosition.toNominalPosition : NumberPosition → NominalPosition
  | .onN   => .nHead
  | .onNum => .num

/-! ### External features -/

/-- Features attached outside nP, which the GLH bars from conditioning
gender ([adamson-2024]): case and definiteness in the nominal
periphery, tense, aspect, and voice on the clausal spine. -/
inductive ExternalFeature where
  | case
  | definiteness
  | tense
  | aspect
  | voice
  deriving DecidableEq, Repr, Fintype

/-- Where an external feature attaches: case and definiteness at D,
the clausal features outside the nominal spine altogether. -/
def ExternalFeature.attachmentSite : ExternalFeature → WithTop SpineHead
  | .case         => some .d
  | .definiteness => some .d
  | .tense        => ⊤
  | .aspect       => ⊤
  | .voice        => ⊤

/-- No external feature attaches within nP. -/
theorem ExternalFeature.not_withinNP (f : ExternalFeature) :
    ¬ f.attachmentSite ≤ (SpineHead.n : WithTop SpineHead) := by
  cases f <;> decide

/-! ### Possession–gender mechanisms -/

/-- The two mechanisms by which inalienable possession can affect
gender ([adamson-2024]): under **possessee gender** the noun's gender
is determined by whether it has an iPossessor — the licensing n itself
bears the gender feature (Teop, Jarawara) — while under **inherited
gender** the noun's gender is the iPossessor's, an unvalued probe on n
valued by Agree (Yanyuwa, Coastal Marind). Both mechanisms place the
possessor in Spec,nP, within the GLH's reach. -/
inductive PossessionGenderMechanism where
  | possesseeGender   -- gender determined by having an iPossessor
  | inheritedGender   -- gender copied from the iPossessor via Agree
  deriving DecidableEq, Repr, Fintype

/-- Both mechanisms involve an iPossessor in Spec,nP. -/
def PossessionGenderMechanism.possessorPosition :
    PossessionGenderMechanism → NominalPosition
  | .possesseeGender => .specN
  | .inheritedGender => .specN

end DistributedMorphology
