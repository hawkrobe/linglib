/-!
# Particle Verb Constructions — Empirical Data

Theory-neutral data on English verb-particle constructions (VPCs / PVCs),
including particle shift alternation and its constraints.

## Phenomena covered

1. **Particle shift alternation**: continuous ("lifted up Hsu") vs split ("lifted Hsu up")
2. **Pronoun constraint**: pronouns force split order (*"lifted up her" vs "lifted her up")
3. **Heavy NP constraint**: heavy NPs force continuous order ("lifted up the box that was on the table")

## References

- Johnson, K. (1991). Object positions. NLLT 9(4):577–636.
- den Dikken, M. (1995). Particles: On the Syntax of Verb-Particle, Triadic, and
  Causative Constructions. OUP.
-/

namespace Phenomena.Constructions.ParticleVerbs

/-! ## Particle verb inventory -/

/-- A particle verb entry: verb + particle + gloss. -/
structure ParticleVerb where
  verb     : String
  particle : String
  meaning  : String
  deriving Repr, DecidableEq, BEq

def pick_up   : ParticleVerb := ⟨"pick",  "up",  "lift / collect"⟩
def lift_up   : ParticleVerb := ⟨"lift",  "up",  "raise"⟩
def throw_out : ParticleVerb := ⟨"throw", "out", "discard"⟩
def put_down  : ParticleVerb := ⟨"put",   "down", "set down"⟩
def call_off  : ParticleVerb := ⟨"call",  "off", "cancel"⟩

def inventory : List ParticleVerb :=
  [pick_up, lift_up, throw_out, put_down, call_off]

/-! ## Particle shift alternation -/

/-- Word order of verb, particle, and direct object. -/
inductive PVCOrder where
  | continuous  -- V Prt DP  ("lifted up the box")
  | split       -- V DP Prt  ("lifted the box up")
  deriving Repr, DecidableEq, BEq

/-- DP weight category, relevant to particle shift constraints. -/
inductive DPWeight where
  | pronoun     -- "her", "it"
  | light       -- "the box", "Hsu"
  | heavy       -- "the box that was sitting on the table"
  deriving Repr, DecidableEq, BEq

/-- A single particle shift datum: a ⟨verb, order, DP weight, judgment⟩ tuple. -/
structure ParticleShiftDatum where
  pv       : ParticleVerb
  order    : PVCOrder
  dpWeight : DPWeight
  judgment : Bool          -- true = grammatical
  sentence : String
  deriving Repr, BEq

/-! ## Core particle shift data -/

/-- Pronouns force split order. -/
def pronoun_split : ParticleShiftDatum :=
  { pv := lift_up, order := .split, dpWeight := .pronoun
  , judgment := true
  , sentence := "lifted her up" }

def pronoun_continuous : ParticleShiftDatum :=
  { pv := lift_up, order := .continuous, dpWeight := .pronoun
  , judgment := false
  , sentence := "*lifted up her" }

/-- Light NPs allow both orders. -/
def light_split : ParticleShiftDatum :=
  { pv := lift_up, order := .split, dpWeight := .light
  , judgment := true
  , sentence := "lifted the box up" }

def light_continuous : ParticleShiftDatum :=
  { pv := lift_up, order := .continuous, dpWeight := .light
  , judgment := true
  , sentence := "lifted up the box" }

/-- Heavy NPs prefer continuous order. -/
def heavy_continuous : ParticleShiftDatum :=
  { pv := lift_up, order := .continuous, dpWeight := .heavy
  , judgment := true
  , sentence := "lifted up the box that was sitting on the table" }

def heavy_split : ParticleShiftDatum :=
  { pv := lift_up, order := .split, dpWeight := .heavy
  , judgment := false
  , sentence := "?lifted the box that was sitting on the table up" }

def shiftData : List ParticleShiftDatum :=
  [pronoun_split, pronoun_continuous, light_split, light_continuous,
   heavy_continuous, heavy_split]

/-! ## Verification theorems -/

/-- Pronouns force split: split OK, continuous bad. -/
theorem pronoun_forces_split :
    pronoun_split.judgment = true ∧ pronoun_continuous.judgment = false := by
  exact ⟨rfl, rfl⟩

/-- Light NPs allow both orders. -/
theorem light_allows_both :
    light_split.judgment = true ∧ light_continuous.judgment = true := by
  exact ⟨rfl, rfl⟩

/-- Heavy NPs disprefer split. -/
theorem heavy_disprefers_split :
    heavy_continuous.judgment = true ∧ heavy_split.judgment = false := by
  exact ⟨rfl, rfl⟩

end Phenomena.Constructions.ParticleVerbs
