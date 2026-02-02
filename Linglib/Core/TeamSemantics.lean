/-
# Team Semantics Infrastructure

Team semantics evaluates formulas relative to **sets** of evaluation points
(teams) rather than single points. This module provides the core infrastructure.

## Background

Team semantics originated in logic (Hodges 1997, Väänänen 2007) and has been
applied to linguistics for:
- **Inquisitive Semantics**: Questions as issues (sets of info states)
- **Free Choice**: Aloni's BSML derives FC via non-emptiness constraints
- **Modified Numerals**: First-order team semantics
- **Exceptional Scope**: Indefinites with team-based evaluation

## Key Concepts

- `Team W`: A set of worlds (characteristic function `W -> Bool`)
- `support`: Team supports formula (all worlds satisfy it)
- `antiSupport`: Team anti-supports formula (all worlds falsify it)
- `SupportRelation`: Bilateral support structure (support + anti-support)

## Architecture

This module provides general infrastructure. Specific applications:
- `Montague/Question/Inquisitive.lean`: Inquisitive semantics for questions
- `Comparisons/FreeChoice/Aloni2022.lean`: BSML for free choice

## References

- Hodges, W. (1997). Compositional semantics for a language of imperfect information.
- Väänänen, J. (2007). Dependence Logic. Cambridge University Press.
- Ciardelli, Groenendijk & Roelofsen (2018). Inquisitive Semantics. Oxford UP.
- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
-/

import Mathlib.Data.Set.Basic

namespace Core.TeamSemantics

-- ============================================================================
-- PART 1: Teams (Sets of Worlds)
-- ============================================================================

/--
A team is a set of worlds, represented as a characteristic function.

In team semantics, formulas are evaluated relative to teams rather than
single worlds. A team represents an information state: the set of worlds
compatible with current information.

This is equivalent to `InfoState` in Inquisitive Semantics.
-/
abbrev Team (W : Type*) := W -> Bool

/-- The empty team (inconsistent information state) -/
def Team.empty {W : Type*} : Team W := fun _ => false

/-- The full team (no information / total ignorance) -/
def Team.full {W : Type*} : Team W := fun _ => true

/-- Singleton team containing just one world -/
def Team.singleton {W : Type*} [DecidableEq W] (w : W) : Team W := fun w' => w == w'

/-- Check if a team is empty (no worlds) -/
def Team.isEmpty {W : Type*} (t : Team W) (worlds : List W) : Bool :=
  !worlds.any t

/-- Check if a team is non-empty -/
def Team.isNonEmpty {W : Type*} (t : Team W) (worlds : List W) : Bool :=
  worlds.any t

/-- Team membership: world w is in team t -/
def Team.mem {W : Type*} (t : Team W) (w : W) : Bool := t w

/-- Team subset: t ⊆ t' -/
def Team.subset {W : Type*} (t t' : Team W) (worlds : List W) : Bool :=
  worlds.all fun w => !t w || t' w

/-- Team intersection: t ∩ t' -/
def Team.inter {W : Type*} (t t' : Team W) : Team W :=
  fun w => t w && t' w

/-- Team union: t ∪ t' -/
def Team.union {W : Type*} (t t' : Team W) : Team W :=
  fun w => t w || t' w

/-- Team complement: W \ t -/
def Team.compl {W : Type*} (t : Team W) : Team W :=
  fun w => !t w

/-- Team difference: t \ t' -/
def Team.diff {W : Type*} (t t' : Team W) : Team W :=
  fun w => t w && !t' w

/-- Filter team by predicate -/
def Team.filter {W : Type*} (t : Team W) (p : W -> Bool) : Team W :=
  fun w => t w && p w

/-- All worlds in team satisfy predicate -/
def Team.all {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.all fun w => !t w || p w

/-- Some world in team satisfies predicate -/
def Team.any {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.any fun w => t w && p w

/-- Convert team to list of worlds -/
def Team.toList {W : Type*} (t : Team W) (worlds : List W) : List W :=
  worlds.filter t

/-- Team from list of worlds -/
def Team.ofList {W : Type*} [DecidableEq W] (ws : List W) : Team W :=
  fun w => ws.contains w

/-- Team equality (extensional, given finite world list) -/
def Team.beq {W : Type*} (t t' : Team W) (worlds : List W) : Bool :=
  worlds.all fun w => t w == t' w

-- ============================================================================
-- PART 2: Support Relations
-- ============================================================================

/--
A proposition in team semantics: evaluated relative to teams.

Unlike classical propositions (W -> Bool), team propositions are
(Team W -> Bool). The key insight is that team propositions can
express properties that single-world propositions cannot, like
"the team is non-empty" or "all worlds in the team agree on p".
-/
abbrev TeamProp (W : Type*) := Team W -> Bool

/--
Lift a classical proposition to a team proposition.

A team supports p iff all worlds in the team satisfy p.
This is the "flatness" or "downward closure" property:
if t ⊨ p and t' ⊆ t, then t' ⊨ p.
-/
def liftProp {W : Type*} (p : W -> Bool) (worlds : List W) : TeamProp W :=
  fun t => t.all p worlds

/--
The non-emptiness atom (NE): team is non-empty.

This is Aloni's key innovation for free choice. NE is NOT flat:
∅ does NOT support NE, but all non-empty subsets do.
-/
def ne {W : Type*} (worlds : List W) : TeamProp W :=
  fun t => t.isNonEmpty worlds

/--
Support relation: team t supports proposition p.

For classical propositions lifted to teams:
  t ⊨ p iff ∀w ∈ t, p(w)

The empty team supports everything (ex falso quodlibet).
-/
def supports {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  t.all p worlds

/--
Anti-support relation: team t anti-supports proposition p.

For classical propositions:
  t ⊣ p iff ∀w ∈ t, ¬p(w)

The empty team anti-supports everything.
-/
def antiSupports {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  t.all (fun w => !p w) worlds

-- ============================================================================
-- PART 3: Bilateral Support Structure
-- ============================================================================

/--
A bilateral formula has both support and anti-support conditions.

This is the foundation for bilateral semantics (Aloni 2022, cf. BUS).
The key property is that negation swaps support and anti-support,
giving us double negation elimination.

In BSML:
- Atomic p: t ⊨⁺ p iff ∀w ∈ t, p(w); t ⊨⁻ p iff ∀w ∈ t, ¬p(w)
- Negation: t ⊨⁺ ¬φ iff t ⊨⁻ φ; t ⊨⁻ ¬φ iff t ⊨⁺ φ
-/
structure BilateralFormula (W : Type*) where
  /-- Positive support: when does team support the formula? -/
  support : Team W -> List W -> Bool
  /-- Negative support: when does team anti-support the formula? -/
  antiSupport : Team W -> List W -> Bool

/-- Atomic formula from a classical proposition -/
def BilateralFormula.atom {W : Type*} (p : W -> Bool) : BilateralFormula W where
  support := fun t worlds => supports t p worlds
  antiSupport := fun t worlds => antiSupports t p worlds

/-- Negation: swap support and anti-support -/
def BilateralFormula.neg {W : Type*} (φ : BilateralFormula W) : BilateralFormula W where
  support := φ.antiSupport
  antiSupport := φ.support

/-- Double negation elimination (definitional!) -/
@[simp]
theorem BilateralFormula.neg_neg {W : Type*} (φ : BilateralFormula W) :
    φ.neg.neg = φ := rfl

/-- Conjunction: both must be supported -/
def BilateralFormula.conj {W : Type*} (φ ψ : BilateralFormula W) : BilateralFormula W where
  support := fun t worlds => φ.support t worlds && ψ.support t worlds
  antiSupport := fun t worlds => φ.antiSupport t worlds || ψ.antiSupport t worlds

/-- Standard disjunction: at least one supported -/
def BilateralFormula.disjStd {W : Type*} (φ ψ : BilateralFormula W) : BilateralFormula W where
  support := fun t worlds => φ.support t worlds || ψ.support t worlds
  antiSupport := fun t worlds => φ.antiSupport t worlds && ψ.antiSupport t worlds

/-- Non-emptiness atom -/
def BilateralFormula.NE {W : Type*} : BilateralFormula W where
  support := fun t worlds => t.isNonEmpty worlds
  antiSupport := fun t worlds => t.isEmpty worlds

-- ============================================================================
-- PART 4: Flatness and Persistence
-- ============================================================================

/--
A team proposition is flat (downward closed) if:
whenever t ⊨ φ and t' ⊆ t, then t' ⊨ φ.

Classical propositions lifted to teams are always flat.
NE is NOT flat (the key to free choice).
-/
def isFlat {W : Type*} (φ : TeamProp W) (worlds : List W) : Prop :=
  ∀ t t' : Team W, t'.subset t worlds = true -> φ t = true -> φ t' = true

/--
A bilateral formula is flat if both support and anti-support are flat.
-/
def BilateralFormula.isFlat {W : Type*} (φ : BilateralFormula W) (worlds : List W) : Prop :=
  (∀ t t' : Team W, t'.subset t worlds = true -> φ.support t worlds = true ->
    φ.support t' worlds = true) ∧
  (∀ t t' : Team W, t'.subset t worlds = true -> φ.antiSupport t worlds = true ->
    φ.antiSupport t' worlds = true)

-- ============================================================================
-- PART 5: Team Partitions (for Split Disjunction)
-- ============================================================================

/--
A partition of team t into t₁ and t₂ such that t₁ ∪ t₂ = t.

This is used for Aloni's split disjunction:
  t ⊨ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ
-/
structure TeamPartition (W : Type*) where
  left : Team W
  right : Team W

/-- Check if partition covers exactly team t -/
def TeamPartition.coversExactly {W : Type*} (p : TeamPartition W) (t : Team W)
    (worlds : List W) : Bool :=
  p.left.union p.right |>.beq t worlds

/-- Generate all possible partitions of a team -/
def TeamPartition.allPartitions {W : Type*} [DecidableEq W] (t : Team W)
    (worlds : List W) : List (TeamPartition W) :=
  let members := t.toList worlds
  -- Generate all subsets as the "left" part; complement (in t) is "right"
  let rec allSubsets : List W -> List (List W)
    | [] => [[]]
    | w :: ws =>
        let withoutW := allSubsets ws
        withoutW ++ withoutW.map (w :: ·)
  (allSubsets members).map fun left =>
    let leftTeam : Team W := Team.ofList left
    let rightTeam : Team W := fun w => t w && !leftTeam w
    { left := leftTeam, right := rightTeam }

-- ============================================================================
-- PART 6: Entailment
-- ============================================================================

/--
Propositional entailment (for proofs).
-/
def Entails {W : Type*} (φ ψ : BilateralFormula W) (worlds : List W) : Prop :=
  ∀ t : Team W, φ.support t worlds = true -> ψ.support t worlds = true

notation:50 φ " ⊨ₜ " ψ => Entails φ ψ

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Core Types
- `Team W`: Set of worlds (characteristic function)
- `TeamProp W`: Team-level proposition
- `BilateralFormula W`: Formula with support and anti-support

### Team Operations
- `empty`, `full`, `singleton`: Constructors
- `inter`, `union`, `compl`, `diff`: Set operations
- `subset`, `isEmpty`, `isNonEmpty`: Predicates
- `all`, `any`, `filter`: Higher-order operations

### Support Relations
- `supports`: Team supports classical proposition
- `antiSupports`: Team anti-supports classical proposition
- `liftProp`: Lift classical to team proposition
- `ne`: Non-emptiness atom (NOT flat!)

### Bilateral Operations
- `atom`: Lift classical proposition
- `neg`: Negation (swap support/anti-support)
- `conj`, `disjStd`: Conjunction, standard disjunction
- `NE`: Non-emptiness as bilateral formula

### Properties
- `isFlat`: Downward closure property
- `TeamPartition`: For split disjunction
- `Entails`: Team-semantic entailment

## Usage

This infrastructure is used by:
- Inquisitive Semantics (questions as issues)
- BSML (Aloni 2022) for free choice
- Other team-based linguistic analyses
-/

end Core.TeamSemantics
