import Mathlib.Data.Set.Basic

/-!
# Team Semantics Infrastructure

Team semantics evaluates formulas relative to sets of evaluation points
(teams) rather than single points. This module provides the core infrastructure.

## Background

Team semantics originated in logic (Hodges 1997, Väänänen 2007) and has been
applied to linguistics for:
- Inquisitive Semantics: questions as issues (sets of info states)
- Free Choice: Aloni's BSML derives FC via non-emptiness constraints
- Modified Numerals: first-order team semantics
- Exceptional Scope: indefinites with team-based evaluation

## Key Concepts

- `Team W`: A set of worlds (characteristic function `W -> Bool`)
- Team operations: empty, full, singleton, subset, union, intersection, etc.

## Architecture

This module provides general infrastructure. Specific applications:
- `Systems/BSML/`: Bilateral State-based Modal Logic (Aloni 2022)
- `Questions/Inquisitive.lean`: Inquisitive semantics for questions

## References

- Hodges, W. (1997). Compositional semantics for a language of imperfect information.
- Väänänen, J. (2007). Dependence Logic. Cambridge University Press.
- Ciardelli, Groenendijk & Roelofsen (2018). Inquisitive Semantics. Oxford UP.
- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
-/

namespace Semantics.Dynamic.TeamSemantics

/--
A team is a set of worlds, represented as a characteristic function.

In team semantics, formulas are evaluated relative to teams rather than
single worlds. A team represents an information state: the set of worlds
compatible with current information.

This is equivalent to `InfoState` in Inquisitive Semantics.
-/
abbrev Team (W : Type*) := W -> Bool

/-- The empty team (inconsistent information state) -/
def Team.empty {W : Type*} : Team W := λ _ => false

/-- The full team (no information / total ignorance) -/
def Team.full {W : Type*} : Team W := λ _ => true

/-- Singleton team containing just one world -/
def Team.singleton {W : Type*} [DecidableEq W] (w : W) : Team W := λ w' => w == w'

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
  worlds.all λ w => !t w || t' w

/-- Team intersection: t ∩ t' -/
def Team.inter {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w && t' w

/-- Team union: t ∪ t' -/
def Team.union {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w || t' w

/-- Team complement: W \ t -/
def Team.compl {W : Type*} (t : Team W) : Team W :=
  λ w => !t w

/-- Team difference: t \ t' -/
def Team.diff {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w && !t' w

/-- Filter team by predicate -/
def Team.filter {W : Type*} (t : Team W) (p : W -> Bool) : Team W :=
  λ w => t w && p w

/-- All worlds in team satisfy predicate -/
def Team.all {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !t w || p w

/-- Some world in team satisfies predicate -/
def Team.any {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.any λ w => t w && p w

/-- Convert team to list of worlds -/
def Team.toList {W : Type*} (t : Team W) (worlds : List W) : List W :=
  worlds.filter t

/-- Team from list of worlds -/
def Team.ofList {W : Type*} [DecidableEq W] (ws : List W) : Team W :=
  λ w => ws.contains w

/-- Team equality (extensional, given finite world list) -/
def Team.beq {W : Type*} (t t' : Team W) (worlds : List W) : Bool :=
  worlds.all λ w => t w == t' w

end Semantics.Dynamic.TeamSemantics
