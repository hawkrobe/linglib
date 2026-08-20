/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.ConstructionGrammar.Licensing

/-!
# Construction-relative composition

Rules of semantic combination are construction-relative: a construction
"specifies how the semantics of the daughters are combined to produce the
semantics of the mother, and what additional semantics, if any, is
contributed by the construction itself" ([kay-michaelis-2019] §4). A
composition rule is partial — it demands daughter denotations of the
right shape — and mismatches are repaired by the override principle
([michaelis-2004], (20)): the lexical item conforms to the meaning of the
structure in which it is embedded.

## Main definitions

* `CompositionRule`: from the daughters' denotations to the mother's
* `CompositionRule.override`: readings under the override principle, one
  per reconciliation operator
* `Constructicon.interps`: all readings of a token, through the licensing
  recognizer
-/

namespace ConstructionGrammar

variable {D : Type*}

/-- A composition rule: from the daughters' denotations to the mother's,
partial because a rule demands daughter denotations of the right shape
([kay-michaelis-2019] §4). -/
abbrev CompositionRule (D : Type*) := List D → Option D

/-- Readings under the override principle ([michaelis-2004], (20)): the
rule's own output where the daughters already conform, and otherwise one
reading per reconciliation operator that makes them conform. Distinct
operators yielding distinct repairs produce genuine ambiguity. -/
def CompositionRule.override [DecidableEq D] (r : CompositionRule D)
    (shifts : List (D → D)) (ds : List D) : List D :=
  match r ds with
  | some d => [d]
  | none => (shifts.filterMap fun s => r (ds.map s)).dedup

/-- Conforming daughters are composed directly: implicit type-shifting
occurs only on mismatch ([michaelis-2004], Table 3). -/
theorem CompositionRule.override_eq_of_eq_some [DecidableEq D]
    {r : CompositionRule D} {ds : List D} {d : D} (shifts : List (D → D))
    (h : r ds = some d) : r.override shifts ds = [d] := by
  simp [CompositionRule.override, h]

/-- With no reconciliation operators, a mismatch has no readings. -/
@[simp]
theorem CompositionRule.override_nil [DecidableEq D]
    (r : CompositionRule D) (ds : List D) :
    r.override [] ds = (r ds).toList := by
  cases h : r ds <;> simp [CompositionRule.override, h]

mutual

/-- All readings of a token: each construction whose typed form the
daughters instantiate contributes the readings its meaning pole — its
composition rule — produces from the daughters' readings; words read
from the lexicon. -/
def Constructicon.interps {D : Type*}
    (cx : Constructicon (CompositionRule D)) (pos : String → Option UD.UPOS)
    (lex : String → Option D) : Token → List D
  | .word w => (lex w).toList
  | .node ts =>
      cx.constructions.flatMap (λ c =>
        if formMatches pos c.form ts then
          (cx.interpsList pos lex ts).filterMap c.meaning
        else [])

/-- All sequences of daughter readings. -/
def Constructicon.interpsList {D : Type*}
    (cx : Constructicon (CompositionRule D)) (pos : String → Option UD.UPOS)
    (lex : String → Option D) : List Token → List (List D)
  | [] => [[]]
  | t :: ts =>
      (cx.interps pos lex t).flatMap (λ d =>
        (cx.interpsList pos lex ts).map (d :: ·))

end

end ConstructionGrammar
