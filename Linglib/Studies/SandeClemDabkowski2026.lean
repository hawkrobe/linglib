/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Syntax.Minimalist.Linearization.Cyclic
import Linglib.Syntax.Minimalist.Movement.Remnant
import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Amalgamation

/-!
# Sande, Clem & Dąbkowski 2026: discontinuous vowel harmony in Guébie

[sande-clem-dabkowski-2026]: in Guébie particle-verb focus constructions, the
fronted particle harmonizes in ATR with the clause-final verb across intervening
harmony-eligible words (their (24)). The analysis: harmony is strictly local at vP
Spell-out, and later A′-movement separates target from trigger — spelled-out
material staying accessible to later syntax (§6.2, via [fox-pesetsky-2005]'s
Cyclic Linearization). Everything below is derived from the two §4 parameters
(Aux blocking V-to-T, remnant fronting) rather than stipulated; the empirical core
is their (44): harmony iff V is spelled out inside vP.

## Main definitions

* `Clause`, `WordOrder`: the §4 parameters and the four attested settings, with
  derived Spell-outs ((45)/(48)) and surface strings ((31)–(34)).
* `Clause.harmony`, `surfaceATR`, `harmonyTableau`: trigger-locality (§6.1), the
  particle's surface value ((12)–(13)), and the (46)/(47) ranking as a tableau.
* `FrozenATR`, `guebiePICMode`: the per-cycle harmony record (§6.1) and the PIC
  stance (§6.2).
* `guebiePredicateDoubling`, `WolofRelClauseShape`: the §3 movement witnesses and
  the §7 Wolof parallel.

## Main results

* `harmony_eq_hasAux`, `discontinuous_harmony`: the (44) correlation derived;
  harmony without surface adjacency.
* `all_clauses_consistent`, `nonedge_particle_fronting_crashes`: every setting
  linearizes; the §6.2 escape-hatch counterfactual crashes.
* `optimal_eq_surfaceATR`, `PartSAuxOV_atr_persists_through_fronting`: the ranking
  derives the surface value, and it survives the CP cycle.
* `guebie_VDIS_positive_instance`, `wolof_harmony_uniform`: doubling is
  narrow-syntactic ((25)–(30), contra [landau-2006]); the Wolof parallel
  ([sy-2005], [martinovic-2019]).

## Implementation notes

Spell-out snapshots are `List String` labels, as in `Studies/FoxPesetsky2005.lean`.
The paper deems the harmony implementation "not crucial" ([sande-2019]'s (46)/(47)
in [hansson-2014]'s Agreement by Projection); `harmonyTableau` renders only the
ranking. §5's rejected phonological approaches ([clements-sezer-1982],
[gafos-1998], [rose-walker-2004]) are formalized in `Studies/Sagey1986.lean`,
`Studies/RoseWalker2004.lean`, `Studies/Hansson2010.lean`. TODO: the Atchan
parallel ((51), Katherine Russell p.c., [russell-2023]) awaits movement
diagnostics; the paper leaves it open and so do we.
-/

namespace SandeClemDabkowski2026

open List
open Minimalist (PICStrength)
open Minimalist.Linearization (Consistent)
open Constraints (Constraint)
open OptimalityTheory

/-! ### The ATR feature ([sande-clem-dabkowski-2026] (1))

Guébie has a ten-vowel system, +ATR `ə e i o u` vs. −ATR `a ɛ ɪ ɔ ʊ`, harmonizing
as a binary feature; affixes and particles agree with the verb root when both are
inside the same Spell-out domain. Only the per-terminal binary value matters here. -/

/-- The ATR feature value of a terminal: `+ATR = true`, `−ATR = false`. -/
abbrev ATR := Bool

/-- The particle's lexical default, surfacing when no harmony trigger is local
    ((13)). Defaults are lexical per particle — /jɔkʊ/ is −ATR, others are +ATR
    ((12)); we model the /jɔkʊ/ type. -/
def particleDefaultATR : ATR := false

/-! ### The §4 syntax: two parameters derive the four orders -/

/-- The two parameters of [sande-clem-dabkowski-2026] §4's predicate-fronting
    analysis: an auxiliary in T blocks V-to-T ((32)/(34)), and the remnant VP
    (containing the particle) may front to Spec,CP ((33)/(34)). -/
structure Clause where
  hasAux  : Bool
  fronted : Bool
  deriving DecidableEq, Repr

/-- V stays in v — hence inside the vP Spell-out — iff Aux occupies T (§4.1). -/
def Clause.verbInVP (c : Clause) : Bool := c.hasAux

/-- Overt terminals spelled out within vP ((45)/(48)): the particle, plus V iff it
    has not raised past v. The object has independently shifted out. -/
def Clause.vPSpellOut (c : Clause) : List String :=
  "Part" :: if c.verbInVP then ["V"] else []

/-- The surface clause, derived compositionally ((31)–(34)): fronted particle,
    subject, T-material, object, in-situ particle, clause-final verb. -/
def Clause.surfaceOrder (c : Clause) : List String :=
  (if c.fronted then ["Part"] else []) ++ ["S"]
    ++ (if c.hasAux then ["Aux"] else ["V"]) ++ ["O"]
    ++ (if c.fronted then [] else ["Part"])
    ++ (if c.hasAux then ["V"] else [])

/-- The two-phase Cyclic-Linearization derivation: vP Spell-out, then the full
    surface clause ([fox-pesetsky-2005]'s final Linearize). Previously-spelled-out
    terminals recur, so Order Preservation is what makes consistency contentful. -/
def Clause.derivation (c : Clause) : List (List String) :=
  [c.vPSpellOut, c.surfaceOrder]

/-- The four attested word orders as parameter settings
    ([sande-clem-dabkowski-2026] (44)). -/
inductive WordOrder where
  /-- `S V O Part`: V moves to T; Part stays in vP, clause-final. -/
  | SVOPart
  /-- `S Aux O Part V`: Aux occupies T, V stays in v; V and Part both in vP. -/
  | SAuxOPartV
  /-- `Part S V O`: V moves to T; the remnant VP (just Part) fronts to Spec,CP. -/
  | PartSVO
  /-- `Part S Aux O V`: V stays in v; the remnant VP (just Part) fronts. -/
  | PartSAuxOV
  deriving DecidableEq, Repr

/-- The parameter settings behind the four orders ((31)–(34)). -/
def WordOrder.clause : WordOrder → Clause
  | .SVOPart    => ⟨false, false⟩
  | .SAuxOPartV => ⟨true,  false⟩
  | .PartSVO    => ⟨false, true⟩
  | .PartSAuxOV => ⟨true,  true⟩

/-- The derived surface strings are the attested orders. -/
theorem surfaceOrder_attested :
    WordOrder.SVOPart.clause.surfaceOrder    = ["S", "V", "O", "Part"] ∧
    WordOrder.SAuxOPartV.clause.surfaceOrder = ["S", "Aux", "O", "Part", "V"] ∧
    WordOrder.PartSVO.clause.surfaceOrder    = ["Part", "S", "V", "O"] ∧
    WordOrder.PartSAuxOV.clause.surfaceOrder = ["Part", "S", "Aux", "O", "V"] := by
  decide

/-! ### Consistency: every setting linearizes; non-edge fronting would not -/

/-- Every parameter setting linearizes consistently. -/
theorem all_clauses_consistent :
    ∀ aux fronted : Bool, Consistent (Clause.derivation ⟨aux, fronted⟩) := by decide

/-- The §6.2 escape-hatch argument: the particle can front because it is "the
    leftmost overt element in the vP phase upon spell-out". A counterfactual vP
    spelling the particle out to the right of V could not front it without an
    ordering cycle. -/
theorem nonedge_particle_fronting_crashes :
    ¬ Consistent [["V", "Part"], ["Part", "S", "Aux", "O", "V"]] := by decide

/-! ### The (44) correlation, derived -/

/-- Harmony applies iff the trigger V is spelled out within vP (§6.1). -/
def Clause.harmony (c : Clause) : Bool :=
  c.vPSpellOut.contains "V"

/-- The (44) correlation derived from the syntax: harmony iff Aux blocks V-to-T. -/
theorem harmony_eq_hasAux (aux fronted : Bool) :
    (Clause.mk aux fronted).harmony = aux := by decide +revert

/-- Fronting is irrelevant to harmony — the discontinuity is purely a surface
    effect of later movement. -/
theorem harmony_independent_of_fronting (aux f₁ f₂ : Bool) :
    (Clause.mk aux f₁).harmony = (Clause.mk aux f₂).harmony := by decide +revert

/-- Discontinuity as a theorem: in the fronted SAuxOV clause, particle and verb
    are not surface-adjacent in either order, yet harmony applies ((24)). -/
theorem discontinuous_harmony :
    (Clause.mk true true).harmony = true ∧
    ¬ (["Part", "V"] <:+: (Clause.mk true true).surfaceOrder ∨
       ["V", "Part"] <:+: (Clause.mk true true).surfaceOrder) := by decide

/-- The particle's surface ATR: the verb root's value under harmony ((12)), its
    lexical default otherwise ((13)). -/
def surfaceATR (c : Clause) (vRoot : ATR) : ATR :=
  if c.harmony then vRoot else particleDefaultATR

/-! ### §6.1's mechanism: the (46)/(47) ranking derives the surface value

The paper implements local harmony as [sande-2019]'s constraints in
[hansson-2014]'s Agreement by Projection, ranked `ATRHARM ≫ IDENT-IO(ATR)`
within the vP domain; the winner harmonizes exactly when a trigger is local. -/

/-- An output candidate for the particle at vP Spell-out: lexical input value,
    domain-local trigger (the verb root, when V is in the domain), and output. -/
structure HarmonyCand where
  lexical : ATR
  trigger : Option ATR
  out     : ATR
  deriving DecidableEq, Repr

/-- (46) `IDENT-IO(ATR)`: one violation if the output differs from the input. -/
def identIO : Constraint HarmonyCand :=
  Constraints.Constraint.binary fun c => c.out ≠ c.lexical

/-- (47) `ATRHARM`: one violation if a domain-local trigger disagrees with the
    output. -/
def atrHarm : Constraint HarmonyCand :=
  Constraints.Constraint.binary fun c => ∃ t ∈ c.trigger, t ≠ c.out

/-- The domain-local trigger: the verb root's value when V is spelled out in vP. -/
def vPTrigger (c : Clause) (vRoot : ATR) : Option ATR :=
  if c.harmony then some vRoot else none

/-- The vP-domain tableau: both output values, ranked `ATRHARM ≫ IDENT-IO(ATR)`. -/
def harmonyTableau (lex : ATR) (trig : Option ATR) : Tableau HarmonyCand 2 :=
  Tableau.ofRanking [⟨lex, trig, true⟩, ⟨lex, trig, false⟩] [atrHarm, identIO]
    (List.cons_ne_nil _ _)

/-- §6.1's mechanism, closed: the unique OT winner under `ATRHARM ≫ IDENT-IO(ATR)`
    surfaces with exactly `surfaceATR` — harmonized when a trigger is local,
    faithful to the lexical default otherwise. -/
theorem optimal_eq_surfaceATR (aux fronted : Bool) (vRoot : ATR) :
    (harmonyTableau particleDefaultATR (vPTrigger ⟨aux, fronted⟩ vRoot)).optimal
      = {⟨particleDefaultATR, vPTrigger ⟨aux, fronted⟩ vRoot,
          surfaceATR ⟨aux, fronted⟩ vRoot⟩} := by
  cases aux <;> cases fronted <;> cases vRoot <;> decide

/-! ### Frozen ATR survives later movement (§6.1)

[fox-pesetsky-2005]'s Order Preservation shape applied to harmony outcomes:
[sande-clem-dabkowski-2026] §6.1 — the particle "will retain this ATR value when it
undergoes focus fronting". The record is append-only across cycles. -/

/-- Per-cycle log of frozen ATR values `(terminal, value)`; append-only. -/
abbrev FrozenATR := List (String × ATR)

/-- Extend the log with one cycle's assignments. -/
def extendFrozenATR (existing new : FrozenATR) : FrozenATR := existing ++ new

/-- Order-Preservation analogue: earlier freezings survive later cycles. -/
theorem extendFrozenATR_preserves (existing new : FrozenATR) {e : String × ATR}
    (h : e ∈ existing) : e ∈ extendFrozenATR existing new :=
  List.mem_append_left _ h

/-- The most recently frozen value on `terminal`, if any. -/
def frozenATR? (table : FrozenATR) (terminal : String) : Option ATR :=
  (table.reverse.find? (·.1 == terminal)).map (·.2)

/-- A later re-freeze overrides — the intended semantics, though
    [sande-clem-dabkowski-2026] posit no CP-cycle ATR re-write for the particle. -/
theorem frozenATR?_later_overrides :
    frozenATR? (extendFrozenATR [("Part", true)] [("Part", false)]) "Part"
      = some false := by decide

/-- The vP-cycle freezing for `PartSAuxOV`: Part inherits the verb root's value
    (e.g. /ni/ 'see' +ATR yields the particle surface form [joku], (11)–(12)). -/
def vPFrozen_PartSAuxOV (vRoot : ATR) : FrozenATR := [("Part", vRoot)]

/-- The CP cycle issues no new ATR assignment for Part; the vP value persists —
    §6.1's "it will retain this ATR value when it undergoes focus fronting". -/
theorem PartSAuxOV_atr_persists_through_fronting (vRoot : ATR) :
    frozenATR? (extendFrozenATR (vPFrozen_PartSAuxOV vRoot) []) "Part"
      = some vRoot := rfl

/-! ### The PIC stance (§6.2) -/

/-- [sande-clem-dabkowski-2026] §6.2: spelled-out material stays accessible to
    later syntax; strict PIC₁/PIC₂ would block the remnant-VP movement. The
    Cyclic-Linearization-bounded regime is `PICStrength.linearizationBound`. -/
def guebiePICMode : PICStrength := .linearizationBound

/-- Under the Guébie PIC mode every phase admits extraction; concrete crashes come
    from `Consistent` instead (`nonedge_particle_fronting_crashes`). -/
theorem guebie_PIC_admits_remnant_movement (φ : Minimalist.Phase)
    (goal : Minimalist.SyntacticObject) :
    Minimalist.admitsExtraction guebiePICMode φ goal := by
  unfold guebiePICMode; exact Minimalist.linearizationBound_admits_all φ goal

/-! ### Predicate fronting is narrow-syntactic (§3)

Three diagnostics: successive cyclicity ((25)–(26)), island sensitivity
((27)–(28)), and island creation ((29)–(30)). This registers Guébie beside
[harizanov-gribanova-2019]'s Russian as a positive instance of
`VerbDoublingIsSyntactic`, against [landau-2006]'s PF-driven Hebrew analysis
(the reason the substrate predicate is per-construction, not universal — see
`HarizanovGribanova2019Amalgamation.lean`). The witnesses are schematic: the
fronted remnant is an evacuation trace plus the verb copy, per their (31). -/

open Minimalist (SyntacticObject LIToken VerbDoublingIsSyntacticIn)
open Minimalist.Movement (RemnantFronting PredicateDoubling properRemnant)
open Minimalist.SyntacticObject

private def guebieVerbTok : LIToken := ⟨.simple .V [], 1⟩
private def guebieVerbLeaf : SyntacticObject := lexLeaf guebieVerbTok

/-- The remnant VP of the verb-doubling configuration ((31)): an evacuation trace
    plus the verb copy, pronounced for recoverability per [koopman-1997]. -/
private def guebieFrontedVP : SyntacticObject :=
  ofPlanar (nodeP traceP (leafP guebieVerbTok))

private def guebieLandingTok : LIToken := ⟨.simple .C [], 2⟩
private def guebieLandingSite : SyntacticObject := lexLeaf guebieLandingTok

/-- The Guébie predicate-fronting witness: V evacuates, the remnant VP fronts to
    Spec,CP, and the trace is pronounced — verb doubling. -/
def guebiePredicateDoubling : PredicateDoubling :=
  { frontedXP        := guebieFrontedVP
    evacuatedHeads   := [guebieVerbLeaf]
    landingSite      := guebieLandingSite
    verb             := guebieVerbLeaf
    verb_evacuated   := List.mem_singleton.mpr rfl
    trace_pronounced := true }

/-- The evacuated verb sat inside the fronted remnant. -/
theorem guebie_properRemnant :
    properRemnant guebiePredicateDoubling.toRemnantFronting := by decide

/-- On the carrier, Internal Merge leaves a trace at the deeper position
    ([marcolli-chomsky-berwick-2025] §1.4.3); surface doubling is the pronunciation
    of both positions. -/
def guebieFrontingDerivation : Derivation :=
  { initial := guebieFrontedVP
    steps   := [.im guebieVerbLeaf] }

/-- Guébie registered as a positive instance of `VerbDoublingIsSyntacticIn`
    (§3's diagnostics; decidable from the derivation structure). -/
theorem guebie_VDIS_positive_instance :
    VerbDoublingIsSyntacticIn guebieFrontingDerivation guebieVerbLeaf := by
  decide

/-! ### The Wolof parallel (§7)

Wolof relative clauses ([sy-2005], [martinovic-2019]) show the same shape: the DP
containing head noun and distal demonstrative "is a phase, so the two are spelled
out in a sufficiently local configuration for harmony to apply"; the head noun then
A′-moves to the left edge, and intervening stative-verb material does not
harmonize ((49)–(50)). -/

inductive WolofRelClauseShape where
  /-- Local DP, no relative clause ((49)): head and demonstrative surface-adjacent. -/
  | localDP
  /-- Relative clause ((50)): head fronted, ATR set inside the DP phase. -/
  | relClause
  deriving DecidableEq, Repr

/-- Head noun and demonstrative are spelled out together at the DP phase in both
    shapes. -/
def wolofDPSpellOut : WolofRelClauseShape → List String
  | .localDP   => ["head", "dem"]
  | .relClause => ["head", "dem"]

def wolofHarmonyApplies (s : WolofRelClauseShape) : Bool :=
  (wolofDPSpellOut s).contains "head" && (wolofDPSpellOut s).contains "dem"

/-- Harmony is predicted in both shapes — the relative clause's discontinuous
    appearance is post-Spell-out movement, not a different harmony mechanism. -/
theorem wolof_harmony_uniform :
    wolofHarmonyApplies .localDP = true ∧
    wolofHarmonyApplies .relClause = true := by decide

end SandeClemDabkowski2026
