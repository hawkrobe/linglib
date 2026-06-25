import Linglib.Syntax.Minimalist.Phase
import Linglib.Features.ScopeTypes

/-!
# [bruening-2001] — QR Obeys Superiority
[bruening-2001] [larson-1988] [may-1985]
[pylkkanen-2008]

Bruening's *Linguistic Inquiry* paper "QR Obeys Superiority: Frozen
Scope and ACD" — both the empirical scope-freezing data set and the
theoretical Minimalist analysis (QR locality + superiority +
phase-theoretic barriers).

## Part I: Empirical data

Theory-neutral scope-freezing examples primarily compiled from
[bruening-2001], with contributions from [larson-1988]
(double-object construction examples) and [may-1985]
(foundational scope-availability vocabulary).

## Part II: Theoretical analysis (Minimalist QR)

Bruening's central thesis — *QR obeys Superiority* — is derived
formally: double-object scope freezing follows from asymmetric
c-command in [pylkkanen-2008]'s Voice + low-Appl tree, where the
goal asymmetrically c-commands the theme. Other freezing contexts
(possessor, passive, attitude) are analyzed via DP-phase /
adjunct-island / clause-boundary barriers.

## Sections
- `ScopeFreezing`: Empirical configurations where inverse scope is unavailable
- `MinimalistAnalysis`: Theoretical derivation of freezing from Minimalist QR

The verb-cluster word-order scope data formerly housed here was
[steedman-2000] §6.8 material and now lives in
`Linglib.Data.Examples.Steedman2000` / `Linglib.Studies.Steedman2000`.
-/

namespace Bruening2001

/-! ### Scope: QR and Scope Economy (relocated from Minimalist/Scope.lean)

Formalization of quantifier scope in the Minimalist tradition.

## Core Mechanisms

1. **Quantifier Raising (QR)**: Covert A'-movement of quantifiers to adjoin to TP/CP
2. **Scope Economy**: QR only applies if it yields a distinct interpretation
3. **Locality**: QR is clause-bounded and blocked by certain structural barriers

## Scope Freezing in Minimalism

Inverse scope is unavailable when:
- **Possessor**: Quantifier inside possessor DP cannot escape (DP is a phase/barrier)
- **Double Object**: Indirect object c-commands direct object; QR would violate locality
- **Passive**: By-phrase is an adjunct; QR from adjuncts is blocked

## Superiority from C-Command (not stipulation)

In earlier versions, `PositionedQuantifier` carried a stipulated
`inDoubleObject : Bool` flag. This has been replaced: the theory layer
provides `superiorityFromTree`, which derives superiority from
asymmetric c-command in a `SyntacticObject` tree.
This study uses it to connect DOC scope freezing to
[larson-1988]'s tree derivation.
-/

section Scope

open ScopeTheory
open Minimalist

-- Structural Positions

/-- Structural positions relevant for scope -/
inductive Position where
  | specTP      -- Subject position (Spec-TP)
  | specVP      -- Object position (Spec-vP or complement of V)
  | adjunct     -- Adjunct position (by-phrase, PP modifier)
  | embedded    -- Inside a DP (possessor, PP complement)
  | complement  -- Clausal complement
  deriving DecidableEq, Repr, Inhabited

/-- A quantifier with its structural position -/
structure PositionedQuantifier where
  quantifier : String
  position : Position
  /-- Is this inside another DP? -/
  insideDP : Bool := false
  /-- The SyntacticObject this quantifier corresponds to in the tree.
      When provided, superiority can be derived from c-command. -/
  so : Option SyntacticObject := none
  deriving Repr

-- QR Operation

/--
Quantifier Raising (QR) as covert movement.

QR adjoins a quantifier to a clausal node (TP or CP),
allowing it to take scope over material it c-commands at LF.
-/
structure QROperation where
  /-- The quantifier being raised -/
  target : PositionedQuantifier
  /-- Landing site -/
  landingSite : Position
  /-- Does this create a new scope relation? -/
  createsNewScope : Bool
  deriving Repr

-- Locality Constraints on QR

/--
Barriers to QR movement.

Following phase theory and earlier barrier theory, certain nodes
block extraction/QR.
-/
inductive QRBarrier where
  | dpPhase       -- DP is a phase; QR cannot escape
  | clauseBoundary -- QR is clause-bounded (cannot cross CP)
  | adjunctIsland -- QR from adjuncts is blocked
  | superiority   -- QR cannot cross a c-commanding quantifier (Bruening)
  deriving DecidableEq, Repr, Inhabited

/-- Check if QR is blocked for a given quantifier -/
def qrIsBlocked (q : PositionedQuantifier) : Option QRBarrier :=
  if q.insideDP then some .dpPhase
  else if q.position == .adjunct then some .adjunctIsland
  else if q.position == .embedded then some .dpPhase
  else none

/-- Superiority derived from a tree: QR of `q2` over `q1` is blocked
    when `q1` asymmetrically c-commands `q2` in `tree`.

    This is the theory-layer primitive. Bridge files use it to derive
    DOC scope freezing from [pylkkanen-2008]'s Voice + low-Appl
    tree derivation. -/
def superiorityFromTree (tree : SyntacticObject)
    (q1 q2 : SyntacticObject) : Bool :=
  decide (SO.asymCCommandsIn tree q1 q2)

-- Scope Economy ([fox-2000])

/--
Scope Economy: QR is only licensed if it creates a truth-conditional difference.

"Covert scope-shifting operations are blocked if they don't have
a semantic effect (i.e., if they yield a logically equivalent interpretation)."
-/
structure ScopeEconomy where
  /-- Surface scope interpretation -/
  surfaceInterpretation : String
  /-- Would-be inverse interpretation -/
  inverseInterpretation : String
  /-- Are they truth-conditionally equivalent? -/
  equivalent : Bool
  deriving Repr

/-- QR is blocked by economy if interpretations are equivalent -/
def economyBlocksQR (e : ScopeEconomy) : Bool :=
  e.equivalent

-- ============================================================================
-- Phase Theory Derivation of QR Barriers
-- ============================================================================

/-- DP-as-barrier follows from PIC: if `φ` is the D-phase (D being a phase head
    under the extended inventory) and `goal` is an accessible term sitting in the
    phase head's c-command domain, then `goal` is frozen — `φ.Impenetrable goal`.

    This derives the previously-stipulated `QRBarrier.dpPhase` from deeper
    principles: PIC makes DP-internal material inaccessible to operations outside
    DP. On the MCB-faithful `SO` phase API the **interior Φ°_ℓ *is* the head's
    c-command domain** (Def 1.14.3, "Z is the interior of the phase"), so a goal
    in that domain is impenetrable by construction (`SO.mem_phaseInterior`). -/
theorem dp_phase_barrier_from_pic (φ : Phase) {goal : SyntacticObject}
    (hacc : goal ∈ φ.tree.Acc)
    (hcc : φ.tree.cCommandsIn (SO.lexLeaf φ.head) goal) :
    φ.Impenetrable goal :=
  SO.mem_phaseInterior.mpr ⟨hacc, hcc⟩

end Scope

-- ============================================================================
-- § Scope Freezing
-- ============================================================================

section ScopeFreezing

/-- Available scope readings for a sentence -/
inductive Availability where
  | ambiguous     -- Both surface and inverse available
  | surfaceOnly   -- Only surface scope (inverse frozen)
  | inverseOnly   -- Only inverse scope (rare)
  deriving DecidableEq, Repr, Inhabited

/-- Confidence in the judgment -/
inductive Confidence where
  | clear         -- Native speakers agree (but introspective)
  | gradient      -- Some variation / context-dependent
  | controversial -- Theoretical disagreement
  deriving DecidableEq, Repr, Inhabited

/-- Source of the judgment -/
inductive DataSource where
  | introspective   -- Linguist intuition (no experimental data)
  | experimental    -- Controlled experiment with ratings
  | corpus          -- Corpus-based evidence
  deriving DecidableEq, Repr, Inhabited

/-- Types of configurations that induce scope freezing -/
inductive FreezingContext where
  | none              -- No freezing context (baseline ambiguous)
  | possessor         -- "A student's teacher..."
  | doubleObject      -- "gave NP NP" vs "gave NP to NP"
  | passive           -- "was V-ed by NP"
  | heavyNP           -- Complex/heavy NP in subject
  | weakCrossover     -- Bound variable blocks inverse
  | adjunct           -- Adjunct scope interactions
  | attitude          -- Attitude verb complements
  deriving DecidableEq, Repr, Inhabited

/-- A scope freezing example with empirical judgment -/
structure Example where
  id : String
  sentence : String
  quant1 : String
  quant2 : String
  context : FreezingContext
  observed : Availability
  confidence : Confidence := .clear
  source : DataSource := .introspective
  surfaceGloss : String := ""
  inverseGloss : String := ""
  notes : String := ""
  deriving Repr


-- Possessor Freezing

def possessor_baseline : Example :=
  { id := "poss-1a"
  , sentence := "A student attended every seminar."
  , quant1 := "a student"
  , quant2 := "every seminar"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's a student who attended every seminar"
  , inverseGloss := "For every seminar, some student attended it"
  , notes := "Baseline: both readings available" }

def possessor_frozen : Example :=
  { id := "poss-1b"
  , sentence := "A student's teacher attended every seminar."
  , quant1 := "a student's teacher"
  , quant2 := "every seminar"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's a student whose teacher attended every seminar"
  , inverseGloss := "*For every seminar, some student's teacher attended it"
  , notes := "Possessor freezes scope" }

def possessor_variant1 : Example :=
  { id := "poss-2a"
  , sentence := "Someone from every city was present."
  , quant1 := "someone from every city"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who is from every city (impossible)"
  , inverseGloss := "For every city, someone from it was present"
  , notes := "Inverse scope is the sensible reading" }

def possessor_variant2 : Example :=
  { id := "poss-2b"
  , sentence := "Someone's friend from every city was present."
  , quant1 := "someone's friend"
  , quant2 := "every city"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Possessor blocks inverse; sentence is odd" }


-- Double Object Freezing

def dative_baseline : Example :=
  { id := "dat-1a"
  , sentence := "Someone gave a book to every student."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who gave a book to every student"
  , inverseGloss := "For every student, someone gave them a book"
  , notes := "PP dative: ambiguous" }

def dative_frozen : Example :=
  { id := "dat-1b"
  , sentence := "Someone gave every student a book."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone who gave every student a book"
  , inverseGloss := "*For every student, someone gave them a book"
  , notes := "Double object: frozen ([barss-lasnik-1986])" }

def dative_variant : Example :=
  { id := "dat-2"
  , sentence := "A teacher showed every student a new problem."
  , quant1 := "a teacher"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , notes := "Double object freezes subject-IO scope" }


-- Passive Freezing

def passive_baseline : Example :=
  { id := "pass-1a"
  , sentence := "Every professor saw a student."
  , quant1 := "every professor"
  , quant2 := "a student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "For every professor, they saw a (possibly different) student"
  , inverseGloss := "There's a student that every professor saw"
  , notes := "Active: ambiguous" }

def passive_frozen : Example :=
  { id := "pass-1b"
  , sentence := "A student was seen by every professor."
  , quant1 := "a student"
  , quant2 := "every professor"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "There's a student that every professor saw"
  , inverseGloss := "?For every professor, some student was seen by them"
  , notes := "Passive: frozen (but judgments vary)" }

def passive_variant : Example :=
  { id := "pass-2"
  , sentence := "Someone was interviewed by every committee."
  , quant1 := "someone"
  , quant2 := "every committee"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "by-phrase scope is limited" }


-- Heavy NP Effects

def heavy_baseline : Example :=
  { id := "heavy-1a"
  , sentence := "A man read every book."
  , quant1 := "a man"
  , quant2 := "every book"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "Simple subject: ambiguous" }

def heavy_frozen : Example :=
  { id := "heavy-1b"
  , sentence := "A man who was sitting in the corner read every book."
  , quant1 := "a man who was sitting in the corner"
  , quant2 := "every book"
  , context := .heavyNP
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Heavy subject: inverse scope degraded" }


-- Weak Crossover and Scope

def crossover_baseline : Example :=
  { id := "wco-1a"
  , sentence := "Someone loves every city."
  , quant1 := "someone"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "No bound variable: ambiguous" }

def crossover_frozen : Example :=
  { id := "wco-1b"
  , sentence := "Someone from it loves every city."
  , quant1 := "someone from it"
  , quant2 := "every city"
  , context := .weakCrossover
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone from some city who loves every city"
  , inverseGloss := "*For every city_i, someone from it_i loves it_i"
  , notes := "Bound pronoun blocks QR (weak crossover)" }


-- Attitude Verb Scope

def attitude_frozen : Example :=
  { id := "att-1"
  , sentence := "Someone believes that every student passed."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .attitude
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "Someone believes the proposition 'every student passed'"
  , inverseGloss := "?For every student, someone believes they passed"
  , notes := "Embedded universal can't easily scope over matrix" }

-- Collected Data

def possessorExamples : List Example :=
  [possessor_baseline, possessor_frozen, possessor_variant1, possessor_variant2]

def doubleObjectExamples : List Example :=
  [dative_baseline, dative_frozen, dative_variant]

def passiveExamples : List Example :=
  [passive_baseline, passive_frozen, passive_variant]

def heavyNPExamples : List Example :=
  [heavy_baseline, heavy_frozen]

def crossoverExamples : List Example :=
  [crossover_baseline, crossover_frozen]

def attitudeExamples : List Example :=
  [attitude_frozen]

def allExamples : List Example :=
  possessorExamples ++ doubleObjectExamples ++ passiveExamples ++
  heavyNPExamples ++ crossoverExamples ++ attitudeExamples

/-- Possessor freezing is robust (clear judgments) -/
def possessorFreezingIsClear : Bool :=
  possessor_frozen.confidence == .clear

/-- Double object freezing is robust -/
def doubleObjectFreezingIsClear : Bool :=
  dative_frozen.confidence == .clear

/-- Passive freezing is more gradient -/
def passiveFreezingIsGradient : Bool :=
  passive_frozen.confidence == .gradient

/-- Count frozen examples -/
def frozenCount : Nat :=
  allExamples.filter (·.observed == .surfaceOnly) |>.length

/-- Count ambiguous baselines -/
def ambiguousCount : Nat :=
  allExamples.filter (·.observed == .ambiguous) |>.length

#guard frozenCount == 9
#guard ambiguousCount == 6

end ScopeFreezing


-- ============================================================================
-- Part II: Minimalist Analysis
-- ============================================================================

section MinimalistAnalysis

open ScopeTheory
open Minimalist

/-! Connects Minimalist QR / Scope Economy theory to the empirical
scope-freezing data above. The central claim is Bruening's "QR obeys
superiority": double-object freezing falls out of asymmetric c-command
in the [pylkkanen-2008] ditransitive tree. -/

-- Freezing Context Analysis

/-- Analyze why a freezing context blocks inverse scope in Minimalism. -/
def analyzeFreezingContext : FreezingContext → Option QRBarrier
  | .none => none                           -- No barrier
  | .possessor => some .dpPhase             -- Quantifier trapped in possessor DP
  | .doubleObject => some .superiority      -- IO c-commands DO
  | .passive => some .adjunctIsland         -- By-phrase is adjunct
  | .heavyNP => none                        -- Not grammatical (processing)
  | .weakCrossover => none                  -- Blocked by binding, not QR locality
  | .adjunct => some .adjunctIsland
  | .attitude => some .clauseBoundary

/-- Does Minimalism predict freezing for this context? -/
def predictsFreezing (ctx : FreezingContext) : Bool :=
  (analyzeFreezingContext ctx).isSome

-- Scope Availability in Minimalism

/-- Minimalist representation of a scope configuration. -/
structure MinimalistScopeConfig where
  /-- Higher quantifier (typically subject) -/
  q1 : PositionedQuantifier
  /-- Lower quantifier (typically object) -/
  q2 : PositionedQuantifier
  /-- Freezing context if any -/
  freezingContext : FreezingContext := .none
  /-- The tree in which q1 and q2 are positioned. When provided,
      superiority is derived from c-command rather than stipulated. -/
  tree : Option Minimalist.SyntacticObject := none
  deriving Repr

/-- Check if superiority blocks QR in this configuration.

    When a tree and SO positions are provided, superiority is DERIVED
    from asymmetric c-command. Otherwise falls back to the freezing
    context annotation. -/
def superiorityBlocked (config : MinimalistScopeConfig) : Bool :=
  match config.tree, config.q1.so, config.q2.so with
  | some t, some s1, some s2 =>
    -- DERIVED: q1 asymmetrically c-commands q2
    superiorityFromTree t s1 s2
  | _, _, _ =>
    -- FALLBACK: use the freezing context annotation
    config.freezingContext == .doubleObject

/-- Compute available scope readings in Minimalism. -/
def availableReadings (config : MinimalistScopeConfig) : Availability :=
  let q2Barrier := qrIsBlocked config.q2
  let contextBarrier := analyzeFreezingContext config.freezingContext
  let superiorityViolation := superiorityBlocked config
  if q2Barrier.isSome || contextBarrier.isSome || superiorityViolation then
    .surfaceOnly
  else
    .ambiguous

-- Predictions for the empirical examples

/-- Build config from a freezing example (fallback path — no tree). -/
def configFromExample (ex : Example) : MinimalistScopeConfig :=
  { q1 := { quantifier := ex.quant1
          , position := .specTP
          , insideDP := ex.context == .possessor }
  , q2 := { quantifier := ex.quant2
          , position := if ex.context == .passive then .adjunct else .specVP }
  , freezingContext := ex.context }

/-- Minimalism's prediction for an example. -/
def predictAvailability (ex : Example) : Availability :=
  availableReadings (configFromExample ex)

/-- Check if Minimalism correctly predicts the example. -/
def correctlyPredicts (ex : Example) : Bool :=
  predictAvailability ex == ex.observed

-- Theoretical Claims as Theorems

/-- Possessor freezing follows from DP being a phase. -/
theorem possessor_freezes_scope :
    predictsFreezing .possessor = true := rfl

/-- Double object freezing follows from superiority. -/
theorem double_object_freezes_scope :
    predictsFreezing .doubleObject = true := rfl

/-- Passive freezing follows from adjunct island. -/
theorem passive_freezes_scope :
    predictsFreezing .passive = true := rfl

/-- Heavy NP is NOT predicted to freeze (it's processing). -/
theorem heavy_np_not_grammatically_frozen :
    predictsFreezing .heavyNP = false := rfl

/-- Baseline (no context) is predicted ambiguous. -/
theorem baseline_is_ambiguous :
    predictsFreezing .none = false := rfl

-- ============================================================================
-- DOC Scope Freezing — superiority derived from c-command
-- ============================================================================

/-! [pylkkanen-2008]'s low-Appl tree produces the DOC structure where V
takes ApplP as complement, so the goal in Spec-ApplP asymmetrically
c-commands the theme in complement of Appl. QR of the theme over the goal
is blocked by superiority, derived from c-command rather than stipulated.

The Voice + low-Appl tree is rebuilt locally (planar-first, since the smart
Merge `SO.node` is noncomputable) so this study stays self-contained and the
`decide` proof reduces. It mirrors `Pylkkanen2008.ditransitiveTree`'s
structure (`[John [Voice [sent [Mary [Appl letter]]]]]`); a future dedup can
re-point at that tree once the `SO`-carrier flip reaches `Studies/Pylkkanen2008`. -/

/-- Voice[AG] head (introduces the external argument, [kratzer-1996]). -/
def voice_ag_t  : Minimalist.LIToken := ⟨.simple .Voice [.V] "Voice[AG]", 400⟩
/-- Low applicative head: takes the theme DP as complement. -/
def appl_low_t  : Minimalist.LIToken := ⟨.simple .Appl [.D] "Appl[LOW]", 402⟩
/-- The ditransitive verb, selecting ApplP. -/
def V_sent_t    : Minimalist.LIToken := ⟨.simple .V [.Appl] "sent", 404⟩
/-- The agent DP. -/
def DP_john_t   : Minimalist.LIToken := ⟨.simple .D [] "John", 406⟩
/-- The goal DP (Spec,ApplP). -/
def DP_mary_t   : Minimalist.LIToken := ⟨.simple .D [] "Mary", 407⟩
/-- The theme DP (complement of Appl). -/
def DP_letter_t : Minimalist.LIToken := ⟨.simple .D [] "a letter", 408⟩

/-- The Voice + low-Appl ditransitive tree
    `[John [Voice [sent [Mary [Appl letter]]]]]`. The goal (Mary) in
    Spec-ApplP asymmetrically c-commands the theme (a letter) in the
    complement of Appl — the [barss-lasnik-1986] asymmetry, structural. -/
def ditransitiveTree : Minimalist.SyntacticObject :=
  SO.ofPlanar
    (SO.nodeP (SO.leafP DP_john_t)
      (SO.nodeP (SO.leafP voice_ag_t)
        (SO.nodeP (SO.leafP V_sent_t)
          (SO.nodeP (SO.leafP DP_mary_t)
            (SO.nodeP (SO.leafP appl_low_t) (SO.leafP DP_letter_t))))))

/-- DOC scope freezing config with the local low-Appl tree:
    superiority is derived from goal asymmetrically c-commanding theme
    in the Voice + low-Appl structure. -/
def docScopeConfig : MinimalistScopeConfig :=
  { q1 := { quantifier := "every worker"
           , position := .specVP
           , so := some (SO.lexLeaf DP_mary_t) }
  , q2 := { quantifier := "a paycheck"
           , position := .specVP
           , so := some (SO.lexLeaf DP_letter_t) }
  , freezingContext := .doubleObject
  , tree := some ditransitiveTree }

/-- Superiority in the DOC is DERIVED from c-command in
[pylkkanen-2008]'s tree: goal (Mary) asymmetrically c-commands
theme (a letter) via low Appl, so QR of theme over goal is blocked. -/
theorem doc_superiority_from_tree :
    superiorityBlocked docScopeConfig = true := by decide

/-! ## Summary

| Context | Minimalist Explanation |
|---------|----------------------|
| Possessor | DP phase blocks QR |
| Double object | Superiority: goal c-commands theme ([pylkkanen-2008] tree) |
| Passive | Adjunct island |
| Heavy NP | NOT grammatical (processing) |
| Attitude | Clause boundary |
-/

end MinimalistAnalysis

end Bruening2001
