/-
# LingLean.Syntax.Minimalism.Basic

Minimalist Program formalization.

The Minimalist Program (Chomsky 1995+) builds structure through:
- Merge: combining two elements into a set
- Move (Internal Merge): re-merging an element already in the structure

## References

- Chomsky (1995). The Minimalist Program.
- Adger (2003). Core Syntax.
- Radford (2009). Analysing English Sentences.
-/

import LingLean.Syntax.Basic
import LingLean.Syntax.Grammar

namespace Minimalism

-- ============================================================================
-- Syntactic Features (Minimalist Style)
-- ============================================================================

/-- Features that drive syntactic operations -/
inductive Feature where
  | cat : Cat → Feature           -- category feature
  | q : Bool → Feature            -- question feature
  | wh : Bool → Feature           -- wh-feature
  | tense : Bool → Feature        -- tense feature
  | epp : Bool → Feature          -- EPP (needs specifier)
  deriving Repr, DecidableEq

/-- A feature bundle -/
abbrev FeatureBundle := List Feature

/-- Check if a bundle has a specific feature -/
def hasFeature (fb : FeatureBundle) (f : Feature) : Bool :=
  fb.contains f

/-- Check if bundle has [+Q] -/
def hasQ (fb : FeatureBundle) : Bool :=
  fb.any fun f => match f with | .q true => true | _ => false

-- ============================================================================
-- Syntactic Objects
-- ============================================================================

/-- A syntactic object: either a lexical item or a derived structure -/
inductive SynObj where
  | lex : Word → FeatureBundle → SynObj
  | set : SynObj → SynObj → FeatureBundle → SynObj  -- {α, β} with label
  | trace : Nat → SynObj                              -- trace of moved element
  deriving Repr

/-- Get the label (features) of a syntactic object -/
def SynObj.label : SynObj → FeatureBundle
  | .lex _ fb => fb
  | .set _ _ fb => fb
  | .trace _ => []

/-- Get the yield (linearized words) of a syntactic object -/
partial def SynObj.yield : SynObj → List Word
  | .lex w _ => [w]
  | .set α β _ => α.yield ++ β.yield
  | .trace _ => []

-- ============================================================================
-- Minimalist Operations
-- ============================================================================

/-- External Merge: combine two separate objects -/
def externalMerge (α β : SynObj) (label : FeatureBundle) : SynObj :=
  .set α β label

/-- Internal Merge (Move): re-merge an element from within the structure -/
structure Movement where
  moved : SynObj
  source : Nat
  target : SynObj
  result : SynObj
  deriving Repr

/-- T-to-C Movement: T head moves to C position. -/
def tToCMovement (c : SynObj) (t : SynObj) : Option SynObj :=
  if hasQ c.label then
    some (.set t c c.label)
  else
    none

-- ============================================================================
-- Derivations
-- ============================================================================

/-- A derivation step -/
inductive DerivStep where
  | extMerge : SynObj → SynObj → FeatureBundle → DerivStep
  | intMerge : Movement → DerivStep
  | headMove : SynObj → SynObj → DerivStep
  deriving Repr

/-- A derivation is a sequence of steps -/
structure Derivation where
  steps : List DerivStep
  result : SynObj

/-- Check if a derivation involves T-to-C movement -/
def Derivation.hasTToC (d : Derivation) : Bool :=
  d.steps.any fun s => match s with
    | .headMove _ c => hasQ c.label
    | _ => false

-- ============================================================================
-- Minimalist Grammar
-- ============================================================================

/-- A Minimalist grammar specifies the lexicon and derivational constraints -/
structure MinimalistGrammar where
  lexicon : List (Word × FeatureBundle)

/-- Minimalist derivations -/
structure MinDerivation (g : MinimalistGrammar) where
  deriv : Derivation
  clauseType : ClauseType
  matrixNeedsTToC : clauseType = .matrixQuestion → deriv.hasTToC
  embeddedNoTToC : clauseType = .embeddedQuestion → ¬deriv.hasTToC

/-- Minimalism Grammar instance -/
instance : Grammar MinimalistGrammar where
  Derivation := Σ g : MinimalistGrammar, MinDerivation g
  realizes d ws ct := d.2.deriv.result.yield = ws ∧ d.2.clauseType = ct
  derives g ws ct := ∃ d : MinDerivation g, d.deriv.result.yield = ws ∧ d.clauseType = ct

-- ============================================================================
-- Phase Theory (Sketch)
-- ============================================================================

/-- Phases are derivational cycles (CP, v*P). -/
inductive Phase where
  | cp : SynObj → Phase
  | vP : SynObj → Phase

/-- Check if a syntactic object is a phase -/
def isPhase (so : SynObj) : Bool :=
  match so.label.find? (fun f => match f with | .cat _ => true | _ => false) with
  | some (.cat .C) => true
  | some (.cat .V) => true
  | _ => false

end Minimalism
