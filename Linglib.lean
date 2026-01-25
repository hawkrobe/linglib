/-
# Linglib

A Lean 4 library for formalizing syntactic theories from theoretical linguistics
and connecting them to computational pragmatics (RSA - Rational Speech Acts).

## Architecture

### Core/ - Shared types and interfaces
- Core.Basic: Word, Cat, ClauseType, Lexicon
- Core.Grammar: Abstract Grammar typeclass
- Core.SemanticTypes: Semantic types
- Core.SemanticBackend: Interface that RSA needs from syntax

### Theories/ - Theoretical frameworks
- CCG/: Combinatory Categorial Grammar
- HPSG/: Head-Driven Phrase Structure Grammar
- Minimalism/: Minimalist Program
- DependencyGrammar/: Word Grammar (Hudson)
- Montague/: Montague-style compositional semantics
- NeoGricean/: Neo-Gricean pragmatics (Geurts 2010)
- Surface/: Simple constraint-checking grammar

### Phenomena/ - Empirical data (theory-independent)
- Basic: MinimalPair, PhenomenonData
- EmpiricalData: Data types, linking functions
- SubjectAuxInversion/, Coordination/, LongDistanceDependencies/
- ScalarImplicatures/, FreeChoice/, DisjunctionIgnorance/
- WordOrderAlternations/VerbPosition/ (V2, verb raising, long head movement)
- GoodmanStuhlmuller2013/, FrankGoodman2012/ (RSA reference game experiments)
- GeurtsPouscoulous2009/ (scalar implicature rates: defaultism vs contextualism)

## Coverage Matrix

                    Coordination  Inversion  LongDistance  ScalarImplicature  TruthConditions
CCG                      ✓            -           -              -                   -
HPSG                     -            ✓           -              -                   -
Minimalism               -            ✓           -              -                   -
DependencyGrammar        ✓            ✓           ✓              -                   -
Montague                 -            -           -              -                   ✓
NeoGricean               -            -           -              ✓                   -
RSA                      -            -           -              ✓                   -

Missing Theories/X/Y.lean = conjecture (theory hasn't proven it handles Y)
-/

-- Core types and interfaces
import Linglib.Core.Basic
import Linglib.Core.Grammar
import Linglib.Core.SemanticTypes
import Linglib.Core.SemanticBackend
import Linglib.Core.Frac
import Linglib.Core.RSA
import Linglib.Core.Pipeline
import Linglib.Core.InformationStructure

-- Theory interfaces (Mathlib pattern)
import Linglib.Core.Interfaces.CoreferenceTheory
import Linglib.Core.Interfaces.ImplicatureTheory

-- Phenomena (empirical data)
import Linglib.Phenomena.Basic
import Linglib.Phenomena.EmpiricalData
import Linglib.Phenomena.SubjectAuxInversion.Data
import Linglib.Phenomena.Coordination.Data
import Linglib.Phenomena.LongDistanceDependencies.Data
import Linglib.Phenomena.GoodmanStuhlmuller2013.Data
import Linglib.Phenomena.FrankGoodman2012.Data

-- BasicPhenomena
import Linglib.Phenomena.BasicPhenomena.Agreement
import Linglib.Phenomena.BasicPhenomena.Case
import Linglib.Phenomena.BasicPhenomena.DativeAlternation
import Linglib.Phenomena.BasicPhenomena.DetNounAgreement
import Linglib.Phenomena.BasicPhenomena.Passive
import Linglib.Phenomena.BasicPhenomena.Subcategorization
import Linglib.Phenomena.BasicPhenomena.WordOrder
import Linglib.Phenomena.BasicPhenomena.Proofs

-- Theories
import Linglib.Theories.HPSG.Basic
import Linglib.Theories.HPSG.Features
import Linglib.Theories.HPSG.Inversion
import Linglib.Theories.HPSG.Coreference

import Linglib.Theories.Minimalism.Basic
import Linglib.Theories.Minimalism.Structure
import Linglib.Theories.Minimalism.Inversion

-- Minimalist Syntax (Chomsky 1995+)
import Linglib.Theories.Minimalism.SyntacticObjects
import Linglib.Theories.Minimalism.Containment
import Linglib.Theories.Minimalism.Labeling
import Linglib.Theories.Minimalism.HeadMovement.Basic
import Linglib.Theories.Minimalism.Constraints.HMC
import Linglib.Theories.Minimalism.HeadMovement.BulgarianLHM
import Linglib.Theories.Minimalism.HeadMovement.GermanicV2
import Linglib.Theories.Minimalism.Agree
import Linglib.Theories.Minimalism.Coreference

import Linglib.Theories.DependencyGrammar.Basic
import Linglib.Theories.DependencyGrammar.LexicalRules
import Linglib.Theories.DependencyGrammar.Inversion
import Linglib.Theories.DependencyGrammar.Coordination
import Linglib.Theories.DependencyGrammar.LongDistance
import Linglib.Theories.DependencyGrammar.Coreference

import Linglib.Theories.CCG.Basic
import Linglib.Theories.CCG.Semantics
import Linglib.Theories.CCG.Coordination
import Linglib.Theories.CCG.Interpret
import Linglib.Theories.CCG.TruthConditions
import Linglib.Theories.CCG.Homomorphism
import Linglib.Theories.CCG.Combinators
import Linglib.Theories.CCG.Intonation

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Quantifiers
import Linglib.Theories.Montague.Attitudes
import Linglib.Theories.Montague.Modality
import Linglib.Theories.Montague.Derivations
import Linglib.Theories.Montague.SemanticBackendInstance
import Linglib.Theories.Montague.SyntaxInterface

import Linglib.Theories.Montague.Numbers
import Linglib.Theories.Montague.Scales
import Linglib.Theories.Montague.Entailment
import Linglib.Theories.Montague.Lexicon
import Linglib.Theories.Montague.SemDerivation
import Linglib.Theories.Montague.Scope

import Linglib.Theories.NeoGricean.Basic
import Linglib.Theories.NeoGricean.Competence
import Linglib.Theories.NeoGricean.Alternatives
import Linglib.Theories.NeoGricean.ScalarImplicatures

import Linglib.Theories.RSA.Basic
import Linglib.Theories.RSA.GoodmanStuhlmuller2013
import Linglib.Theories.RSA.FrankGoodman2012
import Linglib.Theories.RSA.ScalarImplicatures
import Linglib.Theories.RSA.ScontrasPearl2021

import Linglib.Theories.PragmaticComparison

-- Cross-theoretic comparisons
import Linglib.Theories.Comparisons.Coreference
import Linglib.Theories.Comparisons.ScalarImplicature
import Linglib.Theories.Comparisons.CommandRelations
import Linglib.Theories.Comparisons.Implicature

import Linglib.Theories.Surface.Basic

-- Coreference patterns
import Linglib.Phenomena.Coreference.Data

-- Pragmatic phenomena (theory-neutral examples)
import Linglib.Phenomena.ScalarImplicatures.Data
import Linglib.Phenomena.FreeChoice.Data
import Linglib.Phenomena.DisjunctionIgnorance.Data

-- Experimental studies on scalar implicatures
import Linglib.Phenomena.GeurtsPouscoulous2009.Data

-- Quantifier scope ambiguity (Scontras & Pearl 2021)
import Linglib.Phenomena.ScontrasPearl2021.Data

-- Semantic phenomena
import Linglib.Phenomena.Semantics.Entailments
import Linglib.Phenomena.Semantics.Monotonicity
import Linglib.Phenomena.Semantics.TruthConditions

-- Word order alternations (verb position, etc.)
import Linglib.Phenomena.WordOrderAlternations.VerbPosition.Data
