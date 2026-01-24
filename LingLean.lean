/-
# LingLean

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
- Surface/: Simple constraint-checking grammar

### Phenomena/ - Empirical data (theory-independent)
- Basic: MinimalPair, PhenomenonData
- EmpiricalData: Data types, linking functions
- SubjectAuxInversion/, Coordination/, LongDistanceDependencies/

## Coverage Matrix

                    Coordination  Inversion  LongDistance
CCG                      ✓            -           -
HPSG                     -            ✓           -
Minimalism               -            ✓           -
DependencyGrammar        ✓            ✓           ✓
Montague                 -            -           -
RSA                      -            -           -

Missing Theories/X/Y.lean = conjecture (theory hasn't proven it handles Y)
-/

-- Core types and interfaces
import LingLean.Core.Basic
import LingLean.Core.Grammar
import LingLean.Core.SemanticTypes
import LingLean.Core.SemanticBackend

-- Phenomena (empirical data)
import LingLean.Phenomena.Basic
import LingLean.Phenomena.EmpiricalData
import LingLean.Phenomena.SubjectAuxInversion.Data
import LingLean.Phenomena.Coordination.Data
import LingLean.Phenomena.LongDistanceDependencies.Data

-- BasicPhenomena
import LingLean.Phenomena.BasicPhenomena.Agreement
import LingLean.Phenomena.BasicPhenomena.Case
import LingLean.Phenomena.BasicPhenomena.DativeAlternation
import LingLean.Phenomena.BasicPhenomena.DetNounAgreement
import LingLean.Phenomena.BasicPhenomena.Passive
import LingLean.Phenomena.BasicPhenomena.Subcategorization
import LingLean.Phenomena.BasicPhenomena.WordOrder
import LingLean.Phenomena.BasicPhenomena.Proofs

-- Theories
import LingLean.Theories.HPSG.Basic
import LingLean.Theories.HPSG.Features
import LingLean.Theories.HPSG.Inversion

import LingLean.Theories.Minimalism.Basic
import LingLean.Theories.Minimalism.Structure
import LingLean.Theories.Minimalism.Inversion

import LingLean.Theories.DependencyGrammar.Basic
import LingLean.Theories.DependencyGrammar.LexicalRules
import LingLean.Theories.DependencyGrammar.Inversion
import LingLean.Theories.DependencyGrammar.Coordination
import LingLean.Theories.DependencyGrammar.LongDistance

import LingLean.Theories.CCG.Basic
import LingLean.Theories.CCG.Semantics
import LingLean.Theories.CCG.Coordination

import LingLean.Theories.Montague.Basic

import LingLean.Theories.Surface.Basic
