/-
# LingLean: Formal Foundations for Computational Linguistics

A Lean 4 library for formalizing syntactic theories and connecting them
to computational pragmatics.

## Organization

- `LingLean.Syntax`: Syntactic frameworks (HPSG, Minimalism, etc.)
- `LingLean.Semantics`: Semantic types and the RSA backend interface
- `LingLean.Phenomena`: Empirical phenomena with data and analyses
-/

-- Syntax
import LingLean.Syntax.Basic
import LingLean.Syntax.Grammar
import LingLean.Syntax.HPSG.Basic
import LingLean.Syntax.HPSG.Features
import LingLean.Syntax.HPSG.Inversion
import LingLean.Syntax.Minimalism.Basic
import LingLean.Syntax.Minimalism.Structure
import LingLean.Syntax.Minimalism.Inversion

-- Dependency Grammar (Gibson Chapter 3)
import LingLean.Syntax.DependencyGrammar.Basic
import LingLean.Syntax.DependencyGrammar.Examples
import LingLean.Syntax.DependencyGrammar.LexicalRules
import LingLean.Syntax.DependencyGrammar.Proofs

-- CCG
import LingLean.Syntax.CCG.Basic
import LingLean.Syntax.CCG.Semantics

-- Semantics
import LingLean.Semantics.Basic
import LingLean.Semantics.Backend
import LingLean.Semantics.Montague

-- Phenomena
import LingLean.Phenomena.Basic
import LingLean.Phenomena.EmpiricalData
import LingLean.Phenomena.SubjectAuxInversion.Data
import LingLean.Phenomena.SubjectAuxInversion.HPSG
import LingLean.Phenomena.SubjectAuxInversion.Minimalism
import LingLean.Phenomena.SubjectAuxInversion.WordGrammar
import LingLean.Phenomena.LongDistanceDependencies.Data
import LingLean.Phenomena.LongDistanceDependencies.WordGrammar
import LingLean.Phenomena.Coordination.Data
import LingLean.Phenomena.Coordination.WordGrammar
import LingLean.Phenomena.Coordination.CCG

-- Basic Phenomena
import LingLean.Phenomena.BasicPhenomena.Agreement
import LingLean.Phenomena.BasicPhenomena.Case
import LingLean.Phenomena.BasicPhenomena.DativeAlternation
import LingLean.Phenomena.BasicPhenomena.DetNounAgreement
import LingLean.Phenomena.BasicPhenomena.Passive
import LingLean.Phenomena.BasicPhenomena.Subcategorization
import LingLean.Phenomena.BasicPhenomena.WordOrder
