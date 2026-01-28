/-
# Linglib

A Lean 4 library for formalizing syntactic theories from theoretical linguistics
and connecting them to computational pragmatics (RSA - Rational Speech Acts).

## Architecture

### Core/ - Shared types and interfaces
- Core.Basic: Word, Cat, ClauseType, Lexicon
- Core.Grammar: Abstract Grammar typeclass
- Core.Pipeline: Theory composition (provides/requires)

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
import Linglib.Core.Pipeline
import Linglib.Core.InformationStructure
import Linglib.Core.FormalLanguageTheory
import Linglib.Core.QUD
import Linglib.Core.Polarity
import Linglib.Core.Proposition
import Linglib.Core.Presupposition
import Linglib.Core.CommonGround

-- Fragments (pre-built RSA domains)
import Linglib.Fragments.ReferenceGames
import Linglib.Fragments.Quantities
import Linglib.Fragments.Scales

-- RSA Core and Lexical Uncertainty
import Linglib.Theories.RSA.Core
import Linglib.Theories.RSA.LexicalUncertainty.Basic
import Linglib.Theories.RSA.LexicalUncertainty.Compositional

-- Theory interfaces (Mathlib pattern)
import Linglib.Core.Interfaces.CoreferenceTheory
import Linglib.Core.Interfaces.ImplicatureTheory
import Linglib.Core.Interfaces.ScopeTheory
import Linglib.Core.Interfaces.SemanticStructure

-- Phenomena (empirical data)
import Linglib.Phenomena.Basic
import Linglib.Phenomena.EmpiricalData
import Linglib.Phenomena.SubjectAuxInversion.Data
import Linglib.Phenomena.Coordination.Data
import Linglib.Phenomena.LongDistanceDependencies.Data
import Linglib.Phenomena.CrossSerialDependencies.Data
import Linglib.Phenomena.Gapping.Data
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
import Linglib.Theories.Minimalism.Semantics.Interface
import Linglib.Theories.Minimalism.Semantics.RelativeClauses

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
import Linglib.Theories.CCG.Scope
import Linglib.Theories.CCG.CrossSerial
import Linglib.Theories.CCG.GenerativeCapacity
import Linglib.Theories.CCG.Gapping
import Linglib.Theories.CCG.Equivalence

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Variables
import Linglib.Theories.Montague.Modification
import Linglib.Theories.Montague.Composition
import Linglib.Theories.Montague.Quantifiers
import Linglib.Theories.Montague.Attitudes
import Linglib.Theories.Montague.Modality
import Linglib.Theories.Montague.Numbers
import Linglib.Theories.Montague.Scales
import Linglib.Theories.Montague.Conjunction

-- Montague Lexicon
import Linglib.Theories.Montague.Lexicon.Basic

-- Montague Derivations
import Linglib.Theories.Montague.Derivation.Basic
import Linglib.Theories.Montague.Derivation.TruthConditions
import Linglib.Theories.Montague.Derivation.Scope

-- Montague Intensional
import Linglib.Theories.Montague.Intensional.Basic

-- Montague Entailment
import Linglib.Theories.Montague.Entailment.Basic
import Linglib.Theories.Montague.Entailment.Monotonicity
import Linglib.Theories.Montague.Entailment.ScaleInteraction
import Linglib.Theories.Montague.Entailment.Polarity
import Linglib.Theories.Montague.Entailment.PresuppositionPolarity
import Linglib.Theories.Montague.Projection.LocalContext
import Linglib.Theories.Montague.Projection.BeliefEmbedding
import Linglib.Theories.Montague.Projection.TonhauserDerivation

-- Montague Interfaces
import Linglib.Theories.Montague.Interface.SemanticBackend
import Linglib.Theories.Montague.Interface.SyntaxInterface


-- Modal theories (Kratzer vs Simple/Kripke)
import Linglib.Theories.Montague.Lexicon.Modals.Theory
import Linglib.Theories.Montague.Lexicon.Modals.Kratzer
import Linglib.Theories.Montague.Lexicon.Modals.Simple
import Linglib.Theories.Montague.Lexicon.Modals.Compare

import Linglib.Theories.NeoGricean.Basic
import Linglib.Theories.NeoGricean.Competence
import Linglib.Theories.NeoGricean.Alternatives
import Linglib.Theories.NeoGricean.ScalarImplicatures
import Linglib.Theories.NeoGricean.Exhaustivity
import Linglib.Theories.NeoGricean.Spector2007
import Linglib.Theories.NeoGricean.FoxSpector2018
import Linglib.Theories.NeoGricean.Presuppositions

import Linglib.Theories.RSA.Basic
import Linglib.Theories.RSA.GoodmanStuhlmuller2013
import Linglib.Theories.RSA.FrankGoodman2012
import Linglib.Theories.RSA.ScalarImplicatures
import Linglib.Theories.RSA.ScontrasPearl2021
import Linglib.Theories.RSA.Intensional
import Linglib.Theories.RSA.EmbeddedScalars
import Linglib.Theories.RSA.PottsLU
import Linglib.Theories.RSA.AttitudeEmbedding
import Linglib.Theories.RSA.ConditionalEmbedding
import Linglib.Theories.RSA.QuestionEmbedding
import Linglib.Theories.RSA.KaoEtAl2014

-- RSA BToM (Bayesian Theory of Mind) framework
import Linglib.Theories.RSA.BToM.Core
import Linglib.Theories.RSA.BToM.ScontrasTonhauser2025

-- RSA Information Theory (Zaslavsky et al. 2020)
import Linglib.Theories.RSA.InformationTheory.Basic
import Linglib.Theories.RSA.InformationTheory.UtilityDynamics
import Linglib.Theories.RSA.InformationTheory.UtilityNonMonotonicity
import Linglib.Theories.RSA.InformationTheory.PhaseTransition

-- RSA with rational α (for α < 1)
import Linglib.Core.RationalPower
import Linglib.Theories.RSA.CoreQ

import Linglib.Theories.PragmaticComparison

-- Cross-theoretic comparisons
import Linglib.Theories.Comparisons.Coreference
import Linglib.Theories.Comparisons.ScalarImplicature
import Linglib.Theories.Comparisons.CommandRelations
import Linglib.Theories.Comparisons.Implicature
import Linglib.Theories.Comparisons.RSANeoGricean
import Linglib.Theories.Comparisons.SauerlandRSA

import Linglib.Theories.Surface.Basic

-- Coreference patterns
import Linglib.Phenomena.Coreference.Data

-- Pragmatic phenomena (theory-neutral examples)
import Linglib.Phenomena.ScalarImplicatures.Data
import Linglib.Phenomena.FreeChoice.Data
import Linglib.Phenomena.DisjunctionIgnorance.Data
import Linglib.Phenomena.Presuppositions.Data
import Linglib.Phenomena.Presuppositions.ProjectiveContent

-- Experimental studies on scalar implicatures
import Linglib.Phenomena.GeurtsPouscoulous2009.Data

-- Factive predicates empirical data
import Linglib.Phenomena.Factives.DegenTonhauser2021

-- Projection empirical data
import Linglib.Phenomena.Projection.ScontrasTonhauser2025

-- Quantifier scope ambiguity (Scontras & Pearl 2021)
import Linglib.Phenomena.ScontrasPearl2021.Data

-- Scope-word order interactions (Dutch/German)
import Linglib.Phenomena.ScopeWordOrder.Data

-- Semantic phenomena
import Linglib.Phenomena.Semantics.Entailments
import Linglib.Phenomena.Semantics.Monotonicity
import Linglib.Phenomena.Semantics.TruthConditions

-- Adjective semantics (Kamp 1975, Partee 1995, 2001)
import Linglib.Phenomena.Adjectives.Data

-- Imprecision and homogeneity (Haslinger 2024)
import Linglib.Phenomena.Imprecision.Basic

-- Word order alternations (verb position, etc.)
import Linglib.Phenomena.WordOrderAlternations.VerbPosition.Data
