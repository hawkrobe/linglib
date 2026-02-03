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
import Linglib.Core.Proposition
import Linglib.Core.SatisfactionOrdering
import Linglib.Core.Presupposition
import Linglib.Core.CommonGround
import Linglib.Core.Analyticity

-- Dynamic semantics core (InfoState, CCP, update operations)
import Linglib.Theories.DynamicSemantics.Core.Basic
import Linglib.Theories.DynamicSemantics.Core.Update

-- Team semantics (Aloni, Inquisitive Semantics infrastructure)
import Linglib.Core.TeamSemantics

-- Softmax infrastructure (Franke & Degen)
import Linglib.Core.Softmax.Basic
import Linglib.Core.Softmax.Limits
import Linglib.Core.Softmax.MaxEntropy

-- Fragments (pre-built RSA domains)
import Linglib.Theories.RSA.Domains.ReferenceGames
import Linglib.Theories.RSA.Domains.Quantities
import Linglib.Fragments.English.Scales
import Linglib.Fragments.English.PolarityItems
import Linglib.Theories.RSA.Domains.Degrees

-- RSA Core and Extensions
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Extensions.LexicalUncertainty.Basic
import Linglib.Theories.RSA.Extensions.LexicalUncertainty.Compositional

-- Theory interfaces (Mathlib pattern)
import Linglib.Core.Interfaces.CoreferenceTheory
import Linglib.Core.Interfaces.BindingSemantics
import Linglib.Core.Interfaces.ImplicatureTheory
import Linglib.Core.Interfaces.ScopeTheory
import Linglib.Core.Interfaces.SemanticStructure

-- Phenomena (empirical data)
-- Core infrastructure
import Linglib.Phenomena.Core
import Linglib.Phenomena.Basic  -- backwards-compat re-export
import Linglib.Phenomena.EmpiricalData  -- backwards-compat re-export

-- Agreement phenomena
import Linglib.Phenomena.Agreement.Basic
import Linglib.Phenomena.Agreement.Case
import Linglib.Phenomena.Agreement.DetNoun
import Linglib.Phenomena.BasicPhenomena.Proofs

-- Word order phenomena
import Linglib.Phenomena.WordOrder.Basic
import Linglib.Phenomena.WordOrder.SubjectAuxInversion
import Linglib.Phenomena.Coordination.Data

-- Dependencies phenomena
import Linglib.Phenomena.Dependencies.Basic
import Linglib.Phenomena.Dependencies.LongDistance
import Linglib.Phenomena.Dependencies.CrossSerial

-- Argument structure phenomena
import Linglib.Phenomena.ArgumentStructure.Subcategorization
import Linglib.Phenomena.ArgumentStructure.DativeAlternation
import Linglib.Phenomena.ArgumentStructure.Passive

-- RSA Studies (general RSA methodology papers)
import Linglib.Phenomena.RSAStudies.FrankGoodman2012
import Linglib.Phenomena.RSAStudies.KaoBergenGoodman2014
import Linglib.Phenomena.RSAStudies.ScontrasPearl2021
import Linglib.Phenomena.RSAStudies.HawkinsEtAl2025
import Linglib.Phenomena.RSAStudies.HawkinsGweonGoodman2021
import Linglib.Phenomena.RSAStudies.FrankeBergen2020
import Linglib.Phenomena.RSAStudies.GrusdtLassiterFranke2022
import Linglib.Phenomena.RSAStudies.SumersEtAl2023

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
import Linglib.Theories.Minimalism.Amalgamation
import Linglib.Theories.Minimalism.MergeUnification
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
import Linglib.Theories.Montague.Anaphora
import Linglib.Theories.Montague.Modification
import Linglib.Theories.Montague.Composition
import Linglib.Theories.Montague.Determiner.Quantifier
import Linglib.Theories.Montague.Verb.Attitude.Examples
import Linglib.Theories.Montague.Verb.Attitude.Doxastic
import Linglib.Theories.Montague.Verb.Attitude.Preferential
import Linglib.Theories.Montague.Verb.Attitude.CDistributivity
import Linglib.Theories.Montague.Verb.Attitude.Parasitic
import Linglib.Theories.Montague.Verb.Attitude.BuilderProperties
import Linglib.Theories.Montague.Numbers
import Linglib.Theories.Montague.Scales
import Linglib.Theories.Montague.Conjunction

-- Montague Lexicon
import Linglib.Theories.Montague.Core.Lexicon
import Linglib.Theories.Montague.Domain.Degree
import Linglib.Theories.Montague.Noun.Kind.Chierchia1998
import Linglib.Theories.Montague.Noun.Kind.Krifka2004
import Linglib.Theories.Montague.Noun.Kind.Dayal2004
import Linglib.Theories.Montague.Noun.Kind.Generics
import Linglib.Theories.Montague.Noun.Kind.Carlson1977

-- Montague Derivations
import Linglib.Theories.Montague.Core.Derivation
import Linglib.Theories.Montague.Derivation.TruthConditions
import Linglib.Theories.Montague.Derivation.Scope

-- Montague Intensional
import Linglib.Theories.Montague.Intensional.Basic

-- Montague Questions (G&S partition semantics, Inquisitive Semantics)
import Linglib.Theories.Montague.Question.Basic
import Linglib.Theories.Montague.Question.Partition
import Linglib.Theories.Montague.Question.Hamblin
import Linglib.Theories.Montague.Question.DecisionTheory
import Linglib.Theories.Montague.Question.Inquisitive
import Linglib.Theories.Montague.Question.ProbabilisticAnswerhood

-- Montague Entailment
import Linglib.Theories.Montague.Sentence.Entailment.Basic
import Linglib.Theories.Montague.Sentence.Entailment.Monotonicity
import Linglib.Theories.Montague.Sentence.Entailment.NegationTests
import Linglib.Theories.Montague.Sentence.Entailment.ScaleInteraction
import Linglib.Theories.Montague.Core.Polarity
import Linglib.Theories.Montague.Sentence.Entailment.AntiAdditivity
import Linglib.Theories.Montague.Sentence.Entailment.PresuppositionPolarity
import Linglib.Theories.Montague.Sentence.Presupposition.LocalContext
import Linglib.Theories.Montague.Sentence.Presupposition.BeliefEmbedding
import Linglib.Theories.Montague.Sentence.Presupposition.TonhauserDerivation

-- Montague Conditionals
import Linglib.Theories.Montague.Sentence.Conditional.Basic
import Linglib.Theories.Montague.Sentence.Conditional.Assertability
import Linglib.Theories.Montague.Sentence.Conditional.ConditionalType
import Linglib.Theories.Montague.Sentence.Conditional.LeftNested

-- Montague Particles (Additive: too, also, either)
import Linglib.Theories.Montague.Particle.Additive

-- Montague Interfaces
import Linglib.Theories.Montague.Interface.SemanticBackend
import Linglib.Theories.Montague.Interface.SyntaxInterface


-- Gradable adjective theories (threshold semantics, contrary antonyms)
import Linglib.Theories.Montague.Adjective.Theory

-- Modal theories (Kratzer vs Simple/Kripke)
import Linglib.Theories.Montague.Modal.Basic
import Linglib.Theories.Montague.Modal.Kratzer
import Linglib.Theories.Montague.Modal.PhillipsBrown
import Linglib.Theories.Montague.Modal.Simple
import Linglib.Theories.Montague.Modal.Compare

-- Plural semantics (distributivity, non-maximality)
import Linglib.Theories.Montague.Plural.Distributivity

-- NeoGricean Core
import Linglib.Theories.NeoGricean.Core.Basic
import Linglib.Theories.NeoGricean.Core.Competence
import Linglib.Theories.NeoGricean.Core.Alternatives
import Linglib.Theories.NeoGricean.Core.AlternativeGeneration
import Linglib.Theories.NeoGricean.Core.Markedness

-- NeoGricean Exhaustivity
import Linglib.Theories.NeoGricean.Exhaustivity.Basic

-- NeoGricean Scalar Implicatures
import Linglib.Theories.NeoGricean.ScalarImplicatures.Basic
import Linglib.Theories.NeoGricean.ScalarImplicatures.Operations

-- NeoGricean Implementations
import Linglib.Theories.NeoGricean.Implementations.Spector2007
import Linglib.Theories.NeoGricean.Implementations.FoxSpector2018
import Linglib.Theories.NeoGricean.Implementations.MontagueExhaustivity

-- NeoGricean other
import Linglib.Theories.NeoGricean.NegationScope
import Linglib.Theories.NeoGricean.Presuppositions
import Linglib.Theories.NeoGricean.Evaluativity

-- RSA Core
import Linglib.Theories.RSA.Core.BasicQ
import Linglib.Theories.RSA.Core.Intensional
import Linglib.Theories.RSA.Core.Model
-- RSA Scalar Implicatures
import Linglib.Theories.RSA.ScalarImplicatures.Basic
import Linglib.Theories.RSA.ScalarImplicatures.Hurford
import Linglib.Theories.RSA.ScalarImplicatures.Embedded.Basic
import Linglib.Theories.RSA.ScalarImplicatures.Embedded.Attitudes
import Linglib.Theories.RSA.ScalarImplicatures.Embedded.Conditionals
import Linglib.Theories.RSA.ScalarImplicatures.Embedded.Questions

-- RSA Implementations (paper replications)
import Linglib.Theories.RSA.Implementations.FrankGoodman2012
import Linglib.Theories.RSA.Implementations.GoodmanStuhlmuller2013
import Linglib.Theories.RSA.Implementations.ScontrasPearl2021
import Linglib.Theories.RSA.Implementations.KaoEtAl2014_Hyperbole
import Linglib.Theories.RSA.Implementations.KaoEtAl2014_Metaphor
import Linglib.Theories.RSA.Implementations.PottsEtAl2016
import Linglib.Theories.RSA.Implementations.ScontrasTonhauser2025
import Linglib.Theories.RSA.Implementations.TesslerGoodman2022
import Linglib.Theories.RSA.Implementations.HeKaiserIskarous2025
import Linglib.Theories.RSA.Implementations.TesslerFranke2020
import Linglib.Theories.RSA.Implementations.CremersWilcoxSpector2023
import Linglib.Theories.RSA.Implementations.FrankeBergen2020
import Linglib.Theories.RSA.Implementations.LassiterGoodman2017
import Linglib.Theories.RSA.Implementations.YoonEtAl2020
import Linglib.Theories.RSA.Implementations.HawkinsGweonGoodman2021
import Linglib.Theories.RSA.Implementations.WaldonDegen2021
import Linglib.Theories.RSA.Implementations.Franke2011
import Linglib.Theories.RSA.DegenEtAl2020

-- RSA Extensions: Information Theory (Zaslavsky et al. 2020)
import Linglib.Theories.RSA.Extensions.InformationTheory.Basic
import Linglib.Theories.RSA.Extensions.InformationTheory.UtilityDynamics
import Linglib.Theories.RSA.Extensions.InformationTheory.UtilityNonMonotonicity
import Linglib.Theories.RSA.Extensions.InformationTheory.PhaseTransition
import Linglib.Theories.RSA.Extensions.InformationTheory.RateDistortion

-- RSA with rational α (for α < 1)
import Linglib.Core.RationalPower

import Linglib.Theories.PragmaticComparison

-- Bilateral Update Semantics (Elliott & Sudo 2025)
import Linglib.Theories.BilateralUpdateSemantics.Basic
import Linglib.Theories.BilateralUpdateSemantics.FreeChoice

-- Causative Verbs (Nadathur & Lauer 2020)
import Linglib.Core.CausalModel
import Linglib.Theories.NadathurLauer2020.Basic

-- Cross-theoretic comparisons
import Linglib.Theories.Comparisons.Coreference
import Linglib.Theories.Comparisons.ScalarImplicature
import Linglib.Theories.Comparisons.CommandRelations
import Linglib.Theories.Comparisons.Implicature
import Linglib.Theories.Comparisons.RSANeoGricean
import Linglib.Theories.Comparisons.SauerlandRSA
import Linglib.Theories.Comparisons.FreeChoice.Compare
import Linglib.Theories.Comparisons.FreeChoice.Aloni2022

import Linglib.Theories.Surface.Basic

-- Anaphora patterns
import Linglib.Phenomena.Anaphora.DonkeyAnaphora
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Phenomena.Anaphora.CrossSentential
import Linglib.Phenomena.Anaphora.ModalSubordination
import Linglib.Phenomena.Anaphora.BathroomSentences

-- Scalar Implicatures
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013
import Linglib.Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009
import Linglib.Phenomena.ScalarImplicatures.Studies.VanTielEtAl2016
import Linglib.Phenomena.ScalarImplicatures.Studies.Ronai2024
import Linglib.Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021
import Linglib.Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023

-- Modality (free choice)
import Linglib.Phenomena.Modality.Basic
import Linglib.Phenomena.Modality.FreeChoice
import Linglib.Phenomena.Modality.Studies.FreeChoiceFarsi

-- Polarity (NPIs, disjunction ignorance, exceptives)
import Linglib.Phenomena.Polarity.Basic
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Polarity.DisjunctionIgnorance
import Linglib.Phenomena.Polarity.Exceptives

-- Presupposition
import Linglib.Phenomena.Presupposition.Basic
import Linglib.Phenomena.Presupposition.Diagnostics
import Linglib.Phenomena.Presupposition.ProjectiveContent
import Linglib.Phenomena.Presupposition.Studies.DegenTonhauser2021
import Linglib.Phenomena.Presupposition.Studies.ScontrasTonhauser2025

-- Parasitic attitudes → Anaphora
import Linglib.Phenomena.Anaphora.Studies.ParasiticAttitudes

-- Politeness
import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020

-- Additional presupposition studies
import Linglib.Phenomena.Presupposition.Studies.HeKaiserIskarous2025
import Linglib.Phenomena.Presupposition.Studies.LoGuercio2025

-- Quantification (scope freezing, numerals)
import Linglib.Phenomena.Quantification.Basic
import Linglib.Phenomena.Quantification.ScopeFreezing
import Linglib.Phenomena.Quantification.ScopeWordOrder
import Linglib.Phenomena.Quantification.Numerals

-- Entailment
import Linglib.Phenomena.Entailment.Basic
import Linglib.Phenomena.Entailment.Monotonicity

-- Negation
import Linglib.Phenomena.Negation.Basic
import Linglib.Phenomena.Negation.FlexibleNegation
import Linglib.Phenomena.Negation.DoubleNegation

-- Gradability (adjectives, vagueness, degrees)
import Linglib.Phenomena.Gradability.Basic
import Linglib.Phenomena.Gradability.Vagueness
import Linglib.Phenomena.Gradability.Adjectives
import Linglib.Phenomena.Gradability.ComparisonClass
import Linglib.Phenomena.Gradability.Evaluativity

-- Question-answer phenomena (G&S 1984, Van Rooy 2003)
import Linglib.Phenomena.Questions.Basic
import Linglib.Phenomena.Questions.WhComplement
import Linglib.Phenomena.Questions.FocusAnswer
import Linglib.Phenomena.Questions.Exhaustivity
import Linglib.Phenomena.Questions.MultipleWh
import Linglib.Phenomena.Questions.PolarAnswers
import Linglib.Phenomena.Questions.PragmaticAnswerhood
import Linglib.Phenomena.Questions.ScopeReadings
import Linglib.Phenomena.Questions.Coordination
import Linglib.Phenomena.Questions.MentionSome

-- Imprecision and homogeneity (Haslinger 2024)
import Linglib.Phenomena.Imprecision.Basic

-- Plurals (distributivity, non-maximality)
import Linglib.Phenomena.Plurals.Basic
import Linglib.Phenomena.Plurals.Studies.HaslingerEtAl2025

-- Word order alternations (verb position, etc.)
import Linglib.Phenomena.WordOrderAlternations.VerbPosition.Data

-- Conditional phenomena
import Linglib.Phenomena.Conditionals.Data
import Linglib.Phenomena.Conditionals.LeftNested
import Linglib.Phenomena.Conditionals.Studies.RamotowskaEtAl2025
import Linglib.Phenomena.Conditionals.Studies.SubordinateFuture

-- Additive particles (too, also, either) - Thomas (2026)
import Linglib.Phenomena.Additives.Data

-- Generics (bare plurals, kind reference)
import Linglib.Phenomena.Generics.Data
import Linglib.Phenomena.Generics.BarePlurals
import Linglib.Phenomena.Generics.KindReference

-- Ellipsis (sluicing, gapping, fragments)
import Linglib.Phenomena.Ellipsis.Sluicing
import Linglib.Phenomena.Ellipsis.Gapping
import Linglib.Phenomena.Ellipsis.FragmentAnswers

-- Plurals studies
import Linglib.Phenomena.Plurals.Studies.QingEtAl2025

-- Gradability studies
import Linglib.Phenomena.Gradability.Studies.KursatDegen2021
