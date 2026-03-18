import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.ThreeValuedLogic
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding
import Linglib.Theories.Semantics.Presupposition.TonhauserDerivation
import Linglib.Theories.Semantics.Presupposition.Transparency
import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Theories.Semantics.Presupposition.Heritage
import Linglib.Theories.Semantics.Presupposition.Accommodation
import Linglib.Theories.Semantics.Presupposition.DynamicBridge

/-!
# Presupposition Theory — Unified API
@cite{beaver-2001} @cite{heim-1983} @cite{schlenker-2009} @cite{karttunen-peters-1979}

This module re-exports all presupposition-related modules for convenient import.
Import `Linglib.Theories.Semantics.Presupposition.Unified` to get access to:

## Core Types (from `Core.Semantics.Presupposition`)
- `PrProp W` — partial/presuppositional propositions
- `Truth3` — three-valued truth (from `Core.Logic.Truth3`)
- Connective systems: classical, filtering, Belnap, flexible accommodation

## Projection Theories (from `Theories.Semantics.Presupposition.*`)
- **Local contexts** (@cite{schlenker-2009}): `LocalCtx`, `localCtxConsequent`, etc.
- **Heritage functions** (@cite{karttunen-peters-1979}): `HeritageSystem`, bridge theorems
- **Transparency** (@cite{schlenker-2007}): `transparent`, `meetMiddle`-based proofs
- **Belief embedding**: `BeliefLocalCtx`, OLE derivation

## Accommodation (from `Theories.Semantics.Presupposition.Accommodation`)
- `AccommodationLevel` (global/local/intermediate)
- `AccommodationStrategy` (Heim/Lewis, van der Sandt, Fauconnier)
- `AccommodationConstraints` (informativity, consistency, trapping)
- `heimSelect` — Heim's preference-based accommodation level selection
- `TriggerClass` — anaphoric vs. lexical triggers

## Dynamic Bridge (from `Theories.Semantics.Presupposition.DynamicBridge`)
- `PrProp.toCCP` — convert static PrProp to dynamic CCP
- `PrProp.presupTest` / `PrProp.assertFilter` — decomposed CCP components
- `impFilter_presup_matches_local_context` — static = dynamic agreement

## Taxonomy (from `Theories.Semantics.Presupposition.TonhauserDerivation`)
- `SCF_Requires` / `SCF_Allows` — strong contextual felicity classification
- `OLE_Obligatory` / `OLE_NotObligatory` — obligatory local effect
- Derivation theorems connecting local contexts to the four-class taxonomy

## Ontological (from `Theories.Semantics.Presupposition.OntologicalPreconditions`)
- `EventPhase` — presuppositions as event preconditions (@cite{roberts-simons-2024})

## Three-Valued Logic (from `Core.Logic.ThreeValuedLogic`)
- `LP`/`K3`/`MK` consequence relations
- `mkEval` — Middle Kleene evaluation (asymmetric connectives)
- Metatheory: no tautologies, duality, asymmetry
-/
