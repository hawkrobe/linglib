import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Core.Genericity

/-!
# @cite{del-prete-2013} — Imperfectivity and Habituality in Italian

In *Genericity* (Mari, Beyssade, Del Prete eds.), OUP, Oxford Studies in
Theoretical Linguistics 43.

## Core Claim

The Italian Imperfetto (imperfective past) can have both habitual (HAB) and
progressive (PROG) readings, whereas the passato remoto (perfective past)
forces an episodic reading. @cite{del-prete-2013} proposes a **non-quantificational**,
plurality-based analysis of the HAB reading: rather than positing a covert
generic quantifier GEN, HAB readings arise from event plurality under the
Lexical Cumulativity Hypothesis (verbs inherently refer to plural events)
combined with IMPF's forward expansion of the reference time in a Partial
Branching Time model.

## What This File Formalizes

This file captures a **background observation** of the chapter: imperfective
aspect is a prerequisite for habitual/generic readings, while perfective
blocks them. The chapter's deeper contribution — the non-quantificational
event-plurality analysis — is not yet formalized here.

## Italian Evidence

The Imperfetto allows HAB and PROG readings; the passato remoto does not:

- "Gianni leggeva il giornale" (Gianni read-IMPF the newspaper) — HAB or PROG
- "Gianni guidava un'auto sportiva" (Gianni drove-IMPF a sports car) — HAB or PROG

The illustrative examples below demonstrate the imperfective/perfective
contrast that the chapter takes as established background.

## Connection to Existing Infrastructure

- `ViewpointType` / `ViewpointAspectB` in `Aspect/Core.lean`:
  the imperfective/perfective distinction
- `GenericReading` in `Core/Genericity.lean`: the reading that
  imperfective enables and perfective blocks
- `IMPF` / `PRFV` operators in `Aspect/Core.lean`: the formal
  interval relations that underlie the distinction
-/

namespace Phenomena.Generics.Studies.DelPrete2013

open Semantics.Tense.Aspect.Core (ViewpointAspectB)
open Core.Genericity (GenericReading)

-- ═══ Aspect–Reading Compatibility ═══

/-- Whether a given viewpoint aspect permits a generic reading.

    @cite{del-prete-2013}: imperfective permits generic and habitual;
    perfective forces episodic. -/
def permitsGenericReading : ViewpointAspectB → Bool
  | .imperfective => true
  | .perfective => false

/-- Imperfective permits generics; perfective does not. -/
theorem imperfective_permits_generic :
    permitsGenericReading .imperfective = true ∧
    permitsGenericReading .perfective = false :=
  ⟨rfl, rfl⟩

-- ═══ Italian Data ═══

/-- An Italian aspect-genericity datum. -/
structure ItalianDatum where
  italian : String
  gloss : String
  aspect : ViewpointAspectB
  genericOK : Bool
  habitualOK : Bool
  episodicOK : Bool
  source : String
  deriving Repr

/-- "Maria cantava bene" — imperfetto: generic and habitual readings OK. -/
def mariaCantava : ItalianDatum :=
  { italian := "Maria cantava bene"
  , gloss := "Maria sang-IMPF well"
  , aspect := .imperfective
  , genericOK := true
  , habitualOK := true
  , episodicOK := true
  , source := "illustrative (cf. Del Prete 2013)"
  }

/-- "Maria cantò bene" — passato remoto: only episodic. -/
def mariaCanto : ItalianDatum :=
  { italian := "Maria cantò bene"
  , gloss := "Maria sang-PFV well"
  , aspect := .perfective
  , genericOK := false
  , habitualOK := false
  , episodicOK := true
  , source := "illustrative (cf. Del Prete 2013)"
  }

/-- "I cani abbaiavano" — imperfetto: generic reading of bare DP. -/
def iCaniAbbaiavano : ItalianDatum :=
  { italian := "I cani abbaiavano"
  , gloss := "The dogs barked-IMPF"
  , aspect := .imperfective
  , genericOK := true
  , habitualOK := true
  , episodicOK := true
  , source := "illustrative (cf. Del Prete 2013)"
  }

/-- "I cani abbaiarono" — passato remoto: episodic only. -/
def iCaniAbbaiarono : ItalianDatum :=
  { italian := "I cani abbaiarono"
  , gloss := "The dogs barked-PFV"
  , aspect := .perfective
  , genericOK := false
  , habitualOK := false
  , episodicOK := true
  , source := "illustrative (cf. Del Prete 2013)"
  }

def italianData : List ItalianDatum :=
  [mariaCantava, mariaCanto, iCaniAbbaiavano, iCaniAbbaiarono]

-- ═══ Theory–Data Bridge ═══

/-- The theory (`permitsGenericReading`) correctly predicts each datum. -/
theorem theory_predicts_data :
    italianData.all (λ d => permitsGenericReading d.aspect == d.genericOK) := by
  native_decide

/-- Imperfective data always permits generics; perfective data never does. -/
theorem aspect_determines_generic_availability :
    (italianData.filter (λ d => d.aspect == .imperfective)).all
      (λ d => d.genericOK) ∧
    (italianData.filter (λ d => d.aspect == .perfective)).all
      (λ d => !d.genericOK) := by
  native_decide

/-- Perfective blocks both generic and habitual readings simultaneously. -/
theorem perfective_blocks_both :
    (italianData.filter (λ d => d.aspect == .perfective)).all
      (λ d => !d.genericOK && !d.habitualOK) := by
  native_decide

/-- Episodic reading is always available regardless of aspect. -/
theorem episodic_always_available :
    italianData.all (λ d => d.episodicOK) := by
  native_decide

end Phenomena.Generics.Studies.DelPrete2013
