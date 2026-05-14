/-!
# Islands: Descriptive Vocabulary

Cross-paper substrate types for classifying island constraints. Each island
study (`Studies/AuthorYear.lean`) populates these classifications from its
own theoretical commitments; the types themselves are theory-neutral
descriptive labels.

## Types

- `ConstraintType` — Ross 1967's foundational island-constraint inventory
  (CNPC, adjunct, coordinate, subject, sentential subject) plus later
  extensions (manner-of-speaking, definite nominal).
- `ConstraintStrength` — strong (categorical) vs weak (ameliorated by
  D-linking, processing, or other factors).
- `IslandSource` — the *mechanism* a study attributes the island to:
  syntactic (PIC, subjacency, AL), semantic (binding, Specificity Condition),
  processing (memory/retrieval), discourse (information-structural
  backgroundedness).

## Why this file exists

These enums were originally hosted in `Studies/Ross1967.lean`, which forced
every consumer (across Islands/, Questions/, FillerGap/, ArgumentStructure/)
to transitively import Ross's empirical apparatus just to obtain the
classification types. Promoting them to a phenomenon-level data file
matches the CLAUDE.md "Data files (top level)" pattern: no imports from
`Theories/`, shared facts any theory must account for.

## Consumers

Files that classify islands using these types include:
- `Studies/Adger2025.lean` — Angular Locality (graph-theoretic)
- `Studies/ShenHuang2026.lean` — PIC + Specificity composite
- `Studies/CartnerEtAl2026.lean` — cross-constructional invariance
- `Studies/HofmeisterSag2010.lean` — processing/gradient
- `Phenomena/Islands/MannerOfSpeaking.lean` — discourse backgroundedness
- `Phenomena/Questions/Studies/ChanShen2026.lean` — semantic
- `Phenomena/FillerGap/Studies/LuPanDegen2025.lean` — backgroundedness
-/

namespace Phenomena.Islands

/-- Types of island constraints (descriptive labels). Ross's foundational
    five plus later additions (MoS verbs, definite nominals). -/
inductive ConstraintType where
  /-- Wh-word blocks further wh-dependency. -/
  | embeddedQuestion
  /-- Complex NP blocks dependency (Ross 1967). -/
  | complexNP
  /-- Adjunct clause blocks dependency. -/
  | adjunct
  /-- Coordination blocks asymmetric dependency (CSC). -/
  | coordinate
  /-- Subject position blocks dependency. -/
  | subject
  /-- Sentential subject blocks dependency. -/
  | sententialSubject
  /-- MoS verb complement backgrounds content (@cite{lu-pan-degen-2025}). -/
  | mannerOfSpeaking
  /-- Definite/specific DP blocks dependency
      (@cite{chomsky-1973}, @cite{shen-huang-2026}). -/
  | definiteNominal
  deriving Repr, DecidableEq

/-- Constraint strength classification. -/
inductive ConstraintStrength where
  /-- Consistently blocks the dependency. -/
  | strong
  /-- Ameliorated in some contexts (D-linking, processing facilitation,
      stage-level subjects, etc.). -/
  | weak
  deriving Repr, DecidableEq

/-- Source of an island constraint: what mechanism produces it.
Distinguishes structural accounts (subjacency, PIC, Angular Locality),
processing accounts (memory load), semantic accounts (binding restrictions),
and discourse accounts (information structure).

These are descriptive labels for the mechanism — the classification of
which source applies to which island type is a theoretical claim, derived
in individual study files from their theoretical commitments. -/
inductive IslandSource where
  /-- Syntactic: island follows from structural configuration
      (PIC, subjacency, Angular Locality). -/
  | syntactic
  /-- Semantic: island follows from a binding restriction
      (Specificity Condition). -/
  | semantic
  /-- Processing: island is an artifact of memory/retrieval difficulty. -/
  | processing
  /-- Discourse: island arises from information-structural backgroundedness
      (@cite{goldberg-2006}, @cite{lu-pan-degen-2025}). -/
  | discourse
  deriving Repr, DecidableEq

end Phenomena.Islands

-- Re-export at the top level so the existing consumer pattern
-- `import Linglib.Phenomena.Islands.Studies.Ross1967` (which transitively
-- imports this file) continues to expose the enum constructors as
-- `IslandSource.syntactic`, `ConstraintStrength.weak`, etc. without any
-- consumer-side `open` or namespace qualification.
export Phenomena.Islands (ConstraintType ConstraintStrength IslandSource)
