/-
# Existential Free Choice Items: Exhaustification Framework

Formalization of @cite{alonso-ovalle-moghiseh-2025} analysis of EFCIs,
based on @cite{chierchia-2013} exhaustification with domain alternatives.

## Key Concepts

### Two Types of Alternatives
1. Scalar alternatives: Stronger quantificational force (some → all)
2. Domain alternatives: Subdomain restrictions (D → D')

### Pre-exhaustified Domain Alternatives
Domain alternatives are pre-exhaustified via innocent exclusion:
- Original: ∃x∈D. P(x)
- Domain alt for d: ∃x∈{d}. P(x) = P(d)
- Pre-exh'd: P(d) ∧ ∀y≠d. ¬P(y) = "exactly d satisfies P"

### The EFCI puzzle
Without rescue mechanisms, exhaustifying both alt types causes contradiction:
- Scalar negation: ¬∀x. P(x)
- Domain negation: ∀d. ¬[P(d) ∧ ∀y≠d. ¬P(y)]

Combined with assertion ∃x. P(x), this yields ⊥.

### Rescue Mechanisms
1. Modal insertion: Insert covert ◇ (irgendein)
2. Partial exhaustification: Prune one alt type (yek-i)

-/

import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Phenomena.Polarity.Studies.Chierchia2013
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Basic

namespace AlonsoOvalleMoghiseh2025

open Exhaustification

/--
Types of alternatives for EFCIs.

Scalar alternatives differ in quantificational force.
Domain alternatives differ in domain restriction.
-/
inductive AlternativeType where
  /-- Scalar alternatives: some vs all -/
  | scalar
  /-- Domain alternatives: ∃x∈D vs ∃x∈D' for D' ⊂ D -/
  | domain
  deriving DecidableEq, Repr

/--
An EFCI alternative with its type and whether it's pre-exhaustified.
-/
structure EFCIAlternative (World : Type*) where
  /-- The propositional content -/
  content : Set World
  /-- The type of alternative -/
  altType : AlternativeType
  /-- Is this a pre-exhaustified domain alternative? -/
  isPreExhaustified : Bool


/-!
## Domain Alternatives

For an existential over domain D, domain alternatives are existentials
over proper subsets D' ⊂ D.

Singleton subdomain alternatives are most relevant:
- ∃x∈{d}. P(x) = P(d)

These become the basis for pre-exhaustified alternatives.
-/

variable {World : Type*} {Entity : Type*}

/--
A domain: a set of entities that an existential quantifies over.
-/
abbrev Domain (Entity : Type*) := Set Entity

/--
Generate singleton subdomain alternatives.
For domain D = {a, b, c}, generates {a}, {b}, {c}.
-/
def singletonSubdomains (D : Domain Entity) : Set (Domain Entity) :=
  { S | ∃ d ∈ D, S = {d} }

/--
The existential assertion over a domain.
∃x∈D. P(x) holds at world w iff some entity in D satisfies P at w.
-/
def existsInDomain (D : Domain Entity) (P : Entity → Set World) : Set World :=
  λ w => ∃ d ∈ D, P d w

/--
A singleton domain alternative.
∃x∈{d}. P(x) = P(d)
-/
def singletonAlt (d : Entity) (P : Entity → Set World) : Set World :=
  P d


/-!
## Pre-Exhaustified Domain Alternatives

Following @cite{chierchia-2013}, domain alternatives are pre-exhaustified:
the exhaustification operator applies to them before they enter the
alternative set for the main exhaustification.

For singleton alternative P(d):
  Pre-exh(P(d)) = P(d) ∧ ∀y≠d. ¬P(y)
                = "d is the only one satisfying P"

Domain alternatives convey uniqueness.
-/

/--
Pre-exhaustify a singleton domain alternative.
P(d) becomes: P(d) ∧ ∀y∈D, y≠d → ¬P(y)
"d is the unique satisfier in D"
-/
def preExhaustify (D : Domain Entity) (d : Entity) (P : Entity → Set World) : Set World :=
  λ w => P d w ∧ ∀ y ∈ D, y ≠ d → ¬(P y w)

/--
The set of pre-exhaustified domain alternatives.
-/
def preExhDomainAlts (D : Domain Entity) (P : Entity → Set World) : Set (Set World) :=
  { φ | ∃ d ∈ D, φ = preExhaustify D d P }


/-!
## Scalar Alternatives

For an existential ∃x. P(x), the scalar alternative is ∀x. P(x).

In UE contexts: ∀ is stronger than ∃
In DE contexts: ∃ is stronger than ∀
-/

/--
The universal (scalar) alternative to an existential.
-/
def universalAlt (D : Domain Entity) (P : Entity → Set World) : Set World :=
  λ w => ∀ d ∈ D, P d w

/--
The scalar alternative set for an existential.
-/
def scalarAlts (D : Domain Entity) (P : Entity → Set World) : Set (Set World) :=
  { universalAlt D P }


/--
The full EFCI alternative set combines:
1. The prejacent (existential assertion)
2. Scalar alternatives (universal)
3. Pre-exhaustified domain alternatives
-/
def efciAlternatives (D : Domain Entity) (P : Entity → Set World) : Set (Set World) :=
  {existsInDomain D P} ∪ scalarAlts D P ∪ preExhDomainAlts D P

/--
Alternative set with only scalar alternatives (pruned domain).
Used when partial exhaustification prunes domain alternatives.
-/
def scalarOnlyAlts (D : Domain Entity) (P : Entity → Set World) : Set (Set World) :=
  {existsInDomain D P} ∪ scalarAlts D P

/--
Alternative set with only domain alternatives (pruned scalar).
Used when partial exhaustification prunes scalar alternatives.
-/
def domainOnlyAlts (D : Domain Entity) (P : Entity → Set World) : Set (Set World) :=
  {existsInDomain D P} ∪ preExhDomainAlts D P


/-!
## Exhaustification Operator

O_ALT(φ) = φ ∧ ∧{¬ψ : ψ ∈ IE(ALT, φ)}

where IE(ALT, φ) is the set of innocently excludable alternatives.

An alternative ψ is innocently excludable if:
- ψ is in ALT
- ψ is stronger than φ
- Negating ψ is consistent with φ and negations of other IE alternatives
-/

/--
Simple exhaustification: negate all stronger alternatives.
This is a simplified version; full IE requires MC-set computation.
-/
def simpleExh (ALT : Set (Set World)) (φ : Set World) : Set World :=
  λ w => φ w ∧ ∀ ψ ∈ ALT, (∀ v, φ v → ψ v) → ψ ≠ φ → ¬(ψ w)


/-!
## The Problem: Exhaustifying Both Types Causes Contradiction

Consider domain D = {a, b} and predicate "came":

1. Prejacent: ∃x∈{a,b}. came(x) = "a came ∨ b came"

2. Scalar alt: ∀x∈{a,b}. came(x) = "a came ∧ b came"
   After exh: ¬(a came ∧ b came) = "not both came"

3. Pre-exh domain alts:
   - [a]: came(a) ∧ ¬came(b) = "only a came"
   - [b]: came(b) ∧ ¬came(a) = "only b came"
   After exh: ¬[only a] ∧ ¬[only b]
            = (came(a) → came(b)) ∧ (came(b) → came(a))
            = came(a) ↔ came(b)

Combined with prejacent (a ∨ b) and scalar neg ¬(a ∧ b):
- (a ∨ b) ∧ ¬(a ∧ b) ∧ (a ↔ b)
- = (a ∨ b) ∧ (a ⊕ b) ∧ (a ↔ b)
- = ⊥

This is why EFCIs need rescue mechanisms.
-/

/--
Check if an alternative set leads to contradiction when exhaustified.
-/
def isContradictory (ALT : Set (Set World)) (φ : Set World) : Prop :=
  ∀ w, ¬(simpleExh ALT φ w)


/-!
## Rescue Mechanism 1: Modal Insertion (Irgendein-type)

Insert a covert epistemic modal ◇_epi above the existential:
  ◇∃x. P(x)

Now domain alternatives become:
  ◇[P(a) ∧ ∀y≠a. ¬P(y)]

Under modal, these are compatible with each other:
  ◇[only a] ∧ ◇[only b]
= "possibly only a, possibly only b"
= modal variation

No contradiction!
-/

/--
Covert epistemic modal (possibility).
-/
def covertEpi (φ : Set World) : Set World :=
  λ _ => ∃ w, φ w

/--
Modal insertion: wrap existential in covert epistemic.
-/
def withModalInsertion (D : Domain Entity) (P : Entity → Set World) : Set World :=
  covertEpi (existsInDomain D P)

/-!
## Rescue Mechanism 2: Partial Exhaustification (Yek-i-type)

Instead of exhaustifying both alt types, prune one:

Option A: Prune domain alts → only scalar exh
  Result: ∃x. P(x) ∧ ¬∀x. P(x) = "some but not all"
  (Not what yek-i does in root contexts)

Option B: Prune scalar alts → only domain exh
  Result: ∃x. P(x) ∧ ¬[only a] ∧ ¬[only b] ∧...
  For |D| ≥ 2: ∃!x. P(x) = "exactly one satisfies P"
  This IS what yek-i does!
-/

/--
Partial exhaustification with pruned scalar alternatives.
Only domain alternatives are exhaustified.
-/
def partialExhDomainOnly (D : Domain Entity) (P : Entity → Set World) : Set World :=
  simpleExh (domainOnlyAlts D P) (existsInDomain D P)

/--
Partial exhaustification with pruned domain alternatives.
Only scalar alternatives are exhaustified.
-/
def partialExhScalarOnly (D : Domain Entity) (P : Entity → Set World) : Set World :=
  simpleExh (scalarOnlyAlts D P) (existsInDomain D P)


/--
EFCI types based on available rescue mechanisms.
-/
inductive EFCIRescue where
  /-- No rescue available (vreun): ungrammatical in UE root -/
  | none
  /-- Modal insertion available (irgendein): epistemic reading in root -/
  | modalInsertion
  /-- Partial exhaustification available (yek-i): uniqueness in root -/
  | partialExh
  /-- Both mechanisms available -/
  | both
  deriving DecidableEq, Repr

/--
EFCI type determines root context behavior.
-/
def rootBehavior : EFCIRescue → String
  | .none => "Ungrammatical (no rescue)"
  | .modalInsertion => "Epistemic modal reading (speaker ignorance)"
  | .partialExh => "Uniqueness reading (exactly one)"
  | .both => "Either epistemic or uniqueness (context determines)"

/--
EFCI type for vreun (Romanian).
-/
def vreunType : EFCIRescue := .none

/--
EFCI type for irgendein (German).
Actually allows both mechanisms, but modal insertion is primary in root.
-/
def irgendeinType : EFCIRescue := .both

/--
EFCI type for yek-i (Farsi).
Only partial exhaustification available.
-/
def yekiType : EFCIRescue := .partialExh


/-!
## Modal Contexts

Under deontic modals (permission), yek-i yields free choice:
  ◇_deo[∃x. P(x)] with domain exh
= ◇_deo[P(a) ∧ ¬P(b)] ∨ ◇_deo[P(b) ∧ ¬P(a)] (simplified)
= For each x, ◇_deo[P(x)]

Under epistemic modals, yek-i yields modal variation:
  ◇_epi[∃x. P(x)] with domain exh
= At least two individuals are epistemically possible
-/

/--
Modal flavor type.
-/
inductive ModalFlavor where
  | deontic : ModalFlavor   -- Permission, obligation
  | epistemic : ModalFlavor -- Knowledge, belief
  deriving DecidableEq, Repr

/--
EFCI reading type under different conditions.
-/
inductive EFCIReading where
  /-- Plain existential (DE contexts) -/
  | plainExistential
  /-- Uniqueness (root, partial exh) -/
  | uniqueness
  /-- Free choice (deontic modal) -/
  | freeChoice
  /-- Modal variation (epistemic modal) -/
  | modalVariation
  /-- Epistemic ignorance (modal insertion) -/
  | epistemicIgnorance
  deriving DecidableEq, Repr

/--
Determine EFCI reading based on context and rescue mechanism.
-/
def efciReading (rescue : EFCIRescue) (isDE : Bool) (modal : Option ModalFlavor) : Option EFCIReading :=
  if isDE then
    -- DE contexts: always plain existential
    some .plainExistential
  else match modal with
    | some .deontic =>
        -- Under deontic: free choice
        some .freeChoice
    | some .epistemic =>
        -- Under epistemic: modal variation
        some .modalVariation
    | none =>
        -- Root context: depends on rescue mechanism
        match rescue with
        | .none => none  -- Ungrammatical
        | .modalInsertion => some .epistemicIgnorance
        | .partialExh => some .uniqueness
        | .both => some .uniqueness  -- Default to uniqueness; context can shift


/-!
## Theoretical Predictions

1. Root context prediction: yek-i → uniqueness, irgendein → epistemic
2. Deontic prediction: Both → free choice
3. Epistemic prediction: Both → modal variation
4. DE prediction: Both → plain existential
-/

/-- Yek-i in root yields uniqueness -/
theorem yeki_root_uniqueness :
    efciReading yekiType false none = some .uniqueness := rfl

/-- Irgendein in root can yield uniqueness (with partial exh rescue) -/
theorem irgendein_root_uniqueness :
    efciReading irgendeinType false none = some .uniqueness := rfl

/-- Under deontic modal: free choice -/
theorem deontic_freeChoice (rescue : EFCIRescue) :
    efciReading rescue false (some .deontic) = some .freeChoice := rfl

/-- Under epistemic modal: modal variation -/
theorem epistemic_modalVariation (rescue : EFCIRescue) :
    efciReading rescue false (some .epistemic) = some .modalVariation := rfl

/-- In DE context: plain existential -/
theorem de_plainExistential (rescue : EFCIRescue) (modal : Option ModalFlavor) :
    efciReading rescue true modal = some .plainExistential := rfl


/-!
## Cross-FCI Comparison

The Universal FCIs (English *any*, Italian *qualunque*) and their
characteristic distribution are formalized in
`Phenomena/Polarity/Studies/Chierchia2013.lean` (Section "Universal Free
Choice Items"). The contrast theorems below pair the existential-FCI
behaviour modeled here with the universal-FCI behaviour modeled there.
-/

/--
FCI flavor: existential vs universal force.

Note: "Universal" FCIs have existential base meaning but
universal surface force due to obligatory exhaustification.
-/
inductive FCIFlavor where
  | existential  -- irgendein, yek-i, vreun
  | universal    -- any, qualunque, whatever
  deriving DecidableEq, Repr

open Phenomena.Polarity.Studies.Chierchia2013 (ufciGrammatical ufciReading)

/-- Existential FCIs allow root readings -/
theorem efci_allows_root : efciReading .modalInsertion false none = some .epistemicIgnorance := rfl

/-- Universal FCIs block root readings (defined in Chierchia2013) -/
theorem ufci_blocks_root : ufciGrammatical .positiveEpisodic = false := rfl

/-- Both FCIs get FC under modals -/
theorem efci_ufci_fc_under_modal :
    efciReading .modalInsertion false (some .deontic) = some .freeChoice ∧
    ufciReading .deonticModal = some .freeChoice := ⟨rfl, rfl⟩


end AlonsoOvalleMoghiseh2025
