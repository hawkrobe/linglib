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

import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Semantics.Entailment.Polarity
import Linglib.Studies.Chierchia2013
import Linglib.Fragments.Farsi.Determiners
import Linglib.Data.Examples.Schema
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Basic

namespace AlonsoOvalleMoghiseh2025

open Exhaustification
open Data.Examples (LinguisticExample)
export Fragments.Farsi.Determiners (EFCIRescue EFCIReading ModalFlavor)

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
EFCI type determines root context behavior.

The `EFCIRescue` enum is the Fragment-canonical typology
(@cite{alonso-ovalle-moghiseh-2025} Table 2) imported from
`Fragments.Farsi.Determiners`.
-/
def rootBehavior : EFCIRescue → String
  | .none => "Ungrammatical (no rescue)"
  | .modalInsertion => "Epistemic modal reading (speaker ignorance)"
  | .partialExhaustification => "Uniqueness reading (exactly one)"
  | .both => "Either epistemic or uniqueness (context determines)"

/-- EFCI type for vreun (Romanian). -/
def vreunType : EFCIRescue := .none

/-- EFCI type for irgendein (German).
Per @cite{alonso-ovalle-moghiseh-2025} Table 2: irgendein-type EFCIs are
(+ modal insertion, − partial exhaustification). -/
def irgendeinType : EFCIRescue := .modalInsertion

/-- EFCI type for yek-i (Farsi).
Only partial exhaustification available. -/
def yekiType : EFCIRescue := .partialExhaustification


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

/-!
`ModalFlavor` and `EFCIReading` are imported from
`Fragments.Farsi.Determiners` (single canonical definitions).
-/

/-- Determine EFCI reading based on context and rescue mechanism. -/
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
        | .partialExhaustification => some .uniqueness
        | .both => some .epistemicIgnorance
          -- Modal insertion primary when both available (matches Fragment's `getReading`).


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

/-- Irgendein in root yields epistemic ignorance via modal insertion
(@cite{alonso-ovalle-moghiseh-2025} Table 2). -/
theorem irgendein_root_epistemic_ignorance :
    efciReading irgendeinType false none = some .epistemicIgnorance := rfl

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
`Studies/Chierchia2013.lean` (Section "Universal Free
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

open Chierchia2013 (ufciGrammatical ufciReading)

/-- Existential FCIs allow root readings -/
theorem efci_allows_root : efciReading .modalInsertion false none = some .epistemicIgnorance := rfl

/-- Universal FCIs block root readings (defined in Chierchia2013) -/
theorem ufci_blocks_root : ufciGrammatical .positiveEpisodic = false := rfl

/-- Both FCIs get FC under modals -/
theorem efci_ufci_fc_under_modal :
    efciReading .modalInsertion false (some .deontic) = some .freeChoice ∧
    ufciReading .deonticModal = some .freeChoice := ⟨rfl, rfl⟩


-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/AlonsoOvalleMoghiseh2025.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def aom2025_rootUniqueness : LinguisticExample :=
  { id := "aom2025_rootUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "root uniqueness, §2.4.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā umæd."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("umæd", "came")]
    translation := "One of the students came."
    context := "root context (no modal embedding)"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (exactly one student)", .acceptable)]
    paperFeatures := [("contextType", "root"), ("modalFlavor", ""), ("uniqueness", "true"), ("freeChoice", "false"), ("modalVariation", "false")]
    comment := "Supplementary illustration of yek-i's root uniqueness reading. Migrated from the legacy `FreeChoiceFarsi.lean` data file; the example is not a direct transcription from the paper but reflects the paper's central claim about yek-i in root contexts."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticFreeChoice : LinguisticExample :=
  { id := "aom2025_deonticFreeChoice"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, §2.3.1"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG")]
    translation := "You can pick one of these apples."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each apple is a permitted option)", .acceptable), ("embedded uniqueness (only one apple permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true"), ("modalVariation", "false")]
    comment := "Supplementary illustration. Migrated from `FreeChoiceFarsi.lean`. The paper's canonical deontic FC examples are (20a), (25), (26)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticBooks : LinguisticExample :=
  { id := "aom2025_deonticBooks"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, books variant"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in ketāb-hā-ro bekhuni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("ketāb-hā-ro", "book-PL-RA"), ("bekhuni", "read.2SG")]
    translation := "You can read one of these books."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each book is a permitted option)", .acceptable), ("embedded uniqueness (only one book permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Books variant of the deontic FC example. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicModalVariation : LinguisticExample :=
  { id := "aom2025_epistemicModalVariation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "epistemic modal variation, §2.3.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā ketāb-o dozid-e."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("ketāb-o", "book-RA"), ("dozid-e", "stole-3SG")]
    translation := "One of the students (might have) stolen the book."
    context := "epistemic possibility (covert or pragmatic) over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (at least two students are possible)", .acceptable), ("embedded uniqueness (exactly one stole it)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true"), ("freeChoice", "false")]
    comment := "Supplementary illustration of yek-i's modal variation reading under epistemic possibility. Migrated from `FreeChoiceFarsi.lean`. Paper's canonical epistemic example is (32)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicExplicit : LinguisticExample :=
  { id := "aom2025_epistemicExplicit"
    source := ⟨"alonso-ovalle-moghiseh-2025", "explicit epistemic modal"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "momken-e yek-i az dānešju-hā biyād."
    discourseSegments := []
    glossedTokens := [("momken-e", "possible-is"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG")]
    translation := "It's possible that one of the students will come."
    context := "explicit epistemic possibility modal over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (multiple students are possible)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true")]
    comment := "Supplementary example with overt epistemic possibility modal `momken`. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deNegation : LinguisticExample :=
  { id := "aom2025_deNegation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "negation context"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā-ro nadid-æm."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā-ro", "student-PL-RA"), ("nadid-æm", "NEG.see-1SG")]
    translation := "I didn't see any of the students."
    context := "downward-entailing: sentential negation, partitive structure"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (no student seen)", .acceptable)]
    paperFeatures := [("contextType", "DE (negation)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "yek-i in DE contexts contributes plain existential force. The paper (17) shows that bare yek-i cannot scope under sentential negation; this partitive variant (`yek-i az NP`) appears compatible with the polarity-item reading. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deConditional : LinguisticExample :=
  { id := "aom2025_deConditional"
    source := ⟨"alonso-ovalle-moghiseh-2025", "conditional antecedent"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "ægær yek-i az dānešju-hā biyād, xošhāl mišæm."
    discourseSegments := []
    glossedTokens := [("ægær", "if"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG"), ("xošhāl", "happy"), ("mišæm", "become.1SG")]
    translation := "If any of the students comes, I'll be happy."
    context := "downward-entailing: conditional antecedent"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (some student coming suffices)", .acceptable)]
    paperFeatures := [("contextType", "DE (conditional)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "Conditional antecedent is the canonical DE context where yek-i contributes plain existential force (paper §2.2; cf. eq. 16). Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_embeddedUniqueness : LinguisticExample :=
  { id := "aom2025_embeddedUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "embedded uniqueness contrast"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri, #væli do-tā nemituni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG"), ("væli", "but"), ("do-tā", "two-CL"), ("nemituni", "NEG.can.2SG")]
    translation := "You can pick one of these apples, #but not two."
    context := "deontic possibility, with continuation testing uniqueness"
    judgment := .marginal
    alternatives := [("mituni yek-i az in sib-ā-ro bardāri.", .acceptable)]
    readings := [("FC + embedded uniqueness (continuation redundant/contradictory)", .marginal)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Continuation `but not two` is infelicitous (marked `#`) because the embedded uniqueness component already entails that only one apple may be picked. Migrated from `FreeChoiceFarsi.lean` (the original recorded `do-tā væli næ` which appears garbled; corrected here to `do-tā nemituni` 'cannot two')."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_irgendein : LinguisticExample :=
  { id := "aom2025_contrast_irgendein"
    source := ⟨"kratzer-shimoyama-2002", "irgendein root"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(1), Table 1"⟩
    language := "stan1295"
    primaryText := "Irgendjemand hat angerufen."
    discourseSegments := []
    glossedTokens := [("Irgendjemand", "IRGEND.somebody"), ("hat", "AUX.3SG"), ("angerufen", "called.PTCP")]
    translation := "Somebody (the speaker doesn't know/care who) called."
    context := "root context (no modal); contrast with yek-i in (8)"
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic ignorance/indifference (modal insertion)", .acceptable)]
    paperFeatures := [("item", "irgendein"), ("language", "German"), ("rescueMechanism", "modalInsertion"), ("hasModalInRoot", "true"), ("efciType", "irgendein")]
    comment := "Cross-linguistic EFCI contrast: irgendein has a modal component in root contexts (covert epistemic insertion), unlike yek-i."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def aom2025_contrast_yeki : LinguisticExample :=
  { id := "aom2025_contrast_yeki"
    source := ⟨"alonso-ovalle-moghiseh-2025", "yek-i root contrast, §2.4"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Yek-i zæng zæd."
    discourseSegments := []
    glossedTokens := [("Yek-i", "one-INDF"), ("zæng", "ring"), ("zæd", "hit.3SG")]
    translation := "Exactly one person called."
    context := "root context (no modal); contrast with irgendein"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (no modal component)", .acceptable)]
    paperFeatures := [("item", "yek-i"), ("language", "Farsi"), ("rescueMechanism", "partialExhaustification"), ("hasModalInRoot", "false"), ("efciType", "yeki")]
    comment := "Cross-linguistic EFCI contrast row: yek-i in root yields uniqueness with no modal component, the paper's central novel claim."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_vreun : LinguisticExample :=
  { id := "aom2025_contrast_vreun"
    source := ⟨"falaus-2014", "p. 122 (cited at AOM 2025 ex. 4)"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(4), Table 1"⟩
    language := "roma1327"
    primaryText := "*Monica s-a întâlnit cu vreun prieten."
    discourseSegments := []
    glossedTokens := [("Monica", "Monica"), ("s-a", "REFL-have.3SG"), ("întâlnit", "met"), ("cu", "with"), ("vreun", "VREUN"), ("prieten", "friend.MASC")]
    translation := "(intended) Monica met a friend."
    context := "root context (no modal); contrast with irgendein and yek-i"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "vreun"), ("language", "Romanian"), ("rescueMechanism", "none"), ("hasModalInRoot", "false"), ("efciType", "vreun")]
    comment := "Cross-linguistic EFCI contrast: vreun has no rescue mechanism and is ungrammatical in unembedded contexts (Fălăuș 2014: 122, cited at AOM 2025 ex. 4 / Table 1)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [aom2025_rootUniqueness, aom2025_deonticFreeChoice, aom2025_deonticBooks, aom2025_epistemicModalVariation, aom2025_epistemicExplicit, aom2025_deNegation, aom2025_deConditional, aom2025_embeddedUniqueness, aom2025_contrast_irgendein, aom2025_contrast_yeki, aom2025_contrast_vreun]

end Examples
-- END GENERATED EXAMPLES


end AlonsoOvalleMoghiseh2025
