import Mathlib.Order.Nat
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Relation
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic
import Linglib.Core.Relation.ReflTransGen

/-!
# Stratal Optimality Theory
[kiparsky-2000]

Stratal OT is a theory of the phonology-morphology interface where
phonological computation is **cyclic**: it applies at multiple levels
(strata) of morphological structure, with the output of each stratum
feeding the next as input.

## Architecture

The derivation proceeds through ordered strata:

    Stem → Word → Phrase

Each stratum has:
1. A **constraint ranking** (which may differ from other strata)
2. A **GEN function** (producing candidates from the previous output)
3. An **EVAL function** (selecting the optimal candidate)

The crucial property is **constraint reranking**: the same constraint
can occupy different positions in different strata's rankings. This
captures level-ordering effects — e.g., compensatory lengthening is
optimal at the Word level but not at the Phrase level — without ad hoc
rules or extrinsic ordering.

## Sibling derivational architectures

Stratal OT keeps a derivational architecture (strata) inside an
otherwise constraint-based framework. Linglib's siblings:

* `Phonology/Subregular/LocalRewrite.lean` — full extrinsic-
  ordering derivation via local rewrite rules; the modern subregular
  characterization grounds these as Input Strictly Local functions
  ([chandlee-heinz-2018]).
* `Phonology/Constraint/OT/HarmonicSerialism.lean` — gradual constraint
  optimization, no strata.
* `Core/Computability/Subregular/Function/` — function-level subregular
  hierarchy (ISL ⊊ OSL ⊊ Subsequential ⊊ Weakly Deterministic) that
  classifies what each architecture can express
  ([aksenova-rawski-graf-heinz-2020];
  [meinhardt-mai-bakovic-mccollum-2024]).

## Connection to Linglib

Each individual stratum is evaluated using `OptimalityTheory.mkTableau` and
`Tableau.optimal`. This module adds the stratal architecture:
strata ordering, cross-stratal chaining, and reranking specification.

The Telugu weak alternation ([aitha-2026]) is a key application:
the interaction of IDENT-STRESS with FT-BIN across Stem, Word, and
Phrase strata derives the *-am*/*-āni* alternation from a single
underlying form.
-/

namespace OptimalityTheory.Stratal

open Constraints OptimalityTheory
open Core.Optimization.Evaluation

-- ============================================================================
-- § 1: Strata
-- ============================================================================

/-- The three phonological strata of Stratal OT ([kiparsky-2000]).

    | Stratum | Domain                  | Morphological boundary      |
    |---------|-------------------------|-----------------------------|
    | Stem    | Root + derivational mfx | Innermost cycle             |
    | Word    | Stem + inflectional sfx | Prosodic word (PrWd) edge   |
    | Phrase  | Words + clitics + P     | Phonological phrase edge    |

    Each stratum corresponds to a morphological domain. The Stem–Word
    boundary typically aligns with the edge of the prosodic word. -/
inductive Stratum where
  | stem
  | word
  | phrase
  deriving DecidableEq, Repr

/-- Strata are linearly ordered: stem < word < phrase.
    This ordering reflects the direction of morphological derivation
    (innermost to outermost) and determines the feeding relation. -/
def Stratum.rank : Stratum → Nat
  | .stem => 0
  | .word => 1
  | .phrase => 2

instance : LinearOrder Stratum :=
  LinearOrder.lift' Stratum.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [Stratum.rank])

-- ============================================================================
-- § 2: Stratal Evaluation
-- ============================================================================

/-- Evaluate a single stratum: select optimal candidates from a
    candidate set under a constraint ranking.

    Thin wrapper around `mkTableau` + `optimal` that labels the
    evaluation with its stratum. -/
def evalStratum {C : Type*} [DecidableEq C]
    (_stratum : Stratum)
    (candidates : List C)
    (ranking : List (NamedConstraint C))
    (h : candidates ≠ [] := by decide) : Finset C :=
  (mkTableau candidates ranking h).optimal

/-- Chain two strata: take the optimal output of stratum s₁, transform
    it into candidates for stratum s₂ via a bridge function, and evaluate
    under s₂'s ranking.

    The `bridge` function is language-specific: it adds morphological
    material from the next layer (e.g., inflectional suffixes at the Word
    level, postpositions at the Phrase level) and generates candidate
    representations. -/
def chainEval {C₁ C₂ : Type*} [DecidableEq C₂]
    (_stratum : Stratum)
    (s₁Output : C₁)
    (bridge : C₁ → List C₂)
    (ranking : List (NamedConstraint C₂))
    (hBridge : (bridge s₁Output) ≠ []) : Finset C₂ :=
  (mkTableau (bridge s₁Output) ranking hBridge).optimal

-- ============================================================================
-- § 3: Stratal Derivation Record
-- ============================================================================

/-- The full derivational history across all three strata.
    Records the input and output at each level.

    Type parameters:
    - `S`: candidate type at the Stem level
    - `W`: candidate type at the Word level
    - `P`: candidate type at the Phrase level

    Candidate types differ across strata because GEN produces different
    representations at each level (e.g., metrical parses at Stem level,
    segmental modifications at Word level). -/
structure StratalDerivation (S W P : Type*) where
  /-- Underlying representation (input to the Stem stratum). -/
  underlyingForm : S
  /-- Optimal output of the Stem stratum. -/
  stemOutput : S
  /-- Optimal output of the Word stratum. -/
  wordOutput : W
  /-- Optimal output of the Phrase stratum (= surface form). -/
  phraseOutput : P

/-- The surface form is the output of the final (Phrase) stratum. -/
def StratalDerivation.surface {S W P : Type*}
    (d : StratalDerivation S W P) : P :=
  d.phraseOutput

-- ============================================================================
-- § 4: Constraint Reranking
-- ============================================================================

/-- A constraint identity: name and family, independent of ranking
    position. The same `ConstraintId` can appear at different positions
    in different strata's rankings — this is the core mechanism of
    Stratal OT.

    Contrast with `NamedConstraint`, which bundles the identity with an
    evaluation function (tied to a specific candidate type). -/
structure ConstraintId where
  name : String
  family : ConstraintFamily
  deriving DecidableEq, Repr

/-- Extract the identity from a named constraint. -/
def NamedConstraint.toId {C : Type*} (nc : NamedConstraint C) : ConstraintId :=
  ⟨nc.name, nc.family⟩

/-- Find the rank (position) of a constraint by name within a ranking.
    Position 0 = highest-ranked. Returns `none` if the constraint
    is not active at this stratum. -/
def findRank {C : Type*} (name : String)
    (ranking : List (NamedConstraint C)) : Option Nat :=
  go ranking 0
where
  go : List (NamedConstraint C) → Nat → Option Nat
    | [], _ => none
    | c :: cs, i => if c.name == name then some i else go cs (i + 1)

/-- Is constraint `name` ranked higher (closer to position 0) in
    ranking `r₁` than in `r₂`? Captures **promotion** across strata.

    Example: ONSET is promoted from Word to Phrase level in Telugu
    ([aitha-2026] §5.3), switching from below IDENT-STRESS to
    above it. -/
def isPromoted {C : Type*} (name : String)
    (r₁ r₂ : List (NamedConstraint C)) : Prop :=
  match findRank name r₁, findRank name r₂ with
  | some p₁, some p₂ => p₁ < p₂
  | _, _ => False

instance {C : Type*} (name : String) (r₁ r₂ : List (NamedConstraint C)) :
    Decidable (isPromoted name r₁ r₂) := by
  unfold isPromoted; split <;> infer_instance

/-- Is constraint `name` ranked lower in `r₁` than in `r₂`?
    Captures **demotion** across strata.

    Example: *DIST-0 is demoted from Word to Phrase level in Telugu
    ([aitha-2026] §5.3), allowing consonant retention at phrase
    boundaries. -/
def isDemoted {C : Type*} (name : String)
    (r₁ r₂ : List (NamedConstraint C)) : Prop :=
  isPromoted name r₂ r₁

instance {C : Type*} (name : String) (r₁ r₂ : List (NamedConstraint C)) :
    Decidable (isDemoted name r₁ r₂) := by
  unfold isDemoted; infer_instance

/-- Cross-stratum promotion: `name` is ranked higher (closer to 0) in
    `r₁ : List (NamedConstraint C₁)` than in `r₂ : List (NamedConstraint C₂)`.
    Generalises `isPromoted` to permit different candidate types between
    strata, which is the typical case in Stratal OT — e.g. Word-stratum
    candidates carry segmental modifications while Phrase-stratum
    candidates carry boundary-prosody modifications. The constraint
    inventory is shared by *name*, not by candidate type.

    Example: ONSET is promoted from Word to Phrase level in Telugu
    ([aitha-2026] §5.3), even though the Word and Phrase strata
    score different candidate types. -/
def isPromotedAcross {C₁ C₂ : Type*} (name : String)
    (r₁ : List (NamedConstraint C₁)) (r₂ : List (NamedConstraint C₂)) : Prop :=
  match findRank name r₁, findRank name r₂ with
  | some p₁, some p₂ => p₁ < p₂
  | _, _ => False

instance {C₁ C₂ : Type*} (name : String)
    (r₁ : List (NamedConstraint C₁)) (r₂ : List (NamedConstraint C₂)) :
    Decidable (isPromotedAcross name r₁ r₂) := by
  unfold isPromotedAcross; split <;> infer_instance

/-- Cross-stratum demotion. Dual of `isPromotedAcross`.

    Example: `*DIST-0` is demoted from Word to Phrase level in Telugu
    ([aitha-2026] §5.3), permitting consonant retention at phrase
    boundaries that would otherwise trigger compensatory lengthening. -/
def isDemotedAcross {C₁ C₂ : Type*} (name : String)
    (r₁ : List (NamedConstraint C₁)) (r₂ : List (NamedConstraint C₂)) : Prop :=
  isPromotedAcross name r₂ r₁

instance {C₁ C₂ : Type*} (name : String)
    (r₁ : List (NamedConstraint C₁)) (r₂ : List (NamedConstraint C₂)) :
    Decidable (isDemotedAcross name r₁ r₂) := by
  unfold isDemotedAcross; infer_instance

-- ============================================================================
-- § 5: Ranking Specification
-- ============================================================================

/-- A Hasse pair (a, b) means constraint a strictly dominates constraint b
    (a ≫ b). Lists of such pairs specify a partial order on constraints.

    For classical OT, the transitive closure must be a total order. For
    comparative tableaux ([prince-2002]), partial specifications
    suffice.

    Example: the Stem-level ranking in Telugu ([aitha-2026] §5.1)
    is specified as:
    ```
    [("FT-BIN(μ)", "PARSE-SYL"), ("PARSE-SYL", "ALL-FT-LEFT")]
    ``` -/
abbrev RankingSpec := List (String × String)

/-- Does constraint `a` immediately dominate `b` in the specification? -/
def immediatelyDominates (spec : RankingSpec) (a b : String) : Prop :=
  ∃ p ∈ spec, p.1 = a ∧ p.2 = b

instance (spec : RankingSpec) (a b : String) :
    Decidable (immediatelyDominates spec a b) := by
  unfold immediatelyDominates; infer_instance

/-- Does constraint `a` dominate `b`? Reflexive-transitive closure of
    `immediatelyDominates`, decidable on any concrete `spec` via the
    `Core.Relation.ReflTransGen` substrate using the spec's vertex
    universe as the finite carrier. Captures dominance chains of any
    length (the previous depth-3 hardcoded version was incomplete for
    longer chains). -/
def dominates (spec : RankingSpec) : String → String → Prop :=
  Relation.ReflTransGen (immediatelyDominates spec)

/-- All constraints mentioned by `spec` — the finite universe for the
    substrate's `decidable_of_finite`. -/
private def specVerts (spec : RankingSpec) : List String :=
  (spec.map (·.1) ++ spec.map (·.2)).dedup

private theorem immediatelyDominates_dst_mem_specVerts (spec : RankingSpec) :
    ∀ a b, immediatelyDominates spec a b → b ∈ specVerts spec := by
  intro a b ⟨p, hp, _, hp2⟩
  simp only [specVerts, List.mem_dedup, List.mem_append, List.mem_map]
  exact Or.inr ⟨p, hp, hp2⟩

instance (spec : RankingSpec) (a b : String) :
    Decidable (dominates spec a b) :=
  Relation.ReflTransGen.decidable_of_finite (r := immediatelyDominates spec)
    (specVerts spec) (immediatelyDominates_dst_mem_specVerts spec) a b

-- ============================================================================
-- § 6: Cross-Stratal Properties
-- ============================================================================

/-- Output feeding: the output of stratum s is well-formed input for
    stratum s+1. This is the fundamental architectural claim of
    Stratal OT — phonological computation is *cyclic*, and each cycle
    can change the representation in ways that feed or bleed processes
    at the next cycle.

    Key empirical consequence ([aitha-2026]): compensatory
    lengthening is optimal at the Word level (MAX ≫ ALIGN-RIGHT) but
    not at the Phrase level (constraint reranking), producing different
    outputs for the same segmental configuration at different strata. -/
def isOutputFeeding (s : Stratum) : Stratum → Prop
  | .stem => s = .stem     -- Stem feeds itself (no prior stratum)
  | .word => s = .stem     -- Word is fed by Stem
  | .phrase => s = .word   -- Phrase is fed by Word

instance (s t : Stratum) : Decidable (isOutputFeeding s t) := by
  cases t <;> unfold isOutputFeeding <;> infer_instance

theorem stem_feeds_word : isOutputFeeding .stem .word := rfl
theorem word_feeds_phrase : isOutputFeeding .word .phrase := rfl
theorem stem_not_feeds_phrase : ¬ isOutputFeeding .stem .phrase := by decide

end OptimalityTheory.Stratal
