/-!
# Features.Attitudes
@cite{karttunen-1971} @cite{villalta-2008} @cite{anand-hacquard-2013}
@cite{klecha-2016}

Per-verb-entry feature taxonomies for attitude verbs: veridicality
(Karttunen lineage), evaluative valence (positive vs negative
attitudes), preferential strategy (degree comparison vs uncertainty
vs relevance), and the composed `Attitude` type combining doxastic and
preferential dimensions.

## Provenance

Bundled together (rather than 4 separate single-enum files) per the
mathlib idiom of co-locating peer concepts that share theoretical
context (cf. `Mathlib/Order/RelClasses.lean` bundling
`IsRefl`/`IsSymm`/`IsTrans`). Moved from `Core/Lexical/VerbClass.lean`
in the cleanup that dissolved `Core/Lexical/`.

## Framework commitment

Each enum here is anchored on a specific theoretical lineage and not a
pan-framework consensus:

- **Veridicality** (`Veridicality`): Karttunen lineage on factive vs
  non-factive complement-taking verbs (the Hooper 1975 *On Assertive
  Predicates* paper extends this to assertive predicates; not currently
  in `references.bib`). @cite{giannakidou-1998} critiques this binary
  as too coarse and proposes a 3-way veridical / nonveridical /
  antiveridical taxonomy; Schlenker (e.g., @cite{schlenker-2003}) on
  attitude-verb projection draws yet different cuts. The binary
  veridical/non-veridical carve-up here is the classical-DRT default,
  not a neutral substrate.

- **AttitudeValence** (`AttitudeValence`): positive/negative split
  underlies the TSP distribution literature (positive attitudes have
  TSP, negative don't) and "V whether" interpretive asymmetries.
  @cite{stalnaker-1984}-style "directedness" frameworks would
  parameterize this differently.

- **Preferential** (`Preferential`): three-way split between
  degree-comparison (@cite{villalta-2008}), uncertainty-based
  (@cite{anand-hacquard-2013} *worry*-class), and relevance-based.
  **Note**: "relevance-based" is **linglib's coinage** for *qidai*-type
  attitudes resisting both Villalta degree-comparison and A&H
  uncertainty analyses; not a published category. @cite{heim-1992}
  gradable-attitude analysis and @cite{lassiter-2017} expected-utility
  account carve the space differently. The C-distributivity and
  NVP-class derivations downstream depend on this specific 3-way split.

- **Attitude** (composed): unifies doxastic (Hintikka accessibility)
  with preferential (degree/uncertainty). Wholly framework-internal:
  not every attitude-verb taxonomy splits along the doxastic/preferential
  axis (Anand & Hacquard subdivide finer; Villalta lumps differently).

## Out of scope

The current `Attitude` type covers doxastic and preferential cases.
Bouletic verbs (*want*, *wish*) are typically slotted under
`preferential .degreeComparison .positive` per the @cite{heim-1992}
gradable-attitude analysis. Speech-act predicates (*promise*,
*demand*, *order*) are not covered by this feature taxonomy and
would need a parallel `SpeechActPredicate` type in
`Pragmatics/`.
-/

namespace Features

-- ════════════════════════════════════════════════════
-- § 1. Veridicality
-- ════════════════════════════════════════════════════

/-- A doxastic predicate is veridical if believing/knowing p entails p is true.

    Veridical: know, realize, discover
    Non-veridical: believe, think, suspect -/
inductive Veridicality where
  | veridical      -- x V p ⊢ p (knowledge, factives)
  | nonVeridical   -- x V p ⊬ p (belief, opinion)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. AttitudeValence
-- ════════════════════════════════════════════════════

/-- Evaluative valence of a preferential predicate.

    - **Positive**: Expresses desire for the proposition (hope, wish, expect)
    - **Negative**: Expresses aversion to the proposition (fear, worry, dread)

    This distinction is crucial for:
    1. TSP distribution (positive have TSP, negative don't)
    2. Interpretive asymmetry in "V whether" constructions -/
inductive AttitudeValence where
  | positive   -- hope, wish, expect, look_forward_to
  | negative   -- fear, worry, dread
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Preferential (attitude predicate strategy)
-- ════════════════════════════════════════════════════

/-- Which Montague predicate strategy this preferential verb uses.

    Links the Fragment entry to the compositional semantics in
    `Semantics.Attitudes.Preferential`. Properties like C-distributivity
    are DERIVED from this tag via theorems, not stipulated.

    - `degreeComparison`: Uses `mkDegreeComparisonPredicate` → C-distributive
    - `uncertaintyBased`: Uses `worry` constructor → NOT C-distributive
    - `relevanceBased`: Uses `qidai` constructor → NOT C-distributive -/
inductive Preferential where
  /-- Degree comparison semantics: ⟦x V Q⟧ = ∃p ∈ Q. μ(x,p) > θ. C-distributive. -/
  | degreeComparison (valence : AttitudeValence)
  /-- Uncertainty-based semantics (worry): involves global uncertainty. NOT C-distributive. -/
  | uncertaintyBased
  /-- Relevance-based semantics (qidai, care): involves resolution. NOT C-distributive. -/
  | relevanceBased (valence : AttitudeValence)
  deriving DecidableEq, Repr

namespace Preferential

/-- Get the valence from the preferential classification. -/
def valence : Preferential → AttitudeValence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative  -- worry is negative
  | .relevanceBased v => v

end Preferential

-- ════════════════════════════════════════════════════
-- § 4. Attitude (unified composed type)
-- ════════════════════════════════════════════════════

/-- Unified classification for all attitude verbs, covering both doxastic
    (believe, know) and preferential (hope, fear) attitudes.

    This is the **minimal basis** from which theoretical properties are derived:
    1. **Doxastic attitudes**: Use accessibility relations (Hintikka semantics)
    2. **Preferential attitudes**: Use degree/uncertainty semantics (Villalta)

    Derived properties (in Theory layer):
    - C-distributivity: from Preferential structure
    - NVP class: from C-distributivity + valence
    - Parasitic on belief: from being preferential
    - Presupposition projection: from veridicality + attitude type -/
inductive Attitude where
  /-- Doxastic attitude (believe, know, think) with accessibility semantics -/
  | doxastic (veridicality : Veridicality)
  /-- Preferential attitude (hope, fear, worry) with degree/uncertainty semantics -/
  | preferential (kind : Preferential)
  deriving DecidableEq, Repr

namespace Attitude

/-- Get veridicality from an attitude classification. -/
def veridicality : Attitude → Veridicality
  | .doxastic v => v
  | .preferential _ => .nonVeridical  -- Preferential attitudes are non-veridical

/-- Is this a doxastic attitude? -/
def isDoxastic : Attitude → Bool
  | .doxastic _ => true
  | .preferential _ => false

/-- Is this a preferential attitude? -/
def isPreferential : Attitude → Bool
  | .doxastic _ => false
  | .preferential _ => true

/-- Get the preferential classification if this is a preferential attitude. -/
def getPreferential : Attitude → Option Preferential
  | .doxastic _ => none
  | .preferential b => some b

/-- Get valence for preferential attitudes. -/
def valence : Attitude → Option AttitudeValence
  | .doxastic _ => none
  | .preferential b => some b.valence

/-- Can this attitude verb take a circumstantial modal base?
    @cite{klecha-2016}: doxastic attitudes (think, believe) take only DOX;
    preferential attitudes (hope, want, pray) can also take CIR, which
    permits future temporal orientation. This is the source of the
    Upper Limit Constraint: DOX-only verbs block future readings. -/
def PermitsCircumstantial : Attitude → Prop
  | .doxastic _ => False
  | .preferential _ => True

instance : DecidablePred Attitude.PermitsCircumstantial := fun a => by
  cases a <;> unfold Attitude.PermitsCircumstantial <;> infer_instance

end Attitude

end Features
