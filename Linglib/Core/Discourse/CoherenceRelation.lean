/-!
# Discourse Coherence Relations
@cite{hobbs-1979} @cite{kehler-2002} @cite{umbach-2004}

Coherence relations classify how adjacent discourse
segments connect. Each relation belongs to one of three classes (resemblance,
cause–effect, contiguity) and has a directionality that determines which segment
provides the cause/explanation.

## Key insight for IC bias

@cite{kehler-2002} argues that coherence relations determine which participant
listeners seek as a cause/explanation in sentence continuations:
- **Explanation** ("because"): backward causal — listeners seek the *cause* of the
  event described in the first clause
- **Result** ("so"): forward causal — listeners infer the *effect*
- **Occasion** ("and then"): temporal contiguity — no causal search

This interacts with verb semantics to produce implicit causality (IC) bias. @cite{solstad-bott-2022} @cite{solstad-bott-2024}

## Contrast vs Correction

@cite{umbach-2004} argues that both CONTRAST and CORRECTION are resemblance
relations requiring alternatives that are similar (common integrator) and
dissimilar (semantically independent). They differ in their type of exclusion:
- **CONTRAST**: excludes *additional* alternatives (the second alternative holds
  *in addition to* the first; "but" with confirm+deny)
- **CORRECTION**: excludes *by substitution* (the second alternative holds
  *instead of* the first; German *sondern*, English corrective "but")

Both are distinct from PARALLEL/SEQUENCE ("and"-coordination), which requires
similarity+dissimilarity but no exclusion.

-/

namespace Core.Discourse.CoherenceRelation

-- ════════════════════════════════════════════════════
-- § 1. Coherence Classes (@cite{kehler-2002})
-- ════════════════════════════════════════════════════

/-- Kehler's three coherence classes, corresponding to Hume's three
    associative connections between ideas. -/
inductive CoherenceClass where
  | resemblance   -- Parallel, Contrast (similarity of structure)
  | causeEffect   -- Result, Explanation (causal connection)
  | contiguity    -- Occasion, Elaboration (spatiotemporal adjacency)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Coherence Relations
-- ════════════════════════════════════════════════════

/-- Individual discourse coherence relations.
    Each relation specifies how the current segment connects to the prior one.

    @cite{umbach-2004} §3: CONTRAST and CORRECTION are distinct resemblance
    relations that both require similarity+dissimilarity in their alternatives
    but differ in their exclusion type. -/
inductive CoherenceRelation where
  | explanation   -- "because": effect → cause (backward causal)
  | result        -- "so": cause → effect (forward causal)
  | occasion      -- "and then": event₁ → event₂ (temporal sequence)
  | elaboration   -- further detail on the same event
  | parallel      -- structural similarity between segments
  | contrast      -- "but"/"although": similarity + dissimilarity + exclusion of additional alternative
  | correction    -- "but" (corrective) / German *sondern*: exclusion by substitution
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Properties
-- ════════════════════════════════════════════════════

/-- Classify each relation into its coherence class. -/
def CoherenceRelation.toClass : CoherenceRelation → CoherenceClass
  | .explanation  => .causeEffect
  | .result       => .causeEffect
  | .occasion     => .contiguity
  | .elaboration  => .contiguity
  | .parallel     => .resemblance
  | .contrast     => .resemblance
  | .correction   => .resemblance

/-- Causal direction: does the relation seek a cause in the prior segment? -/
inductive CausalDirection where
  | backward   -- Prior segment is effect, continuation provides cause
  | forward    -- Prior segment is cause, continuation provides effect
  | none       -- No causal search
  deriving DecidableEq, Repr

/-- The causal direction of each relation. -/
def CoherenceRelation.causalDirection : CoherenceRelation → CausalDirection
  | .explanation  => .backward    -- "because": backward search for cause
  | .result       => .forward     -- "so": forward to effect
  | .occasion     => .none        -- "and then": temporal, not causal
  | .elaboration  => .none        -- same event, no causal search
  | .parallel     => .none        -- structural, not causal
  | .contrast     => .none        -- resemblance, not causal
  | .correction   => .none        -- resemblance, not causal

/-- Does this relation trigger a search for a cause? -/
def CoherenceRelation.selectsCause (r : CoherenceRelation) : Bool :=
  r.causalDirection == .backward

/-- Does this relation trigger a search for an effect? -/
def CoherenceRelation.selectsEffect (r : CoherenceRelation) : Bool :=
  r.causalDirection == .forward

-- ════════════════════════════════════════════════════
-- § 4. Connective–Relation Mapping
-- ════════════════════════════════════════════════════

/-- German/English connective forms used as experimental stimuli
    (@cite{solstad-bott-2022}, Exps 1–4). -/
inductive Connective where
  | because     -- "weil" / "because" → I-Caus
  | andSo       -- "sodass" / "and so" → I-Cons
  | although    -- "obwohl" / "although"
  | andThen     -- "und dann" / "and then"
  deriving DecidableEq, Repr

/-- Map connectives to the coherence relation they signal. -/
def Connective.toRelation : Connective → CoherenceRelation
  | .because   => .explanation
  | .andSo     => .result
  | .although  => .contrast
  | .andThen   => .occasion

-- ════════════════════════════════════════════════════
-- § 5. Theorems
-- ════════════════════════════════════════════════════

/-- "because" selects for causes (backward causal). -/
theorem because_selects_cause :
    (Connective.toRelation .because).selectsCause = true := rfl

/-- "and so" selects for effects (forward causal / I-Cons). -/
theorem andSo_selects_effect :
    (Connective.toRelation .andSo).selectsEffect = true := rfl

/-- "although" does not select for causes. -/
theorem although_not_causal :
    (Connective.toRelation .although).selectsCause = false := rfl

/-- "and then" does not select for causes. -/
theorem andThen_not_causal :
    (Connective.toRelation .andThen).selectsCause = false := rfl

/-- "because" and "and so" are both causal but in opposite directions: I-Caus is backward, I-Cons is forward. -/
theorem because_andSo_opposite_directions :
    (Connective.toRelation .because).causalDirection = .backward ∧
    (Connective.toRelation .andSo).causalDirection = .forward := ⟨rfl, rfl⟩

/-- Both causal relations (explanation, result) belong to causeEffect class. -/
theorem causal_relations_same_class :
    CoherenceRelation.explanation.toClass =
    CoherenceRelation.result.toClass := rfl

/-- Occasion and elaboration belong to contiguity class. -/
theorem contiguity_relations_same_class :
    CoherenceRelation.occasion.toClass =
    CoherenceRelation.elaboration.toClass := rfl

/-- CONTRAST and CORRECTION are both resemblance relations
    (@cite{umbach-2004} §3.2, @cite{kehler-2002}). -/
theorem contrast_correction_same_class :
    CoherenceRelation.contrast.toClass =
    CoherenceRelation.correction.toClass := rfl

/-- CONTRAST and CORRECTION are distinct relations despite sharing a class.
    @cite{umbach-2004} §3.2: they differ in exclusion type (additional vs
    substitution) and in the implicit question they respond to. German
    lexicalizes the difference: *aber* (contrast) vs *sondern* (correction). -/
theorem contrast_ne_correction :
    CoherenceRelation.contrast ≠ CoherenceRelation.correction := by decide

end Core.Discourse.CoherenceRelation
