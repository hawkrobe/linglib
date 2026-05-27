/-!
# Discourse Coherence Relations
@cite{hobbs-1979} @cite{kehler-2002} @cite{umbach-2004}
Coherence relations classifying how adjacent discourse segments
connect (resemblance / cause–effect / contiguity), with directionality
and projections to coherence class. Kehler 2002's tripartition,
extended with SDRT additions (`background`, `consequence`,
`alternation`); CONTRAST / CORRECTION distinguished per
@cite{umbach-2004}.
-/
namespace Discourse.Coherence
/-! ### Coherence Classes (@cite{kehler-2002}) -/
/-- Kehler's three coherence classes, corresponding to Hume's three
    associative connections between ideas. -/
inductive CoherenceClass where
  | resemblance   -- Parallel, Contrast (similarity of structure)
  | causeEffect   -- Result, Explanation (causal connection)
  | contiguity    -- Occasion, Elaboration (spatiotemporal adjacency)
  deriving DecidableEq, Repr
/-! ### Coherence Relations -/
/-- Discourse coherence relations: Kehler's tripartition plus SDRT
    additions. CONTRAST and CORRECTION are distinguished per
    @cite{umbach-2004} (additional vs substitutive exclusion). -/
inductive CoherenceRelation where
  | explanation   -- "because": effect → cause (backward causal)
  | result        -- "so": cause → effect (forward causal)
  | occasion      -- "and then": event₁ → event₂ (= SDRT's Narration)
  | elaboration   -- further detail on the same event
  | parallel      -- structural similarity between segments
  | contrast      -- "but"/"although": similarity + dissimilarity + exclusion of additional alternative
  | correction    -- "but" (corrective) / German *sondern*: exclusion by substitution
  | background    -- @cite{asher-lascarides-2003}: scene-setting; β provides setting for α
  | consequence   -- @cite{asher-lascarides-2003}: discourse-level conditional
  | alternation   -- @cite{asher-lascarides-2003}: discourse-level disjunction
  deriving DecidableEq, Repr
/-! ### Properties -/
/-- Classify each relation into its coherence class. -/
def CoherenceRelation.toClass : CoherenceRelation → CoherenceClass
  | .explanation  => .causeEffect
  | .result       => .causeEffect
  | .occasion     => .contiguity
  | .elaboration  => .contiguity
  | .parallel     => .resemblance
  | .contrast     => .resemblance
  | .correction   => .resemblance
  | .background   => .contiguity     -- scene-setting: spatiotemporal adjacency
  | .consequence  => .causeEffect    -- discourse-level conditional
  | .alternation  => .resemblance    -- discourse-level disjunction
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
  | .background   => .none        -- scene-setting, not causal
  | .consequence  => .forward     -- discourse-level conditional, hypothetical-causal
  | .alternation  => .none        -- discourse-level disjunction, not causal
/-- Does this relation trigger a search for a cause? -/
def CoherenceRelation.selectsCause (r : CoherenceRelation) : Prop :=
  r.causalDirection = .backward
instance (r : CoherenceRelation) : Decidable r.selectsCause := by
  unfold CoherenceRelation.selectsCause; infer_instance
/-- Does this relation trigger a search for an effect? -/
def CoherenceRelation.selectsEffect (r : CoherenceRelation) : Prop :=
  r.causalDirection = .forward
instance (r : CoherenceRelation) : Decidable r.selectsEffect := by
  unfold CoherenceRelation.selectsEffect; infer_instance
/-! ### Connective–Relation Mapping -/
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
/-! ### Theorems -/
/-- "because" selects for causes (backward causal). -/
theorem because_selects_cause :
    (Connective.toRelation .because).selectsCause := rfl
/-- "and so" selects for effects (forward causal / I-Cons). -/
theorem andSo_selects_effect :
    (Connective.toRelation .andSo).selectsEffect := rfl
/-- "although" does not select for causes. -/
theorem although_not_causal :
    ¬ (Connective.toRelation .although).selectsCause := by decide
/-- "and then" does not select for causes. -/
theorem andThen_not_causal :
    ¬ (Connective.toRelation .andThen).selectsCause := by decide
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
    (@cite{umbach-2004}, @cite{kehler-2002}). -/
theorem contrast_correction_same_class :
    CoherenceRelation.contrast.toClass =
    CoherenceRelation.correction.toClass := rfl
/-- CONTRAST and CORRECTION are distinct despite sharing a class
    (@cite{umbach-2004}). -/
theorem contrast_ne_correction :
    CoherenceRelation.contrast ≠ CoherenceRelation.correction := by decide
end Discourse.Coherence
