import Linglib.Core.ProcessingModel

/-!
# Cue-Based Retrieval
@cite{lewis-vasishth-2005} @cite{lewis-etal-2006}

Content-addressable memory retrieval for sentence processing. Items in
working memory are encoded with feature bundles and retrieved via parallel
cue matching: the parser generates retrieval cues from grammatical
constraints, and the item best matching those cues is accessed.

## Cue Source Decomposition

Following @cite{bakay-etal-2026}, retrieval cues are classified by source:

- **Structural** cues derive from hierarchical relations in the evolving
  parse (c-command, clause-mateness, argument position). These are
  *relational*: they describe the configuration between the retrieval
  site and the candidate, not intrinsic properties of the candidate alone.

- **Item-level** cues target morphosyntactic features stored with the
  item (case marking, phi-features like number and gender).

- **Positional** cues reflect serial position, recency, and linear order.

The central empirical question is whether structural cues contribute to
retrieval independently of item-level and positional cues.

## Two Accounts

Two classes of model predict a **structural advantage** — that
c-commanding antecedents are retrieved over non-c-commanding distractors
even when item-level cues don't distinguish them:

1. **Weighted activation** (@cite{lewis-vasishth-2005}; @cite{kush-2013}):
   Activation is a weighted sum of cue matches. Structural cues can be
   weighted more heavily, or structural features (like Kush's LOCAL:1/0)
   can be dynamically maintained to approximate c-command.

2. **Privileged access** (@cite{mcelree-2006}; @cite{oberauer-2002}):
   Structurally prominent items occupy a "region of direct access" and
   bypass cue-based search entirely.

The models diverge on **interference**: the weighted model predicts graded
interference from feature-matching distractors, while the privileged-
access model predicts little early interference from non-prominent items.
@cite{bakay-etal-2026} find limited, inconsistent evidence for number-
based interference, leaving this distinction open.

-/

set_option autoImplicit false

namespace Processing.CueBasedRetrieval

-- ============================================================================
-- §1: Core Types
-- ============================================================================

/-- Source of a retrieval cue.

    @cite{bakay-etal-2026}'s core empirical contribution is decomposing
    the structural cues that prior studies confounded with clause-level and
    case-marking cues (their Figure 1 Venn diagram), and showing that
    structural cues guide retrieval independently. -/
inductive CueSource where
  /-- Hierarchical relations: c-command, clause-mate, argument role -/
  | structural
  /-- Morphosyntactic features of the item: case, number, gender -/
  | itemLevel
  /-- Serial order: recency, linear precedence -/
  | positional
  deriving DecidableEq, BEq, Repr

/-- A retrieval cue: a feature value tagged with its source.

    When a dependency is encountered (e.g., a reciprocal anaphor),
    the grammar generates a bundle of retrieval cues specifying the
    required antecedent. For example, processing Turkish *birbirleri*
    generates:
    - structural: +c-commanding, +clause-mate
    - item-level: +plural
    - positional: (none — no recency preference) -/
structure Cue (F : Type) where
  source : CueSource
  feature : F
  deriving Repr

/-- An item in working memory, stored with a feature bundle.

    Features encode both intrinsic properties (case, number, category)
    and dynamically assigned structural properties (c-commands-anaphor,
    clause-mate-of-anaphor). The structural features are computed from
    the evolving parse and dynamically updated at clause boundaries
    (@cite{kush-2013}: LOCAL:1 items reset to LOCAL:0). -/
structure Item (F : Type) where
  label : String
  features : List F
  deriving Repr

-- ============================================================================
-- §2: Cue Matching
-- ============================================================================

section Matching

variable {F : Type} [BEq F]

/-- Does an item's feature bundle contain a given feature? -/
def Item.hasFeature (item : Item F) (f : F) : Bool :=
  item.features.any (· == f)

/-- Does an item match a given cue? Match is based on the feature value
    only; the cue source is metadata for the retrieval model, not a
    matching criterion. -/
def Item.matchesCue (item : Item F) (c : Cue F) : Bool :=
  item.hasFeature c.feature

/-- Count of cue matches from a specific source type. -/
def matchCount (item : Item F) (cues : List (Cue F)) (s : CueSource) : Nat :=
  (cues.filter (λ c => c.source == s && item.matchesCue c)).length

/-- Total cue matches across all source types. -/
def totalMatchCount (item : Item F) (cues : List (Cue F)) : Nat :=
  (cues.filter (item.matchesCue ·)).length

/-- **Fan**: number of items matching a particular cue.
    Higher fan reduces the associative boost each item receives from
    that cue, leading to similarity-based interference
    (@cite{van-dyke-mcelree-2011}). -/
def fan (cue : Cue F) (items : List (Item F)) : Nat :=
  (items.filter (·.matchesCue cue)).length

/-- An item is a **distractor** for a retrieval scenario if it matches
    some but not all cues — a partial cue match that competes with
    the target. -/
def isDistractor (item : Item F) (cues : List (Cue F)) : Bool :=
  let m := totalMatchCount item cues
  0 < m && m < cues.length

end Matching

-- ============================================================================
-- §3: Retrieval Scenarios
-- ============================================================================

/-- A retrieval scenario: a probe triggers retrieval with a set of cues,
    and multiple items in memory compete for access. -/
structure Scenario (F : Type) where
  /-- Description of what triggered retrieval (e.g., "reciprocal anaphor") -/
  probe : String
  /-- Cues generated by the grammar at the retrieval site -/
  cues : List (Cue F)
  /-- Items currently in working memory -/
  items : List (Item F)
  deriving Repr

/-- Number of interfering items (partial cue matches) in a scenario.
    Maps to `ProcessingModel.ProcessingProfile.referentialLoad`. -/
def Scenario.interferenceCount {F : Type} [BEq F] (s : Scenario F) : Nat :=
  s.items.filter (isDistractor · s.cues) |>.length

-- ============================================================================
-- §4: Weighted Activation Model
-- ============================================================================

/-! ### Weighted Activation

@cite{lewis-vasishth-2005}: activation = Σ (weight × match). Items with
higher activation are retrieved faster and more accurately. The weights
determine the relative importance of different cue sources.

The key prediction: when structural cues are weighted positively, items
matching more structural cues are retrieved, *independent* of item-level
overlap between target and distractor. -/

section Weighted

variable {F : Type} [BEq F]

/-- Weighted activation: total score is a weighted sum of match counts
    by source type. Weights are natural numbers; only their relative
    magnitude matters for ordering predictions. -/
def weightedActivation (ws wi wp : Nat) (item : Item F) (cues : List (Cue F)) : Nat :=
  ws * matchCount item cues .structural +
  wi * matchCount item cues .itemLevel +
  wp * matchCount item cues .positional

/-- **Structural Advantage Theorem** (weighted activation model).

    If the target matches strictly more structural cues than the distractor,
    they tie on item-level and positional cues, and the structural weight
    is positive, then the target has strictly higher activation.

    This is the qualitative prediction tested by @cite{bakay-etal-2026}
    Experiments 1–3: c-commanding antecedents are retrieved over
    non-c-commanding distractors even when clause, case, and number
    are controlled.

    The proof reduces to monotonicity of multiplication over ℕ. -/
theorem structural_advantage
    (ws wi wp : Nat) (h_ws : 0 < ws)
    (target distractor : Item F) (cues : List (Cue F))
    (h_struct : matchCount distractor cues .structural <
                matchCount target cues .structural)
    (h_item : matchCount target cues .itemLevel =
              matchCount distractor cues .itemLevel)
    (h_pos : matchCount target cues .positional =
             matchCount distractor cues .positional) :
    weightedActivation ws wi wp distractor cues <
    weightedActivation ws wi wp target cues := by
  simp only [weightedActivation, h_item, h_pos]
  exact Nat.add_lt_add_right
    (Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left h_struct h_ws) _) _

/-- **Recency Advantage**: when only positional cues differ
    (more recent = more positional matches), a more recent item has
    higher activation, all else equal.

    @cite{bakay-etal-2026} Experiment 1 finds that the recency advantage
    is *additive* with the structural advantage: linearly recent targets
    receive even more looks. -/
theorem recency_advantage
    (ws wi wp : Nat) (h_wp : 0 < wp)
    (recent distant : Item F) (cues : List (Cue F))
    (h_struct : matchCount recent cues .structural =
                matchCount distant cues .structural)
    (h_item : matchCount recent cues .itemLevel =
              matchCount distant cues .itemLevel)
    (h_pos : matchCount distant cues .positional <
             matchCount recent cues .positional) :
    weightedActivation ws wi wp distant cues <
    weightedActivation ws wi wp recent cues := by
  simp only [weightedActivation, h_struct, h_item]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h_pos h_wp) _

end Weighted

-- ============================================================================
-- §5: Privileged Access Model
-- ============================================================================

/-! ### Privileged Access

@cite{mcelree-2006}; @cite{oberauer-2002}: structurally prominent items
(those c-commanding the retrieval site) occupy a "region of direct access"
in working memory. They are retrieved without search, yielding an immediate
structural advantage independent of cue matching.

This model predicts *less* interference from feature-matching distractors
than the weighted model, because non-prominent items don't compete
directly — they require slower, search-based retrieval. -/

section Privileged

variable {F : Type} [BEq F]

/-- An item is **privileged** (in the region of direct access) if it
    matches all structural cues. Under the privileged-access model,
    such items are retrieved without search. -/
def isPrivileged (item : Item F) (cues : List (Cue F)) : Bool :=
  (cues.filter (·.source == .structural)).all (item.matchesCue ·)

/-- Under privileged access, if the target is privileged and the
    distractor is not, the target is accessed directly regardless of
    the distractor's item-level cue match quality.

    This captures the key prediction shared with the weighted model
    (structural advantage), while remaining agnostic about interference
    from non-privileged distractors. -/
theorem privileged_structural_advantage
    (target distractor : Item F) (cues : List (Cue F))
    (h_target : isPrivileged target cues = true)
    (h_distractor : isPrivileged distractor cues = false) :
    isPrivileged target cues ≠ isPrivileged distractor cues := by
  simp [h_target, h_distractor]

end Privileged

-- ============================================================================
-- §6: Connection to ProcessingModel
-- ============================================================================

/-! ### Bridge to ProcessingModel

A retrieval scenario can be projected to a `ProcessingProfile` for
comparison across conditions. The mapping:

| Retrieval property | ProcessingProfile dimension |
|---|---|
| Number of distractors | `referentialLoad` |
| Distance to target | `locality` |
| Clause boundaries crossed | `boundaries` |
| Structural cue match quality | `ease` |

This bridge connects cue-based retrieval predictions to the Pareto-
dominance comparison framework in `Core.ProcessingModel`. -/

section Bridge

variable {F : Type} [BEq F]

/-- Project a retrieval scenario onto a processing profile.
    Requires explicit target identification and distance information. -/
def toProcessingProfile
    (scenario : Scenario F)
    (target : Item F)
    (distance : Nat)
    (clauseBoundaries : Nat) : ProcessingModel.ProcessingProfile where
  locality := distance
  boundaries := clauseBoundaries
  referentialLoad := scenario.interferenceCount
  ease := totalMatchCount target scenario.cues

end Bridge

end Processing.CueBasedRetrieval
