import Linglib.Core.Temporal.Allen

/-!
# Relation Origins and Declerck's PUTI
@cite{declerck-1991} @cite{declerck-2006}

Step 6 of the Tense-API redesign. A **relation origin** tags *where*
a temporal relation between two TOs came from — grammatical tense,
lexical aspect, an overt adverbial, a pragmatic default, world
knowledge, or direct stipulation. Tagged relations let downstream
modules distinguish:

- **Defeasible defaults** (e.g., the iconic-ordering reading produced
  by Declerck's PUTI) from **semantic entailments** (relations
  contributed by tense morphology).
- **Encoded vs. inferred** content: a `precedes` relation contributed
  by the past perfect's chain link is encoded; the same `precedes`
  inferred from "first … then …" discourse markers is a different
  speech act.
- **Conflict resolution**: when a tense-encoded relation and a PUTI
  default disagree, the encoded relation wins. Tagging the origin
  makes the conflict observable.

The **PUTI lemma** (Declerck's *Principle of Unmarked Temporal
Interpretation*) states that the pragmatically-default Allen atom-set
between two situations is fully determined by their boundedness
profile: bounded+bounded → iconic (sequential), unbounded+unbounded →
simultaneous, mixed → inclusion (the bounded inside the unbounded).
PUTI is a **defeasible default**, not a semantic entailment —
origin-tagging is what lets us say so.
-/

namespace Core.Time

-- ════════════════════════════════════════════════════
-- § Relation Origin
-- ════════════════════════════════════════════════════

/-- The provenance of a temporal relation between two TOs.

    - `tense`: the relation is encoded by tense morphology (e.g., the
      `before` link in the past perfect's chain).
    - `aspect`: the relation comes from aspectual / lexical-aspectual
      semantics (e.g., perfective E ⊆ R).
    - `adverbial`: the relation is contributed by an overt temporal
      adverbial ("yesterday", "before noon").
    - `puti`: the relation is the pragmatic default produced by
      Declerck's Principle of Unmarked Temporal Interpretation
      (boundedness-based; see `putiDefault`).
    - `context`: the relation is inherited from prior discourse,
      world knowledge, or conversational implicature.
    - `stipulated`: direct stipulation (e.g., as a hypothesis in a
      formal derivation).

    The tag is **content-free**: an origin doesn't change *which*
    Allen atom holds, only *why*. Conflict-resolution policies
    (encoded > defeasible) live at the consumer site. -/
inductive RelationOrigin where
  | tense
  | aspect
  | adverbial
  | puti
  | context
  | stipulated
  deriving DecidableEq, Repr, Inhabited

namespace RelationOrigin

/-- Defeasible origins are those a hearer can override: PUTI defaults
    and inherited contextual relations. Tense, aspect, adverbial, and
    stipulated relations are non-defeasible (their content is
    encoded/asserted). -/
def isDefeasible : RelationOrigin → Bool
  | .puti => true
  | .context => true
  | _ => false

@[simp] theorem puti_defeasible : RelationOrigin.puti.isDefeasible = true := rfl
@[simp] theorem context_defeasible : RelationOrigin.context.isDefeasible = true := rfl
@[simp] theorem tense_not_defeasible : RelationOrigin.tense.isDefeasible = false := rfl
@[simp] theorem aspect_not_defeasible : RelationOrigin.aspect.isDefeasible = false := rfl
@[simp] theorem adverbial_not_defeasible : RelationOrigin.adverbial.isDefeasible = false := rfl
@[simp] theorem stipulated_not_defeasible : RelationOrigin.stipulated.isDefeasible = false := rfl

end RelationOrigin

-- ════════════════════════════════════════════════════
-- § Tagged Allen Relations
-- ════════════════════════════════════════════════════

/-- An Allen atom-set tagged with its provenance — "this is the atom-
    set holding between two TOs, and here's why." Atom-sets (rather
    than single atoms) cover both exact-atom claims (`precedesSet`)
    and union claims (`beforeSet`, `containmentSet`).

    Two tagged relations are **compatible** if their atom-sets
    intersect (`Compatible`); incompatibility on a non-defeasible-only
    pair indicates a genuine theoretical contradiction. -/
structure OriginTaggedRelation where
  /-- The atom-set asserted to hold. -/
  atoms : List AllenRelation
  /-- Where the assertion comes from. -/
  origin : RelationOrigin
  deriving Repr

namespace OriginTaggedRelation

/-- Two tagged relations are **compatible** when their atom-sets
    share at least one atom. Used for conflict detection: an encoded
    tense relation is compatible with a PUTI default exactly when the
    default is consistent with the encoded content. -/
def Compatible (r₁ r₂ : OriginTaggedRelation) : Prop :=
  ∃ a, a ∈ r₁.atoms ∧ a ∈ r₂.atoms

/-- A relation is **defeasible** if its origin is. -/
def isDefeasible (r : OriginTaggedRelation) : Bool := r.origin.isDefeasible

end OriginTaggedRelation

-- ════════════════════════════════════════════════════
-- § Declerck's PUTI Lemma
-- ════════════════════════════════════════════════════

/-! Declerck's *Principle of Unmarked Temporal Interpretation*
    (@cite{declerck-1991}). Given two situations described by
    minimally-marked clauses, the default Allen atom-set between their
    event times is determined by their boundedness profile:

    - **bounded + bounded** → iconic / sequential: the second is after
      the first (`beforeSet = {precedes, meets}` from the perspective
      of situation 1).
    - **unbounded + unbounded** → simultaneous (`equalSet = {equal}`,
      strict identity at the point-time level; on intervals the
      `containmentSet` weakens to inclusion).
    - **bounded + unbounded** → the bounded situation is inside the
      unbounded one (`containmentSet = {starts, equal, finishes,
      during}`).
    - **unbounded + bounded** → the unbounded situation contains the
      bounded one (`reverseContainmentSet`).

    PUTI is **defeasible**: an explicit adverbial or contextual
    relation can override it. The `putiDefault` function returns the
    *unmarked* atom-set, tagged with origin `.puti` so the result is
    visibly an inference rather than an entailment. -/

/-- Declerck's PUTI default Allen atom-set for a (s₁, s₂) boundedness
    pair. -/
def putiDefault (b₁ b₂ : SituationBoundedness) : List AllenRelation :=
  match b₁, b₂ with
  | .bounded,   .bounded   => AllenRelation.beforeSet
  | .unbounded, .unbounded => AllenRelation.equalSet
  | .bounded,   .unbounded => AllenRelation.containmentSet
  | .unbounded, .bounded   => AllenRelation.reverseContainmentSet

/-- The PUTI default packaged as an `OriginTaggedRelation` — explicitly
    tagged `.puti` so consumers can see it's a defeasible default. -/
def putiTaggedRelation (b₁ b₂ : SituationBoundedness) : OriginTaggedRelation where
  atoms := putiDefault b₁ b₂
  origin := .puti

/-- The PUTI lemma (Declerck's Principle of Unmarked Temporal
    Interpretation): for any boundedness pair, the unmarked default is
    exactly the atom-set determined by `putiDefault`, tagged `.puti`.
    (The "lemma" is a definitional fact over the four-case classifier;
    its content is the four-case classifier itself, made manipulable as
    a tagged Allen atom-set.) -/
theorem puti_lemma (b₁ b₂ : SituationBoundedness) :
    (putiTaggedRelation b₁ b₂).atoms = putiDefault b₁ b₂ ∧
    (putiTaggedRelation b₁ b₂).origin = .puti := ⟨rfl, rfl⟩

/-- PUTI defaults are always defeasible. -/
@[simp] theorem puti_default_defeasible (b₁ b₂ : SituationBoundedness) :
    (putiTaggedRelation b₁ b₂).isDefeasible = true := rfl

-- ── Per-case PUTI defaults (for clarity at call sites) ──

@[simp] theorem puti_bounded_bounded :
    putiDefault .bounded .bounded = AllenRelation.beforeSet := rfl

@[simp] theorem puti_unbounded_unbounded :
    putiDefault .unbounded .unbounded = AllenRelation.equalSet := rfl

@[simp] theorem puti_bounded_unbounded :
    putiDefault .bounded .unbounded = AllenRelation.containmentSet := rfl

@[simp] theorem puti_unbounded_bounded :
    putiDefault .unbounded .bounded = AllenRelation.reverseContainmentSet := rfl

end Core.Time
