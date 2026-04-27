import Linglib.Theories.Morphology.DM.Impoverishment

/-!
# Phrase-Level Postsyntactic Operations
@cite{halle-marantz-1993} @cite{arregi-nevins-2012} @cite{middleton-2026}

Sister to `Impoverishment.lean` and `Metathesis.lean`, which operate at
the **focus** level — modifying features within a single terminal node.
This file lifts both operations to the **phrase** level — deleting
whole terminals (e.g., Basque Participant Dissimilation,
@cite{arregi-nevins-2012} §4.6, @cite{middleton-2026} (16)) or
swapping adjacent terminals (e.g., Basque Ergative Metathesis,
@cite{arregi-nevins-2012} §3.2, @cite{middleton-2026} (13)).

The two-tier framework matches DM's actual practice: some impoverishment
rules delete features (Taos), others delete entire terminals (Basque
Participant Dissimilation). Likewise, some metathesis rules swap
features within a node (Taos ω/π reordering) and others swap whole
terminals (Basque Ergative Metathesis).

The phrase-level rules use a `PhraseFocus` view: a target terminal
zoomed with `leftCtx` (terminals to its left) and `rightCtx` (terminals
to its right). Rules scan a phrase left-to-right and apply at the first
matching position.

The architectural claim that **impoverishment precedes metathesis**
(upheld by both A&N and Middleton) is encoded as
`runPhraseImpovThenMeta` vs `runPhraseMetaThenImpov`, with a
divergence theorem available for empirical witnesses.
-/

namespace Morphology.DM.LinearPostsyntax

open Minimalist

-- ============================================================================
-- § 1: Phrases and Phrase Foci
-- ============================================================================

/-- A morphological phrase: a linear sequence of terminal nodes, each a
    `FeatureBundle`. The element order is the linear (post-linearization)
    order; `phrase.head?` is leftmost. -/
abbrev MorphPhrase := List FeatureBundle

/-- A view of a phrase from a chosen target terminal. `leftCtx` is the
    list of terminals to the left of the focus, in original order;
    `rightCtx` is to the right. -/
structure PhraseFocus where
  leftCtx : List FeatureBundle
  focus : FeatureBundle
  rightCtx : List FeatureBundle
  deriving Repr

-- ============================================================================
-- § 2: Terminal-Level Impoverishment (Whole-Node Deletion)
-- ============================================================================

/-- A **terminal-level Impoverishment** rule: deletes a whole terminal
    when its phrase neighborhood matches `condition`. Models the DM
    rules that target nodes rather than individual features (e.g.,
    Basque Participant Dissimilation, @cite{middleton-2026} (16)). -/
structure TermImpovRule where
  condition : PhraseFocus → Prop
  decCond : DecidablePred condition

instance (rule : TermImpovRule) (pf : PhraseFocus) :
    Decidable (rule.condition pf) := rule.decCond pf

/-- Build a `TermImpovRule` from a Boolean predicate over `PhraseFocus`. -/
def termImpov (cond : PhraseFocus → Bool) : TermImpovRule where
  condition pf := cond pf = true
  decCond _ := inferInstanceAs (Decidable (cond _ = true))

/-- Apply a terminal-deletion rule, scanning left-to-right. If no
    terminal matches, return the phrase unchanged. -/
def applyTermImpov (rule : TermImpovRule) (phrase : MorphPhrase) : MorphPhrase :=
  let rec go (left rest : List FeatureBundle) : List FeatureBundle :=
    match rest with
    | [] => left
    | t :: rest' =>
      let pf : PhraseFocus :=
        { leftCtx := left, focus := t, rightCtx := rest' }
      if rule.condition pf then
        left ++ rest'
      else
        go (left ++ [t]) rest'
  go [] phrase

-- ============================================================================
-- § 3: Terminal-Level Metathesis (Adjacent Swap)
-- ============================================================================

/-- A **terminal-level Metathesis** rule: swaps two adjacent terminals
    when the condition holds at their joint context. The condition
    takes `(leftCtx, t1, t2, rightCtx)` — by convention `t1` is the
    immediate left of `t2`. Models the DM rules that reorder whole
    terminals (e.g., Basque Ergative Metathesis,
    @cite{middleton-2026} (13)). -/
structure TermMetaRule where
  condition : List FeatureBundle → FeatureBundle → FeatureBundle →
              List FeatureBundle → Prop
  decCond : ∀ left t1 t2 right, Decidable (condition left t1 t2 right)

instance (rule : TermMetaRule) (left t1 t2 right) :
    Decidable (rule.condition left t1 t2 right) :=
  rule.decCond left t1 t2 right

/-- Build a `TermMetaRule` from a Boolean predicate. -/
def termMeta
    (cond : List FeatureBundle → FeatureBundle → FeatureBundle →
            List FeatureBundle → Bool) :
    TermMetaRule where
  condition left t1 t2 right := cond left t1 t2 right = true
  decCond _ _ _ _ :=
    inferInstanceAs (Decidable (cond _ _ _ _ = true))

/-- Apply a terminal-swap rule: scan left-to-right, swap the first
    adjacent pair whose joint context satisfies `rule.condition`. -/
def applyTermMeta (rule : TermMetaRule) (phrase : MorphPhrase) : MorphPhrase :=
  let rec go (left rest : List FeatureBundle) : List FeatureBundle :=
    match rest with
    | [] => left
    | [t] => left ++ [t]
    | t1 :: t2 :: rest' =>
      if rule.condition left t1 t2 rest' then
        left ++ (t2 :: t1 :: rest')
      else
        go (left ++ [t1]) (t2 :: rest')
  go [] phrase

-- ============================================================================
-- § 4: Generic Chain Runner for Phrase Rules
-- ============================================================================

/-- Apply a list of phrase-level rules left-to-right, threading the
    phrase through each step. Specializes to impoverishment and
    metathesis chains below. -/
def runPhraseChain {R : Type} (apply : R → MorphPhrase → MorphPhrase)
    (rules : List R) (phrase : MorphPhrase) : MorphPhrase :=
  rules.foldl (init := phrase) (λ p rule => apply rule p)

/-- Concatenating two chains is the same as running them sequentially. -/
theorem runPhraseChain_append {R : Type} (apply : R → MorphPhrase → MorphPhrase)
    (rs₁ rs₂ : List R) (phrase : MorphPhrase) :
    runPhraseChain apply (rs₁ ++ rs₂) phrase =
      runPhraseChain apply rs₂ (runPhraseChain apply rs₁ phrase) := by
  simp only [runPhraseChain, List.foldl_append]

/-- The empty chain is the identity. -/
@[simp] theorem runPhraseChain_nil {R : Type} (apply : R → MorphPhrase → MorphPhrase)
    (phrase : MorphPhrase) : runPhraseChain apply [] phrase = phrase := rfl

/-- Apply a sequence of terminal-deletion rules to a phrase. -/
def applyTermImpovChain (rules : List TermImpovRule) (phrase : MorphPhrase) : MorphPhrase :=
  runPhraseChain applyTermImpov rules phrase

/-- Apply a sequence of terminal-swap rules to a phrase. -/
def applyTermMetaChain (rules : List TermMetaRule) (phrase : MorphPhrase) : MorphPhrase :=
  runPhraseChain applyTermMeta rules phrase

-- ============================================================================
-- § 5: Two Pipelines (Impov-Then-Meta vs Meta-Then-Impov)
-- ============================================================================

/-- **The endorsed pipeline** (both A&N and @cite{middleton-2026}):
    impoverishment first, then metathesis. -/
def runPhraseImpovThenMeta
    (impovs : List TermImpovRule) (metas : List TermMetaRule)
    (phrase : MorphPhrase) : MorphPhrase :=
  applyTermMetaChain metas (applyTermImpovChain impovs phrase)

/-- **The rejected pipeline**: metathesis first, then impoverishment.
    The Basque data of @cite{middleton-2026} §3.1 (and
    @cite{arregi-nevins-2012} §3.1.1) shows this order produces wrong
    surface forms. -/
def runPhraseMetaThenImpov
    (impovs : List TermImpovRule) (metas : List TermMetaRule)
    (phrase : MorphPhrase) : MorphPhrase :=
  applyTermImpovChain impovs (applyTermMetaChain metas phrase)

/-- **Divergence claim.** When the two orders produce different phrases
    on a given input, the architectural choice has empirical content:
    one of the pipelines must be wrong, so the data picks the order. -/
theorem runPhraseImpov_neq_runPhraseMeta_of_diverges
    (impovs : List TermImpovRule) (metas : List TermMetaRule) (phrase : MorphPhrase)
    (h : applyTermMetaChain metas (applyTermImpovChain impovs phrase) ≠
         applyTermImpovChain impovs (applyTermMetaChain metas phrase)) :
    runPhraseImpovThenMeta impovs metas phrase ≠
      runPhraseMetaThenImpov impovs metas phrase := h

end Morphology.DM.LinearPostsyntax
