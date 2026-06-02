/-!
# Horn 1989: Negation ambiguity for metalinguistic negation
[horn-1989] [horn-1985] [burton-roberts-1989]

Horn, L. R. (1989). *A Natural History of Negation*. Univ. of Chicago Press.
Foundation: Horn, L. R. (1985). Metalinguistic negation and pragmatic
ambiguity. *Language* 61(1), 121–174.

## Defining commitment

There are TWO negations in natural language: **descriptive** negation
(truth-functional, targets at-issue content) and **metalinguistic**
negation (objects to the appropriateness of the negated utterance, NOT
to its truth conditions). The lexical item *not* is ambiguous between
these two. Selection between them is constrained by syntactic and
prosodic context.

This is the alternative analysis K-G argues against in §5 (paper p.29):
> "The apparently metalinguistic character of metalinguistic negation
> is explained by the presence of covertly quoted material in the scope
> of the negation rather than by positing anything unusual about the
> negation operator itself, as suggested by Horn (1989) and Potts (2007)."

K-G's view: ONE negation operator + covert mixed quotation `𝔐` +
appropriateness operator `𝔄` derives the same truth conditions and
syntactic restrictions WITHOUT positing lexical ambiguity in *not*.

## Three syntactic predictions Horn 1989 / Burton-Roberts 1989 identify

These are the empirical generalisations that any analysis of
metalinguistic negation must derive. K-G (paper p.32) shows that the
covert-mixed-quotation analysis derives all three; Horn's ambiguity
analysis is committed to them by stipulating that metalinguistic
negation is a distinct lexical item with these distributional
restrictions baked in.

1. **Morpheme incorporation failure** (Horn 1989 p.392; [horn-1985]):
   morphologically incorporated negation (`unhappy`) cannot host
   metalinguistic readings. "She's not happy, she's ecstatic" is fine;
   "#She's unhappy, she's ecstatic" is anomalous.

2. **NPI licensing failure** (Horn 1989): metalinguistic negation does
   not license NPIs. "John didn't manage to solve some of the problems"
   has a metalinguistic reading; "#John didn't manage to solve any of
   the problems" does not.

3. **Double-negation-elimination failure** (Burton-Roberts 1989,
   [burton-roberts-1989]): when both negations are metalinguistic,
   `¬¬p` is NOT equivalent to `p`. "She's not not happy, she's
   inconsolable" is fine; "#She's happy, she's inconsolable" is not.

## Note on scope

Stub formalisation. Encodes Horn's two-negation commitment plus the
three syntactic predictions as named theorems. Sufficient to host the
K-G consilience theorem in `KirkGiannini2024.lean`: K-G derives the
same three predictions WITHOUT lexical ambiguity in *not*.
-/

set_option autoImplicit false

namespace Horn1989

/-- **Horn's two negations.** The lexical item *not* is ambiguous
    between these. -/
inductive NegationKind where
  /-- Descriptive (truth-functional) negation: targets at-issue. -/
  | descriptive
  /-- Metalinguistic negation: targets appropriateness of the utterance. -/
  | metalinguistic
  deriving DecidableEq, Repr

/-- A negation occurrence is one of the two kinds, plus the propositional
    target it scopes over. -/
structure NegOccurrence (P : Type) where
  kind : NegationKind
  target : P
  deriving Repr

/-- **Horn 1989 prediction 1: morphological incorporation blocks
    metalinguistic readings.** `unhappy`-style incorporated negations
    are necessarily descriptive — they cannot host metalinguistic
    correction. -/
def IncorporatedNegation (P : Type) := { n : NegOccurrence P // n.kind = .descriptive }

theorem incorporated_neg_is_descriptive (P : Type) (n : IncorporatedNegation P) :
    n.val.kind = .descriptive := n.property

theorem incorporated_neg_blocks_metalinguistic (P : Type) (n : IncorporatedNegation P) :
    n.val.kind ≠ .metalinguistic := by
  rw [n.property]; intro h; cases h

/-- **Horn 1989 prediction 2: NPIs are not licensed by metalinguistic
    negation.** An NPI in the scope of metalinguistic *not* is
    ungrammatical. We encode this as a structural disallowance. -/
inductive PolarityItem where
  /-- Negative polarity item (e.g., `any`, `ever`). -/
  | npi
  /-- Positive polarity item (e.g., `some`, `already`). -/
  | ppi
  /-- Polarity-neutral. -/
  | neutral
  deriving DecidableEq, Repr

/-- A polarity-marked occurrence in the scope of a negation. -/
structure NegScopeOccurrence (P : Type) where
  neg : NegOccurrence P
  polarity : PolarityItem
  deriving Repr

/-- An occurrence is licit iff NPIs only appear under descriptive negation. -/
def NegScopeOccurrence.licit {P : Type} (occ : NegScopeOccurrence P) : Prop :=
  occ.polarity = .npi → occ.neg.kind = .descriptive

theorem metalinguistic_neg_blocks_npi_licensing {P : Type} (occ : NegScopeOccurrence P)
    (h_meta : occ.neg.kind = .metalinguistic) (h_npi : occ.polarity = .npi) :
    ¬ occ.licit := by
  intro h_licit
  have := h_licit h_npi
  rw [h_meta] at this
  cases this

/-- **Burton-Roberts 1989 prediction: DN-elimination fails for
    metalinguistic negations.** When both `¬`s in `¬¬p` are
    metalinguistic, the result does NOT reduce to `p`. We encode this
    by tracking the negation chain and requiring that any pure
    descriptive double negation reduces, while a chain containing any
    metalinguistic negation does not. -/
abbrev NegChain (P : Type) := List (NegOccurrence P)

/-- All negations in the chain are descriptive. -/
def NegChain.allDescriptive {P : Type} (chain : NegChain P) : Prop :=
  ∀ n ∈ chain, n.kind = .descriptive

/-- At least one negation in the chain is metalinguistic. -/
def NegChain.containsMetalinguistic {P : Type} (chain : NegChain P) : Prop :=
  ∃ n ∈ chain, n.kind = .metalinguistic

/-- The DN-elimination condition: a chain reduces iff it's all-descriptive
    and length 2. (Length-2 condition is the prototypical DN case
    "not not happy"; the substantive predicate is `allDescriptive`.) -/
def NegChain.dneEliminates {P : Type} (chain : NegChain P) : Prop :=
  chain.length = 2 ∧ chain.allDescriptive

/-- **Burton-Roberts 1989's syntactic prediction.** A chain containing any
    metalinguistic negation fails DN-elimination — the surface "not not p"
    does NOT reduce to p when either negation has metalinguistic force. -/
theorem metalinguistic_neg_blocks_dn_elimination {P : Type}
    (chain : NegChain P) (h : chain.containsMetalinguistic) :
    ¬ chain.dneEliminates := by
  rintro ⟨_, h_all⟩
  obtain ⟨n, hn, h_meta⟩ := h
  have h_desc : n.kind = .descriptive := h_all n hn
  rw [h_meta] at h_desc
  cases h_desc

end Horn1989
