/-!
# @cite{yalcin-2007}: Epistemic Contradictions and the Embedding Diagnostic

@cite{yalcin-2007}

Yalcin (2007) introduced the term *epistemic contradiction* for sentences of
the form `p ∧ ◇¬p` and `¬p ∧ ◇p`, and argued — via their behavior under
embedding — that these are *semantic* contradictions, not merely pragmatic
ones (as Moore-style sentences `p ∧ ¬Kp` are).

The diagnostic battery: Moore sentences become felicitous under embedding
("Suppose it's raining and I don't know it" — fine), while epistemic
contradictions remain infelicitous in the same environments. This is the
foundational empirical observation grounding the subsequent literature
(Mandelkern 2019 @cite{mandelkern-2019}; Klinedinst & Rothschild 2012
@cite{klinedinst-rothschild-2012}; Holliday & Mandelkern 2024
@cite{holliday-mandelkern-2024}).

## Three kinds of (in)felicity

1. **Moore sentences** (`p ∧ ¬Kp` — "It's raining but I don't know that it's
   raining"): pragmatically odd to assert, but felicitous under embedding.
   Often credited to Moore (1942) "Russell's Theory of Descriptions".
2. **Epistemic contradictions / Wittgenstein sentences** (`p ∧ ◇¬p` — "It's
   raining and it might not be raining"): infelicitous *even under
   embedding*. The "Wittgenstein" terminology was added by Mandelkern (2019)
   for the symmetric form `◇¬p ∧ p`; Yalcin's original term was "epistemic
   contradiction." This file uses the unified `SentenceType.wittgenstein`
   constructor for both orderings.
3. **Classical contradictions** (`p ∧ ¬p`): always infelicitous, in any
   environment.

The key empirical generalization: Wittgenstein sentences pattern with
classical contradictions (not with Moore sentences) under embedding —
suggesting they are semantic contradictions, not pragmatic infelicities.

## Embedding environments

Yalcin's diagnostic uses five embedding environments to distinguish
pragmatic from semantic infelicity. Moore sentences become felicitous under
all five; Wittgenstein sentences remain infelicitous in all five.

## Theory-neutrality caveat

This is the empirical pattern that the *truth-conditional* tradition takes
to be settled (Yalcin 2007, Mandelkern 2019, Holliday & Mandelkern 2024).
Dynamic-semantic accounts (Veltman 1996, Groenendijk-Stokhof-Veltman 1996)
and expressivist accounts treat this terrain differently — they do not
divide the data into "semantic vs pragmatic" buckets the same way. The
empirical *judgments* recorded here are widely shared; the *labels*
("semantic," "pragmatic") presuppose some theory of how truth-conditional
content interacts with assertion, which is itself contested.
-/

namespace Phenomena.Modality.Studies.Yalcin2007

/-- A sentence type: how epistemic modality interacts with assertion.

    The `.wittgenstein` constructor covers both `p ∧ ◇¬p` (Yalcin's
    original "epistemic contradiction") and `◇¬p ∧ p` (the order Mandelkern
    (2019) renamed "Wittgenstein sentence"). The two orderings pattern
    identically under the embedding diagnostic, though dynamic-semantic
    accounts (Veltman 1996) make them inequivalent. -/
inductive SentenceType where
  | moore          -- p ∧ ¬Kp ("It's raining but I don't know it")
  | wittgenstein   -- p ∧ ◇¬p ("It's raining and it might not be")
  | classical      -- p ∧ ¬p ("It's raining and it's not raining")
  deriving DecidableEq, Repr

/-- Embedding environments that distinguish Moore from Wittgenstein.

    Yalcin's five canonical environments. Holliday & Mandelkern (2024) (1c),
    (8a-c) emphasize that quantifier restrictors and quantifier scopes are
    *also* canonical environments where the diagnostic applies; those cases
    are not yet captured here. -/
inductive EmbeddingEnv where
  | suppose        -- "Suppose it's raining and it might not be"
  | conditional    -- "If it's raining and it might not be, then..."
  | epistemic      -- "It might be that it's raining and it might not be"
  | disjunction    -- "Either ... or it's raining and it might not be"
  | attitude       -- "John thinks it's raining and it might not be"
  deriving DecidableEq, Repr

/-- Moore sentences become felicitous under embedding; Wittgenstein and
    classical contradictions remain infelicitous. This is the core
    diagnostic separating pragmatic from semantic contradiction.

    Currently uniform across `EmbeddingEnv` cases. The audit-recommended
    extension to `SentenceType → EmbeddingEnv → Bool` (3×5 table) plus
    `quantifier_restrictor` / `quantifier_scope` cases per HM 2024 (1c)/(8a-c)
    is deferred to a separate session. -/
def felicitousUnderEmbedding : SentenceType → Bool
  | .moore => true
  | .wittgenstein => false
  | .classical => false

end Phenomena.Modality.Studies.Yalcin2007
