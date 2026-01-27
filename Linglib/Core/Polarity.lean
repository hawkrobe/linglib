/-
# Context Polarity

Theory-neutral infrastructure for monotonicity/polarity in semantics and pragmatics.

Used by:
- NeoGricean: determines which alternatives count as "stronger"
- RSA: could use for polarity-sensitive inference
- Any theory computing scalar implicatures

Note: The semantic typeclasses (IsUpwardEntailing, IsDownwardEntailing) remain
in Montague.Entailment.Polarity since they depend on concrete Prop'/entails.
-/

namespace Core.Polarity

/-- Whether a context preserves or reverses entailment direction -/
inductive ContextPolarity where
  | upward    -- Preserves entailment (stronger alternatives)
  | downward  -- Reverses entailment (weaker alternatives become stronger)
  deriving DecidableEq, Repr

end Core.Polarity
