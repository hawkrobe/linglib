/-!
# Sweetser's three domains of conditional meaning

@cite{sweetser-1990} @cite{bar-asher-siegal-2026}

Conditionals can express dependencies at three levels:
- **content**: real-world causal or temporal dependency.
  *"If you drop the glass, it will shatter."*
- **epistemic**: inference based on speaker's knowledge.
  *"If the lights are on, someone is home."*
- **speechAct**: illocutionary relevance — the antecedent licenses the
  speech act performed by the consequent.
  *"If you're hungry, there's food in the fridge."*

@cite{bar-asher-siegal-2026}: content-domain conditionals frequently
presuppose or invite causal interpretations, connecting conditional
semantics to the causal-model infrastructure in `Causation/`.

Extracted from `Conditionals/ConditionalType.lean` (was lines 309–368).
-/

namespace Semantics.Conditionals

/-- @cite{sweetser-1990}'s three domains of conditional meaning. -/
inductive SweetserDomain where
  /-- Real-world causal/temporal dependency between events. -/
  | content
  /-- Epistemic inference from evidence to conclusion. -/
  | epistemic
  /-- Illocutionary relevance: antecedent licenses the speech act. -/
  | speechAct
  deriving DecidableEq, Repr

namespace SweetserDomain

/-- Does this domain trigger causal inference?

Content-domain conditionals invite causal readings: "If P then Q" is
often interpreted as "P causes Q" or "P is a precondition for Q."
Epistemic and speech-act domains involve inference and relevance, not
causation. -/
def triggersCausalInference : SweetserDomain → Bool
  | .content => true
  | .epistemic => false
  | .speechAct => false

/-- Does this domain involve speaker knowledge?

Epistemic conditionals express reasoning from evidence; content and
speech-act conditionals do not. -/
def involvesEpistemicReasoning : SweetserDomain → Bool
  | .content => false
  | .epistemic => true
  | .speechAct => false

end SweetserDomain

/-- Content domain triggers causal inference. -/
theorem content_triggers_causal :
    SweetserDomain.content.triggersCausalInference = true := rfl

/-- Epistemic domain does not trigger causal inference. -/
theorem epistemic_not_causal :
    SweetserDomain.epistemic.triggersCausalInference = false := rfl

/-- Speech-act domain does not trigger causal inference. -/
theorem speechAct_not_causal :
    SweetserDomain.speechAct.triggersCausalInference = false := rfl

end Semantics.Conditionals
