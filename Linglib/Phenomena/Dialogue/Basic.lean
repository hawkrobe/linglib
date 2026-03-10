/-!
# Dialogue: Empirical Observations

Theory-neutral observations about multi-turn conversation dynamics.
These are patterns that any model of conversation must account for,
independent of whether the model is Bayesian (RSA), game-theoretic,
or information-structural.

## Key Phenomena

1. **Common ground development**: shared beliefs become more specific
2. **Belief convergence**: participants learn from each other
3. **Cooperative contributions**: speakers are informative and non-redundant
4. **Contradiction resistance**: CG resists contradictory updates
-/

namespace Phenomena.Dialogue

/-- An empirical observation about conversational dynamics. -/
structure ConversationDatum where
  description : String
  /-- Does shared uncertainty decrease over the conversation? -/
  uncertaintyDecreases : Bool
  /-- Do participants' beliefs become more similar? -/
  beliefsConverge : Bool
  /-- Are contributions non-redundant (new information)? -/
  contributionsInformative : Bool
  deriving Repr

/-- Successful information-sharing: both participants contribute, beliefs converge. -/
def successfulInfoSharing : ConversationDatum where
  description := "Both participants hold different beliefs; each contributes new information"
  uncertaintyDecreases := true
  beliefsConverge := true
  contributionsInformative := true

/-- Asymmetric conversation: one participant is informed, the other uncertain. -/
def asymmetricInfoSharing : ConversationDatum where
  description := "One participant holds strong beliefs; the other is uncertain"
  uncertaintyDecreases := true
  beliefsConverge := true
  contributionsInformative := true

/-- Contradictory beliefs: both hold strong conflicting priors. -/
def contradictoryBeliefs : ConversationDatum where
  description := "Both participants hold strong but conflicting beliefs"
  uncertaintyDecreases := true
  beliefsConverge := true
  contributionsInformative := true

/-- Noncommittal speaker: one participant has no strong beliefs to share. -/
def noncommittalSpeaker : ConversationDatum where
  description := "One participant has no strong beliefs; should avoid random assertions"
  uncertaintyDecreases := true
  beliefsConverge := true
  contributionsInformative := false

end Phenomena.Dialogue
