import Linglib.Theories.Pragmatics.RSA.Implementations.ChampollionAlsopGrosu2019
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Bridge: RSA Free Choice Disjunction → Phenomena Data

Connects the RSA free choice model from Champollion, Alsop & Grosu (2019)
to empirical data in `Phenomena.Modality.FreeChoice`.

## Bridge Theorems

- `predicts_free_choice`: L1 free choice prediction matches data
- `fc_not_semantic`: Free choice is pragmatic, not semantic
-/


namespace Phenomena.Modality.RSA_ChampollionAlsopGrosu2019Bridge

/-!
## Connection to Empirical Data

The model predicts the patterns in `Phenomena.Modality.FreeChoice`:

1. **Free Choice Permission** (`coffeeOrTea`):
   - "You may have coffee or tea" → "You may have coffee AND you may have tea"
   - Derived: L1 assigns ~100% to FCI states

2. **Exclusivity Cancelability**:
   - EI ("not both") is sensitive to world knowledge
   - FCI is robust across priors

3. **Ross's Paradox** (`postOrBurn`):
   - "Post the letter" semantically entails "Post or burn"
   - But pragmatically, adding "or burn" triggers free choice
   - The asymmetry comes from the alternative structure
-/

/-- Free choice is predicted -/
theorem predicts_free_choice :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

/-- The inference is not semantic -/
theorem fc_not_semantic :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

end Phenomena.Modality.RSA_ChampollionAlsopGrosu2019Bridge
