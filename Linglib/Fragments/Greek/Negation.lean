import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Attitudes.Intensional
/-!
# Greek Negation Fragment
@cite{tsiakmakis-2025}

Greek distinguishes two sentential negation markers that are in
complementary distribution by mood:

- ***dhen* (δεν)**: indicative negator (NEG₁). Standard sentential negation
  reversing truth conditions: ⟦dhen⟧ = λp.¬p.

- ***min* (μην)**: subjunctive/modal negator (NEG₂). Appears in non-veridical
  environments (imperatives, subjunctive complements, fear-predicate
  complements). As canonical negation, ⟦min⟧ = λp.∀w' ∈ Best_g(w) : ¬p(w').
  As expletive negation, the negation component is absent:
  ⟦min_expletive⟧ = λp.∀w' ∈ Best_g(w) : p(w').

The two markers are the overt morphological reflex of the NEG₁/NEG₂
distinction that @cite{tsiakmakis-2025} argues is cross-linguistically valid.
-/

namespace Fragments.Greek.Negation

open Semantics.Modality.Kratzer (ModalBase OrderingSource necessity)
open Core.Proposition (BProp)
open Semantics.Attitudes.Intensional (World)

-- ============================================================================
-- § 1: Negation Marker Entries
-- ============================================================================

/-- A Greek sentential negation marker. -/
structure NegMarkerEntry where
  /-- Surface form (romanization) -/
  form : String
  /-- Greek orthography -/
  greek : String
  /-- Indicative (dhen) or subjunctive/modal (min) -/
  isIndicative : Bool
  /-- Does the marker function as standard truth-reversing negation? -/
  isStandardNegation : Bool
  /-- Can the marker license NCIs like *tipota* 'nothing'? -/
  licensesNCIs : Bool
  deriving Repr, BEq

/-- *dhen* (δεν): indicative sentential negation.
    Negates the verbal predicate of an indicative sentence.
    Licenses NCIs (*tipota*, *kanenas*). -/
def dhen : NegMarkerEntry :=
  { form := "dhen"
  , greek := "δεν"
  , isIndicative := true
  , isStandardNegation := true
  , licensesNCIs := true }

/-- *min* (μην): subjunctive/modal negation.
    Appears in non-veridical environments: imperatives, subjunctive
    complements, fear-predicate complements, conditionals, biased questions.
    Does NOT license NCIs when expletive. -/
def min : NegMarkerEntry :=
  { form := "min"
  , greek := "μην"
  , isIndicative := false
  , isStandardNegation := false
  , licensesNCIs := false }

-- ============================================================================
-- § 2: Semantics
-- ============================================================================

/-- Semantics of *dhen*: standard truth-functional negation.
    ⟦dhen⟧ = λp.¬p -/
def dhenSem (p : World → Bool) : World → Bool :=
  λ w => !p w

/-- Semantics of negative *min*: modal negation over Best worlds.
    ⟦min⟧^g(w) = λp. ∀w' ∈ Best_g(w) : ¬p(w')
    Used in imperatives (*Min pas!* 'Don't go!') and with canonical *dhen*
    (*Fovame min dhen efaye* 'I fear he maybe didn't eat'). -/
def minNegSem (f : ModalBase World) (g : OrderingSource World) (p : BProp World)
    (w : World) : Prop :=
  necessity f g (λ w' => !p w') w

/-- Semantics of expletive *min*: modal without negation.
    ⟦min_expletive⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w')
    Used in fear complements (*Fovame min efaye* 'I fear he maybe ate'),
    conditionals (*Min ksexaso kati* 'If I forget something'), and
    biased questions (*Min efaye?* 'Did he maybe eat?'). -/
def minExplSem (f : ModalBase World) (g : OrderingSource World) (p : BProp World)
    (w : World) : Prop :=
  necessity f g p w

-- ============================================================================
-- § 3: Structural Properties
-- ============================================================================

/-- Greek has exactly two sentential negation markers. -/
def allMarkers : List NegMarkerEntry := [dhen, min]

/-- The two markers differ in mood selection. -/
theorem mood_complementarity :
    dhen.isIndicative = true ∧ min.isIndicative = false := ⟨rfl, rfl⟩

/-- Only *dhen* is standard truth-reversing negation. -/
theorem dhen_is_standard :
    dhen.isStandardNegation = true ∧ min.isStandardNegation = false := ⟨rfl, rfl⟩

/-- Only *dhen* licenses NCIs. -/
theorem nci_licensing :
    dhen.licensesNCIs = true ∧ min.licensesNCIs = false := ⟨rfl, rfl⟩

end Fragments.Greek.Negation
