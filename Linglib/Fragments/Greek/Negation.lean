import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Core.Lexical.NegMarker
import Mathlib.Data.Fin.Basic
/-!
# Greek Negation Fragment
@cite{tsiakmakis-2025} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

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
-- NB: not opening Core.Lexical.NegMarker namespace-wide to avoid
-- collision with the local `MoodMarkerEntry` (Tsiakmakis 2025 paper
-- apparatus). The Core entries below are fully qualified.

abbrev World := Fin 4

-- ============================================================================
-- § 1: Negation Marker Entries (Tsiakmakis 2025 paper apparatus)
-- ============================================================================

/-- A Greek sentential negation marker, augmented with the mood/NCI
    properties from @cite{tsiakmakis-2025}'s NEG₁/NEG₂ analysis.

    Distinct from the cross-linguistic `Core.Lexical.NegMarker.NegMarkerEntry`
    substrate (which carries only form/morphemeType/position): this
    structure exposes the Tsiakmakis-specific paper apparatus that other
    languages don't have analogues for. The Core entries `dhenMarker` and
    `minMarker` below are the cross-linguistic typology face. -/
structure MoodMarkerEntry where
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
def dhen : MoodMarkerEntry :=
  { form := "dhen"
  , greek := "δεν"
  , isIndicative := true
  , isStandardNegation := true
  , licensesNCIs := true }

/-- *min* (μην): subjunctive/modal negation.
    Appears in non-veridical environments: imperatives, subjunctive
    complements, fear-predicate complements, conditionals, biased questions.
    Does NOT license NCIs when expletive. -/
def min : MoodMarkerEntry :=
  { form := "min"
  , greek := "μην"
  , isIndicative := false
  , isStandardNegation := false
  , licensesNCIs := false }

-- ============================================================================
-- § 1b: Cross-linguistic substrate (Core.Lexical.NegMarker)
-- ============================================================================

/-- *dhen* in Core substrate form. Cross-linguistic typology face of the
    indicative negator; the paper-specific mood/NCI apparatus lives on
    `MoodMarkerEntry` above. -/
def dhenMarker : Core.Lexical.NegMarker.NegMarkerEntry :=
  { form := "dhen"
  , morphemeType := .particle
  , position := .preverbal }

/-- *min* in Core substrate form. -/
def minMarker : Core.Lexical.NegMarker.NegMarkerEntry :=
  { form := "min"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Greek negation system: two mood-conditioned preverbal particles.
    *dhen* (indicative, default-context) listed first, *min* (subjunctive/
    modal) second. The Fragment-side joint consumed by
    `Phenomena/Negation/Typology.lean`. -/
def negationSystem : Core.Lexical.NegMarker.NegationSystem :=
  Core.Lexical.NegMarker.NegationSystem.ofISO "ell" [dhenMarker, minMarker]

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
def minNegSem (f : ModalBase World) (g : OrderingSource World) (p : World → Prop)
    (w : World) : Prop :=
  necessity f g (λ w' => ¬p w') w

/-- Semantics of expletive *min*: modal without negation.
    ⟦min_expletive⟧^g(w) = λp. ∀w' ∈ Best_g(w) : p(w')
    Used in fear complements (*Fovame min efaye* 'I fear he maybe ate'),
    conditionals (*Min ksexaso kati* 'If I forget something'), and
    biased questions (*Min efaye?* 'Did he maybe eat?'). -/
def minExplSem (f : ModalBase World) (g : OrderingSource World) (p : World → Prop)
    (w : World) : Prop :=
  necessity f g p w

-- ============================================================================
-- § 3: Structural Properties
-- ============================================================================

/-- Greek has exactly two sentential negation markers. -/
def allMarkers : List MoodMarkerEntry := [dhen, min]

end Fragments.Greek.Negation
