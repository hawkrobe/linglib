import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# @cite{cinque-1999} vs @cite{hacquard-2006}: Modal Position

@cite{hacquard-2010} @cite{cinque-1999} @cite{hacquard-2006}Two approaches to the correlation between modal position (high vs low in
the clause) and modal flavor (epistemic vs root/circumstantial):

## @cite{cinque-1999}: Cartographic Stipulation

Cinque proposes a universal hierarchy of functional projections with
dedicated heads for each modal flavor:

    Mod_epistemic > Mod_irrealis >... > Mod_root > Mod_ability

Each modal type occupies a fixed position in the clause. The
position–flavor correlation is STIPULATED: epistemic modals are high
because there is an Epistemic Modality Phrase above TP; root modals are
low because there is an Ability/Root Modality Phrase below AspP.

## @cite{hacquard-2006}: Content Licensing Derivation

Hacquard derives the same correlation from a single principle: epistemic
modal bases require a **contentful** event (one with propositional
content). VP events lack content; speech act and attitude events have
content. Since aspect binds modals to VP events, a modal below AspP
cannot be epistemic. No dedicated functional heads are needed.

## Comparison Axes

| Property | Cinque | Hacquard |
|----------|--------|----------|
| Mechanism | Dedicated functional heads | Content licensing |
| Position correlation | Stipulated | Derived |
| Cross-linguistic prediction | Universal hierarchy | Universal content predicate |
| Flexibility | None (fixed heads) | Varies with event structure |
| Embedded contexts | Must re-stipulate | Falls out from attitude events |

-/

namespace Phenomena.Modality.ComparePosition

open Semantics.Modality.EventRelativity
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Cinque's Hierarchy: Stipulated Position–Flavor Map
-- ════════════════════════════════════════════════════

/-- A Cinque-style functional projection for modality.
Each modal flavor occupies a dedicated syntactic position. -/
inductive CinqueModHead where
  /-- Mod_epistemic: above TP (high) -/
  | modEpistemic
  /-- Mod_irrealis: above TP (high) -/
  | modIrrealis
  /-- Mod_root: below AspP (low) -/
  | modRoot
  /-- Mod_ability: below AspP (low) -/
  | modAbility
  deriving DecidableEq, BEq, Repr

/-- Cinque's stipulated flavor for each head. -/
def CinqueModHead.flavor : CinqueModHead → ModalFlavor
  | .modEpistemic => .epistemic
  | .modIrrealis => .epistemic
  | .modRoot => .circumstantial
  | .modAbility => .circumstantial

/-- Cinque's stipulated height for each head. -/
def CinqueModHead.isHigh : CinqueModHead → Bool
  | .modEpistemic => true
  | .modIrrealis => true
  | .modRoot => false
  | .modAbility => false

/-- In Cinque's system, high = epistemic and low = circumstantial.
This correlation is true BY STIPULATION — it's built into the
functional head inventory. -/
theorem cinque_high_epistemic :
    ∀ h : CinqueModHead,
      h.isHigh = (h.flavor == .epistemic) := by
  intro h; cases h <;> rfl


-- ════════════════════════════════════════════════════
-- § 2. Hacquard's Derivation: Content Licensing
-- ════════════════════════════════════════════════════

/-- Hacquard derives the SAME correlation from content licensing,
without stipulating dedicated functional heads.

High modals (above AspP) are bound to contentful events → epistemic
available. Low modals (below AspP) are bound to VP events → no
epistemic (content licensing blocks it).

The derivation:
1. VP events lack content (EventBinder.vpEvent.hasContent = false)
2. Low modals are bound to VP events (ModalPosition.belowAsp.defaultBinder =.vpEvent)
3. Epistemic requires content (EventBinder.canProjectEpistemic = hasContent)
4. Therefore: low modals cannot be epistemic -/
theorem hacquard_derives_correlation :
    -- Step 1: VP events lack content
    EventBinder.vpEvent.hasContent = false ∧
    -- Step 2: Low modals → VP event binder
    ModalPosition.belowAsp.defaultBinder = .vpEvent ∧
    -- Step 3: Epistemic requires content
    (∀ b : EventBinder, b.canProjectEpistemic = b.hasContent) ∧
    -- Conclusion: low modals cannot project epistemic
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false ∧
    -- And: high modals CAN project epistemic
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true :=
  ⟨rfl, rfl, λ _ => rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 3. Extensional Equivalence (Matrix Clauses)
-- ════════════════════════════════════════════════════

/-- Both accounts predict the SAME position–flavor correlation for
matrix clauses: high modals get epistemic, low modals get
circumstantial. The accounts are extensionally equivalent here.

The difference is explanatory depth: Cinque stipulates the
correlation; Hacquard derives it from content licensing. -/
theorem matrix_clause_equivalence :
    -- Cinque: high heads are epistemic
    (∀ h : CinqueModHead, h.isHigh = true →
      h.flavor = .epistemic) ∧
    -- Hacquard: high position → epistemic available
    (ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true) ∧
    -- Cinque: low heads are circumstantial
    (∀ h : CinqueModHead, h.isHigh = false →
      h.flavor = .circumstantial) ∧
    -- Hacquard: low position → only circumstantial
    (ModalPosition.belowAsp.defaultBinder.availableFlavors = [.circumstantial]) := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · intro h hh; cases h <;> simp_all [CinqueModHead.isHigh, CinqueModHead.flavor]
  · intro h hh; cases h <;> simp_all [CinqueModHead.isHigh, CinqueModHead.flavor]


-- ════════════════════════════════════════════════════
-- § 4. Where They Diverge: Embedded Contexts
-- ════════════════════════════════════════════════════

/-! The accounts make different predictions for EMBEDDED modals
(under attitude verbs like "believe", "want"). Hacquard predicts that
a high modal in an embedded clause binds to the ATTITUDE event (not the
speech event), yielding the attitude holder's epistemic state. This
falls out from the same content licensing principle: attitude events
are contentful → epistemic R available.

Cinque must re-stipulate: the embedded clause has its own Mod_epistemic
head, and the modal "knows" to occupy it. The question of WHY the
modal gets the attitude holder's knowledge (not the speaker's) has no
structural answer in the cartographic account. In Hacquard's account,
it follows from the event binding chain:

    [VP_att believe [ModP might [AspP PFV [VP be pregnant]]]]
                e₁ ←───────┘
    CON(e₁) = Jane's beliefs → epistemic R for *might* -/

/-- Hacquard's system handles embedded epistemic modals via
`ModalPosition.withAttitude`: a high modal under an attitude verb
binds to the attitude event (not the speech event). The attitude
event is contentful, so epistemic R is available. -/
theorem embedded_epistemic_derived :
    -- Attitude events are contentful
    EventBinder.attitude.hasContent = true ∧
    -- High embedded modal binds to attitude event
    ModalPosition.aboveAsp.withAttitude = .attitude ∧
    -- Attitude event licenses epistemic
    ModalPosition.aboveAsp.withAttitude.canProjectEpistemic = true ∧
    -- Low embedded modal still binds to VP event → no epistemic
    ModalPosition.belowAsp.withAttitude = .vpEvent ∧
    ModalPosition.belowAsp.withAttitude.canProjectEpistemic = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 5. Explanatory Depth: Counting Primitives
-- ════════════════════════════════════════════════════

/-- Cinque requires n functional heads (one per modal flavor at each
height level). Hacquard requires 1 principle (content licensing) +
1 binary distinction (contentful vs contentless events).

We count: Cinque uses 4 heads (§1); Hacquard uses 3 event binders
with 1 content predicate. The number of combinatoric PRIMITIVES
is smaller in Hacquard's system. -/
theorem hacquard_fewer_primitives :
    -- Cinque: 4 functional heads
    [CinqueModHead.modEpistemic, .modIrrealis, .modRoot, .modAbility].length = 4 ∧
    -- Hacquard: 3 event binders × 1 content predicate
    [EventBinder.speechAct, .attitude, .vpEvent].length = 3 := ⟨rfl, rfl⟩

/-- Content licensing unifies the contentful/contentless distinction
across ALL three binders. Cinque would need separate stipulations
for each functional head. -/
theorem content_licensing_is_uniform :
    -- One predicate (hasContent) applies to all binders
    EventBinder.speechAct.hasContent = true ∧
    EventBinder.attitude.hasContent = true ∧
    EventBinder.vpEvent.hasContent = false ∧
    -- And it directly determines epistemic availability
    (∀ b : EventBinder, b.canProjectEpistemic = b.hasContent) :=
  ⟨rfl, rfl, rfl, λ _ => rfl⟩


end Phenomena.Modality.ComparePosition
