import Linglib.Phenomena.TenseAspect.Studies.Izvorski1997.Data
import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Fragments.Bulgarian.Evidentials
import Linglib.Core.Discourse.Evidence

/-!
# Izvorski (1997) Bridge Theorems @cite{izvorski-1997}
@cite{koev-2017} @cite{kratzer-1981}

Bridge connecting Izvorski's (1997, SALT 7) epistemic modal analysis of the
Bulgarian evidential to Kratzer's modal semantics and Koev's (2017) non-modal
analysis.

## The EV Operator (Paper's (17)–(19))

Izvorski's formal proposal uses Kratzer's two-parameter modal semantics:

- **f(w)** = {p : speaker considers p indirect evidence in w} — MODAL BASE
- **g(w)** = {p : speaker believes p w.r.t. indirect evidence in w} — ORDERING SOURCE
- **(19)**: ⟦EV p⟧^{f,g} = p true in all best worlds in ∩f(w) under g(w)

The **presupposition** (8ii) that the speaker has indirect evidence is stated
informally in the paper. We formalize it as ∩f(w) ≠ ∅ (the modal base yields
consistent accessible worlds), which is a standard interpretation: if the
modal base encodes indirect evidence, its non-emptiness means such evidence
exists.

## Key Contrasts

- **Ev vs. must** (§3): Same quantificational force (both □). Different modal
  base — Ev restricts to indirect evidence only; must allows any epistemic base.
- **Izvorski vs. Koev**: Modal assertion (□p) vs. flat assertion (p). These
  diverge when some best accessible world falsifies p. They collapse when
  the modal base is totally realistic.

-/

namespace Phenomena.TenseAspect.Studies.Izvorski1997.Bridge

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)
open Core.Presupposition
open Core.Evidence
open Semantics.Tense.Evidential
open Fragments.Bulgarian.Evidentials
open Core.Proposition (World4)

-- ════════════════════════════════════════════════════
-- § 1. The EV Operator ((17)–(19))
-- ════════════════════════════════════════════════════

/-- Izvorski's EV operator (formalization of (17)–(19) + (8ii)).

    - **presup**: indirect evidence available (∩f(w) ≠ ∅).
      The paper states (8ii) informally: "has a presupposition that the
      evidence for the core proposition is indirect." We formalize this
      as the modal base yielding a non-empty set of accessible worlds,
      since the modal base IS the indirect evidence — its consistency
      means such evidence exists.

    - **assertion**: □_{f,g} p — Kratzer necessity over the best worlds
      accessible via the indirect evidence base, per (19). -/
def izvorskiEv (f : ModalBase) (g : OrderingSource)
    (p : BProp World) : PrProp World where
  presup := λ w => !(accessibleWorlds f w).isEmpty
  assertion := λ w => necessity f g p w

-- ════════════════════════════════════════════════════
-- § 2. Concrete Scenario (World4)
-- ════════════════════════════════════════════════════

/-! Model the wine example from the paper's prose (pp. 230–231):
    "Let the indirect evidence be the presence of empty wine bottles in
    John's office and g(w) contain the proposition 'If there are empty
    wine bottles in someone's office, that person has drunk them.'"

    World assignment:
    - w0: John drank, bottles empty (indirect evidence supports p)
    - w1: John drank, no bottles visible (direct evidence only)
    - w2: John didn't drink, bottles empty (misleading evidence)
    - w3: John didn't drink, no evidence -/

/-- Proposition: John drank the wine (true at w0, w1). -/
def johnDrank : BProp World
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => false

/-- Proposition: empty bottles observed (true at w0, w2). -/
def bottlesEmpty : BProp World
  | .w0 => true
  | .w1 => false
  | .w2 => true
  | .w3 => false

/-- Ev's modal base: only indirect evidence (bottle observation).
    Restricts accessibility to worlds compatible with the indirect
    evidence — {w0, w2}. -/
def evBase : ModalBase := λ _ => [bottlesEmpty]

/-- Must's modal base: all available evidence (bottles + direct observation).
    Restricts accessibility further — {w0}. -/
def mustBase : ModalBase := λ _ => [bottlesEmpty, johnDrank]

/-- Ordering source: beliefs formed from evidence.
    The speaker infers John drank (based on the bottles). -/
def beliefOrdering : OrderingSource := λ _ => [johnDrank]

-- ════════════════════════════════════════════════════
-- § 3. Scenario Verification
-- ════════════════════════════════════════════════════

/-- The presupposition of Ev is satisfied: accessible worlds via the
    indirect evidence base are non-empty ({w0, w2}). -/
theorem ev_presup_satisfied (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).presup w = true := by
  cases w <;> native_decide

/-- With the belief ordering, best worlds = {w0} (w0 satisfies the
    belief that John drank, w2 does not). So □p = true. -/
theorem ev_asserts_drank (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).assertion w = true := by
  cases w <;> native_decide

-- ════════════════════════════════════════════════════
-- § 4. Ev vs. Must: Same Force, Different Base
-- ════════════════════════════════════════════════════

/-! The paper's central claim (§3): Ev and must are both epistemic
    necessity modals (both □). They differ ONLY in the modal base.
    Ev restricts to indirect evidence; must uses all available evidence.

    Consequence: must's accessible worlds ⊆ Ev's accessible worlds
    (more evidence → fewer compatible worlds). -/

/-- Must's accessible worlds are a subset of Ev's (for our scenario).
    evBase has only [bottlesEmpty] → accessible = {w0, w2}.
    mustBase has [bottlesEmpty, johnDrank] → accessible = {w0}.
    {w0} ⊆ {w0, w2}. -/
theorem must_accessible_subset_ev (w w' : World)
    (hw' : w' ∈ accessibleWorlds mustBase w) :
    w' ∈ accessibleWorlds evBase w := by
  cases w <;> cases w' <;> simp_all [accessibleWorlds, propIntersection,
    mustBase, evBase, bottlesEmpty, johnDrank, allWorlds,
    Core.Proposition.FiniteWorlds.worlds]

/-- General form: restricting the modal base can only enlarge
    accessibility. If f_ev ⊆ f_must (Ev uses fewer evidence
    propositions), then accessible(f_must) ⊆ accessible(f_ev).
    This is Kratzer's `extension_antitone` applied to evidence bases. -/
theorem restricted_base_enlarges_access
    (f_ev f_must : ModalBase)
    (h : ∀ w p, p ∈ f_ev w → p ∈ f_must w)
    (w w' : World)
    (hw' : w' ∈ accessibleWorlds f_must w) :
    w' ∈ accessibleWorlds f_ev w := by
  rw [accessible_is_extension] at hw' ⊢
  exact extension_antitone (f_ev w) (f_must w) w' (h w) hw'

/-- Both Ev and must reach the same verdict on this scenario: John
    drank. The difference is structural (what evidence is in the base),
    not in the truth value of the conclusion. -/
theorem ev_and_must_agree_here (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).assertion w =
    necessity mustBase beliefOrdering johnDrank w := by
  cases w <;> native_decide

-- ════════════════════════════════════════════════════
-- § 5. Izvorski vs. Koev: Modal vs. Non-Modal
-- ════════════════════════════════════════════════════

/-! Our bridge (not from the paper): the Izvorski–Koev contrast is
    about the STATUS of the assertion. Koev: assertion = p directly.
    Izvorski: assertion = □_{f,g} p (Kratzer necessity). -/

/-- Helper: a proposition true only at w0. -/
private def pOnlyW0 : BProp World
  | .w0 => true
  | _ => false

/-- The modal assertion can diverge from p: when some best accessible
    world falsifies p, □p = false even though p holds at the evaluation
    world. This is where the two analyses make different predictions. -/
theorem izvorski_koev_diverge :
    ∃ (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
      (izvorskiEv f g p).assertion w ≠ p w :=
  -- Empty base (all worlds accessible), empty ordering, p true only at w0.
  -- □p = false (w1,w2,w3 falsify p), but p w0 = true.
  ⟨emptyBackground, emptyBackground, pOnlyW0, .w0, by native_decide⟩

/-- When the modal base is totally realistic (only the actual world
    accessible), □p collapses to p — recovering Koev's full commitment.
    If the speaker's evidence uniquely determines the actual world,
    modal and non-modal analyses agree. -/
theorem izvorski_collapses_to_koev_when_realistic
    (f : ModalBase) (p : BProp World) (w : World)
    (hTotal : accessibleWorlds f w = [w]) :
    (izvorskiEv f emptyBackground p).assertion w = p w := by
  simp only [izvorskiEv, necessity]
  rw [empty_ordering_emptyBackground]
  rw [hTotal]
  simp only [List.all_cons, List.all_nil, Bool.and_true]

-- ════════════════════════════════════════════════════
-- § 6. Presupposition Projection
-- ════════════════════════════════════════════════════

/-- Paper (15): the evidential presupposition projects past negation.
    "Apparently, Ivan didn't pass the exam" still presupposes indirect
    evidence — negation targets the assertion (Ivan passed), not the
    evidence. This follows from `PrProp.neg_presup`. -/
theorem izvorski_projection (f : ModalBase) (g : OrderingSource) (p : BProp World) :
    (PrProp.neg (izvorskiEv f g p)).presup = (izvorskiEv f g p).presup :=
  PrProp.neg_presup _

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Existing Infrastructure
-- ════════════════════════════════════════════════════

/-- The existing nfutL entry is compatible with Izvorski's analysis:
    EP = downstream (T ≤ A) corresponds to indirect evidence being
    retrospective — the speaker acquires evidence after the event. -/
theorem nfutL_compatible_with_izvorski : nfutL.ep = .downstream := rfl

end Phenomena.TenseAspect.Studies.Izvorski1997.Bridge
