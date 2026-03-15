import Linglib.Core.Discourse.Evidence
import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Fragments.Bulgarian.Evidentials

/-!
# @cite{izvorski-1997}: The Present Perfect as an Epistemic Modal — Data @cite{izvorski-1997}

Empirical data from @cite{izvorski-1997}. In Bulgarian, Turkish, Norwegian,
and other languages, present perfect morphology doubles as an indirect evidential
(the "Perfect of Evidentiality" = PE). The paper's central proposal (8):

> The indirect evidential Ev is an epistemic modal which:
> (i) has universal quantificational force,
> (ii) has a presupposition that the evidence for the core proposition is indirect.

The key empirical contrasts establishing (8):

1. **Ev vs. must** ((10)–(13)): Both are epistemic necessity modals (same □
   force), but Ev restricts the modal base to *indirect* evidence only. Must
   allows any epistemic base. The difference is in the *base*, not the force.
2. **Presupposition diagnostics** ((14)–(16)): The indirect-evidence requirement
   is a *presupposition* (not an implicature) — it resists cancellation (14),
   projects past negation (15), and denial targets the assertion (16).

-/

namespace Phenomena.TenseAspect.Studies.Izvorski1997.Data

-- ════════════════════════════════════════════════════
-- § 1. Languages with PE
-- ════════════════════════════════════════════════════

/-- Languages exhibiting the Perfect of Evidentiality (@cite{izvorski-1997}, fn. 1).
    The paper's body text discusses Bulgarian, Turkish, and Norwegian;
    footnote 1 lists ~25 languages across 6 families. -/
inductive PELanguage where
  | bulgarian | turkish | norwegian | macedonian | albanian
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Ev vs. Must: Same Force, Different Base
-- ════════════════════════════════════════════════════

/-- Binary evidence basis: Izvorski's central contrast variable.
    The paper argues that Ev and must have the same quantificational
    force (□) but differ in whether the modal base is restricted to
    indirect evidence only. -/
inductive EvidenceBasis where
  | direct | indirect
  deriving DecidableEq, Repr, BEq

/-- A data point from the Ev/must paradigm.
    The paper's argument (§3, pp. 227–229):
    - (10)–(11): With indirect evidence, both Ev and must are felicitous
    - (12)–(13): Ev + "I have no evidence" → contradictory;
      must + "I have no evidence" → acceptable (must doesn't presuppose
      indirect evidence)
    - Prose (p. 228): With direct evidence (speaker witnessed the event),
      Ev is infelicitous; must is fine -/
structure EvMustDatum where
  evidenceBasis : EvidenceBasis
  evFelicitous : Bool
  mustFelicitous : Bool
  label : String
  deriving Repr, BEq

/-- Indirect evidence context: both Ev and must felicitous.
    Paper (10)–(11): "Knowing how much John likes wine..." -/
def evMust_indirect : EvMustDatum where
  evidenceBasis := .indirect
  evFelicitous := true
  mustFelicitous := true
  label := "(10)–(11): indirect evidence context"

/-- Direct evidence context: Ev infelicitous, must fine.
    Paper prose (p. 228): when speaker has direct evidence (witnessed
    the event), PE is infelicitous but must is acceptable. -/
def evMust_direct : EvMustDatum where
  evidenceBasis := .direct
  evFelicitous := false
  mustFelicitous := true
  label := "prose p.228: direct evidence context"

/-- All Ev/must data points. -/
def evMustData : List EvMustDatum := [evMust_indirect, evMust_direct]

-- ════════════════════════════════════════════════════
-- § 3. Presupposition Diagnostics ((14)–(16))
-- ════════════════════════════════════════════════════

/-- Standard presupposition diagnostics applied to the evidential. -/
inductive PresupDiagnostic where
  | cancellation | projection | denial
  deriving DecidableEq, Repr, BEq

/-- A presupposition diagnostic datum. -/
structure PresupDiagnosticDatum where
  diagnostic : PresupDiagnostic
  evidentialSurvives : Bool
  label : String
  deriving Repr, BEq

/-- (14): Cancellation fails — "Maria apparently kissed Ivan. # I witnessed it."
    The indirect-evidence requirement cannot be cancelled, so it is a
    presupposition, not an implicature. -/
def presup_cancellation : PresupDiagnosticDatum where
  diagnostic := .cancellation
  evidentialSurvives := true
  label := "(14): Ev + 'I witnessed it' → contradictory"

/-- (15): Projection under negation — "Apparently, Ivan didn't pass the exam."
    The indirect-evidence requirement projects past negation: the speaker
    still has indirect evidence; what's negated is that Ivan passed. -/
def presup_projection : PresupDiagnosticDatum where
  diagnostic := .projection
  evidentialSurvives := true
  label := "(15): not-Ev-p still presupposes indirect evidence"

/-- (16): Denial targets assertion — "Ivan passed-PE the exam. That's not true."
    The denial targets p (Ivan passed), not the evidential content (that the
    speaker has indirect evidence). -/
def presup_denial : PresupDiagnosticDatum where
  diagnostic := .denial
  evidentialSurvives := true
  label := "(16): denial targets p, not evidence"

/-- All presupposition diagnostic data. -/
def presupData : List PresupDiagnosticDatum :=
  [presup_cancellation, presup_projection, presup_denial]

-- ════════════════════════════════════════════════════
-- § 4. Generalizations
-- ════════════════════════════════════════════════════

/-- Ev requires indirect evidence: felicitous with indirect, infelicitous
    with direct. This captures (8ii). -/
def evRequiresIndirect (d : EvMustDatum) : Bool :=
  match d.evidenceBasis with
  | .indirect => d.evFelicitous
  | .direct => !d.evFelicitous

/-- Must allows both evidence bases — no presupposition on evidence type. -/
def mustAllowsBoth (d : EvMustDatum) : Bool := d.mustFelicitous

/-- All data points satisfy the indirect-evidence generalization. -/
theorem all_evRequiresIndirect :
    evMustData.all evRequiresIndirect = true := by native_decide

/-- All data points satisfy the must-allows-both generalization. -/
theorem all_mustAllowsBoth :
    evMustData.all mustAllowsBoth = true := by native_decide

/-- All diagnostics confirm presupposition status (not implicature). -/
theorem all_evidentialSurvives :
    presupData.all (·.evidentialSurvives) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Bridge: EV Operator and Modal Semantics
-- ════════════════════════════════════════════════════

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)
open Core.Presupposition
open Core.Evidence
open Semantics.Tense.Evidential
open Fragments.Bulgarian.Evidentials
open Core.Proposition (World4)

/-- Izvorski's EV operator (formalization of (17)–(19) + (8ii)). -/
def izvorskiEv (f : ModalBase) (g : OrderingSource)
    (p : BProp World) : PrProp World where
  presup := λ w => !(accessibleWorlds f w).isEmpty
  assertion := λ w => necessity f g p w

def johnDrank : BProp World
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => false

def bottlesEmpty : BProp World
  | .w0 => true
  | .w1 => false
  | .w2 => true
  | .w3 => false

def evBase : ModalBase := λ _ => [bottlesEmpty]

def mustBase : ModalBase := λ _ => [bottlesEmpty, johnDrank]

def beliefOrdering : OrderingSource := λ _ => [johnDrank]

theorem ev_presup_satisfied (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).presup w = true := by
  cases w <;> native_decide

theorem ev_asserts_drank (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).assertion w = true := by
  cases w <;> native_decide

theorem must_accessible_subset_ev (w w' : World)
    (hw' : w' ∈ accessibleWorlds mustBase w) :
    w' ∈ accessibleWorlds evBase w := by
  cases w <;> cases w' <;> simp_all [accessibleWorlds, propIntersection,
    mustBase, evBase, bottlesEmpty, johnDrank, allWorlds,
    Core.Proposition.FiniteWorlds.worlds]

theorem restricted_base_enlarges_access
    (f_ev f_must : ModalBase)
    (h : ∀ w p, p ∈ f_ev w → p ∈ f_must w)
    (w w' : World)
    (hw' : w' ∈ accessibleWorlds f_must w) :
    w' ∈ accessibleWorlds f_ev w := by
  rw [accessible_is_extension] at hw' ⊢
  exact extension_antitone (f_ev w) (f_must w) w' (h w) hw'

theorem ev_and_must_agree_here (w : World) :
    (izvorskiEv evBase beliefOrdering johnDrank).assertion w =
    necessity mustBase beliefOrdering johnDrank w := by
  cases w <;> native_decide

private def pOnlyW0 : BProp World
  | .w0 => true
  | _ => false

theorem izvorski_koev_diverge :
    ∃ (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
      (izvorskiEv f g p).assertion w ≠ p w :=
  ⟨emptyBackground, emptyBackground, pOnlyW0, .w0, by native_decide⟩

theorem izvorski_collapses_to_koev_when_realistic
    (f : ModalBase) (p : BProp World) (w : World)
    (hTotal : accessibleWorlds f w = [w]) :
    (izvorskiEv f emptyBackground p).assertion w = p w := by
  simp only [izvorskiEv, necessity]
  rw [empty_ordering_emptyBackground]
  rw [hTotal]
  simp only [List.all_cons, List.all_nil, Bool.and_true]

theorem izvorski_projection (f : ModalBase) (g : OrderingSource) (p : BProp World) :
    (PrProp.neg (izvorskiEv f g p)).presup = (izvorskiEv f g p).presup :=
  PrProp.neg_presup _

theorem nfutL_compatible_with_izvorski : nfutL.ep = .downstream := rfl

end Phenomena.TenseAspect.Studies.Izvorski1997.Data
