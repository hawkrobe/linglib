import Linglib.Semantics.Reference.Context.Tower
import Linglib.Semantics.Reference.Context.Shifts
import Linglib.Semantics.Attitudes.Doxastic
import Linglib.Semantics.Reference.ShiftedIndexicals
import Linglib.Semantics.Reference.Kaplan
import Linglib.Semantics.Reference.Monsters
import Linglib.Semantics.Reference.PersonFeatures

/-!
# Schlenker 2003: attitude verbs as context quantifiers

[schlenker-2003]'s attitude semantics: attitude verbs quantify over
*contexts* of the reported speech act, not just worlds. Standard
Hintikka semantics ([hintikka-1962]) — ∀w'. R(x,w,w') → p(w') — is the
special case where the embedded meaning reads only the world coordinate
(`contextBox_world_only`); in languages with shifted indexicals
(Amharic, Zazaki) the agent coordinate carries semantic content that
world quantification cannot express, because the embedded first person
reads the agent of the shifted context (`reportedContext_agent`) while
English *I* is invariant under the shift (`english_I_invariant`).

`ContextBox` is the operator: at each accessible world the embedded
meaning is evaluated against `reportedContext`, the context of the
reported speech act — the innermost context after pushing the attitude
shift, with the holder as agent, the accessible world as world, and the
remaining coordinates inherited. `doxastic_holdsAt_iff_contextBox`
grounds the `DoxasticPredicate` API of `Doxastic.lean` as veridicality
plus context quantification over a world-only meaning.

`SatisfiesFixity` renders the paper's Fixity Thesis, his (1): a meaning
whose truth value is independent of the context tower. World-only
meanings satisfy it (`fixity_world_only`); the shift-reading meanings
of his monster-friendly logics (Appendix B) are the failures. A
tower-general monstrous operator — an embedded meaning consuming the
whole shifted tower, needed for mixed origin/local readings — is the
generalization to mint when a study requires it; `ContextBox`'s meaning
consults only the reported context.

The model sections verify the argument end to end on a two-person,
two-world model: English *I* refers to the actual speaker even under
attitudes (Kaplan's thesis), Amharic *I* shifts to the attitude
holder, `ContextBox` captures both patterns — reducing to `BoxAt` on
world-only meanings, where Fixity holds, and strictly exceeding it on
agent-reading meanings — and person features as presuppositions
derive logophoric pronouns.
-/

namespace Schlenker2003

open Semantics.Context
open Doxastic (BoxAt)

variable {W E P T : Type*}

/-! ### The context of the reported speech act -/

/-- The context of the reported speech act ([schlenker-2003] (4)): push
    the attitude shift onto the tower and read the innermost context —
    the holder becomes the agent, the accessible world the world, and
    the remaining coordinates are inherited. -/
def reportedContext (t : ContextTower (KContext W E P T)) (holder : E)
    (w' : W) : KContext W E P T :=
  (t.push (attitudeShift holder w')).innermost

@[simp] theorem reportedContext_world
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').world = w' := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_agent
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').agent = holder := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_time
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').time = t.innermost.time := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_position
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').position = t.innermost.position := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_addressee
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').addressee = t.innermost.addressee := by
  simp [reportedContext, attitudeShift]

/-! ### Context quantification -/

/-- `ContextBox R holder φ t w worlds` iff at every accessible world
    `w'` the embedded meaning `φ` holds of the context of the reported
    speech act — [schlenker-2003]'s attitude verb quantifying over
    contexts, with the finite `worlds` list as the decidable rendering
    of the quantification (cf. `BoxAt`). -/
def ContextBox (R : E → W → W → Prop) (holder : E)
    (φ : KContext W E P T → Prop)
    (t : ContextTower (KContext W E P T)) (w : W) (worlds : List W) : Prop :=
  ∀ w' ∈ worlds, R holder w w' → φ (reportedContext t holder w')

instance (R : E → W → W → Prop) [∀ a w w', Decidable (R a w w')]
    (holder : E) (φ : KContext W E P T → Prop) [DecidablePred φ]
    (t : ContextTower (KContext W E P T)) (w : W) (worlds : List W) :
    Decidable (ContextBox R holder φ t w worlds) :=
  inferInstanceAs (Decidable (∀ w' ∈ worlds, _))

/-- With a world-only meaning, context quantification is Hintikka world
    quantification — the sense in which [hintikka-1962]'s semantics is
    a special case of [schlenker-2003]'s. -/
theorem contextBox_world_only
    (R : E → W → W → Prop) (holder : E) (p : W → Prop)
    (t : ContextTower (KContext W E P T)) (w : W) (worlds : List W) :
    ContextBox R holder (fun c => p c.world) t w worlds ↔
    BoxAt R holder w worlds p := by
  simp only [ContextBox, BoxAt, reportedContext_world]

/-- `DoxasticPredicate.HoldsAt` is a veridicality check plus context
    quantification over a world-only meaning — every doxastic predicate
    of `Doxastic.lean` is a special case of [schlenker-2003]'s context
    quantification. -/
theorem doxastic_holdsAt_iff_contextBox
    (V : Doxastic.DoxasticPredicate W E) (agent : E)
    (p : W → Prop) (w : W) (worlds : List W)
    (t : ContextTower (KContext W E P T)) :
    V.HoldsAt agent p w worlds ↔
    (Doxastic.VeridicalityHolds V.veridicality p w ∧
     ContextBox V.access agent (fun c => p c.world) t w worlds) := by
  simp only [Doxastic.DoxasticPredicate.HoldsAt,
    contextBox_world_only]

/-! ### The Fixity Thesis -/

/-- The Fixity Thesis, [schlenker-2003] (1): "the semantic value of an
    indexical is fixed solely by the context of the actual speech act,
    and cannot be affected by any logical operators." Rendered on
    tower-parameterized meanings: the truth value is independent of the
    tower configuration. It holds of every meaning of a monster-free
    language and fails for the shift-reading meanings of the paper's
    monster-friendly logics (Appendix B). -/
def SatisfiesFixity (φ : ContextTower (KContext W E P T) → W → Prop) : Prop :=
  ∀ (t₁ t₂ : ContextTower (KContext W E P T)) (w : W), φ t₁ w ↔ φ t₂ w

/-- World-only meanings satisfy the Fixity Thesis. -/
theorem fixity_world_only (p : W → Prop) :
    SatisfiesFixity (W := W) (E := E) (P := P) (T := T)
      (fun _ w => p w) :=
  fun _ _ _ => Iff.rfl

/-! ### Shifted indexicals -/

open Semantics.Reference.Kaplan (pronI_access pronI_shift_invariant)

/-- English *I* is invariant under the attitude shift used by
    `ContextBox` — it resolves to the origin agent (the actual
    speaker), not the attitude holder. -/
theorem english_I_invariant
    (t : ContextTower (KContext W E P T)) (holder : E) (w' : W) :
    pronI_access.resolve (t.push (attitudeShift holder w')) =
    pronI_access.resolve t :=
  pronI_shift_invariant t (attitudeShift holder w')


open Semantics.Reference.ShiftedIndexicals (amharic_pronI)
open Semantics.Reference.Kaplan (pronI_access)

-- ════════════════════════════════════════════════════════════════
-- § Concrete Setup
-- ════════════════════════════════════════════════════════════════

inductive Person | alice | bob
  deriving DecidableEq, Repr

inductive World | w0 | w1
  deriving DecidableEq, Repr

abbrev Ctx := KContext World Person Unit Unit

/-- Speech-act context: Alice speaking to Bob at world w0. -/
def speechCtx : Ctx :=
  { agent := .alice, addressee := .bob, world := .w0,
    time := (), position := () }

def rootT : ContextTower Ctx := ContextTower.root speechCtx

/-- Bob's doxastic accessibility: both worlds are compatible with
    what Bob believes. -/
def bobBel : Person → World → World → Prop
  | .bob, _, _ => True
  | .alice, _, w' => w' = .w0

instance : ∀ a w w', Decidable (bobBel a w w') := by
  intro a w w'; cases a <;> simp [bobBel] <;> infer_instance

/-- Tower after attitude shift: "Bob said that ..." pushes Bob as
    agent and w1 as the attitude world. -/
def shiftedT : ContextTower Ctx :=
  rootT.push (attitudeShift .bob .w1)

-- ════════════════════════════════════════════════════════════════
-- § English vs Amharic "I" Under Attitude Shift
-- ════════════════════════════════════════════════════════════════

/-- English "I" = Alice (actual speaker), even under Bob's attitude verb. -/
theorem english_I_is_speaker :
    pronI_access.resolve shiftedT = .alice := rfl

/-- Amharic "I" = Bob (attitude holder), shifted by the attitude verb. -/
theorem amharic_I_is_holder :
    amharic_pronI.resolve shiftedT = .bob := rfl

/-- English and Amharic "I" diverge under the same attitude shift. -/
theorem indexicals_diverge :
    pronI_access.resolve shiftedT ≠ amharic_pronI.resolve shiftedT := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § Context Quantification: English vs Amharic Truth Conditions
-- ════════════════════════════════════════════════════════════════

/-- Happiness predicate: Alice is happy in w0 only; Bob is happy in both. -/
def isHappy : Person → World → Prop
  | .alice, .w0 => True
  | .alice, .w1 => False
  | .bob, _ => True

instance : ∀ p w, Decidable (isHappy p w) := by
  intro p w; cases p <;> cases w <;> simp [isHappy] <;> infer_instance

/-- English: "Bob said that I am happy" = "Bob said that Alice is happy."
    The meaning is world-only (Alice is fixed by origin-reading "I"),
    so context quantification reduces to standard world quantification. -/
theorem english_reduces_to_BoxAt :
    ContextBox bobBel .bob (fun c => isHappy .alice c.world) rootT .w0 [.w0, .w1] ↔
    BoxAt bobBel .bob .w0 [.w0, .w1] (isHappy .alice) :=
  contextBox_world_only bobBel .bob (isHappy .alice) rootT .w0 [.w0, .w1]

/-- English version is false: Alice is NOT happy in all of Bob's
    belief worlds (she's unhappy in w1). -/
theorem english_result :
    ¬ ContextBox bobBel .bob (fun c => isHappy .alice c.world)
      rootT .w0 [.w0, .w1] := by
  decide

/-- Amharic: "Bob said that I am happy" = "Bob said that Bob is happy."
    The meaning reads the agent from the shifted context (Bob),
    so ContextBox does NOT reduce to BoxAt. -/
theorem amharic_result :
    ContextBox bobBel .bob (fun c => isHappy c.agent c.world)
      rootT .w0 [.w0, .w1] := by
  decide

/-- The English and Amharic versions have different truth values:
    English fails, Amharic holds. This is the formal content of
    [schlenker-2003]'s argument that context quantification is
    strictly more expressive than world quantification. -/
theorem english_amharic_differ :
    ¬ ContextBox bobBel .bob (fun c => isHappy .alice c.world)
      rootT .w0 [.w0, .w1] ∧
    ContextBox bobBel .bob (fun c => isHappy c.agent c.world)
      rootT .w0 [.w0, .w1] :=
  ⟨english_result, amharic_result⟩

-- ════════════════════════════════════════════════════════════════
-- § Fixity Thesis
-- ════════════════════════════════════════════════════════════════

/-- World-only meanings satisfy the Fixity Thesis: the truth value of
    "Alice is happy" is tower-independent. -/
theorem fixity_english :
    SatisfiesFixity (W := World) (E := Person) (P := Unit) (T := Unit)
      (fun _ w => isHappy .alice w) :=
  fixity_world_only (isHappy .alice)

-- ════════════════════════════════════════════════════════════════
-- § Context Quantification ↔ Shifted Indexicals Bridge
-- ════════════════════════════════════════════════════════════════

/-- The agent of the reported context is exactly what Amharic "I"
    (`amharic_pronI`) resolves to. -/
theorem bridge_reportedContext_amharic :
    (reportedContext rootT .bob .w1).agent =
    amharic_pronI.resolve shiftedT := by
  decide

/-- English "I" gives the same result with or without the shift:
    both return Alice (the origin agent). -/
theorem bridge_english_invariant :
    pronI_access.resolve shiftedT =
    pronI_access.resolve rootT :=
  english_I_invariant rootT .bob .w1

-- ════════════════════════════════════════════════════════════════
-- § Person Features: Logophoric Pronouns
-- ════════════════════════════════════════════════════════════════

open Semantics.Reference.PersonFeatures

/-- Bob is logophoric under the attitude shift: he is +author(local)
    (agent of the embedded context) but −author* (not the actual
    speaker Alice). -/
theorem bob_is_logophoric :
    isLogophoric .bob shiftedT .local = true := by
  native_decide

/-- Alice (the speaker) is never logophoric: +author* blocks it. -/
theorem alice_not_logophoric :
    isLogophoric .alice shiftedT .local = false := by
  native_decide

end Schlenker2003
