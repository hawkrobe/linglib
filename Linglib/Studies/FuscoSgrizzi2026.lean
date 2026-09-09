import Linglib.Semantics.Modality.EventRelativity
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Fragments.Italian.Predicates
import Linglib.Data.Examples.FuscoSgrizzi2026

/-!
# Fusco and Sgrizzi (2026): Belief or Action? Semantic Ambiguity in the Italian Non-finite Domain

This file formalizes [fusco-sgrizzi-2026]'s account of the belief and intention readings of
Italian *convincere* 'convince' with its two infinitival complements: *Marco ha convinto Gianni di
avere un figlio* reports a belief, *Marco ha convinto Gianni a avere un figlio* an intention.
Where [grano-2024] ties the alternation to mood and finiteness, the paper ties it to the size of
the complement. The *di*-infinitive is a CP: it hosts modal auxiliaries, allows subject as well
as object control, and can be assessed for truth. The *a*-infinitive stops below tense and above
vP: it hosts negation, passive and low aspectual verbs and forms a temporal domain of its own, but
blocks clitic climbing and subject control and cannot be assessed for truth. The readings follow
from the size through one lexical entry: *convincere* causes a rational-attitude state with the
property its complement supplies (`Frame.convincere`, the paper's (24)). A *di*-complement closes
the eventuality argument of the bare infinitive into a proposition, which *di* quantifies over
the state's content worlds; an *a*-complement keeps it open, and *a*, anchored to the state,
quantifies over the state's inertia worlds and binds the event to the state by the causal
relation (`aP`). Both heads are Kratzer necessity over backgrounds the state projects, the
event-relative modality of [hacquard-2010]: *di* over a content background, *a* over a
circumstantial base ordered by inertia ([dowty-1979], [kratzer-2013]). This is the causal
self-referentiality of intention ([searle-1983]): in every inertia world the intended event is
caused by the attitude state, hence later than it, the future orientation of *a*-infinitives
([wurmbrand-2014]; `intention_future`). Complement size is the extended projection's
`ComplementSize`, ordered by functional level; the reading is read off the CP threshold, and the
diagnostics of sections 3 and 3.1 are predicted by the heads the complement reaches
(`rows_predicted`).

## Implementation notes

* The *a*-infinitive is recorded with negation as its highest head, the highest the paper places
  inside it. The functional sequence does not separate negation from tense and modal heads, so
  the absence of modal auxiliaries ((9) and (10)) and the ban on past-oriented complements ((5))
  stay in the prose and in `intention_future`.
* The two heads are stated over abstract eventualities and worlds, with the content background,
  the circumstantial base and the inertial ordering as anchoring functions of the state.
* The examples are `Data.Examples.FuscoSgrizzi2026`; the lexical entries are those of
  `Fragments/Italian/Predicates.lean`.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
* [searle-1983]
* [wurmbrand-2014]
* [dowty-1979]
* [kratzer-2013]
* [hacquard-2010]
* [rizzi-1997]
-/

namespace FuscoSgrizzi2026

open Modality Modality.Kratzer Minimalist Italian.Predicates Data.Examples

section Semantics

variable {I V W : Type*}

/-- Existential closure of the eventuality argument of a bare infinitive, the paper's (23b): the
head a *di*-infinitive contains and an *a*-infinitive lacks. -/
def closure (P : V → W → Prop) : W → Prop := λ w => ∃ e, P e w

/-- The head *a* (25): anchored to the attitude state, it is necessity over the state's inertia
worlds, the best worlds of a circumstantial base under an inertial ordering ([dowty-1979],
[kratzer-2013]), with the eventuality of its complement bound to the state by the causal
relation. -/
def aP (circumstances : AnchoringFn V W) (inertia : OrderingFn V W)
    (causeStar : V → V → W → Prop) (P : V → W → Prop) (s : V) (w : W) : Prop :=
  necessity (circumstances s) (inertia s) (λ w' => ∃ e, causeStar s e w' ∧ P e w') w

/-- The head *di* (26): necessity over the state's content worlds of a proposition. -/
def diP (content : AnchoringFn V W) (Q : W → Prop) (s : V) (w : W) : Prop :=
  simpleNecessity (content s) Q w

/-- The relations the denotation (24) draws on: convincing events, the thematic relations,
causation between eventualities, and the class of rational attitudes. -/
structure Frame (I V W : Type*) where
  convince : V → W → Prop
  agent : V → I → W → Prop
  patient : V → I → W → Prop
  cause : V → V → Prop
  rationalAttitude : V → Prop
  experiencer : I → V → Prop

/-- ⟦convincere⟧ (24): an event of `y` convincing `x` causes a rational-attitude state of `x`
with the property `P` the complement supplies. -/
def Frame.convincere (F : Frame I V W) (P : V → Prop) (x y : I) (e : V) (w : W) : Prop :=
  ∃ s, F.convince e w ∧ F.agent e y w ∧ F.patient e x w ∧ F.cause e s ∧ F.rationalAttitude s ∧
    F.experiencer x s ∧ P s

variable (F : Frame I V W) (content circumstances : AnchoringFn V W) (inertia : OrderingFn V W)
  (causeStar : V → V → W → Prop) (P : V → W → Prop) (x y : I) (e : V) (w : W)

/-- The belief report: *convincere* with the *di*-complement, the closed proposition held at the
state's content worlds. -/
def beliefReport : Prop := F.convincere (λ s => diP content (closure P) s w) x y e w

/-- The intention report: *convincere* with the *a*-complement. -/
def intentionReport : Prop := F.convincere (λ s => aP circumstances inertia causeStar P s w) x y e w

/-- Causal self-referentiality: an intention report puts the attitude state in a causal chain to
the intended event throughout the state's inertia worlds. -/
theorem intention_causal (h : intentionReport F circumstances inertia causeStar P x y e w) :
    ∃ s, F.cause e s ∧
      ∀ w', kratzerBestR (circumstances s) (inertia s) w w' → ∃ e', causeStar s e' w' ∧ P e' w' :=
  let ⟨s, _, _, _, hc, _, _, ha⟩ := h
  ⟨s, hc, ha⟩

/-- Future orientation: when causes precede their effects, the intended event of an intention
report lies after the attitude state in every inertia world, which excludes a past-oriented
complement, as in (5b). -/
theorem intention_future {T : Type*} [Preorder T] (τ : V → T)
    (hτ : ∀ s e' w', causeStar s e' w' → τ s < τ e')
    (h : intentionReport F circumstances inertia causeStar P x y e w) :
    ∃ s, F.cause e s ∧
      ∀ w', kratzerBestR (circumstances s) (inertia s) w w' → ∃ e', τ s < τ e' ∧ P e' w' :=
  let ⟨s, hc, ha⟩ := intention_causal F circumstances inertia causeStar P x y e w h
  ⟨s, hc, λ w' hw' => let ⟨e', hce, hP⟩ := ha w' hw'; ⟨e', hτ s e' w' hce, hP⟩⟩

end Semantics

/-! ### Readings from complement size -/

/-- The two construals of a rational attitude. -/
inductive Reading
  | belief
  | intention
  deriving DecidableEq, Repr

/-- The reading a complement size yields: a phase-sized complement carries the closure head and
is read as belief, a smaller one as intention. -/
def readingFromSize (cs : ComplementSize) : Reading :=
  if ComplementSize.cP ≤ cs then .belief else .intention

/-- The complement each infinitival complementizer selects: *di* a CP (21), *a* a projection
below tense with negation as its highest head (22). -/
def InfComplementizer.complementSize : InfComplementizer → ComplementSize
  | .di => .cP
  | .a_ => ⟨.Neg⟩

/-- The reading each complementizer yields. -/
def InfComplementizer.reading (c : InfComplementizer) : Reading :=
  readingFromSize (InfComplementizer.complementSize c)

/-- *convincere* has both readings, one per complementizer. -/
theorem convincere_readings :
    convincere.infComplements.map InfComplementizer.reading = [.belief, .intention] := by
  decide

/-- *credere* 'believe' has the belief reading only. -/
theorem credere_readings : credere.infComplements.map InfComplementizer.reading = [.belief] := by
  decide

/-! ### The diagnostics of sections 3 and 3.1 -/

/-- A property of an infinitival complement the paper tests. -/
inductive Diagnostic
  | belief
  | intention
  | truthAssessable
  | subjectControl
  | passive
  | aspectual
  | negation
  | independentTime
  | cliticClimbing
  deriving DecidableEq, Repr

/-- What complement size predicts for a diagnostic: the readings by the phase threshold; truth
assessment by propositionality; subject control by the finiteness head that hosts the logophoric
centre ([rizzi-1997]); passive, low aspectual verbs and negation by the Voice, v and negation
heads; a temporal domain of its own by structure above vP; clitic climbing by a complement no
larger than vP. -/
def Diagnostic.Predicted : Diagnostic → ComplementSize → Prop
  | .belief, cs => readingFromSize cs = .belief
  | .intention, cs => readingFromSize cs = .intention
  | .truthAssessable, cs => .cP ≤ cs
  | .subjectControl, cs => .finP ≤ cs
  | .passive, cs => ⟨.Voice⟩ ≤ cs
  | .aspectual, cs => .vP ≤ cs
  | .negation, cs => ⟨.Neg⟩ ≤ cs
  | .independentTime, cs => .vP < cs
  | .cliticClimbing, cs => cs ≤ .vP

instance (d : Diagnostic) (cs : ComplementSize) : Decidable (d.Predicted cs) := by
  cases d <;> unfold Diagnostic.Predicted <;> infer_instance

/-- A sentence of the paper: the size of its infinitival complement, the diagnostic it tests, and
whether it is grammatical. -/
structure Row where
  size : ComplementSize
  diagnostic : Diagnostic
  grammatical : Bool
  deriving DecidableEq

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let s ← ex.parse? "size" [("cP", InfComplementizer.complementSize .di),
    ("aP", InfComplementizer.complementSize .a_), ("vP", ComplementSize.vP)]
  let d ← ex.parse? "diagnostic" [("belief", Diagnostic.belief), ("intention", .intention),
    ("truthAssessable", .truthAssessable), ("subjectControl", .subjectControl),
    ("passive", .passive), ("aspectual", .aspectual), ("negation", .negation),
    ("independentTime", .independentTime), ("cliticClimbing", .cliticClimbing)]
  let g ← ex.parse? "grammatical" [("yes", true), ("no", false)]
  pure ⟨s, d, g⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The paper's sentences are grammatical exactly where complement size predicts. -/
theorem rows_predicted : ∀ r ∈ rows, (r.grammatical = true ↔ r.diagnostic.Predicted r.size) := by
  decide

end FuscoSgrizzi2026
