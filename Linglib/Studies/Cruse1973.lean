import Linglib.Semantics.ArgumentStructure.EnergySource
import Linglib.Data.Examples.Cruse1973

/-!
# Some thoughts on agentivity

Cruse replaces the referential definitions of agentivity, Fillmore's animate perceived
instigator and Gruber's wilful source, by an entailment test: a noun is a doer in a sentence
when the sentence entails that the noun did something. The test admits inanimate doers,
process verbs and statives, against the received opinions, so doing is heterogeneous: at
least four features each suffice for it, the volitive, the effective, the initiative and the
agentive, an instrument being none of them, and each has contextual diagnostics of its own.

We check the paper's examples against its diagnostics: normality in each frame is what the
noun's features predict, the three counterexamples to the received opinions are among the
data, and the volitive and the effective alone each make a doer.

## References

* [D. A. Cruse, *Some thoughts on agentivity* (1973)][cruse-1973]
* [C. J. Fillmore, *The case for case* (1968)][fillmore-1968]
* [J. S. Gruber, *Look and see* (1967)][gruber-1967]
* [M. A. K. Halliday, *Notes on transitivity and theme in English: part 1*
  (1967)][halliday-1967]
* [M. A. K. Halliday, *Notes on transitivity and theme in English: part 3*
  (1968)][halliday-1968]
* [J. Lyons, *Structural semantics* (1963)][lyons-1963]
* [J. Lyons, *Introduction to theoretical linguistics* (1968)][lyons-1968]
* [J. M. Anderson, *The grammar of case* (1971)][anderson-1971]
* [W. L. Chafe, *Meaning and the structure of language* (1970)][chafe-1970]
-/

namespace Cruse1973

open ArgumentStructure

/-- The doing features the paper attributes to a noun in relation to its verb. -/
structure Profile where
  /-- An act of will is stated or implied. -/
  volitive : Bool := false
  /-- The action is initiated by giving a command. -/
  initiative : Bool := false
  /-- The source of the noun's energy, if it bears force. -/
  energy : Option EnergySource := none
  deriving DecidableEq

/-- A doer: any feature suffices, an instrument's borrowed energy excepted. -/
def Profile.IsDoer (p : Profile) : Prop :=
  p.volitive = true ∨ p.initiative = true ∨ ∃ s ∈ p.energy, s.IsSelfEnergetic

instance : DecidablePred Profile.IsDoer := λ _ => by unfold Profile.IsDoer; infer_instance

/-- The frames the paper places a sentence in. -/
inductive Frame where
  /-- *What X did was …*, for a subject. -/
  | doForm
  /-- *What happened to X was that …*, for a subject. -/
  | happenForm
  /-- *X VP entails X did something*, or the normality of *X VP: it therefore follows that X did
  something*, for a subject or an object. -/
  | entails
  /-- A purpose phrase *in order to …*. -/
  | purpose
  /-- The imperative. -/
  | imperative
  /-- Modification by *carefully*. -/
  | carefully
  /-- Reflexivization of an ergative verb used intransitively, or *V oneself Adj* for a
  non-ergative, with minor rather than considerable semantic effects. -/
  | reflexive
  /-- A manner adverb of energy output, *powerfully*, *vigorously* or *energetically*, for
  gross physical actions. -/
  | manner
  /-- Transitive *fly* with the noun as its object. -/
  | causative
  /-- A context denying a precondition of initiation by command. -/
  | initiativeDenial
  /-- The progressive form, Lyons's criterion for stativity. -/
  | progressive
  /-- The sentence itself. -/
  | plain
  deriving DecidableEq

/-- Normality of a sentence in a frame as the paper's diagnostics predict it from the noun's
profile. The paper claims only that each feature suffices for the *do* form; that a noun with
no feature is no doer is read off its happen-sentences. The sentence itself is normal, and
the progressive, tied to stativity rather than to the profile, is left normal, no progressive
example carrying a profile. -/
def Frame.Normal (t : Frame) (p : Profile) : Prop :=
  match t with
  | .doForm | .entails => p.IsDoer
  | .happenForm => ¬ p.IsDoer
  | .purpose | .imperative => p.volitive = true
  | .carefully => p.volitive = true ∧ p.energy = some .internal
  | .reflexive | .manner | .causative => p.energy = some .internal
  | .initiativeDenial => p.initiative = false
  | .progressive | .plain => True

instance : DecidableRel Frame.Normal := λ t _ => by
  cases t <;> simp only [Frame.Normal] <;> infer_instance

/-- Lyons's verb classes at issue in the received opinions. -/
inductive VerbClass where
  /-- An obligatorily process verb, *die*. -/
  | process
  /-- A stative verb, *stand*, *have*. -/
  | stative
  deriving DecidableEq

/-! ### The paper's examples -/

/-- The frames by their `paperFeatures` labels. -/
def Frame.labels : List (String × Frame) :=
  [("do", .doForm), ("happen", .happenForm), ("entails", .entails), ("purpose", .purpose),
   ("imperative", .imperative), ("carefully", .carefully), ("reflexive", .reflexive),
   ("manner", .manner), ("causative", .causative), ("initiativeDenial", .initiativeDenial),
   ("progressive", .progressive), ("plain", .plain)]

/-- The profiles by their `paperFeatures` labels. -/
def Profile.labels : List (String × Profile) :=
  [("", {}), ("volitive", { volitive := true }), ("initiative", { initiative := true }),
   ("agentive", { energy := some .internal }), ("effective", { energy := some .imparted }),
   ("instrumental", { energy := some .instrumental }),
   ("volitive+agentive", { volitive := true, energy := some .internal })]

/-- An example of the paper: its frame, the profile of its noun, and the judgment, the paper's
query mark read as questionable and a failed entailment as one. -/
structure Datum where
  frame : Frame
  /-- The profile attributed to the noun, if any; the stative and neutralized examples carry
  none. -/
  profile : Option Profile
  /-- Whether the attribution is the study's rather than the paper's. -/
  inferred : Bool
  /-- Whether the noun is marked inanimate. -/
  inanimate : Bool
  /-- The verb's class, where a received opinion is at issue. -/
  verbClass : Option VerbClass
  /-- Whether *do* and *happen* are neutralized, as in *why does the door do that*. -/
  neutralized : Bool
  judgment : Features.Judgment

/-- An example read into its frame, profile and judgment. -/
def datum (e : Data.Examples.LinguisticExample) : Option Datum := do
  pure { frame := ← e.parse? "frame" Frame.labels
         profile := e.parse? "features" Profile.labels
         inferred := decide (e.feature? "inferred" = some "true")
         inanimate := decide (e.feature? "animate" = some "false")
         verbClass := e.parse? "verbClass" [("process", .process), ("stative", .stative)]
         neutralized := decide (e.feature? "neutralized" = some "true")
         judgment := e.judgment }

/-- Every example names its frame. -/
theorem isSome_datum : ∀ e ∈ Examples.all, (datum e).isSome := by decide

/-- The paper's examples. -/
def data : List Datum := Examples.all.filterMap datum

/-- A sentence is normal in its frame exactly when its noun's profile predicts it,
neutralization aside. -/
theorem acceptable_iff_normal : ∀ d ∈ data, d.neutralized = false →
    ∀ p ∈ d.profile, (d.judgment = .acceptable ↔ d.frame.Normal p) := by
  decide

/-! ### Against the received opinions -/

/-- An inanimate noun is a doer: the wind, the computer, the bullet. -/
theorem exists_inanimate_doer :
    ∃ d ∈ data, d.inanimate = true ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by decide

/-- A process verb has a *do*-interpretation: dying in order to save us. -/
theorem exists_process_doer :
    ∃ d ∈ data, d.verbClass = some .process ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

/-- A stative verb has a *do*-interpretation: standing, having one's passport ready. -/
theorem exists_stative_doer :
    ∃ d ∈ data, d.verbClass = some .stative ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

/-! ### The heterogeneity of doing -/

/-- The volitive alone makes a doer on the paper's own attribution: drifting so as to avoid
enemy territory. -/
theorem exists_volitive_doer : ∃ d ∈ data, d.inferred = false ∧
    d.profile = some { volitive := true } ∧ d.frame = .doForm ∧ d.judgment = .acceptable := by
  decide

/-- The effective alone makes a doer on the paper's own attribution: the flying stone breaking
the window. The agentive alone, as in sneezing, rests on the study's attribution. -/
theorem exists_effective_doer : ∃ d ∈ data, d.inferred = false ∧
    d.profile = some { energy := some .imparted } ∧ d.frame = .doForm ∧
    d.judgment = .acceptable := by
  decide

end Cruse1973
