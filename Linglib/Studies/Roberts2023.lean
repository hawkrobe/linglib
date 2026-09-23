module

public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Modality.Kratzer.Ordering
public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Mood.Defs
public import Linglib.Discourse.QUD.Basic
public import Mathlib.Data.List.Lex

/-!
# Roberts (2023): Imperatives in dynamic pragmatics

This file formalizes the paper's semantics and dynamic pragmatics for imperative mood. An
imperative denotes a property indexed to the addressee, its realization conditions. Over
circumstances, world–time pairs, a goal-based ordering source gives an agent's goals at a
circumstance, the timely futures of a circumstance are its possible futures at which those
goals remain in force, `timelyFut`, and a futurate circumstantial modal base delivers the
actual future circumstances in which realizing the prejacent is feasible. The applicable
circumstances are those in whose timely futures realizing the prejacent is never worse, by
the goals held there, than not realizing it, `applic`, and the property holds of an addressee
who in every applicable circumstance comes to realize the prejacent in time, `realizes`. The
content is conditional and futurate but not deontic: deontic force arises when a direction is
accepted and the realization of the property joins the addressee's goals on the scoreboard,
after which, other goals being equal, circumstances realizing it are preferred,
`Scoreboard.accept_prefers`. The illocutionary force linking principle sends each type of
denotation to the scoreboard coordinate it updates, and the conservativity presupposition on
imperative subjects restricts quantificational subjects to the addressees, `nobody_livesOn`.

## Implementation notes

Possible futures are the substrate's `futureHistoryBase`, and a goal held at a circumstance
remains in force at a later one when it is among the goals held there. Goal-relative
preference is the paper's first pass, a lexicographic ranking by priority, and a direction's
goal is appended below the goals already held, the paper's example being that staying alive
outranks pleasing a teacher. The addressee-part relation is flattened to membership in the set
of addressees. The comparison of the two rival accounts, the type-theoretic desiderata, and
embedded imperatives are discussed in the paper without a proposal formalized here.

## References

* [C. Roberts, *Imperatives in dynamic pragmatics* (2023)][roberts-2023]
* [M. Kaufmann, *Interpreting imperatives* (2012)][kaufmann-2012]
* [P. Portner, *The semantics of imperatives within a theory of clause types*
  (2004)][portner-2004]
* [P. Portner, *Imperatives and modals* (2007)][portner-2007]
* [C. Roberts, *Information structure in discourse: towards an integrated formal theory of
  pragmatics* (2012)][roberts-2012]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [A. Kratzer, *The notional category of modality* (1981)][kratzer-1981]
* [F. Veltman, *Notes on imperatives* (2018)][veltman-2018]
-/

@[expose] public section

namespace Roberts2023

open Reference HistoricalAlternatives Modality.Kratzer Quantifier Quantifier.GQ Quantifier.NP

variable {W T E : Type*}

/-! ### Circumstances, goals and futures -/

/-- A proposition (46): a set of circumstances, world–time pairs (45). -/
abbrev Proposition (W T : Type*) := Set (Index W T)

/-- A goal-based ordering source (49): an agent's goals at a circumstance, highest priority
first. -/
abbrev GoalSource (W T : Type*) := Index W T → List (Proposition W T)

section Semantics

variable [LT T] (history : HistoricalAlternatives W T) (g : GoalSource W T)

/-- The timely future circumstances of a circumstance (50): its possible futures at which the
goals held at it remain in force. -/
def timelyFut (c : Index W T) : Set (Index W T) :=
  {c' ∈ futureHistoryBase history c | ∀ p ∈ g c, p ∈ g c'}

theorem timelyFut_subset (c : Index W T) :
    timelyFut history g c ⊆ futureHistoryBase history c :=
  λ _ h => h.1

open Classical in
/-- Goal-relative preference (52), the paper's first pass: circumstances are ranked by the
highest-priority goal, ties broken by the next; `c` is worse than `c'` when `c'` realizes the
first goal on which they differ. -/
def GoalsLT (G : List (Proposition W T)) (c c' : Index W T) : Prop :=
  List.Lex (· < ·) (G.map λ p => decide (c ∈ p)) (G.map λ p => decide (c' ∈ p))

variable (f : ModalBase (Index W T)) (P : Index W T → E → Prop) (a : E)

/-- A futurate circumstantial modal base (51) for the realization of `P` by `a`: every
circumstance compatible with the base at a circumstance lies in its world, later than it, and
has a timely future at which `a` realizes `P`. -/
def IsFuturate : Prop :=
  ∀ c c', c' ∈ accessibleWorlds f c →
    c'.world = c.world ∧ c.time < c'.time ∧ ∃ c'' ∈ timelyFut history g c', P c'' a

/-- The applicable circumstances (53) for the realization of `P` by `a` at `c`: those
compatible with the modal base at `c` in whose timely futures a realizer of `P` is never
worse than a non-realizer by the goals held there. -/
def applic (c : Index W T) : Set (Index W T) :=
  {c' ∈ accessibleWorlds f c |
    ∀ c₁ ∈ timelyFut history g c', ∀ c₂ ∈ timelyFut history g c',
      P c₁ a → ¬ P c₂ a → ¬ GoalsLT (g c') c₁ c₂}

/-- The realization conditions (54): `a` has the property at `c` when in every applicable
circumstance `a` comes, at a timely later time in the same world, to realize `P`. -/
def realizes (c : Index W T) : Prop :=
  ∀ c' ∈ applic history g f P a c,
    ∃ t', c'.time < t' ∧ P (c'.world, t') a ∧ (c'.world, t') ∈ timelyFut history g c'

variable {history g f P a}

/-- Applicable circumstances are actual future circumstances: in the world of evaluation and
later than it. -/
theorem applic_future (hf : IsFuturate history g f P a) {c c' : Index W T}
    (h : c' ∈ applic history g f P a c) : c'.world = c.world ∧ c.time < c'.time :=
  let ⟨h₁, h₂, _⟩ := hf c c' h.1
  ⟨h₁, h₂⟩

/-- Realization is later still: the property is futurate. -/
theorem realizes_time_lt {c c' : Index W T} (h : realizes history g f P a c)
    (hc' : c' ∈ applic history g f P a c) : ∃ t', c'.time < t' ∧ P (c'.world, t') a :=
  let ⟨t', ht, hP, _⟩ := h c' hc'
  ⟨t', ht, hP⟩

/-- A circumstance at whose timely futures realizing the prejacent is worse than not, by the
goals held there, is not applicable: a goal already accomplished or no longer relevant
makes no circumstance applicable. -/
theorem not_mem_applic {c c' c₁ c₂ : Index W T} (h₁ : c₁ ∈ timelyFut history g c')
    (h₂ : c₂ ∈ timelyFut history g c') (hP : P c₁ a) (hnP : ¬ P c₂ a)
    (hlt : GoalsLT (g c') c₁ c₂) : c' ∉ applic history g f P a c :=
  λ h => h.2 c₁ h₁ c₂ h₂ hP hnP hlt

/-- An if-clause adds its proposition to the modal base. -/
def condition (f : ModalBase (Index W T)) (q : Proposition W T) : ModalBase (Index W T) :=
  λ c => q :: f c

/-- A condition shrinks the applicable circumstances. -/
theorem applic_condition_subset (q : Proposition W T) (c : Index W T) :
    applic history g (condition f q) P a c ⊆ applic history g f P a c :=
  λ _ h => ⟨accessibleWorlds_anti (List.subset_cons_self _ _) h.1, h.2⟩

/-- A futurate modal base stays futurate under a condition. -/
theorem IsFuturate.condition (hf : IsFuturate history g f P a) (q : Proposition W T) :
    IsFuturate history g (condition f q) P a :=
  λ c c' h => hf c c' (accessibleWorlds_anti (List.subset_cons_self _ _) h)

/-- Imperatives are conditional: a direction entails its restriction by an if-clause, which
only makes explicit some of the conditions on applicability. -/
theorem realizes_condition {c : Index W T} (h : realizes history g f P a c)
    (q : Proposition W T) : realizes history g (condition f q) P a c :=
  λ c' hc' => h c' (applic_condition_subset q c hc')

end Semantics

/-! ### The scoreboard and the pragmatics of direction -/

/-- The central coordinates of the scoreboard: the common ground, the questions under
discussion, and each interlocutor's evident goals in priority order. -/
structure Scoreboard (I W T : Type*) where
  cg : Set (Proposition W T)
  qud : List (Question (Index W T))
  goals : I → List (Proposition W T)

/-- The denotation of a root sentence: a proposition, a question, or a property indexed to
the addressee. -/
inductive Denotation (I W T : Type*)
  | proposition (p : Proposition W T)
  | question (q : Question (Index W T))
  | property (P : Index W T → I → Prop)

variable {I : Type*}

/-- The illocutionary force linking principle (56): the default force of a root sentence is
fixed by the type of its denotation. -/
def Denotation.force : Denotation I W T → Mood.Illocutionary
  | .proposition _ => .declarative
  | .question _ => .interrogative
  | .property _ => .imperative

namespace Scoreboard

variable [DecidableEq I] (K : Scoreboard I W T) (i : I)

/-- Accepting a move (57), (58), (59): an asserted proposition joins the common ground, a
posed question the questions under discussion, and a property directed to `i` adds its
realization by `i` to `i`'s goals, below those already held. -/
def accept : Denotation I W T → Scoreboard I W T
  | .proposition p => { K with cg := insert p K.cg }
  | .question q => { K with qud := q :: K.qud }
  | .property P => { K with goals := Function.update K.goals i (K.goals i ++ [{c | P c i}]) }

variable (P : Index W T → I → Prop)

/-- A direction leaves the common ground untouched. -/
@[simp] theorem accept_property_cg : (K.accept i (.property P)).cg = K.cg := rfl

/-- A direction leaves the questions under discussion untouched. -/
@[simp] theorem accept_property_qud : (K.accept i (.property P)).qud = K.qud := rfl

theorem accept_property_goals :
    (K.accept i (.property P)).goals i = K.goals i ++ [{c | P c i}] := by
  simp [accept]

/-- A direction leaves the goals of every other interlocutor untouched. -/
theorem accept_property_goals_of_ne {j : I} (hj : j ≠ i) :
    (K.accept i (.property P)).goals j = K.goals j := by
  simp [accept, Function.update_of_ne hj]

/-- Deontic force is pragmatic: once `i` accepts a direction, among circumstances alike with
respect to `i`'s prior goals one in which `i` realizes the property is preferred to one in
which `i` does not. -/
theorem accept_prefers {c c' : Index W T} (h : ∀ p ∈ K.goals i, c ∈ p ↔ c' ∈ p)
    (hc : P c i) (hc' : ¬ P c' i) :
    GoalsLT ((K.accept i (.property P)).goals i) c' c := by
  rw [accept_property_goals]
  unfold GoalsLT
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.map_congr_left λ p hp => decide_eq_decide.mpr (h p hp).symm]
  exact List.Lex.append_left _ (List.Lex.rel (by simp [hc, hc'])) _

end Scoreboard

/-! ### Imperative subjects -/

/-- The second-person pronoun (66), overt or null: application to an addressee. -/
def pro (x : E) : NP E := λ Q => Q x

/-- *Nobody* restricted to the addressees (68). -/
def nobody (addr : E → Prop) : NP E := λ Q => ∀ x, addr x → ¬ Q x

/-- An addressee's pronoun satisfies the conservativity presupposition (65): it lives on the
set of addressees. -/
theorem pro_livesOn {addr : E → Prop} {x : E} (hx : addr x) : LivesOn (pro x) addr :=
  λ _ => ⟨λ h => ⟨hx, h⟩, λ h => h.2⟩

/-- Restricted *nobody* satisfies the conservativity presupposition. -/
theorem nobody_livesOn (addr : E → Prop) : LivesOn (nobody addr) addr :=
  λ _ => ⟨λ h x hx hQ => h x hx hQ.2, λ h x hx hQ => h x hx ⟨hx, hQ⟩⟩

/-- The derivation (42′) of *Nobody move!*: the addressees have the property when in every
applicable circumstance there is a timely later time at which none of them moves, so each of
them is directed not to move in the applicable circumstances. -/
theorem realizes_nobody_move_iff [LT T] (history : HistoricalAlternatives W T)
    (g : GoalSource W T) (f : ModalBase (Index W T)) (addr : E → Prop)
    (move : Index W T → E → Prop) (c : Index W T) (x : E) :
    realizes history g f (λ c _ => nobody addr (move c)) x c ↔
      ∀ c' ∈ applic history g f (λ c _ => nobody addr (move c)) x c,
        ∃ t', c'.time < t' ∧ (∀ y, addr y → ¬ move (c'.world, t') y) ∧
          (c'.world, t') ∈ timelyFut history g c' :=
  Iff.rfl

end Roberts2023
