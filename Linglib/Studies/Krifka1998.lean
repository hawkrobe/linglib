import Linglib.Semantics.Aspect.Cumulativity

/-!
# Krifka (1998): The Origins of Telicity

This file formalizes [krifka-1998]'s account of telicity as a property of event
predicates rather than of events: a predicate is telic when no event it applies to has a
proper part it also applies to that starts or ends at a different time. Telicity is then
derived rather than stipulated. For verbs of consumption and creation it follows from the
mereological transfer between object and event that the thematic relation performs, the
strictly incremental relations of `Aspect.Incremental`; for movement verbs it follows from
the conditions the paper adds to the part relation: expansion, adjacency, source and goal.

Quantized predicates are telic (`isTelic_of_qua`) but not conversely, and cumulative
predicates are atelic once they apply to two non-contemporaneous events. On a model of
*eat*, *eat apples* is cumulative and *eat two
apples* quantized (`eat_two_apples_qua`). Expansion with mapping to objects makes the
verb phrase of a quantized object telic (`isTelic_vp_of_seinc`), and a movement with a
specified source and goal is telic (`isTelic_sourceGoal`). The movement diagrams of the
paper are checked against the adjacency condition on a finite model (`Movement`).

## Implementation notes

* Temporal precedence is a parameter of the telicity notions. The paper's consequence of
  its event axioms that overlapping events never precede each other enters as
  `NoPartPrecedes`, which is all the proofs use.
* Overlap is `Mereology.Overlap`, relative to a possible null element. The paper's part
  structures have none, so the expansion theorems assume that the thematic relation never
  relates the null object.
* The source and goal conditions quantify the subpath and the subevent separately; the
  formalization ties them through the thematic relation, as the paper's telicity proof does.
* The strict-movement telicity claim of the paper does not follow from adjacency and
  mapping to objects alone (adjacency may be empty), and the tangentiality condition on
  sums of movements, the derived measure functions for movement and the changes in other
  dimensions are not formalized.
* In the finite model, the diagram's detour consists of the segments `h` and `i`; the
  paper's list of movements calls the second one `j`.

## References

* [krifka-1998]
-/

namespace Krifka1998

open Mereology ArgumentStructure Aspect.Incremental Aspect.Cumulativity

variable {α β : Type*}

/-! ### Telicity by initial and final parts -/

section Telicity

variable [PartialOrder β] (precedes : β → β → Prop)

/-- An initial part of an event: a part no part of the event precedes. -/
def IsInitialPart (e' e : β) : Prop := e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e'

/-- A final part of an event: a part no part of the event follows. -/
def IsFinalPart (e' e : β) : Prop := e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e' e''

/-- A telic predicate: every `P`-part of a `P`-event is an initial and a final part of it. -/
def IsTelic (P : β → Prop) : Prop :=
  ∀ e e', P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

/-- Parts of an event neither precede nor follow it. -/
def NoPartPrecedes : Prop := ∀ a b : β, a ≤ b → ¬ precedes a b ∧ ¬ precedes b a

variable {precedes}

theorem isInitialPart_self (h : NoPartPrecedes precedes) (e : β) :
    IsInitialPart precedes e e :=
  ⟨le_rfl, λ ⟨_, h', hp⟩ => (h _ _ h').1 hp⟩

theorem isFinalPart_self (h : NoPartPrecedes precedes) (e : β) : IsFinalPart precedes e e :=
  ⟨le_rfl, λ ⟨_, h', hp⟩ => (h _ _ h').2 hp⟩

/-- Quantized predicates are telic. -/
theorem isTelic_of_qua (h : NoPartPrecedes precedes) {P : β → Prop} (hP : QUA P) :
    IsTelic precedes P := λ e e' he he' hle => by
  obtain rfl : e' = e := by_contra λ hne => hP he' he hne hle
  exact ⟨isInitialPart_self h _, isFinalPart_self h _⟩

/-- Among contemporaneous events every predicate is telic. -/
theorem isTelic_of_not_precedes (h : ∀ a b, ¬ precedes a b) (P : β → Prop) :
    IsTelic precedes P :=
  λ _ _ _ _ hle => ⟨⟨hle, λ ⟨_, _, hp⟩ => h _ _ hp⟩, ⟨hle, λ ⟨_, _, hp⟩ => h _ _ hp⟩⟩

end Telicity

/-- Telic but not quantized: the predicate true of every event running from three to four,
on two such events one part of the other. -/
theorem exists_isTelic_not_qua : ∃ P : Bool → Prop, IsTelic (λ _ _ => False) P ∧ ¬ QUA P :=
  ⟨λ _ => True, isTelic_of_not_precedes (λ _ _ => id) _,
    λ h => h (x := false) trivial (y := true) trivial Bool.noConfusion (Bool.false_le true)⟩

/-- A cumulative predicate true of two events, a part of one following the other, is not
telic. -/
theorem not_isTelic_of_cum [SemilatticeSup β] {precedes : β → β → Prop} {P : β → Prop}
    (hP : CUM P) {e e' e'' : β} (he : P e) (he' : P e') (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes P :=
  λ hT => (hT (e ⊔ e') e' (hP he he') he' le_sup_right).2.2 ⟨e'', h''.trans le_sup_left, hp⟩

/-! ### Eating apples -/

section Eat

/-- A model of *eat*: three apples, and an eating event identified with the apples it
consumes. -/
def eat (x e : Finset (Fin 3)) : Prop := x = e

private theorem eat_sinc : SINC eat where
  mso _ _ _ h hlt := ⟨_, h ▸ hlt, rfl⟩
  uo _ _ _ h hle := ⟨_, h ▸ hle, rfl, λ _ _ hz => hz⟩
  mse _ _ _ h hlt := ⟨_, h ▸ hlt, rfl⟩
  ue _ _ _ h hle := ⟨_, h ▸ hle, rfl, λ _ _ hz => hz.symm⟩
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, rfl, rfl⟩

instance : IsSincVerb eat :=
  IsSincVerb.mk' eat_sinc (λ _ _ _ hx hy => hx.trans hy.symm)
    (λ _ _ _ _ hx hy => show _ ⊔ _ = _ ⊔ _ by rw [hx, hy])

/-- *eat apples* is cumulative: the bare plural is cumulative and *eat* is cumulative. -/
theorem eat_apples_cum : CUM (VP eat Finset.Nonempty) :=
  cum_propagation λ _ hx _ _ => hx.mono Finset.subset_union_left

/-- *eat two apples* is quantized: a measure phrase is quantized and *eat* is strictly
incremental. -/
theorem eat_two_apples_qua : QUA (VP eat (Finset.card · = 2)) :=
  qua_propagation (extMeasure_qua 2)

end Eat

/-- *eat it*: with a particular object, a strictly incremental verb phrase is quantized. -/
theorem qua_vp_eq [SemilatticeSup α] [SemilatticeSup β] {θ : α → β → Prop} [IsSincVerb θ]
    (y : α) : QUA (VP θ (· = y)) :=
  qua_propagation (singleton_qua y)

/-! ### Telicity by expansion -/

section Expansion

variable [SemilatticeSup α] [SemilatticeSup β] (precedes : β → β → Prop) (θ : α → β → Prop)

/-- Expansion: the objects of temporally ordered events do not overlap. -/
def EXP : Prop := ∀ x y e e', θ x e → θ y e' → precedes e e' → ¬ Overlap x y

/-- A strictly expansive incremental relation: expansion with mapping to objects. -/
def SEINC : Prop := EXP precedes θ ∧ MO θ

variable {precedes θ} (h : SEINC precedes θ) (h₀ : ∀ x e, θ x e → ¬ IsBot x) {x : α} {e e' : β}
include h h₀

/-- Under a strictly expansive incremental relation, an object's events are initial parts
of each other. -/
theorem isInitialPart_of_seinc (hx : θ x e) (hx' : θ x e') (hle : e' ≤ e) :
    IsInitialPart precedes e' e :=
  ⟨hle, λ ⟨e'', h'', hp⟩ =>
    let ⟨y, hy, hθ⟩ := h.2 x e e'' hx h''
    h.1 y x e'' e' hθ hx' hp ⟨y, h₀ y e'' hθ, le_rfl, hy⟩⟩

/-- Under a strictly expansive incremental relation, an object's events are final parts of
each other. -/
theorem isFinalPart_of_seinc (hx : θ x e) (hx' : θ x e') (hle : e' ≤ e) :
    IsFinalPart precedes e' e :=
  ⟨hle, λ ⟨e'', h'', hp⟩ =>
    let ⟨y, hy, hθ⟩ := h.2 x e e'' hx h''
    h.1 x y e' e'' hx' hθ hp ⟨y, h₀ y e'' hθ, hy, le_rfl⟩⟩

/-- The events of a fixed object under a strictly expansive incremental relation form a
telic predicate. -/
theorem isTelic_of_seinc (x : α) : IsTelic precedes (θ x) :=
  λ _ _ hx hx' hle => ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

/-- *eat two apples* is telic: the verb phrase of a quantized object under a strictly
expansive incremental relation with unique participants. -/
theorem isTelic_vp_of_seinc (hUP : UP θ) {OBJ : α → Prop} (hOBJ : QUA OBJ) :
    IsTelic precedes (VP θ OBJ) := by
  rintro e e' ⟨x, hOx, hx⟩ ⟨x', hOx', hx'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := h.2 x e e' hx hle
  obtain rfl := hUP x' x'' e' hx' hx''
  obtain rfl : x' = x := by_contra λ hne => hOBJ hOx' hOx hne hx''le
  exact ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

end Expansion

/-! ### Movement relations -/

section Movement

variable [SemilatticeSup α] [SemilatticeSup β] (adjα : α → α → Prop) (adjβ : β → β → Prop)
  (precedes : β → β → Prop) (isPath : α → Prop) (θ : α → β → Prop)

/-- The adjacency property: two subevents of a movement are temporally adjacent iff their
paths are spatially adjacent. -/
def ADJ : Prop :=
  ∀ x e y z e' e'', θ x e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x → θ y e' → θ z e'' →
    (adjβ e' e'' ↔ adjα y z)

/-- A strict movement relation: adjacency, mapping to objects, and paths as objects. -/
def SMR : Prop := ADJ adjα adjβ θ ∧ MO θ ∧ ∀ x e, θ x e → isPath x

/-- A movement relation: the closure of a strict movement relation under sums of
temporally ordered events. -/
def MR : Prop :=
  ∃ θ', SMR adjα adjβ isPath θ' ∧ ∀ x e, θ x e ↔ Aspect.PrecedenceClosure precedes θ' x e

/-- The subpaths of a movement adjacent to `y` are the paths of its initial parts. -/
def Source (y x : α) (e : β) : Prop :=
  ∀ x' e', θ x' e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsInitialPart precedes e' e)

/-- The subpaths of a movement adjacent to `y` are the paths of its final parts. -/
def Goal (y x : α) (e : β) : Prop :=
  ∀ x' e', θ x' e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsFinalPart precedes e' e)

variable {adjα adjβ precedes isPath θ}

/-- A strict movement relation closed under sums of temporally ordered events is a movement
relation. -/
theorem mr_of_smr (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x₁ x₂ e₁ e₂, θ x₁ e₁ → θ x₂ e₂ → precedes e₁ e₂ → θ (x₁ ⊔ x₂) (e₁ ⊔ e₂)) :
    MR adjα adjβ precedes isPath θ :=
  ⟨θ, h, λ _ _ => ⟨.base, Aspect.PrecedenceClosure.closure_subset (λ _ _ => id) hClosed⟩⟩

/-- *walk from the university to the capitol* is telic: a movement with a specified source
and goal, under mapping to objects and uniqueness of participants. -/
theorem isTelic_sourceGoal (hax : NoPartPrecedes precedes) (hMO : MO θ) (hUP : UP θ)
    (u v : α) :
    IsTelic precedes
      (λ e => ∃ x, θ x e ∧ Source adjα precedes θ u x e ∧ Goal adjα precedes θ v x e) := by
  rintro e e' ⟨x, hx, hS, hG⟩ ⟨x', hx', hS', hG'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := hMO x e e' hx hle
  obtain rfl := hUP x' x'' e' hx' hx''
  exact ⟨(hS x' e' hx' hx''le hle).1 ((hS' x' e' hx' le_rfl le_rfl).2 (isInitialPart_self hax e')),
    (hG x' e' hx' hx''le hle).1 ((hG' x' e' hx' le_rfl le_rfl).2 (isFinalPart_self hax e'))⟩

end Movement

/-! ### The movement diagrams -/

section Diagram

/-- The path segments of the paper's diagram: `a` to `g` in a line, `h` and `i` a detour
from `c` to `f`. -/
inductive Seg | a | b | c | d | e | f | g | h | i
  deriving DecidableEq

/-- The adjacent pairs of segments. -/
def Seg.edges : List (Seg × Seg) :=
  [(.a, .b), (.b, .c), (.c, .d), (.d, .e), (.e, .f), (.f, .g), (.c, .h), (.h, .i), (.i, .f)]

/-- Adjacency of segments. -/
def Seg.adj (s t : Seg) : Prop := (s, t) ∈ edges ∨ (t, s) ∈ edges

instance (s t : Seg) : Decidable (s.adj t) := by unfold Seg.adj; infer_instance

/-- Adjacency of paths: disjoint, with an adjacent pair of segments. -/
def pathAdj (x y : Finset Seg) : Prop := Disjoint x y ∧ ∃ s ∈ x, ∃ t ∈ y, s.adj t

/-- Adjacency of events: disjoint, with a consecutive pair of times. -/
def eventAdj (e e' : Finset (Fin 7)) : Prop :=
  Disjoint e e' ∧ ∃ i ∈ e, ∃ j ∈ e', i.val + 1 = j.val ∨ j.val + 1 = i.val

instance (x y : Finset Seg) : Decidable (pathAdj x y) := by unfold pathAdj; infer_instance

instance (e e' : Finset (Fin 7)) : Decidable (eventAdj e e') := by
  unfold eventAdj; infer_instance

/-- The pairs a diagram relates: its atomic movements and the whole. -/
def support (L : List (Seg × Fin 7)) : List (Finset Seg × Finset (Fin 7)) :=
  L.map (λ p => ({p.1}, {p.2})) ++ [((L.map Prod.fst).toFinset, (L.map Prod.snd).toFinset)]

/-- The movement relation a diagram depicts. -/
def Movement (L : List (Seg × Fin 7)) (x : Finset Seg) (e : Finset (Fin 7)) : Prop :=
  (x, e) ∈ support L

instance (L : List (Seg × Fin 7)) (x : Finset Seg) (e : Finset (Fin 7)) :
    Decidable (Movement L x e) := by
  unfold Movement; infer_instance

private theorem adj_movement_iff {L : List (Seg × Fin 7)} :
    ADJ pathAdj eventAdj (Movement L) ↔
      ∀ p ∈ support L, ∀ q ∈ support L, ∀ r ∈ support L,
        q.2 ≤ p.2 → r.2 ≤ p.2 → q.1 ≤ p.1 → r.1 ≤ p.1 → (eventAdj q.2 r.2 ↔ pathAdj q.1 r.1) :=
  ⟨λ h p hp q hq r hr h₁ h₂ h₃ h₄ => h p.1 p.2 q.1 r.1 q.2 r.2 hp h₁ h₂ h₃ h₄ hq hr,
    λ h _ _ _ _ _ _ hp h₁ h₂ h₃ h₄ hq hr => h _ hp _ hq _ hr h₁ h₂ h₃ h₄⟩

/-- A walk along `a` to `f`. -/
def walk : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.d, 3), (.e, 4), (.f, 5)]

/-- A stop-and-go movement: a pause between `c` and `d`. -/
def stopAndGo : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.d, 4), (.e, 5), (.f, 6)]

/-- Telekinesis: from `b` straight to `e`. -/
def telekinesis : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.e, 2), (.f, 3)]

/-- An Echternach movement: a return along `c` and `b`. -/
def echternach : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.c, 3), (.b, 4)]

/-- An Alcatraz movement: around the circle `c`, `d`, `e`, `f`, `i`, `h`. -/
def alcatraz : List (Seg × Fin 7) := [(.c, 0), (.d, 1), (.e, 2), (.f, 3), (.i, 4), (.h, 5)]

/-- A movement along a disconnected path. -/
def disconnected : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.e, 4), (.f, 5)]

theorem adj_walk : ADJ pathAdj eventAdj (Movement walk) := adj_movement_iff.2 (by decide)

theorem not_adj_stopAndGo : ¬ ADJ pathAdj eventAdj (Movement stopAndGo) := λ h =>
  absurd (h {.a, .b, .c, .d, .e, .f} {0, 1, 2, 4, 5, 6} {.c} {.d} {2} {4} (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_telekinesis : ¬ ADJ pathAdj eventAdj (Movement telekinesis) := λ h =>
  absurd (h {.a, .b, .e, .f} {0, 1, 2, 3} {.b} {.e} {1} {2} (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_echternach : ¬ ADJ pathAdj eventAdj (Movement echternach) := λ h =>
  absurd (h {.a, .b, .c} {0, 1, 2, 3, 4} {.c} {.c} {2} {3} (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_alcatraz : ¬ ADJ pathAdj eventAdj (Movement alcatraz) := λ h =>
  absurd (h {.c, .d, .e, .f, .i, .h} {0, 1, 2, 3, 4, 5} {.h} {.c} {5} {0} (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- A connected set of segments: no proper nonempty subset is closed under adjacency. -/
def Connected (x : Finset Seg) : Prop :=
  ∀ y ∈ x.powerset, y.Nonempty → y ≠ x → ∃ s ∈ y, ∃ t ∈ x \ y, s.adj t

/-- The disconnected movement satisfies adjacency but its path is not connected. -/
theorem adj_disconnected :
    ADJ pathAdj eventAdj (Movement disconnected) ∧ ¬ Connected {.a, .b, .e, .f} :=
  ⟨adj_movement_iff.2 (by decide),
    λ h => absurd (h {.a, .b} (by decide) (by decide) (by decide)) (by decide)⟩

end Diagram

end Krifka1998
