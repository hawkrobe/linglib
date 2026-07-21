import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Semantics.Presupposition.Trivalent

/-!
# Geurts 2005: Disjunctions as Modals
[geurts-2005]

Single-paper study of Bart Geurts, *Entertaining Alternatives: Disjunctions
as Modals* (Natural Language Semantics 13:383–410). Following
[zimmermann-2000], disjunctions are conjunctions of modal propositions:
"S₁ or … or Sₙ" has logical form A₁M₁B₁ ∧ … ∧ AₙMₙBₙ, where

* Aᵢ is a **modal domain** (subset of background C, context-dependent),
* Mᵢ is a **modal quantifier** (∃ or ∀, paper p.394),
* Bᵢ is the **descriptive content** of the disjunct.

## Three departures from Zimmermann (paper §3, p.391)

1. **Modal flavour** is not restricted to epistemic. The background C may
   be epistemic, deontic, circumstantial, etc.; Geurts: "I will drop the
   premiss that disjunctions are always *epistemic* modals" (p.391). Force
   (∃ vs ∀) is a separate dimension carried by `ModalForce`.
2. Overt and covert modals **fuse**: two operators per disjunct, not four.
3. Context dependence of modal **domains** Aᵢ does the work of Zimmermann's
   Self-Reflection Principle.

## Three constraints on interpretation (paper §3, p.395)

* **Exhaustivity**: C ⊆ ⋃(Aᵢ ∩ Bᵢ).
* **Disjointness**: (Aᵢ ∩ Bᵢ) ∩ (Aⱼ ∩ Bⱼ) = ∅ for i ≠ j.
* **Non-triviality**: Aᵢ ≠ ∅.

## Main declarations

* `Disjunct`, `MDisjunction` — substrate types for one disjunct and the list
  of disjuncts.
* `Disjunct.holds`, `MDisjunction.holds` — truth conditions.
* `Disjunct.cell`, `exhaustivity`, `disjointness`, `disjointness₂`,
  `nonTriviality` — the three constraints (Disjointness in n-ary form via
  `List.Pairwise`, and a binary specialisation used by the bridge theorems
  and Case #3).
* `defaultBinding` — by default A = C (paper p.394).
* `fromPartialProp`, `fromPartialProp_*_iff_orFlex`, `fromPartialProp_*_iff_orBelnap` —
  specialisation to presuppositional propositions: when domain = presup and
  content = assertion, the Geurts disjunction coincides pointwise with
  `PartialProp.orFlex` = `PartialProp.orBelnap` ([belnap-1970]).
* `exhaustivity_implies_uninformative` — used by
  `Studies/Yagi2025.lean` as the formal residue of
  [schlenker-2009]'s local-context-failure observation.

## Implementation notes

* Force is the project-canonical `Semantics.Modality.ModalForce` (necessity |
  weakNecessity | possibility, [von-fintel-iatridou-2008]). Geurts
  treats only ∃/∀; we route `weakNecessity` to the universal branch (every
  weak-necessity claim still quantifies universally over its refined
  best-worlds set).
* The `fromPartialProp_*_iff_*` lemmas are structural: `PartialProp.orFlex.presup` is
  defined as the union of disjunct presuppositions, so the iff is
  unfolding, not stipulation. The architecture intentionally avoids the
  "stipulate then prove equivalence" anti-pattern.

## Scope: wide-scope only

This file formalises Geurts's **wide-scope** analysis: every disjunction is
treated as A₁M₁B₁ ∧ … ∧ AₙMₙBₙ at LF from the outset. Free choice
"◇A ∧ ◇B follows" is immediate because the LF *is* the conjunction; the
substantive move is the LF reanalysis (p.391), not a structural inference.

## Todo

* Geurts §6 (pp.405–407) flags negated disjunctions, conditional antecedents,
  and attitude-embedded disjunctions as cases his modal analysis "runs into
  trouble" with; the speaker's-content / factual-content two-level patch in
  the §6 closing paragraphs is not formalised here.
* [ciardelli-guerrini-2026] argue "You may A or may B" gets free
  choice from the narrow-scope LF ◇(A ∨ B) via modal concord
  ([zeijlstra-2007]), not from wide-scope ◇A ∧ ◇B. Truth-conditionally
  the two analyses agree; the cross-framework comparison belongs to the
  later paper's study file ([ciardelli-guerrini-2026]).
* Geurts §5 (pp.402–404) ultimately suggests Disjointness is itself a
  conversational effect grounded in exhaustivity; formalised here only as
  the stipulated constraint, not the deeper pragmatic derivation.
-/

namespace Geurts2005

open Semantics.Modality
open Semantics.Presupposition

variable {W : Type*}

/-! ### Modal disjuncts and disjunction -/

/-- A single disjunct in a modal disjunction: AᵢMᵢBᵢ. -/
structure Disjunct (W : Type*) where
  /-- Modal domain Aᵢ (subset of the background, determined by context). -/
  domain : Set W
  /-- Modal force Mᵢ (from an overt modal or a covert default). -/
  force : ModalForce
  /-- Descriptive content Bᵢ. -/
  content : Set W

/-- A modal disjunction: a conjunction of modal propositions. -/
abbrev MDisjunction (W : Type*) := List (Disjunct W)

/-! ### Truth conditions -/

/-- A single disjunct is true iff its modal claim holds.

Possibility: ∃ w ∈ A, B(w). Necessity (and weak necessity, which still
universally quantifies over a refined domain): ∀ w ∈ A, B(w). -/
def Disjunct.holds (d : Disjunct W) : Prop :=
  match d.force with
  | .possibility => ∃ w, d.domain w ∧ d.content w
  | .necessity | .weakNecessity => ∀ w, d.domain w → d.content w

instance Disjunct.decidableHolds [Fintype W] (d : Disjunct W)
    [DecidablePred d.domain] [DecidablePred d.content] :
    Decidable d.holds := by
  unfold Disjunct.holds
  cases d.force <;> infer_instance

/-- A modal disjunction is true iff every disjunct's modal claim holds. -/
def MDisjunction.holds (disj : MDisjunction W) : Prop :=
  ∀ d ∈ disj, d.holds

/-! ### The three constraints (paper §3, p.395) -/

/-- The "modal cell" of a disjunct: worlds in both domain and content. -/
@[reducible] def Disjunct.cell (d : Disjunct W) : Set W := d.domain ∩ d.content

/-- **Exhaustivity**: C ⊆ ⋃(Aᵢ ∩ Bᵢ). Every background world falls in some
disjunct's modal cell. -/
def exhaustivity (C : Set W) (disj : MDisjunction W) : Prop :=
  ∀ w, C w → ∃ d ∈ disj, d.cell w

/-- **Disjointness** (n-ary, paper p.395): distinct disjuncts have disjoint
cells. -/
def disjointness (disj : MDisjunction W) : Prop :=
  disj.Pairwise (fun d₁ d₂ => ∀ w, ¬(d₁.cell w ∧ d₂.cell w))

/-- **Disjointness₂** — binary specialisation used by the bridge theorems
and the Case #3 worked example. -/
def disjointness₂ (d₁ d₂ : Disjunct W) : Prop :=
  ∀ w, ¬(d₁.cell w ∧ d₂.cell w)

theorem disjointness_pair_iff (d₁ d₂ : Disjunct W) :
    disjointness [d₁, d₂] ↔ disjointness₂ d₁ d₂ := by
  simp [disjointness, disjointness₂]

/-- **Non-triviality**: Aᵢ ≠ ∅. Each modal domain is non-empty. -/
def nonTriviality (disj : MDisjunction W) : Prop :=
  ∀ d, d ∈ disj → ∃ w : W, d.domain w

/-! ### Key predictions -/

/-- Each disjunct's modal claim holds individually.

Immediate because Geurts's wide-scope LF (p.391) *is* the conjunction
A₁M₁B₁ ∧ … ∧ AₙMₙBₙ from the outset: free choice "◇A ∧ ◇B follows" is a
direct projection of one conjunct, not a structural inference from ◇(A∨B).
The substantive move is the LF reanalysis, not this lemma. -/
theorem free_choice (disj : MDisjunction W)
    (h_holds : disj.holds) (d : Disjunct W) (hd : d ∈ disj) : d.holds :=
  h_holds d hd

/-- Disjointness gives the exclusive reading (paper §5, pp.402–404):
exclusivity of 'or' is derived from Disjointness, not from a scalar
implicature. -/
theorem disjointness_gives_exclusivity (d₁ d₂ : Disjunct W)
    (h_dis : disjointness₂ d₁ d₂) (w : W) (h_in_1 : d₁.cell w) :
    ¬ d₂.cell w := fun h => h_dis w ⟨h_in_1, h⟩

/-- Exhaustivity + Disjointness: every C-world lies in at most one cell.

The exhaustivity hypothesis is the upper bound (every C-world lies in
*some* cell); together they yield exact partition of C across the two
disjuncts. -/
theorem partition_unique (C : Set W) (d₁ d₂ : Disjunct W)
    (h_exh : exhaustivity C [d₁, d₂]) (h_dis : disjointness₂ d₁ d₂)
    (w : W) (hw : C w) :
    (d₁.cell w ∨ d₂.cell w) ∧ ¬(d₁.cell w ∧ d₂.cell w) := by
  refine ⟨?_, fun h => h_dis w h⟩
  rcases h_exh w hw with ⟨d, hmem, hcell⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl hcell
  · exact Or.inr hcell

/-! ### Default domain binding (paper §3, p.394) -/

/-- Default domain binding: by default each modal domain equals the
background C. The hearer tries A = C first and only restricts if the
constraints force it (paper p.394: "the hearer first attempts to equate the
quantifier domain with the background set"). -/
def defaultBinding (C : Set W) (content : List (Set W)) (f : ModalForce) :
    MDisjunction W :=
  content.map (fun b => { domain := C, force := f, content := b })

/-- With default binding and possibility force, truth is equivalent to:
each disjunct's content is satisfied somewhere in C. The basic free-choice
structure. -/
theorem default_existential_holds_iff (C : Set W) (bs : List (Set W)) :
    (defaultBinding C bs .possibility).holds ↔ ∀ b ∈ bs, ∃ w, C w ∧ b w := by
  simp only [MDisjunction.holds, defaultBinding, List.mem_map, Disjunct.holds,
    forall_exists_index, and_imp]
  constructor
  · intro h b hb; exact h _ b hb rfl
  · rintro h _ b hb rfl; exact h b hb

/-! ### Specialisation to PartialProp

When presuppositions conflict, modal domains coincide with presuppositional
domains and Geurts's disjunction specialises to `PartialProp.orFlex`. These
lemmas are structural (the orFlex domain is defined as the union of
disjunct presuppositions in `Semantics/Presupposition/Basic.lean`), not
stipulated bridges. -/

/-- Construct a Geurts possibility disjunction from two presuppositional
propositions: domains = presuppositions, contents = assertions. -/
def fromPartialProp (p q : PartialProp W) : MDisjunction W :=
  [ { domain := p.presup, force := .possibility, content := p.assertion }
  , { domain := q.presup, force := .possibility, content := q.assertion } ]

/-- The overall presupposition of a Geurts disjunction from PartialProps coincides
with `PartialProp.orFlex.presup`: p.presup ∨ q.presup. -/
theorem fromPartialProp_presup_iff_orFlex (p q : PartialProp W) (w : W) :
    (∃ d ∈ fromPartialProp p q, d.domain w) ↔ (PartialProp.orFlex p q).presup w := by
  simp [fromPartialProp, PartialProp.orFlex, PartialProp.orBelnap]

/-- The assertion side: Geurts cells = `PartialProp.orFlex.assertion`. -/
theorem fromPartialProp_cell_iff_orFlex (p q : PartialProp W) (w : W) :
    (∃ d ∈ fromPartialProp p q, d.cell w) ↔ (PartialProp.orFlex p q).assertion w := by
  simp only [fromPartialProp, Disjunct.cell, PartialProp.orFlex,
             List.mem_cons, List.not_mem_nil, or_false,
             exists_eq_or_imp, exists_eq_left]
  rfl

/-- Via the definitional identity `orFlex` = `orBelnap`: Geurts
presupposition = orBelnap presupposition ([belnap-1970] conditional
assertion). -/
theorem fromPartialProp_presup_iff_orBelnap (p q : PartialProp W) (w : W) :
    (∃ d ∈ fromPartialProp p q, d.domain w) ↔ (PartialProp.orBelnap p q).presup w :=
  fromPartialProp_presup_iff_orFlex p q w

/-- Via the definitional identity `orFlex` = `orBelnap`: Geurts cell =
orBelnap assertion. -/
theorem fromPartialProp_cell_iff_orBelnap (p q : PartialProp W) (w : W) :
    (∃ d ∈ fromPartialProp p q, d.cell w) ↔ (PartialProp.orBelnap p q).assertion w :=
  fromPartialProp_cell_iff_orFlex p q w

/-- If Geurts's exhaustivity holds for C, the disjunction (orFlex/orBelnap)
is already true throughout C — the disjunction is uninformative.

The formal residue of [schlenker-2009]'s local-context-failure
discussion: pragmatic conditions on local contexts force s₀ to contain only
worlds where some disjunct is true, making the disjunction trivially
satisfied. Geurts's Exhaustivity is the explicit form of that constraint.
Consumed by `Studies/Yagi2025.lean`. -/
theorem exhaustivity_implies_uninformative (p q : PartialProp W)
    (C : Set W) (h_exh : exhaustivity C (fromPartialProp p q))
    (w : W) (hw : C w) :
    (PartialProp.orFlex p q).assertion w :=
  (fromPartialProp_cell_iff_orFlex p q w).mp (h_exh w hw)

/-- When presuppositions conflict (p ∧ q = ⊥), the Geurts domains are
automatically disjoint — Disjointness is satisfied for free. -/
theorem conflicting_presups_disjoint (p q : PartialProp W)
    (h_conflict : ∀ w, ¬(p.presup w ∧ q.presup w)) :
    disjointness₂
      { domain := p.presup, force := .possibility, content := p.assertion }
      { domain := q.presup, force := .possibility, content := q.assertion } := by
  intro w ⟨h1, h2⟩
  simp [Disjunct.cell] at h1 h2
  exact h_conflict w ⟨h1.1, h2.1⟩

/-! ### Worked example: paper §3 Case #3, "It must be here or it must be there"

Universal force; A ⊊ C and A' ⊊ C; the constraints force A∪A' = C
(partition of C by the two modal domains, paper p.397). -/

inductive Loc where | here | there | elsewhere
  deriving DecidableEq, Repr, Inhabited, Fintype

def isHere : Set Loc := fun w => match w with | .here => True | _ => False
def isThere : Set Loc := fun w => match w with | .there => True | _ => False

instance : DecidablePred isHere :=
  fun w => by cases w <;> simp only [isHere] <;> infer_instance

instance : DecidablePred isThere :=
  fun w => by cases w <;> simp only [isThere] <;> infer_instance

/-- Background C: it's either here or there (not elsewhere). -/
def bgHereOrThere : Set Loc := fun w =>
  match w with | .here => True | .there => True | .elsewhere => False

instance : DecidablePred bgHereOrThere :=
  fun w => by cases w <;> simp only [bgHereOrThere] <;> infer_instance

/-- Disjunct 1: ∀ over domain {here}, content {here}. -/
def dHere : Disjunct Loc :=
  { domain := isHere, force := .necessity, content := isHere }

/-- Disjunct 2: ∀ over domain {there}, content {there}. -/
def dThere : Disjunct Loc :=
  { domain := isThere, force := .necessity, content := isThere }

/-- "It must be here or it must be there" with domain restriction. -/
def mustHereOrThere : MDisjunction Loc := [dHere, dThere]

theorem mustHereOrThere_holds : mustHereOrThere.holds := by
  intro d hd
  simp only [mustHereOrThere, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · intro w hw; exact hw
  · intro w hw; exact hw

theorem mustHereOrThere_exhaustive :
    exhaustivity bgHereOrThere mustHereOrThere := by
  intro w hw
  cases w
  · exact ⟨dHere, by simp [mustHereOrThere], by simp [Disjunct.cell, dHere, isHere]⟩
  · exact ⟨dThere, by simp [mustHereOrThere], by simp [Disjunct.cell, dThere, isThere]⟩
  · simp [bgHereOrThere] at hw

theorem mustHereOrThere_disjoint : disjointness₂ dHere dThere := by
  intro w ⟨h1, h2⟩
  cases w <;> simp_all [Disjunct.cell, dHere, dThere, isHere, isThere]

/-- "It must be here or it must be there" does NOT entail "it must be here"
(paper p.397): "it does not follow from (27) that It must be here, nor does
it follow that It must be there." -/
theorem must_here_not_entailed : ¬ ∀ w : Loc, bgHereOrThere w → isHere w := by
  decide

/-! ### Worked example: paper §3 Case #1, "It may be here or it may be there"

Existential force; default A = A' = C. -/

/-- "It may be here or it may be there" with default domain binding. -/
def mayHereOrThere : MDisjunction Loc :=
  defaultBinding bgHereOrThere [isHere, isThere] .possibility

theorem mayHereOrThere_holds : mayHereOrThere.holds := by
  intro d hd
  simp only [mayHereOrThere, defaultBinding, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨.here, trivial, trivial⟩
  · exact ⟨.there, trivial, trivial⟩

/-- Free choice: ◇(here) holds individually. -/
theorem mayHereOrThere_fc_here :
    Disjunct.holds (W := Loc)
      { domain := bgHereOrThere, force := .possibility, content := isHere } :=
  ⟨.here, trivial, trivial⟩

/-- Free choice: ◇(there) holds individually. -/
theorem mayHereOrThere_fc_there :
    Disjunct.holds (W := Loc)
      { domain := bgHereOrThere, force := .possibility, content := isThere } :=
  ⟨.there, trivial, trivial⟩

end Geurts2005
