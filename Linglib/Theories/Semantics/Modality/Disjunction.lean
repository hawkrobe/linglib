/-
# Disjunctions as Modals
@cite{yagi-2025}

Formalizes @cite{geurts-2005} "Entertaining Alternatives: Disjunctions as Modals"
(Natural Language Semantics 13:383–410).

## Thesis

Following @cite{zimmermann-2000}, disjunctions are conjunctions of modal propositions.
"S₁ or … or Sₙ" has logical form A₁M₁B₁ ∧ … ∧ AₙMₙBₙ, where:
- Aᵢ is a **modal domain** (subset of background C)
- Mᵢ is a **modal quantifier** (◇ or □, from overt modal or covert default)
- Bᵢ is the **descriptive content** of the disjunct

Three innovations over Zimmermann:
1. Modal force is not restricted to epistemic — it is context-dependent
2. Overt and covert modals **fuse** (two operators, not four)
3. Context dependence of modal domains does the work of Self-Reflection

## Three Constraints on Interpretation (§3)

- **Exhaustivity**: C ⊆ ∪(Aᵢ ∩ Bᵢ) — background worlds are covered
- **Disjointness**: (Aᵢ ∩ Bᵢ) ∩ (Aⱼ ∩ Bⱼ) = ∅ — alternatives don't overlap
- **Non-triviality**: Aᵢ ≠ ∅ — each modal domain is non-empty

## Bridge Theorems

- `PrProp.orFlex` is the special case where domains = presuppositions
- `PrProp.orFlex = PrProp.orBelnap`: three-way equivalence —
  Geurts (modal conjunction) = Belnap (conditional assertion) = Yagi (flexible accommodation)
- This identity generalizes beyond disjunction: `PrProp.belnapLift` shows
  that flexible accommodation and Belnap conditional assertion are the same
  construction for ANY binary connective (`andFlex = andBelnap`, etc.)
- Exhaustivity + conflicting presuppositions → disjunction uninformative
  (captures Schlenker's local context failure, @cite{yagi-2025} §2.4)
- Free choice (◇(A∨B) → ◇A ∧ ◇B) follows from the structure
- Exclusive 'or' follows from Disjointness, not scalar implicature

## Note on "may A or may B" sentences

@cite{ciardelli-guerrini-2026} argue that sentences like "You may A or you
may B" — which @cite{geurts-2005} analyzes as overt modal disjunctions —
receive their FC reading from the **narrow-scope** LF ◇(A ∨ B) via modal
concord (@cite{zeijlstra-2007}), not from the wide-scope LF ◇A ∨ ◇B.
Since ◇(A ∨ B) ↔ ◇A ∨ ◇B truth-conditionally, the two analyses agree on
truth conditions but differ on compositional source. The Geurts analysis
here is compatible with C&G if the "overt modals" in such sentences are
reanalyzed as uninterpretable concord markers rather than semantic operators.
See `CiardelliGuerrini2026`.

-/

import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.Presupposition

namespace Semantics.Modality.Disjunction

open Core.Proposition
open Core.Presupposition

variable {W : Type*}


-- ══════════════════════════════════════════════════════════
-- § Modal disjuncts and disjunction
-- ══════════════════════════════════════════════════════════

/-- Modal force: existential (◇) or universal (□). -/
inductive Force where
  | existential  -- ◇: may, might, can
  | universal    -- □: must, have to, will
  deriving DecidableEq, Repr

/-- A single disjunct in a modal disjunction: Aᵢ Mᵢ Bᵢ. -/
structure Disjunct (W : Type*) where
  /-- Modal domain Aᵢ (subset of background, determined by context). -/
  domain : BProp W
  /-- Modal force Mᵢ (from overt modal or covert default). -/
  force : Force
  /-- Descriptive content Bᵢ. -/
  content : BProp W

/-- A modal disjunction: conjunction of modal propositions. -/
abbrev MDisjunction (W : Type*) := List (Disjunct W)


-- ══════════════════════════════════════════════════════════
-- § Truth conditions
-- ══════════════════════════════════════════════════════════

/-- A single disjunct is true iff its modal claim holds.
◇: ∃w ∈ A, B(w). □: ∀w ∈ A, B(w). -/
def Disjunct.holds [FiniteWorlds W] (d : Disjunct W) : Bool :=
  match d.force with
  | .existential => FiniteWorlds.worlds.any (fun w => d.domain w && d.content w)
  | .universal   => FiniteWorlds.worlds.all (fun w => !d.domain w || d.content w)

/-- A modal disjunction is true iff every disjunct's modal claim holds. -/
def MDisjunction.holds [FiniteWorlds W] (disj : MDisjunction W) : Bool :=
  disj.all (fun d => d.holds)


-- ══════════════════════════════════════════════════════════
-- § The three constraints (Geurts §3, p. 395)
-- ══════════════════════════════════════════════════════════

/-- The "modal cell" of a disjunct: worlds in both domain and content. -/
def Disjunct.cell (d : Disjunct W) : BProp W := fun w => d.domain w && d.content w

/-- **Exhaustivity**: C ⊆ ∪(Aᵢ ∩ Bᵢ). All background worlds are covered
by some disjunct's modal cell. -/
def exhaustivity (C : BProp W) (disj : MDisjunction W) : Prop :=
  ∀ w, C w = true → disj.any (fun d => d.cell w) = true

/-- **Disjointness** for binary disjunctions: cells don't overlap.
(Aᵢ ∩ Bᵢ) ∩ (Aⱼ ∩ Bⱼ) = ∅ for i ≠ j. -/
def disjointness₂ (d₁ d₂ : Disjunct W) : Prop :=
  ∀ w, ¬(d₁.cell w = true ∧ d₂.cell w = true)

/-- **Non-triviality**: Aᵢ ≠ ∅. Each modal domain is non-empty. -/
def nonTriviality [FiniteWorlds W] (disj : MDisjunction W) : Prop :=
  ∀ d, d ∈ disj → FiniteWorlds.worlds.any d.domain = true


-- ══════════════════════════════════════════════════════════
-- § Key predictions
-- ══════════════════════════════════════════════════════════

/-- Free choice: for a modal disjunction, each disjunct's modal claim
holds individually.

Geurts §3 Case #1/2: "It may be here or it may be there" →
each individual "may" claim holds. This is immediate from the
structure: the disjunction IS a conjunction of modal claims. -/
theorem free_choice [FiniteWorlds W] (disj : MDisjunction W)
    (h_holds : disj.holds = true)
    (d : Disjunct W) (hd : d ∈ disj) :
    d.holds = true := by
  simp [MDisjunction.holds, List.all_eq_true] at h_holds
  exact h_holds d hd

/-- Disjointness gives exclusive reading.

If cells are disjoint and world w is in cell 1, it is not in cell 2.
This is Geurts §5: exclusive 'or' from Disjointness, NOT scalar implicature. -/
theorem disjointness_gives_exclusivity (d₁ d₂ : Disjunct W)
    (h_dis : disjointness₂ d₁ d₂) (w : W)
    (h_in_1 : d₁.cell w = true) :
    d₂.cell w = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact h_dis w ⟨h_in_1, h⟩

/-- Exhaustivity + Disjointness → each C-world in exactly one cell. -/
theorem partition_unique (C : BProp W) (d₁ d₂ : Disjunct W)
    (_h_exh : exhaustivity C [d₁, d₂])
    (h_dis : disjointness₂ d₁ d₂)
    (w : W) (_hw : C w = true) (h1 : d₁.cell w = true) :
    d₂.cell w = false :=
  disjointness_gives_exclusivity d₁ d₂ h_dis w h1


-- ══════════════════════════════════════════════════════════
-- § Default domain binding (Geurts §3, p. 394)
-- ══════════════════════════════════════════════════════════

/-- Default domain binding: by default, each modal domain equals
the background C. The hearer tries A = C first, and only restricts
if constraints force it (Geurts p. 394). -/
def defaultBinding (C : BProp W) (content : List (BProp W)) (f : Force) :
    MDisjunction W :=
  content.map (fun b => { domain := C, force := f, content := b })

/-- With default binding and existential force, truth = each disjunct
is possible w.r.t. C. This is the basic free choice structure. -/
theorem default_existential_holds_iff [FiniteWorlds W]
    (C : BProp W) (bs : List (BProp W)) :
    (defaultBinding C bs .existential).holds =
    bs.all (fun b => FiniteWorlds.worlds.any (fun w => C w && b w)) := by
  simp only [MDisjunction.holds, defaultBinding, List.all_map, Function.comp_def,
    Disjunct.holds]


-- ══════════════════════════════════════════════════════════
-- § Bridge: Geurts disjunction → PrProp.orFlex
-- When presuppositions conflict, modal domains = presuppositional
-- domains, and the Geurts disjunction specializes to orFlex.
-- ══════════════════════════════════════════════════════════

/-- Construct a Geurts existential disjunction from two presuppositional
propositions: domains = presuppositions, contents = assertions.
Requires decidability for the Prop→Bool bridge. -/
def fromPrProp (p q : PrProp W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion] : MDisjunction W :=
  [ { domain := fun w => decide (p.presup w), force := .existential,
      content := fun w => decide (p.assertion w) }
  , { domain := fun w => decide (q.presup w), force := .existential,
      content := fun w => decide (q.assertion w) } ]

/-- The overall presupposition of a Geurts disjunction from PrProps is
p.presup ∨ q.presup — matching PrProp.orFlex. -/
theorem fromPrProp_presup_iff_orFlex (p q : PrProp W) (w : W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion] :
    (fromPrProp p q).any (fun d => d.domain w) = true ↔
    (PrProp.orFlex p q).presup w := by
  simp [fromPrProp, PrProp.orFlex, List.any_cons, List.any_nil, decide_eq_true_eq]

/-- The assertion of a Geurts disjunction from PrProps matches orFlex:
(p.presup ∧ p.assertion) ∨ (q.presup ∧ q.assertion). -/
theorem fromPrProp_cell_iff_orFlex (p q : PrProp W) (w : W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion] :
    (fromPrProp p q).any (fun d => d.cell w) = true ↔
    (PrProp.orFlex p q).assertion w := by
  simp [fromPrProp, Disjunct.cell, PrProp.orFlex, List.any_cons, List.any_nil,
    Bool.and_eq_true, decide_eq_true_eq]

/-- The three-way equivalence: Geurts (modal conjunction) =
PrProp.orBelnap (conditional assertion, @cite{belnap-1970}).
Transitivity via `fromPrProp_presup_iff_orFlex` + `orFlex_eq_orBelnap`. -/
theorem fromPrProp_presup_iff_orBelnap (p q : PrProp W) (w : W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion] :
    (fromPrProp p q).any (fun d => d.domain w) = true ↔
    (PrProp.orBelnap p q).presup w := by
  rw [fromPrProp_presup_iff_orFlex, ← PrProp.orFlex_eq_orBelnap]

/-- The three-way equivalence (assertion side):
Geurts cell = orBelnap assertion = orFlex assertion. -/
theorem fromPrProp_cell_iff_orBelnap (p q : PrProp W) (w : W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion] :
    (fromPrProp p q).any (fun d => d.cell w) = true ↔
    (PrProp.orBelnap p q).assertion w := by
  rw [fromPrProp_cell_iff_orFlex, ← PrProp.orFlex_eq_orBelnap]

/-- **Exhaustivity forces uninformativity.** If Geurts's exhaustivity
constraint holds for context C, the disjunction (orFlex/orBelnap) is
already true throughout C — the disjunction is uninformative.

This captures the essence of @cite{schlenker-2009}'s local context failure
(@cite{yagi-2025} §2.4): the pragmatic condition on local contexts forces
s₀ to contain only worlds where some disjunct is true, making the
disjunction trivially satisfied. Geurts's exhaustivity constraint makes
this explicit: it IS the constraint that contexts must be covered by
disjunct cells. -/
theorem exhaustivity_implies_uninformative (p q : PrProp W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion]
    (C : BProp W) (h_exh : exhaustivity C (fromPrProp p q))
    (w : W) (hw : C w = true) :
    (PrProp.orFlex p q).assertion w := by
  exact (fromPrProp_cell_iff_orFlex p q w).mp (h_exh w hw)

/-- When presuppositions conflict (p ∧ q = ⊥), the Geurts domains are
automatically disjoint — the Disjointness constraint is satisfied for free. -/
theorem conflicting_presups_disjoint (p q : PrProp W)
    [DecidablePred p.presup] [DecidablePred p.assertion]
    [DecidablePred q.presup] [DecidablePred q.assertion]
    (h_conflict : ∀ w, ¬(p.presup w ∧ q.presup w)) :
    disjointness₂
      { domain := fun w => decide (p.presup w), force := .existential,
        content := fun w => decide (p.assertion w) }
      { domain := fun w => decide (q.presup w), force := .existential,
        content := fun w => decide (q.assertion w) } := by
  intro w ⟨h1, h2⟩
  simp [Disjunct.cell, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  exact h_conflict w ⟨h1.1, h2.1⟩


-- ══════════════════════════════════════════════════════════
-- § Worked example: Geurts §3, Cases #3–#4
-- "It must be here or it must be there" (universal force)
-- ══════════════════════════════════════════════════════════

inductive Loc where | here | there | elsewhere
  deriving DecidableEq, Repr, Inhabited

instance : FiniteWorlds Loc where
  worlds := [.here, .there, .elsewhere]
  complete := fun w => by cases w <;> simp

def isHere : BProp Loc | .here => true | _ => false
def isThere : BProp Loc | .there => true | _ => false

/-- Background C: it's either here or there (not elsewhere). -/
def bgHereOrThere : BProp Loc | .here => true | .there => true | .elsewhere => false

/-- Disjunct 1: □(here) over domain {here}. -/
def dHere : Disjunct Loc := { domain := isHere, force := .universal, content := isHere }

/-- Disjunct 2: □(there) over domain {there}. -/
def dThere : Disjunct Loc := { domain := isThere, force := .universal, content := isThere }

/-- "It must be here or it must be there" with domain restriction.
Exhaustivity+Disjointness force A = {here}, A' = {there}. -/
def mustHereOrThere : MDisjunction Loc := [dHere, dThere]

/-- The disjunction holds: □(here) over {here} ∧ □(there) over {there}. -/
theorem mustHereOrThere_holds : mustHereOrThere.holds = true := by decide

/-- Exhaustivity: bgHereOrThere ⊆ {here} ∪ {there}. -/
theorem mustHereOrThere_exhaustive :
    exhaustivity bgHereOrThere mustHereOrThere := by
  intro w hw; cases w <;> simp_all [bgHereOrThere, mustHereOrThere, dHere, dThere,
    Disjunct.cell, isHere, isThere, List.any_cons, List.any_nil]

/-- Disjointness: {here} ∩ {there} = ∅. -/
theorem mustHereOrThere_disjoint : disjointness₂ dHere dThere := by
  intro w ⟨h1, h2⟩
  simp [Disjunct.cell, dHere, dThere, isHere, isThere] at h1 h2
  cases w <;> simp_all

/-- Key prediction: "It must be here or it must be there" does NOT entail
"it must be here". The necessity over the full background fails. -/
theorem must_here_not_entailed :
    FiniteWorlds.worlds.all (fun w => !bgHereOrThere w || isHere w) = false := by
  decide


-- ══════════════════════════════════════════════════════════
-- § Worked example: Geurts §3, Case #1
-- "It may be here or it may be there" (existential force)
-- ══════════════════════════════════════════════════════════

/-- "It may be here or it may be there" with default domain binding. -/
def mayHereOrThere : MDisjunction Loc :=
  defaultBinding bgHereOrThere [isHere, isThere] .existential

/-- The disjunction holds: ◇(here) w.r.t. C ∧ ◇(there) w.r.t. C. -/
theorem mayHereOrThere_holds : mayHereOrThere.holds = true := by decide

/-- Free choice: ◇(here) holds individually. -/
theorem mayHereOrThere_fc_here :
    Disjunct.holds (W := Loc)
      { domain := bgHereOrThere, force := .existential, content := isHere } = true := by
  decide

/-- Free choice: ◇(there) holds individually. -/
theorem mayHereOrThere_fc_there :
    Disjunct.holds (W := Loc)
      { domain := bgHereOrThere, force := .existential, content := isThere } = true := by
  decide


end Semantics.Modality.Disjunction
