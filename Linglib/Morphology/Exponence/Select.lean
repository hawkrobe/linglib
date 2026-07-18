import Linglib.Morphology.Exponence.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.MinMax

/-!
# Elsewhere selection over rules of exponence
[kiparsky-1973] [halle-marantz-1993] [stump-2001] [caha-2009]

Selection over the specificity preorder of `Morphology/Exponence/Basic.lean`.
An **Elsewhere winner** is a `≤`-minimal applicable rule; over a coherent
vocabulary comparable winners select one exponent, so the prediction relation
`Realizes` is well defined up to incomparability. `selectBy` computes a winner
by optimizing a specificity **score** `f : R → α` into a linear order — the
common shape of every framework engine's competition (`argmax` over the
applicable sublist; min-scores enter via `OrderDual`). Its soundness law
`selectBy_isElsewhereWinner` discharges each engine's winner-is-Elsewhere
theorem from that engine's score-reflection lemma. The order/select/realize
triad: `Basic` orders rules by specificity, `selectBy` selects the optimal
applicable rule, `realize` reads off its exponent. The theory models
selection within a single rule block; realizational frameworks compose
per-block winners into the paradigm function ([stump-2001]). Since
`Realizes.eq` makes the per-block prediction unique, *optional* multiple
exponence within a block (free co-realization variants, Jubba Maay —
[trommer-zimmermann-2015] p. 60) is outside scope, not merely a
multi-block composition matter; deterministic symbiotic co-exponence
composes across blocks as usual.

## Main declarations

* `IsElsewhereWinner`, `Coherent`, `exists_isElsewhereWinner` — the Prop
  selection theory: minimality, coherence, existence
* `Realizes` — the framework-neutral prediction relation
* `selectBy`, `realize` — score selection and the realized exponent
* `selectBy_isElsewhereWinner`, `realize_realizes` — score selection is
  Elsewhere selection
-/

namespace Morphology.Exponence

variable {Ctx F : Type*} {R : Type*} [Preorder R] [Exponence R Ctx F]

/-! ### Elsewhere winners -/

/-- An **Elsewhere winner** for vocabulary `v` at context `c`: a
`≤`-minimal applicable member of `v` — no applicable rule in `v` is
strictly more specific. -/
def IsElsewhereWinner (v : List R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s => s ∈ v ∧ Exponence.Applies (F := F) s c) r

/-- A winner is at least as specific as any applicable member of the
vocabulary that is at least as specific as it. -/
theorem IsElsewhereWinner.le_of_le {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : s ∈ v)
    (happ : Exponence.Applies (F := F) s c) (h : s ≤ r) : r ≤ s :=
  Minimal.le_of_le hr ⟨hs, happ⟩ h

/-! ### Coherence and uniqueness -/

/-- Comparable Elsewhere winners at the same context are equivalent. -/
theorem IsElsewhereWinner.antisymmRel {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : IsElsewhereWinner v c s)
    (h : s ≤ r ∨ r ≤ s) : AntisymmRel (· ≤ ·) r s := by
  rcases h with h | h
  · exact ⟨hr.le_of_le hs.1.1 hs.1.2 h, h⟩
  · exact ⟨h, hs.le_of_le hr.1.1 hr.1.2 h⟩

/-- A **coherent** vocabulary assigns equivalent rules the same
exponent, so the exponent descends to the antisymmetrization of the
specificity preorder ([caha-2009]-style antihomophony, stated
order-theoretically). Incomparable competitors are tolerated, where
[stump-2001]'s Pāṇinian Determinism Hypothesis forbids them. -/
def Coherent (v : List R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    Exponence.exponent (F := F) r = Exponence.exponent (F := F) s

/-- Over a coherent vocabulary, comparable winners select the same
exponent: Elsewhere selection is well defined up to incomparability. -/
theorem IsElsewhereWinner.exponent_eq {v : List R} {c : Ctx} {r s : R}
    (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    Exponence.exponent (F := F) r = Exponence.exponent (F := F) s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner —
proved, where [stump-2001] guarantees existence by stipulating a
bottom-element Identity Function Default. -/
theorem exists_isElsewhereWinner {v : List R} {c : Ctx}
    (h : ∃ r ∈ v, Exponence.Applies (F := F) r c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

/-! ### The prediction relation -/

/-- The framework-neutral prediction: `φ` is realized at `c` when some
Elsewhere winner carries it. -/
def Realizes (v : List R) (c : Ctx) (φ : F) : Prop :=
  ∃ r, IsElsewhereWinner v c r ∧ Exponence.exponent (F := F) r = φ

/-- Over a coherent vocabulary whose winners are comparable, the
prediction is unique. -/
theorem Realizes.eq {v : List R} {c : Ctx} {φ ψ : F} (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hφ : Realizes v c φ) (hψ : Realizes v c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hcmp hr hs)

/-! ### Score selection

For a specificity **score** `f : R → α` into a linear order, `selectBy`
picks the applicable rule of greatest score. Engines whose score is
minimized (span, tree size, `Finsupp`-support card) pass it through
`OrderDual α`. -/

variable [∀ c : Ctx, DecidablePred (fun r : R => Exponence.Applies (F := F) r c)]

/-- The rules of `v` applicable at `c`, in vocabulary order. -/
def applicable (v : List R) (c : Ctx) : List R :=
  v.filter (fun r => Exponence.Applies (F := F) r c)

omit [Preorder R] in
@[simp] theorem mem_applicable {v : List R} {c : Ctx} {r : R} :
    r ∈ applicable v c ↔ r ∈ v ∧ Exponence.Applies (F := F) r c := by
  simp only [applicable, List.mem_filter, decide_eq_true_eq]

variable {α : Type*} [LinearOrder α]

/-- Selection by specificity score: the applicable rule of `v` at `c`
with greatest score `f`, ties broken by vocabulary order (`⊥` when
nothing applies). -/
def selectBy (f : R → α) (v : List R) (c : Ctx) : Option R :=
  (applicable v c).argmax f

omit [Preorder R] in
theorem selectBy_mem {f : R → α} {v : List R} {c : Ctx} {r : R}
    (h : selectBy f v c = some r) : r ∈ v :=
  (mem_applicable.mp (List.argmax_mem h)).1

omit [Preorder R] in
theorem selectBy_applies {f : R → α} {v : List R} {c : Ctx} {r : R}
    (h : selectBy f v c = some r) : Exponence.Applies (F := F) r c :=
  (mem_applicable.mp (List.argmax_mem h)).2

omit [Preorder R] in
theorem selectBy_eq_none_iff {f : R → α} {v : List R} {c : Ctx} :
    selectBy f v c = none ↔ applicable v c = [] :=
  List.argmax_eq_none

/-- With the score reflecting specificity contravariantly on applicable
rules, the selection is at least as specific as every applicable rule
— it is `≤` all of them, no comparability assumed. -/
theorem selectBy_le_of_applies {f : R → α} {v : List R} {c : Ctx} {r s : R}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Exponence.Applies (F := F) r c →
      Exponence.Applies (F := F) s c → (r ≤ s ↔ f s ≤ f r))
    (h : selectBy f v c = some r) (hs : s ∈ v)
    (hsapp : Exponence.Applies (F := F) s c) : r ≤ s :=
  (hf r (selectBy_mem h) s hs (selectBy_applies h) hsapp).mpr
    (List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsapp⟩) h)

/-- **Soundness**: a score reflecting specificity contravariantly on
comparable applicable rules selects an Elsewhere winner. Only the
conditional (`mpr`) direction is needed — argmax supplies `f s ≤ f r`
and minimality supplies `s ≤ r`, so `hf` just closes `r ≤ s`.
Linear-domain engines discharge `hf` from the `mpr` of their `le_iff`;
`Finset`-support engines, where card `≤` does not imply support `⊆`,
discharge it via `Finset.eq_of_subset_of_card_le`. -/
theorem selectBy_isElsewhereWinner {f : R → α} {v : List R} {c : Ctx} {r : R}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Exponence.Applies (F := F) r c →
      Exponence.Applies (F := F) s c → s ≤ r → f s ≤ f r → r ≤ s)
    (h : selectBy f v c = some r) : IsElsewhereWinner v c r := by
  refine ⟨⟨selectBy_mem h, selectBy_applies h⟩, ?_⟩
  rintro s ⟨hs, hsapp⟩ hsr
  exact hf r (selectBy_mem h) s hs (selectBy_applies h) hsapp hsr
    (List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsapp⟩) h)

omit [Preorder R] in
/-- Contexts with the same applicable rules select the same rule. -/
theorem selectBy_congr {f : R → α} {v : List R} {c c' : Ctx}
    (h : applicable v c = applicable v c') :
    selectBy f v c = selectBy f v c' := by
  rw [selectBy, selectBy, h]

/-! ### Realization -/

/-- The realized exponent: the score-selected winner's exponent
(`none` when no rule applies). -/
def realize (f : R → α) (v : List R) (c : Ctx) : Option F :=
  (selectBy f v c).map (Exponence.exponent (F := F))

/-- A realized exponent is genuinely predicted: it is `Realizes`. -/
theorem realize_realizes {f : R → α} {v : List R} {c : Ctx} {φ : F}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Exponence.Applies (F := F) r c →
      Exponence.Applies (F := F) s c → s ≤ r → f s ≤ f r → r ≤ s)
    (h : realize f v c = some φ) : Realizes v c φ := by
  rw [realize, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r, selectBy_isElsewhereWinner hf hr, rfl⟩

omit [Preorder R] in
theorem realize_eq_none_iff {f : R → α} {v : List R} {c : Ctx} :
    realize f v c = none ↔ applicable v c = [] := by
  rw [realize, Option.map_eq_none_iff]
  exact selectBy_eq_none_iff

omit [Preorder R] in
theorem realize_congr {f : R → α} {v : List R} {c c' : Ctx}
    (h : applicable v c = applicable v c') :
    realize f v c = realize f v c' := by
  rw [realize, realize, selectBy_congr h]

end Morphology.Exponence
