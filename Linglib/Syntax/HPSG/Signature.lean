import Mathlib.Order.Basic
import Mathlib.Order.Max
import Linglib.Core.Relation.ReflTransGen

/-!
# RSRL signatures
[richter-2000], [richter-2024], [pollard-sag-1994]

An RSRL **signature** (Def. 47): a sort hierarchy `[PartialOrder Srt]` (`a ≤ b` = "`a` at least
as specific as `b`") with appropriateness declarations and relation symbols. The
model-theoretic foundation of HPSG (Pollard & Sag 1994 onward); `Interpretation.lean` gives the
models, `Description.lean` the description language.
-/

namespace HPSG.RSRL

universe u

/-- Build a `PartialOrder` from a decidable boolean order whose laws hold (typically `by decide`
on a finite type). Reducible so `≤` unfolds to `leB · · = true` in instance search. -/
@[reducible] def partialOrderOfBool {α : Type u} (leB : α → α → Bool)
    (le_refl : ∀ a, leB a a = true)
    (le_trans : ∀ a b c, leB a b = true → leB b c = true → leB a c = true)
    (le_antisymm : ∀ a b, leB a b = true → leB b a = true → a = b) : PartialOrder α where
  le a b := leB a b = true
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

/-! ### Structural subsumption order from a covers relation

`partialOrderOfBool` discharges transitivity by `decide`, which is `|α|³` and exceeds the elaborator
recursion depth on a large sort hierarchy. The mathlib-idiomatic alternative is to define `≤` as the
**reflexive-transitive closure** of a *direct-subsumption* (`covers`) relation, so transitivity is
structural (`ReflTransGen.trans`) and never a proof obligation — and antisymmetry follows from a `rank`
function every edge strictly decreases. The author then declares the `~|α|`-edge DAG and a depth
function, not the transitively-closed relation. -/

private theorem rankLe_of_reflTransGen {α : Type u} {covers : α → α → Prop} {rank : α → ℕ}
    (hrank : ∀ a b, covers a b → rank b < rank a)
    {a b : α} (hab : Relation.ReflTransGen covers a b) : rank b ≤ rank a := by
  induction hab with
  | refl => exact le_refl _
  | tail _ hr ih => exact le_of_lt (lt_of_lt_of_le (hrank _ _ hr) ih)

private theorem eq_of_reflTransGen_rank_eq {α : Type u} {covers : α → α → Prop} {rank : α → ℕ}
    (hrank : ∀ a b, covers a b → rank b < rank a)
    {a b : α} (hab : Relation.ReflTransGen covers a b) (h : rank a = rank b) : a = b := by
  cases hab with
  | refl => rfl
  | tail hac hcb =>
    exfalso
    have h1 := rankLe_of_reflTransGen hrank hac
    have h2 := hrank _ _ hcb
    omega

/-- Build a `PartialOrder` from a **direct-subsumption ("covers") relation** and a `rank` that every
edge strictly decreases. `≤` is `ReflTransGen covers`; transitivity is structural and antisymmetry
follows from `rank` — no `decide` over the order, so it scales where `partialOrderOfBool` does not. -/
@[reducible] def partialOrderOfCovers {α : Type u} (covers : α → α → Prop) (rank : α → ℕ)
    (hrank : ∀ a b, covers a b → rank b < rank a) : PartialOrder α where
  le a b := Relation.ReflTransGen covers a b
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ hab hba :=
    eq_of_reflTransGen_rank_eq hrank hab
      (Nat.le_antisymm (rankLe_of_reflTransGen hrank hba) (rankLe_of_reflTransGen hrank hab))

/-- `Decidable (a ≤ b)` for `partialOrderOfCovers`, via finite reachability over an explicit list of
all sorts (`Core.Relation.ReflTransGen.decidable_of_finite` — mathlib has no `Decidable (ReflTransGen
…)`; the **`List`**-based variant kernel-reduces under `decide` where the `Finset`/`Quotient` one does
not). `allSorts` need only contain every `covers`-target; pass the sort enumeration. -/
@[reducible] def decidableLEOfCovers {α : Type u} [DecidableEq α] {covers : α → α → Prop}
    [DecidableRel covers] (allSorts : List α) (complete : ∀ a b, covers a b → b ∈ allSorts)
    (a b : α) : Decidable (Relation.ReflTransGen covers a b) :=
  Relation.ReflTransGen.decidable_of_finite allSorts complete a b

/-- An RSRL signature ([richter-2000], Def. 47) over a sort hierarchy `Srt`. -/
structure Signature (Srt : Type u) [PartialOrder Srt] where
  /-- Attributes (feature names). -/
  Attr : Type u
  /-- Relation symbols (unused until a principle needs relations). -/
  Rel : Type u
  /-- Relation arities. -/
  arity : Rel → Nat
  /-- Appropriateness: `approp σ α = some τ` means `α` is appropriate to `σ` with value sort `τ`. -/
  approp : Srt → Attr → Option Srt
  /-- Feature inheritance: a more specific sort inherits appropriateness with an at-least-as-
  specific value. -/
  approp_inherits : ∀ {σ₁ σ₂ : Srt} {α : Attr} {τ₁ : Srt},
    σ₂ ≤ σ₁ → approp σ₁ α = some τ₁ → ∃ τ₂, approp σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁

/-- A **species** is a maximally specific sort — minimal in the specificity order. -/
abbrev IsSpecies {Srt : Type u} [PartialOrder Srt] (σ : Srt) : Prop := IsMin σ

/-- An **atomic** sort: a species with no appropriate attributes. (Distinct from `IsAtom`.) -/
def Signature.IsAtomicSort {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) (σ : Srt) :
    Prop := IsMin σ ∧ ∀ α, Sig.approp σ α = none

/-- A `:`-rooted attribute **path** (Def. 52, variable-free fragment): `[]` is the described
entity, `α :: p` follows `α` then the rest. -/
abbrev Path {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List Sig.Attr

/-- An RSRL **term** (Def. 52): rooted at the described entity (`colon`) or a variable (`var n`),
extended by attributes (`feat t α`). Variables support relations and quantification. -/
inductive Term {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- The described entity (RSRL `:`). -/
  | colon : Term Sig
  /-- A variable. -/
  | var : Nat → Term Sig
  /-- Follow attribute `α` from `t` (RSRL `tα`). -/
  | feat : Term Sig → Sig.Attr → Term Sig

/-- The `:`-rooted term following a path: `Term.path [α, β] = (colon.feat α).feat β`. -/
def Term.path {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} (p : Path Sig) : Term Sig :=
  p.foldl Term.feat Term.colon

/-- Derive the `Signature.approp_inherits` obligation from an `isSome`-gated **propagation** lemma.
When appropriateness values do not refine down the order (a sort and its subsorts carry the *same*
value for an attribute — the common case), the inherited value is `τ₁` itself, so the propagation
`σ₂ ≤ σ₁ → (approp σ₁ α).isSome → approp σ₂ α = approp σ₁ α` suffices. A large signature proves that
propagation by `decide` (no `∃`-search, no `τ₁` quantifier — far cheaper) and feeds it here. -/
theorem approp_inh_of_propagates {Srt : Type u} [PartialOrder Srt] {Attr : Type u}
    {approp : Srt → Attr → Option Srt}
    (h : ∀ (σ₁ σ₂ : Srt) (α : Attr),
      σ₂ ≤ σ₁ → (approp σ₁ α).isSome = true → approp σ₂ α = approp σ₁ α)
    {σ₁ σ₂ : Srt} {α : Attr} {τ₁ : Srt} (hle : σ₂ ≤ σ₁) (happ : approp σ₁ α = some τ₁) :
    ∃ τ₂, approp σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by
  have hsome : (approp σ₁ α).isSome = true := by rw [happ]; rfl
  exact ⟨τ₁, (h σ₁ σ₂ α hle hsome).trans happ, le_refl τ₁⟩

end HPSG.RSRL
