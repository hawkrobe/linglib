import Linglib.Semantics.Intensional.Variables

/-!
# Maximality and Coppock–Beaver Factorization
[sharvy-1980] [kriz-2015] [coppock-beaver-2015] [russell-1905]

Predicate operators consumed by the `Description` interpretation function in
`Semantics/Definiteness/Interpret.lean`. They operate over entity predicates
`E → Prop` — the extensional fragment of `Intensional.Denot E W .et`.
At type `.et` a denotation reduces to `E → Prop` with no occurrence of the
situation type `W`, so these world-blind operators do not bind it: they apply
to any IL denotation of type `.et` by defeq, with `E` inferred from the
predicate's domain.

## What this module provides

- **Coppock–Beaver factorization** ([coppock-beaver-2015]): the Russellian
  iota is split into two independent predicates over restrictors —
  `Existence` (∃x. P x) and `Uniqueness` (∀ x y. P x → P y → x = y). The
  classical Russellian condition `existsUnique` is the conjunction.

- **Sharvy maximality** ([sharvy-1980]): the maximal P-satisfier under a
  partial order on `E`. For singular count nouns this collapses to
  Russellian iota; for plurals (with a join-semilattice on entities) it
  returns the join of all satisfiers. We supply both:
    - `russellIota` — order-free unique-element selector
    - `sharvyMax` — preorder-relative maximal-element selector

- **Križ homogeneity** ([kriz-2015]): the predicate `homogeneous P S`
  holds when the scope predicate is either uniformly true or uniformly false
  on the satisfiers of P. Required for the [kriz-2015] semantics of
  plural definites, where "the boys are tall" presupposes homogeneity rather
  than universality.

## Design notes

- **No semantic interpretation here.** This file provides only the operators.
  `Semantics/Definiteness/Interpret.lean` wires `Description` constructors to them.

- **Ord-free vs. order-relative.** `russellIota` uses only `Eq`; `sharvyMax`
  requires `PartialOrder E`. This is the [sharvy-1980] /
  [link-1983] split: singular definites work over flat individuals,
  plural definites need the join-semilattice from mereology
  ([link-1983]).

- **`Option` is the right return type.** A definite description with an
  unsatisfied uniqueness presupposition has no referent; rather than throw
  an exception or produce an arbitrary witness, we return `none`. The
  interpretation function in `Semantics/Definiteness/Interpret.lean` lifts this to
  presupposition failure at the propositional level.
-/

namespace Semantics.Definiteness

/-! ### Coppock–Beaver factorization -/

/-- [coppock-beaver-2015]'s Existence component. Asserted, not
    presupposed, in their factorization of the Russellian iota. -/
def Existence {E : Type} (P : E → Prop) : Prop :=
  ∃ x : E, P x

/-- [coppock-beaver-2015]'s Uniqueness component. Presupposed (rather
    than asserted) on their account; this is the projection contrast that
    distinguishes "the King of France isn't bald" (uniqueness presupposed)
    from a plain Russellian negation (uniqueness in scope of negation). -/
def Uniqueness {E : Type} (P : E → Prop) : Prop :=
  ∀ x y : E, P x → P y → x = y

/-- The classical Russellian condition: `∃!x. P x`. By construction the
    conjunction of [coppock-beaver-2015]'s two components. -/
def existsUnique {E : Type} (P : E → Prop) : Prop :=
  Existence P ∧ Uniqueness P

/-- Russellian existence-and-uniqueness is exactly the conjunction of
    Coppock–Beaver Existence and Uniqueness. By definition. -/
theorem existsUnique_iff_existence_and_uniqueness
    {E : Type} (P : E → Prop) :
    existsUnique P ↔ (Existence P ∧ Uniqueness P) := Iff.rfl

/-- Existence and Uniqueness are logically independent. The empty predicate
    `λ _ => False` satisfies Uniqueness (vacuously) but not Existence —
    [coppock-beaver-2015]'s key motivating data. -/
theorem uniqueness_does_not_imply_existence {E : Type} :
    Uniqueness (E := E) (fun _ => False) ∧ ¬ Existence (E := E) (fun _ => False) := by
  refine ⟨?_, ?_⟩
  · intro x y hx _; exact False.elim hx
  · rintro ⟨_, h⟩; exact h

/-! ### Russellian iota (order-free) -/

/-- The order-free unique-element selector: returns the witness when there
    is exactly one P-satisfier. Order-free version usable when no preorder is
    declared on `E`. -/
noncomputable def russellIota {E : Type} (P : E → Prop) : Option E :=
  letI := Classical.dec (existsUnique P)
  if h : existsUnique P then some h.1.choose else none

/-- `russellIota` returns `some` exactly when Russellian existence-and-
    uniqueness holds. -/
theorem russellIota_isSome_iff_existsUnique
    {E : Type} (P : E → Prop) :
    (russellIota P).isSome ↔ existsUnique P := by
  classical
  unfold russellIota
  by_cases h : existsUnique P
  · simp [h]
  · simp [h]

/-- The witness returned by `russellIota` satisfies the predicate. -/
theorem russellIota_witness_satisfies
    {E : Type} (P : E → Prop) (e : E)
    (h : russellIota P = some e) : P e := by
  classical
  unfold russellIota at h
  by_cases hexu : existsUnique P
  · rw [dif_pos hexu] at h
    have heq : hexu.1.choose = e := Option.some_inj.mp h
    rw [← heq]; exact hexu.1.choose_spec
  · rw [dif_neg hexu] at h; cases h

/-- Two witnesses returned by `russellIota` (over the same predicate) must
    coincide. By Uniqueness. -/
theorem russellIota_witness_unique
    {E : Type} (P : E → Prop) (e₁ e₂ : E)
    (h₁ : russellIota P = some e₁) (h₂ : russellIota P = some e₂) :
    e₁ = e₂ := by
  rw [h₁] at h₂
  exact Option.some_inj.mp h₂

/-- Computable list-based Russellian iota: returns the unique witness when
    `domain.filter P` is a singleton, `none` otherwise. This is the concrete
    operational counterpart to `russellIota` and the canonical referent
    selector used by `Semantics.Presupposition.presupOfReferent`. -/
def russellIotaList {E : Type*} (domain : List E) (P : E → Bool) : Option E :=
  match domain.filter P with
  | [e] => some e
  | _ => none

/-- `russellIotaList` returns `some e` iff `domain.filter P` is the singleton
    `[e]`. By definition, modulo the `match` reduction. -/
theorem russellIotaList_eq_some_iff {E : Type*} (domain : List E) (P : E → Bool)
    (e : E) :
    russellIotaList domain P = some e ↔ domain.filter P = [e] := by
  unfold russellIotaList
  cases h : domain.filter P with
  | nil => simp
  | cons hd tl =>
    cases tl with
    | nil => simp
    | cons hd' tl' => simp

/-! ### Sharvy maximality (preorder-relative) -/

/-- [sharvy-1980]: an entity `e` is *maximal* among the P-satisfiers
    when `e` satisfies `P` and dominates every other P-satisfier under `≤`.
    For singular count nouns the order is flat (only `e ≤ e`) so maximality
    coincides with Russellian uniqueness; for plurals (with [link-1983]'s
    join semilattice) maximality returns the sum of all atoms. -/
def IsMaximal {E : Type} [LE E] (P : E → Prop) (e : E) : Prop :=
  P e ∧ ∀ x : E, P x → x ≤ e

/-- Sharvy maximality is unique: at most one entity is `IsMaximal P` under a
    partial order. Antisymmetry collapses two maxima into one. -/
theorem isMaximal_unique
    {E : Type} [PartialOrder E]
    (P : E → Prop) (e₁ e₂ : E)
    (h₁ : IsMaximal P e₁) (h₂ : IsMaximal P e₂) : e₁ = e₂ := by
  exact le_antisymm (h₂.2 _ h₁.1) (h₁.2 _ h₂.1)

/-- The Sharvy maximal-element selector. Returns the unique maximal
    P-satisfier when one exists; `none` otherwise (no satisfier, or no
    upper bound among the satisfiers). -/
noncomputable def sharvyMax
    {E : Type} [PartialOrder E] (P : E → Prop) : Option E :=
  letI := Classical.dec (∃ e, IsMaximal P e)
  if h : ∃ e, IsMaximal P e then some h.choose else none

/-- `sharvyMax` returns `some` exactly when a maximal P-satisfier exists. -/
theorem sharvyMax_isSome_iff_isMaximal
    {E : Type} [PartialOrder E] (P : E → Prop) :
    (sharvyMax P).isSome ↔ ∃ e, IsMaximal P e := by
  classical
  unfold sharvyMax
  by_cases h : ∃ e, IsMaximal P e
  · simp [h]
  · simp [h]

/-- The witness returned by `sharvyMax` is maximal. -/
theorem sharvyMax_witness_isMaximal
    {E : Type} [PartialOrder E] (P : E → Prop) (e : E)
    (h : sharvyMax P = some e) : IsMaximal P e := by
  classical
  unfold sharvyMax at h
  by_cases hex : ∃ e, IsMaximal P e
  · rw [dif_pos hex] at h
    have heq : hex.choose = e := Option.some_inj.mp h
    rw [← heq]; exact hex.choose_spec
  · rw [dif_neg hex] at h; cases h

/-- The witness returned by `sharvyMax` satisfies `P`. -/
theorem sharvyMax_witness_satisfies
    {E : Type} [PartialOrder E] (P : E → Prop) (e : E)
    (h : sharvyMax P = some e) : P e :=
  (sharvyMax_witness_isMaximal P e h).1

/-! ### Križ homogeneity -/

/-- [kriz-2015]: a scope predicate `S` is *homogeneous* on the
    P-satisfiers when it holds either of all of them or of none of them.
    This is what licenses "the boys are tall" — Križ argues uniformity is
    presupposed, so partial-truth cases (some boys tall, others not) yield
    presupposition failure rather than `False`. -/
def Homogeneous {E : Type} (P S : E → Prop) : Prop :=
  (∀ x, P x → S x) ∨ (∀ x, P x → ¬ S x)

/-- Homogeneity is symmetric in its two failure modes (uniformly-S vs
    uniformly-¬S). Both yield well-defined truth values; only the *split*
    case is presupposition failure. By definition. -/
theorem homogeneous_symmetric_in_truth_value
    {E : Type} (P S : E → Prop) :
    Homogeneous P S ↔ ((∀ x, P x → S x) ∨ (∀ x, P x → ¬ S x)) := Iff.rfl

/-- Russellian uniqueness implies Križ homogeneity (vacuously beyond the
    unique witness): if there is exactly one P-satisfier, then any S is
    trivially uniform on the (singleton) extension of P. -/
theorem uniqueness_implies_homogeneous_classical
    {E : Type} (P S : E → Prop)
    (hU : Uniqueness P) :
    Homogeneous P S := by
  classical
  by_cases h : ∃ e, P e
  · obtain ⟨e, he⟩ := h
    by_cases hS : S e
    · left; intro x hx
      have hxe : x = e := hU x e hx he
      rw [hxe]; exact hS
    · right; intro x hx hSx
      have hxe : x = e := hU x e hx he
      rw [hxe] at hSx; exact hS hSx
  · left; intro x hx; exact (h ⟨x, hx⟩).elim

end Semantics.Definiteness
