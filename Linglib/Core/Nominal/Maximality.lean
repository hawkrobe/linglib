import Linglib.Core.IntensionalLogic.Variables

/-!
# Maximality and Coppock–Beaver Factorization
@cite{sharvy-1980} @cite{kriz-2015} @cite{coppock-beaver-2015} @cite{russell-1905}

Predicate operators consumed by the `NominalKind` interpretation function in
`Core/Nominal/Interpret.lean`. All operators live over
`Core.IntensionalLogic.Frame.Denot` so they slot directly into the IL stack.

## What this module provides

- **Coppock–Beaver factorization** (@cite{coppock-beaver-2015}): the Russellian
  iota is split into two independent predicates over restrictors —
  `Existence` (∃x. P x) and `Uniqueness` (∀ x y. P x → P y → x = y). The
  classical Russellian condition `existsUnique` is the conjunction.

- **Sharvy maximality** (@cite{sharvy-1980}): the maximal P-satisfier under a
  partial order on `F.Entity`. For singular count nouns this collapses to
  Russellian iota; for plurals (with a join-semilattice on entities) it
  returns the join of all satisfiers. We supply both:
    - `russellIota` — order-free unique-element selector
    - `sharvyMax` — preorder-relative maximal-element selector

- **Križ homogeneity** (@cite{kriz-2015}): the predicate `homogeneous P S`
  holds when the scope predicate is either uniformly true or uniformly false
  on the satisfiers of P. Required for the @cite{kriz-2015} semantics of
  plural definites, where "the boys are tall" presupposes homogeneity rather
  than universality.

## Design notes

- **No semantic interpretation here.** This file provides only the operators.
  `Core/Nominal/Interpret.lean` wires `NominalKind` constructors to them.

- **Ord-free vs. order-relative.** `russellIota` uses only `Eq`; `sharvyMax`
  requires `PartialOrder F.Entity`. This is the @cite{sharvy-1980} /
  @cite{link-1983} split: singular definites work over flat individuals,
  plural definites need the join-semilattice from mereology
  (@cite{link-1983}).

- **`Option` is the right return type.** A definite description with an
  unsatisfied uniqueness presupposition has no referent; rather than throw
  an exception or produce an arbitrary witness, we return `none`. The
  interpretation function in `Core/Nominal/Interpret.lean` lifts this to
  presupposition failure at the propositional level.
-/

namespace Core.Nominal

open Core.IntensionalLogic

-- ════════════════════════════════════════════════════════════════
-- § Coppock–Beaver Factorization
-- ════════════════════════════════════════════════════════════════

/-- @cite{coppock-beaver-2015}'s Existence component. Asserted, not
    presupposed, in their factorization of the Russellian iota. -/
def Existence {F : Frame} (P : F.Denot .et) : Prop :=
  ∃ x : F.Entity, P x

/-- @cite{coppock-beaver-2015}'s Uniqueness component. Presupposed (rather
    than asserted) on their account; this is the projection contrast that
    distinguishes "the King of France isn't bald" (uniqueness presupposed)
    from a plain Russellian negation (uniqueness in scope of negation). -/
def Uniqueness {F : Frame} (P : F.Denot .et) : Prop :=
  ∀ x y : F.Entity, P x → P y → x = y

/-- The classical Russellian condition: `∃!x. P x`. By construction the
    conjunction of @cite{coppock-beaver-2015}'s two components. -/
def existsUnique {F : Frame} (P : F.Denot .et) : Prop :=
  Existence P ∧ Uniqueness P

/-- Russellian existence-and-uniqueness is exactly the conjunction of
    Coppock–Beaver Existence and Uniqueness. By definition. -/
theorem existsUnique_iff_existence_and_uniqueness
    {F : Frame} (P : F.Denot .et) :
    existsUnique P ↔ (Existence P ∧ Uniqueness P) := Iff.rfl

/-- Existence and Uniqueness are logically independent. The empty predicate
    `λ _ => False` satisfies Uniqueness (vacuously) but not Existence —
    @cite{coppock-beaver-2015}'s key motivating data. -/
theorem uniqueness_does_not_imply_existence {F : Frame} :
    Uniqueness (F := F) (fun _ => False) ∧ ¬ Existence (F := F) (fun _ => False) := by
  refine ⟨?_, ?_⟩
  · intro x y hx _; exact False.elim hx
  · rintro ⟨_, h⟩; exact h

-- ════════════════════════════════════════════════════════════════
-- § Russellian Iota (order-free)
-- ════════════════════════════════════════════════════════════════

/-- The order-free unique-element selector: returns the witness when there
    is exactly one P-satisfier. Order-free version usable when no preorder is
    declared on `F.Entity`. -/
noncomputable def russellIota {F : Frame} (P : F.Denot .et) : Option F.Entity :=
  letI := Classical.dec (existsUnique P)
  if h : existsUnique P then some h.1.choose else none

/-- `russellIota` returns `some` exactly when Russellian existence-and-
    uniqueness holds. -/
theorem russellIota_isSome_iff_existsUnique
    {F : Frame} (P : F.Denot .et) :
    (russellIota P).isSome ↔ existsUnique P := by
  classical
  unfold russellIota
  by_cases h : existsUnique P
  · simp [h]
  · simp [h]

/-- The witness returned by `russellIota` satisfies the predicate. -/
theorem russellIota_witness_satisfies
    {F : Frame} (P : F.Denot .et) (e : F.Entity)
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
    {F : Frame} (P : F.Denot .et) (e₁ e₂ : F.Entity)
    (h₁ : russellIota P = some e₁) (h₂ : russellIota P = some e₂) :
    e₁ = e₂ := by
  rw [h₁] at h₂
  exact Option.some_inj.mp h₂

/-- Computable list-based Russellian iota: returns the unique witness when
    `domain.filter P` is a singleton, `none` otherwise. This is the concrete
    operational counterpart to `russellIota` and the canonical referent
    selector used by `Core.Presupposition.presupOfReferent`. -/
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

-- ════════════════════════════════════════════════════════════════
-- § Sharvy Maximality (preorder-relative)
-- ════════════════════════════════════════════════════════════════

/-- @cite{sharvy-1980}: an entity `e` is *maximal* among the P-satisfiers
    when `e` satisfies `P` and dominates every other P-satisfier under `≤`.
    For singular count nouns the order is flat (only `e ≤ e`) so maximality
    coincides with Russellian uniqueness; for plurals (with @cite{link-1983}'s
    join semilattice) maximality returns the sum of all atoms. -/
def IsMaximal {F : Frame} [LE F.Entity] (P : F.Denot .et) (e : F.Entity) : Prop :=
  P e ∧ ∀ x : F.Entity, P x → x ≤ e

/-- Sharvy maximality is unique: at most one entity is `IsMaximal P` under a
    partial order. Antisymmetry collapses two maxima into one. -/
theorem isMaximal_unique
    {F : Frame} [PartialOrder F.Entity]
    (P : F.Denot .et) (e₁ e₂ : F.Entity)
    (h₁ : IsMaximal P e₁) (h₂ : IsMaximal P e₂) : e₁ = e₂ := by
  exact le_antisymm (h₂.2 _ h₁.1) (h₁.2 _ h₂.1)

/-- The Sharvy maximal-element selector. Returns the unique maximal
    P-satisfier when one exists; `none` otherwise (no satisfier, or no
    upper bound among the satisfiers). -/
noncomputable def sharvyMax
    {F : Frame} [PartialOrder F.Entity] (P : F.Denot .et) : Option F.Entity :=
  letI := Classical.dec (∃ e, IsMaximal P e)
  if h : ∃ e, IsMaximal P e then some h.choose else none

/-- `sharvyMax` returns `some` exactly when a maximal P-satisfier exists. -/
theorem sharvyMax_isSome_iff_isMaximal
    {F : Frame} [PartialOrder F.Entity] (P : F.Denot .et) :
    (sharvyMax P).isSome ↔ ∃ e, IsMaximal P e := by
  classical
  unfold sharvyMax
  by_cases h : ∃ e, IsMaximal P e
  · simp [h]
  · simp [h]

/-- The witness returned by `sharvyMax` is maximal. -/
theorem sharvyMax_witness_isMaximal
    {F : Frame} [PartialOrder F.Entity] (P : F.Denot .et) (e : F.Entity)
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
    {F : Frame} [PartialOrder F.Entity] (P : F.Denot .et) (e : F.Entity)
    (h : sharvyMax P = some e) : P e :=
  (sharvyMax_witness_isMaximal P e h).1

-- ════════════════════════════════════════════════════════════════
-- § Križ Homogeneity
-- ════════════════════════════════════════════════════════════════

/-- @cite{kriz-2015}: a scope predicate `S` is *homogeneous* on the
    P-satisfiers when it holds either of all of them or of none of them.
    This is what licenses "the boys are tall" — Križ argues uniformity is
    presupposed, so partial-truth cases (some boys tall, others not) yield
    presupposition failure rather than `False`. -/
def Homogeneous {F : Frame} (P S : F.Denot .et) : Prop :=
  (∀ x, P x → S x) ∨ (∀ x, P x → ¬ S x)

/-- Homogeneity is symmetric in its two failure modes (uniformly-S vs
    uniformly-¬S). Both yield well-defined truth values; only the *split*
    case is presupposition failure. By definition. -/
theorem homogeneous_symmetric_in_truth_value
    {F : Frame} (P S : F.Denot .et) :
    Homogeneous P S ↔ ((∀ x, P x → S x) ∨ (∀ x, P x → ¬ S x)) := Iff.rfl

/-- Russellian uniqueness implies Križ homogeneity (vacuously beyond the
    unique witness): if there is exactly one P-satisfier, then any S is
    trivially uniform on the (singleton) extension of P. -/
theorem uniqueness_implies_homogeneous_classical
    {F : Frame} (P S : F.Denot .et)
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

end Core.Nominal
