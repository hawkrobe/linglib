/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Rel
import Mathlib.Logic.Relator
import Mathlib.Order.Basic

/-!
# Control Dependencies

The framework-neutral stratum of control theory. Control is pre-theoretically
an antecedence relation between the understood subject of a clause-like
complement and the matrix argument that supplies its interpretation
([landau-2013] (74)); the one definition in the literature written to be
neutral between the rival mechanisms is [stiebels-2007] (22): the control
predicate requires one of its arguments to be (improperly) included in the
reference of the embedded subject, "open as to how the control reading is
obtained: either structurally or semantically/lexically". A dependency here is
a relation `SetRel Pos Pos` over argument positions, read
`antecedent ~[r] dependent`, with a valuation `val : Pos → Ref` assigning
referents; exhaustive inclusion is the kernel refinement `Control.Shares`, and
proper inclusion — a partial reading ([landau-2000]) — is strict growth
`val a < val b` along the dependency.

Grammatical dependencies share the fixed format of the configurational matrix:
[koster-1987]'s five shared properties, as explained by
[neeleman-vandekoot-2002] — c-command by the antecedent, obligatoriness,
uniqueness of the antecedent, nonuniqueness of the dependent, and locality.
Every clause of the matrix is mathlib vocabulary in the `SetRel` lattice:
c-command and locality are refinements `r ⊆ s`, uniqueness of the antecedent
is `SetRel.IsInjective`, obligatoriness is `dependent ⊆ r.cod`. Movement
chains, bound anaphora, and both control mechanisms instantiate the format, so
nothing here chooses between base-generation and movement.

Composition `○` serves the theories that decompose a control dependency into
legs (e.g. [landau-2024]'s binding over predication): a composite keeps every
refinement (`SetRel.comp_subset_comp`), obligatoriness
(`cod_comp_of_dom_subset`), both uniqueness properties (`IsFunctional.comp`,
`IsInjective.comp`), and sharing (`Shares.comp`) of its legs, and a partial
reading localizes to a leg (`exists_lt_of_comp_lt`).

What a dependency shares distinguishes the enforcement species —
[bresnan-1982]'s functional vs. anaphoric control: *functional* control shares
the occupant assignment itself (structure sharing; movement chains),
*anaphoric* control only the referent valuation. Occupant sharing is the
stronger: a shared assignment transports along every map of it (`Shares.map`),
so every occupant property transports across the dependency
(`Shares.iff_of_rel`) and one observed mismatch refutes it
(`not_shares_of_mismatch`) — the refutation engine of the overt-copy
diagnostics ([polinsky-potsdam-2006]).

The `SetRel` declarations are general relation algebra that mathlib currently
lacks; each is marked `[UPSTREAM]`.

## Main definitions

- `SetRel.IsFunctional`, `SetRel.IsInjective`, `SetRel.IsBiUnique`
- `SetRel.ker`: the kernel of a function, as a relation
- `Control.Shares`: exhaustive argument sharing as kernel refinement
-/

namespace SetRel

variable {α β γ : Type*} {R : SetRel α β} {S : SetRel β γ} {f : α → β} {a b : α}

/-- `[UPSTREAM]` A relation is functional when it relates each left element to
    at most one right element. -/
protected abbrev IsFunctional (R : SetRel α β) : Prop :=
  Relator.RightUnique (· ~[R] ·)

/-- `[UPSTREAM]` A relation is injective when it relates each right element to
    at most one left element. -/
protected abbrev IsInjective (R : SetRel α β) : Prop :=
  Relator.LeftUnique (· ~[R] ·)

/-- `[UPSTREAM]` A relation is bi-unique when it is injective and functional. -/
protected abbrev IsBiUnique (R : SetRel α β) : Prop :=
  Relator.BiUnique (· ~[R] ·)

/-- `[UPSTREAM]` Functionality is the relation-algebra inequality
    `R.inv ○ R ⊆ .id`. -/
theorem isFunctional_iff_inv_comp_subset_id : R.IsFunctional ↔ R.inv ○ R ⊆ .id where
  mp h := fun ⟨_, _⟩ ⟨_, hba, hab'⟩ => h hba hab'
  mpr h := fun _ _ _ hab hab' => mem_id.1 (h ⟨_, mem_inv.2 hab, hab'⟩)

/-- `[UPSTREAM]` Injectivity is the relation-algebra inequality
    `R ○ R.inv ⊆ .id`. -/
theorem isInjective_iff_comp_inv_subset_id : R.IsInjective ↔ R ○ R.inv ⊆ .id where
  mp h := fun ⟨_, _⟩ ⟨_, hab, hba'⟩ => h hab hba'
  mpr h := fun _ _ _ hab ha'b => mem_id.1 (h ⟨_, hab, mem_inv.2 ha'b⟩)

/-- `[UPSTREAM]` Functional relations compose. -/
theorem IsFunctional.comp (hR : R.IsFunctional) (hS : S.IsFunctional) :
    (R ○ S).IsFunctional :=
  fun _ _ _ ⟨_, hab, hbc⟩ ⟨_, hab', hb'c⟩ => hS (hR hab hab' ▸ hbc) hb'c

/-- `[UPSTREAM]` Injective relations compose. -/
theorem IsInjective.comp (hR : R.IsInjective) (hS : S.IsInjective) :
    (R ○ S).IsInjective :=
  fun _ _ _ ⟨_, hab, hbc⟩ ⟨_, ha'b', hb'c⟩ => hR (hS hbc hb'c ▸ hab) ha'b'

/-- `[UPSTREAM]` The kernel of a function, as a relation: `a ~[ker f] b` iff
    `f a = f b`. -/
def ker (f : α → β) : SetRel α α := f.graph ○ f.graph.inv

@[simp] theorem mem_ker : a ~[ker f] b ↔ f a = f b := by simp [ker, eq_comm]

instance : (ker f).IsRefl where refl _ := mem_ker.2 rfl

instance : (ker f).IsSymm where symm _ _ h := mem_ker.2 (mem_ker.1 h).symm

instance : (ker f).IsTrans where
  trans _ _ _ h h' := mem_ker.2 ((mem_ker.1 h).trans (mem_ker.1 h'))

/-- `[UPSTREAM]` The codomain of a composite is the image of the first leg's
    codomain under the second leg. -/
theorem cod_comp : (R ○ S).cod = S.image R.cod := by aesop

/-- `[UPSTREAM]` The domain of a composite is the preimage of the second leg's
    domain under the first leg. -/
theorem dom_comp : (R ○ S).dom = R.preimage S.dom := by aesop

/-- `[UPSTREAM]` The composite's codomain is the second leg's when the second
    leg's domain is covered by the first leg's codomain. -/
theorem cod_comp_of_dom_subset (h : S.dom ⊆ R.cod) : (R ○ S).cod = S.cod := by
  rw [cod_comp, image_eq_cod_of_dom_subset h]

/-- `[UPSTREAM]` The composite's domain is the first leg's when the first
    leg's codomain is covered by the second leg's domain. -/
theorem dom_comp_of_cod_subset (h : R.cod ⊆ S.dom) : (R ○ S).dom = R.dom := by
  rw [dom_comp, preimage_eq_dom_of_cod_subset h]

end SetRel

namespace Control

open SetRel

/-! ### Argument sharing -/

variable {Pos Ref : Type*} {val : Pos → Ref} {ante bind pred : SetRel Pos Pos}
  {a b p c : Pos}

/-- A dependency enforces exhaustive argument sharing when related positions
    are co-valued — the dependency refines the kernel of the valuation. -/
abbrev Shares (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ante ⊆ .ker val

/-- Related positions of a sharing dependency are co-valued. -/
theorem Shares.eq (hs : Shares val ante) (h : a ~[ante] b) : val a = val b :=
  mem_ker.1 (hs h)

/-- A refinement of a sharing dependency shares. -/
theorem Shares.mono (h : ante ⊆ bind) (hs : Shares val bind) :
    Shares val ante :=
  h.trans hs

/-- Sharing composes through the mediating position. -/
theorem Shares.comp (hb : Shares val bind) (hp : Shares val pred) :
    Shares val (bind ○ pred) :=
  (comp_subset_comp hb hp).trans comp_subset_self

/-- Exhaustive sharing excludes partial readings: no strict growth of the
    referent along the dependency ([landau-2000]). -/
theorem Shares.not_lt [Preorder Ref] (hs : Shares val ante)
    (h : a ~[ante] b) : ¬ val a < val b := by
  simp [hs.eq h]

/-- Under exhaustive sharing, joint antecedents are co-valued — split control
    needs a non-exhaustive leg. -/
theorem Shares.eq_of_two (hs : Shares val ante) (ha : a ~[ante] p)
    (hb : b ~[ante] p) : val a = val b :=
  (hs.eq ha).trans (hs.eq hb).symm

/-- A partial reading in a composite localizes to a leg: if referents grow
    monotonely along the first leg and strictly across the composite, one of
    the two legs already grows strictly. -/
theorem exists_lt_of_comp_lt [PartialOrder Ref]
    (hb : ∀ ⦃x m⦄, x ~[bind] m → val x ≤ val m)
    (h : a ~[bind ○ pred] c) (hlt : val a < val c) :
    (∃ x m, x ~[bind] m ∧ val x < val m) ∨
      ∃ m x, m ~[pred] x ∧ val m < val x := by
  obtain ⟨m, ham, hmc⟩ := h
  rcases (hb ham).lt_or_eq with hlt' | heq
  · exact Or.inl ⟨a, m, ham, hlt'⟩
  · exact Or.inr ⟨m, c, hmc, heq ▸ hlt⟩

/-! ### Enforcement

What a dependency shares distinguishes the enforcement species
([bresnan-1982]): functional control shares the occupant assignment itself
(structure sharing — movement chains, LFG control equations), anaphoric
control only the referent valuation. Occupant sharing is the stronger: a
shared assignment transports along every map of it (`Shares.map`), so every
occupant property transports across the dependency (`Shares.iff_of_rel`) —
and one observed mismatch refutes it (`not_shares_of_mismatch`), the engine
of the overt-copy diagnostics ([polinsky-potsdam-2006]). -/

variable {Item : Type*} {occ : Pos → Item}

/-- Sharing an assignment transports along any map of it: token identity
    yields referential co-valuation for every referent map. -/
theorem Shares.map (hs : Shares occ ante) (f : Item → Ref) :
    Shares (f ∘ occ) ante :=
  fun _ h => mem_ker.2 (congrArg f (hs.eq h))

/-- Under a shared assignment, every property of the assigned value transports
    across the dependency: copies are indistinguishable. -/
theorem Shares.iff_of_rel (hs : Shares occ ante) (h : a ~[ante] b)
    (P : Item → Prop) : P (occ a) ↔ P (occ b) :=
  iff_of_eq (congrArg P (hs.eq h))

/-- One observed mismatch refutes a shared assignment — the refutation engine
    of the copy-control diagnostics. -/
theorem not_shares_of_mismatch {P : Item → Prop} (h : a ~[ante] b)
    (hPa : P (occ a)) (hPb : ¬ P (occ b)) : ¬ Shares occ ante :=
  fun hs => hPb (hs.eq h ▸ hPa)

end Control
