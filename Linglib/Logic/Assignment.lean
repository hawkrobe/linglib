module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Basic
public import Linglib.Core.Order.Flat

/-!
# Variable assignments

A *variable assignment* maps variables to values. Three registers share
this file: total assignments (Tarski-style, [heim-kratzer-1998],
[henkin-monk-tarski-1971]), partial assignments (variables may be
unvalued, [spector-2025], [beaver-krahmer-2001]), and plural assignments
(sets of partial assignments — the information states of plural dynamic
semantics, [van-den-berg-1996], [brasoveanu-2008],
[haug-dalrymple-2020]).

## Main definitions

* `Assignment E`: total assignments `ℕ → E`, on the Heim–Kratzer
  ℕ-register.
* `PartialAssign Var D`: partial assignments `Var → Flat D`, ordered by extension, with
  `PartialAssign.domain` the variables an assignment values and `PartialAssign.single x d` the
  assignment valuing `x` alone.
* `PluralAssign Var D`: sets of partial assignments, with the
  [spector-2025] operators `restrict`, `SingularAt`, `Singular`.

## Main results

* `PartialAssign.le_iff_eqOn_domain`: one assignment extends another when it agrees with it on
  the other's domain.
* `PartialAssign.covBy_iff_exists_update`: one assignment covers another when it values exactly
  one more variable, the counterpart of `Set.covBy_iff_exists_insert`.

## Implementation notes

* `PartialAssign` takes values in `Flat D`, the decidable counterpart of
  mathlib's partial values `Part D` with the same order
  (`Flat.le_iff_ofOption_le`): `Part`-valued partiality would forfeit
  `DecidableEq` on assignments, which `Finset`-state systems (QBSML) and
  `decide`-checked studies need. The pointwise order is extension, `⊥` is
  the assignment valuing nothing, `g x = ⊥` says `x` is unvalued and
  `g x = ↑d` that it has the value `d`; there is no wrapper predicate.
* Update is mathlib's `Function.update`; `PartialAssign.update` only
  fuses the coercion (cf. `Finsupp.update`), and its lemmas are one-step
  consequences of the `Function.update_*` laws. The Heim–Kratzer notation
  `g[n ↦ x]` for total update is `Assignment`-scoped, declared below.
* Random assignment `[x]`, relating assignments that agree off `x`, is
  `DynamicSemantics.Update.randomAssign` at the function-type register structure; it is not
  redefined here.
* Use these names only for the variable-binding role — the state that
  quantifiers `update` and free variables look up. A `ℕ → E` that is not
  variable-binding state (interpretation tables, lookup arrays) should
  stay a plain function type.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [L. Henkin, J. D. Monk and A. Tarski, *Cylindric algebras, part I*
  (1971)][henkin-monk-tarski-1971]
* [B. Spector, *Trivalence and transparency: A non-dynamic approach to anaphora*
  (2025)][spector-2025]
* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [M. H. van den Berg, *Some aspects of the internal structure of discourse: the dynamics of
  nominal anaphora* (1996)][van-den-berg-1996]
* [A. Brasoveanu, *Donkey pluralities: plural information states versus non-atomic
  individuals* (2008)][brasoveanu-2008]
* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
-/

@[expose] public section

/-! ### Total assignments -/

/-- Total variable assignment on the ℕ-register: instantiated at the
entity type for entity pronouns, at indices for situation pronouns, at
`Time` for temporal variables. Update is `Function.update` directly —
no parallel API. -/
abbrev Assignment (E : Type*) := Nat → E

namespace Assignment

/-- [heim-kratzer-1998]'s assignment modification `g[n ↦ x]`, i.e. `Function.update g n x`;
the `Function.update_*` lemmas are its laws. -/
scoped notation:max g "[" n " ↦ " x "]" => Function.update g n x

end Assignment

/-! ### Partial assignments -/

/-- Partial assignment: `g x = ⊥` means `x` is unvalued, and the pointwise
order of `Flat` is extension. Trivalent systems read the gap as the
third value; state-based systems (`QBSML.Index`) carry one per
world–assignment index. -/
abbrev PartialAssign (Var D : Type*) := Var → Flat D

namespace PartialAssign

variable {Var D : Type*} {g h : PartialAssign Var D} {x y : Var}

/-- The variables `g` values, as `Finsupp.support`. -/
def domain (g : PartialAssign Var D) : Set Var := {x | g x ≠ ⊥}

@[simp] theorem mem_domain : x ∈ g.domain ↔ g x ≠ ⊥ := Iff.rfl

@[simp] theorem domain_bot : (⊥ : PartialAssign Var D).domain = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ h rfl

/-- `h` extends `g` when it keeps every value `g` has. -/
theorem le_iff_eqOn_domain : g ≤ h ↔ Set.EqOn g h g.domain := by
  refine Pi.le_def.trans (forall_congr' fun x ↦ ⟨fun hx hne ↦ Flat.eq_of_le hx fun _ ↦ hne,
    fun hx ↦ ?_⟩)
  rcases eq_or_ne (g x) ⊥ with h0 | hne
  · rw [h0]; exact bot_le
  · exact (hx hne).le

theorem domain_mono (hgh : g ≤ h) : g.domain ⊆ h.domain :=
  fun x hx ↦ Flat.ne_bot_of_le (hgh x) hx

/-- One assignment covers another when it values exactly one more variable and agrees
elsewhere: `Pi.covBy_iff` at the flat order of height one. -/
theorem covBy_iff : g ⋖ h ↔ ∃ x, g x = ⊥ ∧ h x ≠ ⊥ ∧ ∀ y ≠ x, g y = h y := by
  simp only [Pi.covBy_iff, Flat.covBy_iff, and_assoc]

variable [DecidableEq Var]

/-- Update at `x`: `Function.update` with the value coerced into `Flat`. -/
def update (g : PartialAssign Var D) (x : Var) (d : D) :
    PartialAssign Var D :=
  Function.update g x ↑d

@[simp] theorem update_at (g : PartialAssign Var D) (x : Var) (d : D) :
    g.update x d x = ↑d :=
  Function.update_self ..

@[simp] theorem update_ne (g : PartialAssign Var D) {x y : Var} (d : D)
    (h : y ≠ x) : g.update x d y = g y :=
  Function.update_of_ne h ..

/-- Updating at `x` to its existing value is a no-op, the partial-assignment
face of `Function.update_eq_self`. -/
theorem update_self {x : Var} {a : D} (h : g x = ↑a) : g.update x a = g := by
  rw [update, ← h]; exact Function.update_eq_self x g

theorem update_comm (h : x ≠ y) (a b : D) (g : PartialAssign Var D) :
    (g.update x a).update y b = (g.update y b).update x a :=
  Function.update_comm h ..

@[simp] theorem update_idem (x : Var) (a b : D) (g : PartialAssign Var D) :
    (g.update x a).update x b = g.update x b :=
  Function.update_idem ..

@[simp] theorem domain_update (g : PartialAssign Var D) (x : Var) (d : D) :
    (g.update x d).domain = insert x g.domain := by
  ext y
  obtain rfl | hy := eq_or_ne y x <;> simp [*]

/-- Valuing an unvalued variable is a covering step of the extension order. -/
theorem covBy_update {x : Var} (hx : g x = ⊥) (d : D) : g ⋖ g.update x d :=
  covBy_iff.2 ⟨x, hx, by simp, fun _ hy ↦ (update_ne g d hy).symm⟩

/-- Covering is valuing one unvalued variable, as `Set.covBy_iff_exists_insert`. -/
theorem covBy_iff_exists_update : g ⋖ h ↔ ∃ x d, g x = ⊥ ∧ g.update x d = h := by
  refine ⟨fun hc ↦ ?_, fun ⟨x, d, hx, he⟩ ↦ he ▸ covBy_update hx d⟩
  obtain ⟨x, hx, hhx, hagree⟩ := covBy_iff.1 hc
  obtain ⟨d, hd⟩ := Flat.ne_bot_iff_exists.1 hhx
  refine ⟨x, d, hx, funext fun y ↦ ?_⟩
  obtain rfl | hy := eq_or_ne y x
  · simp [hd]
  · rw [update_ne _ _ hy, hagree y hy]

/-- The assignment valuing `x` alone, at `d`, as `Finsupp.single`. -/
def single (x : Var) (d : D) : PartialAssign Var D :=
  update ⊥ x d

theorem bot_update (x : Var) (d : D) : (⊥ : PartialAssign Var D).update x d = single x d :=
  rfl

@[simp] theorem single_eq_same (x : Var) (d : D) : single x d x = ↑d :=
  update_at ..

@[simp] theorem single_eq_of_ne {x y : Var} (d : D) (h : y ≠ x) : single x d y = ⊥ :=
  update_ne _ _ h

@[simp] theorem domain_single (x : Var) (d : D) : (single x d).domain = {x} := by
  simp [single]

end PartialAssign

/-! ### Plural assignments -/

/-- Plural assignment: a set of partial assignments, the plural
information state of [van-den-berg-1996]-style dynamic semantics
(Plural CDRT, PPCDRT) and of [spector-2025]'s static reuse. The full
`Set` API applies: `∅`, `Set.univ`, `{g}`, `∪`, `⊆`,
`Set.Nonempty`, … -/
abbrev PluralAssign (Var D : Type*) := Set (PartialAssign Var D)

namespace PluralAssign

variable {Var D : Type*}

/-- The assignments in `G` mapping `x` to `a` ([spector-2025] §6.2:
`G_{x=a}`). -/
def restrict (G : PluralAssign Var D) (x : Var) (a : D) :
    PluralAssign Var D :=
  {g ∈ G | g x = ↑a}

@[simp] theorem mem_restrict {G : PluralAssign Var D} {x : Var} {a : D}
    {g : PartialAssign Var D} : g ∈ G.restrict x a ↔ g ∈ G ∧ g x = ↑a :=
  Iff.rfl

/-- `G` assigns `x` uniquely to `d`: some assignment maps `x` to `d`, and
every assignment valuing `x` agrees ([spector-2025] §6.2). Assignments
leaving `x` unvalued may coexist — only the valued rows must agree,
which is the reading Spector's static reuse needs. -/
def SingularAt (G : PluralAssign Var D) (x : Var) (d : D) : Prop :=
  (∃ g ∈ G, g x = ↑d) ∧ ∀ g ∈ G, g x ≠ ⊥ → g x = ↑d

/-- `G` assigns `x` uniquely to some value — [spector-2025]'s `atomic(x)`. -/
def Singular (G : PluralAssign Var D) (x : Var) : Prop :=
  ∃ d, G.SingularAt x d

theorem SingularAt.unique {G : PluralAssign Var D} {x : Var} {d d' : D}
    (h : G.SingularAt x d) (h' : G.SingularAt x d') : d = d' := by
  obtain ⟨⟨g, hg, hgd⟩, -⟩ := h
  exact Flat.coe_inj.1 (hgd.symm.trans (h'.2 g hg (hgd ▸ Flat.coe_ne_bot)))

theorem SingularAt.singular {G : PluralAssign Var D} {x : Var} {d : D}
    (h : G.SingularAt x d) : G.Singular x :=
  ⟨d, h⟩

theorem SingularAt.eq_of_mem_restrict {G : PluralAssign Var D} {x : Var} {d a : D}
    {g : PartialAssign Var D} (h : G.SingularAt x d) (hg : g ∈ G.restrict x a) : a = d :=
  Flat.coe_inj.1 (hg.2.symm.trans (h.2 g hg.1 (hg.2 ▸ Flat.coe_ne_bot)))

@[simp] theorem singularAt_singleton {g : PartialAssign Var D} {x : Var} {d : D} :
    ({g} : PluralAssign Var D).SingularAt x d ↔ g x = ↑d :=
  ⟨fun h ↦ by obtain ⟨⟨g', hg', hd⟩, -⟩ := h; exact (hg' : g' = g) ▸ hd,
    fun h ↦ ⟨⟨g, rfl, h⟩, fun g' (hg' : g' = g) _ ↦ hg' ▸ h⟩⟩

/-- A nonempty restriction of `G` to `x = a` assigns `x` uniquely to `a`. -/
theorem singularAt_restrict {G : PluralAssign Var D} {x : Var} {a : D}
    (h : (G.restrict x a).Nonempty) : (G.restrict x a).SingularAt x a :=
  ⟨h.imp fun _ hg ↦ ⟨hg, hg.2⟩, fun _ hg _ ↦ hg.2⟩

theorem singularAt_restrict_iff {G : PluralAssign Var D} {x : Var} {a d : D} :
    (G.restrict x a).SingularAt x d ↔ (G.restrict x a).Nonempty ∧ d = a :=
  ⟨fun h ↦ ⟨h.1.imp fun _ hg ↦ hg.1, h.unique (singularAt_restrict ⟨_, h.1.choose_spec.1⟩)⟩,
    fun ⟨hne, hd⟩ ↦ hd.symm ▸ singularAt_restrict hne⟩

end PluralAssign
