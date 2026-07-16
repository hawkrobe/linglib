import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function

/-!
# Information states

An *information state* is a set of world–assignment pairs, with the
assignments partial — [kamp-vangenabith-reyle-2011]'s Def. 23 (sets of
pairs of a world and an embedding), the form the field standardly
assumes: the absurd state is `∅`, the initial state is `W × {g_⊤}`
(`initial`), and the lattice of states is `Set`'s. Partiality is by
`Option` ([elliott-sudo-2025]'s Def. 3.1: total functions into
`D ∪ {∗}`), so no component of a state carries a proof obligation.

There is no base field: Def. 23's "Dom(f) = X" is the *uniform* stratum
(`UniformAt`), and a base is the index of a fiber, not part of the data.
Points with domain `X` are world–`X`-environment pairs, constructively
(`Possibility.domEquiv` — the total-assignment rendering needed choice
and an inhabitant of `M` to recover this). Informativeness
([kamp-vangenabith-reyle-2011] Def. 25) is *subsistence*: every point of
the weaker state has a descendant in the stronger — the order of
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9 and
[elliott-sudo-2025] Def. 3.3, promoted here from the bilateral system to
the root.

## Main definitions

- `Possibility.dom`, `Possibility.Descendant`: the defined referents of
  a partial point, and same-world graph-extension.
- `State W V M`: information states; `initial`, with `∅` the absurd
  state.
- `Subsists` (`≺`), `subsistsIn` (`⪯`): the informativeness order.
- `worlds`, `Familiar`: worldly content and familiarity.
- `State.UniformAt`, `Possibility.domEquiv`: the indexed stratum and its
  constructive classification.
- `Possibility.restrict`, `State.restrict`, `State.randomAssign`:
  domain restriction (pointwise, by direct image) and random assignment.

## Main results

- `subsistsIn_restrict`: restriction only forgets — the restricted state
  subsists in the original.
- `uniformAt_initial`: the initial state is the empty-base fiber.

## References

- [kamp-vangenabith-reyle-2011], Defs. 23, 25
- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [heim-1982]
-/

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Partial points -/

namespace Possibility

/-- The referents a partial point defines — Def. 23's `Dom(f)`. -/
def dom (p : Possibility W V (Option M)) : Set V :=
  {v | (p.assignment v).isSome}

@[simp] theorem mem_dom {p : Possibility W V (Option M)} {v : V} :
    v ∈ p.dom ↔ (p.assignment v).isSome := Iff.rfl

/-- `q` is a *descendant* of `p` ([elliott-sudo-2025], Def. 3.3): same
world, and `q`'s assignment extends `p`'s wherever the latter is defined
([groenendijk-stokhof-veltman-1996]'s graph-extension). -/
def Descendant (p q : Possibility W V (Option M)) : Prop :=
  p.world = q.world ∧ ∀ x e, p.assignment x = some e → q.assignment x = some e

theorem Descendant.refl (p : Possibility W V (Option M)) :
    p.Descendant p :=
  ⟨rfl, fun _ _ h => h⟩

theorem Descendant.trans {p q r : Possibility W V (Option M)}
    (hpq : p.Descendant q) (hqr : q.Descendant r) : p.Descendant r :=
  ⟨hpq.1.trans hqr.1, fun x e h => hqr.2 x e (hpq.2 x e h)⟩

/-- Descendance grows the domain. -/
theorem Descendant.dom_subset {p q : Possibility W V (Option M)}
    (h : p.Descendant q) : p.dom ⊆ q.dom := fun v hv => by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hv
  exact Option.isSome_iff_exists.mpr ⟨e, h.2 v e he⟩

end Possibility

/-! ### Information states -/

/-- An information state: a set of world–assignment pairs, the
assignments partial (Def. 23). The absurd state is `∅`; the lattice of
states is `Set`'s. -/
abbrev State (W V M : Type*) := Set (Possibility W V (Option M))

/-- The initial information state `W × {g_⊤}`: every world live, no
referent defined. -/
def State.initial : State W V M := {p | ∀ v, p.assignment v = none}

/-- `p` *subsists* in `s` ([elliott-sudo-2025], Def. 3.3): it has a
descendant in `s`. -/
def Subsists (p : Possibility W V (Option M)) (s : State W V M) : Prop :=
  ∃ q ∈ s, p.Descendant q

@[inherit_doc] scoped notation:50 p " ≺ " s => Subsists p s

theorem Subsists.of_mem {p : Possibility W V (Option M)} {s : State W V M}
    (h : p ∈ s) : p ≺ s :=
  ⟨p, h, Possibility.Descendant.refl p⟩

/-- `s` subsists in `s'`: the informativeness order, Def. 25's
projection form — every point of the weaker state has a descendant in
the stronger. -/
def subsistsIn (s s' : State W V M) : Prop :=
  ∀ p ∈ s, p ≺ s'

@[inherit_doc] scoped notation:50 s " ⪯ " s' => subsistsIn s s'

theorem subsistsIn_refl (s : State W V M) : s ⪯ s :=
  fun _ hp => Subsists.of_mem hp

theorem subsistsIn_trans {s t u : State W V M} (hst : s ⪯ t)
    (htu : t ⪯ u) : s ⪯ u := fun p hp => by
  obtain ⟨q, hq, hpq⟩ := hst p hp
  obtain ⟨r, hr, hqr⟩ := htu q hq
  exact ⟨r, hr, hpq.trans hqr⟩

/-- The worldly content of a state ([elliott-sudo-2025] Def. 3.1's 𝒲). -/
def worlds (s : State W V M) : Set W :=
  Possibility.world '' s

@[simp] theorem mem_worlds {s : State W V M} {w : W} :
    w ∈ worlds s ↔ ∃ p ∈ s, Possibility.world p = w := Iff.rfl

/-- A referent is *familiar* at a state ([elliott-sudo-2025], Def. 3.2;
[heim-1982]'s files): defined at every point. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, p.assignment x ≠ none

/-! ### Restriction and random assignment -/

namespace Possibility

variable [DecidableEq V]

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Finset V) (p : Possibility W V (Option M)) :
    Possibility W V (Option M) :=
  ⟨p.world, fun v => if v ∈ X then p.assignment v else none⟩

@[simp] theorem restrict_world (X : Finset V)
    (p : Possibility W V (Option M)) :
    (p.restrict X).world = p.world := rfl

/-- Restriction is an ancestor. -/
theorem restrict_descendant (X : Finset V)
    (p : Possibility W V (Option M)) : (p.restrict X).Descendant p :=
  ⟨rfl, fun x e h => by
    by_cases hx : x ∈ X
    · simpa [restrict, hx] using h
    · simp [restrict, hx] at h⟩

end Possibility

namespace State

/-! ### The uniform stratum -/

/-- The state is uniform at `X`: every point defines exactly the
referents in `X` — Def. 23's "Dom(f) = X", as a stratum rather than a
component. -/
def UniformAt (X : Finset V) (I : State W V M) : Prop :=
  ∀ p ∈ I, Possibility.dom p = (↑X : Set V)

/-- The initial state is uniform at the empty base. -/
theorem uniformAt_initial : UniformAt ∅ (initial : State W V M) :=
  fun p hp => by
    ext v
    simp [Possibility.dom, hp v]

variable [DecidableEq V]

/-- Restriction of a state: pointwise, by direct image. -/
def restrict (X : Finset V) (I : State W V M) : State W V M :=
  Possibility.restrict X '' I

/-- Restriction only forgets: the restricted state subsists in the
original. -/
theorem subsistsIn_restrict (X : Finset V) (I : State W V M) :
    I.restrict X ⪯ I := by
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, hq, Possibility.restrict_descendant X q⟩

/-- Random assignment ([elliott-sudo-2025], (43);
[groenendijk-stokhof-1991]'s `x := random`): indeterministically extend
each point to a defined value at `x`. -/
def randomAssign (I : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ I, ∃ m : M,
    p = ⟨q.world, Function.update q.assignment x (some m)⟩}

end State

/-! ### The indexed classification -/

namespace Possibility

variable [DecidableEq V]

/-- Partial points with domain `X` are world–`X`-environment pairs —
constructively: the classification that the total-assignment rendering
recovered only with choice and an inhabitant of `M`. -/
def domEquiv (X : Finset V) :
    {p : Possibility W V (Option M) // p.dom = (↑X : Set V)} ≃
      W × ((↑X : Set V) → M) where
  toFun p :=
    (p.1.world, fun v => (p.1.assignment v.1).get
      ((Set.ext_iff.mp p.2 v.1).mpr v.2))
  invFun e :=
    ⟨⟨e.1, fun v => if h : v ∈ (↑X : Set V) then some (e.2 ⟨v, h⟩)
      else none⟩, by
      ext v
      by_cases h : v ∈ (↑X : Set V) <;> simp [dom, h]⟩
  left_inv p := by
    obtain ⟨⟨w, g⟩, hp⟩ := p
    refine Subtype.ext (Possibility.ext rfl (funext fun v => ?_))
    by_cases h : v ∈ (↑X : Set V)
    · simp only [dif_pos h, Option.some_get]
    · have hnone : g v = none := Option.not_isSome_iff_eq_none.mp
        fun hs => h ((Set.ext_iff.mp hp v).mp hs)
      simp only [dif_neg h]
      exact hnone.symm
  right_inv e := by
    refine Prod.ext rfl (funext fun v => ?_)
    simp

end Possibility

end DynamicSemantics
