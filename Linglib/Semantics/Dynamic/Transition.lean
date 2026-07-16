import Linglib.Semantics.Dynamic.State

/-!
# Transitions between context fibers
[kamp-vangenabith-reyle-2011] (Defs. 24, 27)

The hom type of indexed dynamic semantics: a `Transition W M X Y` is a
world-indexed relation between an `X`-environment and a `Y`-environment,
`Y ⊇ X`. Objects are bases; a DRS denotes an arrow `X ⟶ X ∪ U`;
sequencing is world-pointwise relational composition. The predecessor of
this file stated transitions on total assignments and carried
`supported_left`/`supported_right` invariants; typing the relation at the
environments dissolves both, and the identity transition becomes plain
equality rather than agreement-on-`X`.

Applying a transition acts fiberwise on sets of environments — the
presheaf fibers of `Category.lean` — functorially (`apply_comp`). The
chapter's own name for the induced map is the (regular) *Context Change
Potential* (Def. 24); *transition* names the underlying relation, after
the transition-system reading of dynamic semantics ([fernando-1992],
cited there).

## Main declarations

* `Transition` — the typed relation; `id`, `comp` and their laws.
* `Transition.apply` — Def. 24's context change, on fibers.
* `Transition.copy` — repackaging along base equalities (the
  `Filter.copy` pattern; the cast point, kept out of every statement).
* `Transition.IsExtension` — Def. 27(ii): established referents persist.
* `Transition.randomAssign` — the generating arrow `X ⟶ insert x X`.
-/

namespace DynamicSemantics

variable {W V M : Type*} {X Y Z : Finset V}

/-- A transition: a world-indexed relation from `X`-environments to
`Y`-environments. The `grow` field makes arrows context-extending —
bases never shrink. -/
@[ext] structure Transition (W M : Type*) {V : Type*} (X Y : Finset V) where
  /-- The world-indexed relation between input and output environments. -/
  rel : W → ((↑X : Set V) → M) → ((↑Y : Set V) → M) → Prop
  /-- Bases only grow along an update. -/
  grow : X ⊆ Y

namespace Transition

/-- The identity transition at `X`: equality of environments. -/
def id (X : Finset V) : Transition W M X X where
  rel _ e e' := e = e'
  grow := subset_rfl

@[simp] theorem rel_id {w : W} {e e' : (↑X : Set V) → M} :
    (id X : Transition W M X X).rel w e e' ↔ e = e' := Iff.rfl

/-- Sequencing: world-pointwise relational composition. -/
def comp (u : Transition W M X Y) (v : Transition W M Y Z) :
    Transition W M X Z where
  rel w := Relation.Comp (u.rel w) (v.rel w)
  grow := u.grow.trans v.grow

@[simp] theorem id_comp (u : Transition W M X Y) : (id X).comp u = u := by
  ext w e e'
  exact ⟨fun ⟨k, hek, hk⟩ => hek ▸ hk, fun h => ⟨e, rfl, h⟩⟩

@[simp] theorem comp_id (u : Transition W M X Y) : u.comp (id Y) = u := by
  ext w e e'
  exact ⟨fun ⟨k, hk, hke⟩ => hke ▸ hk, fun h => ⟨e', h, rfl⟩⟩

theorem comp_assoc (u : Transition W M X Y) (v : Transition W M Y Z)
    {Z' : Finset V} (t : Transition W M Z Z') :
    (u.comp v).comp t = u.comp (v.comp t) := by
  ext w e e'
  exact ⟨fun ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    fun ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-! ### Application to fibers -/

/-- Context change ([kamp-vangenabith-reyle-2011], Def. 24), on the
presheaf fibers: relate environments through the transition, worlds
preserved. -/
def apply (u : Transition W M X Y)
    (T : Set (W × ((↑X : Set V) → M))) :
    Set (W × ((↑Y : Set V) → M)) :=
  {e' | ∃ e, (e'.1, e) ∈ T ∧ u.rel e'.1 e e'.2}

theorem mem_apply {u : Transition W M X Y}
    {T : Set (W × ((↑X : Set V) → M))} {w : W} {g : (↑Y : Set V) → M} :
    (w, g) ∈ u.apply T ↔ ∃ e, (w, e) ∈ T ∧ u.rel w e g := Iff.rfl

/-- Applying the identity transition is the identity. -/
@[simp] theorem apply_id (T : Set (W × ((↑X : Set V) → M))) :
    (id X).apply T = T := by
  ext ⟨w, e⟩
  exact ⟨fun ⟨k, hk, hke⟩ => (show k = e from hke) ▸ hk, fun h => ⟨e, h, rfl⟩⟩

/-- `apply` is functorial: sequencing then applying is applying twice. -/
theorem apply_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (T : Set (W × ((↑X : Set V) → M))) :
    (u.comp v).apply T = v.apply (u.apply T) := by
  ext ⟨w, h⟩
  constructor
  · rintro ⟨e, he, k, hek, hkh⟩
    exact ⟨k, ⟨e, he, hek⟩, hkh⟩
  · rintro ⟨k, ⟨e, he, hek⟩, hkh⟩
    exact ⟨e, he, k, hek, hkh⟩

/-! ### Random assignment -/

/-- The random-assignment transition ([groenendijk-stokhof-1991]'s random
reset `k[x]g`, [heim-1982]'s indefinite widening): preserve the input off
`x`, leave the output free at `x` — the generating arrow
`X ⟶ insert x X` of context extension. -/
def randomAssign [DecidableEq V] (X : Finset V) (x : V) :
    Transition W M X (insert x X) where
  rel _ e e' := ∀ (v : V) (hv : v ∈ X), v ≠ x →
    e ⟨v, hv⟩ = e' ⟨v, Finset.mem_insert_of_mem hv⟩
  grow := Finset.subset_insert x X

/-! ### Typing total-assignment relations

Frameworks state their clauses on total assignments (DPL's Definition 2,
DRT's verification). `ofTotal` types such a relation at contexts by
existential extension; the predecessor's `supported_left`/
`supported_right` fields return as *hypotheses* — `ReadsAt`/`WritesAt` —
carried by the framework's own congruence lemmas, and under them the
typing is faithful (`ofTotal_rel_restrict`) and functorial
(`ofTotal_comp`). -/

section OfTotal

variable {R S : W → (V → M) → (V → M) → Prop}

/-- The relation reads its input only at `X`. -/
def ReadsAt (X : Finset V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f f' g⦄, Set.EqOn f f' (↑X : Set V) → (R w f g ↔ R w f' g)

/-- The relation constrains its output only at `Y`. -/
def WritesAt (Y : Finset V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f g g'⦄, Set.EqOn g g' (↑Y : Set V) → (R w f g ↔ R w f g')

/-- Type a total-assignment relation at contexts, by existential
extension of the environments. -/
def ofTotal (h : X ⊆ Y) (R : W → (V → M) → (V → M) → Prop) :
    Transition W M X Y where
  rel w e e' := ∃ f g : V → M, (↑X : Set V).restrict f = e ∧
    (↑Y : Set V).restrict g = e' ∧ R w f g
  grow := h

/-- Under the support hypotheses, the typing is faithful: related
environments are exactly the restrictions of related assignments. -/
theorem ofTotal_rel_restrict {h : X ⊆ Y} (hR : ReadsAt X R)
    (hW : WritesAt Y R) {w : W} {f g : V → M} :
    (ofTotal h R).rel w ((↑X : Set V).restrict f)
      ((↑Y : Set V).restrict g) ↔ R w f g := by
  constructor
  · rintro ⟨f', g', hf', hg', hR'⟩
    rw [hR (Set.restrict_eq_restrict_iff.mp hf'),
      hW (Set.restrict_eq_restrict_iff.mp hg')] at hR'
    exact hR'
  · intro hfg
    exact ⟨f, g, rfl, rfl, hfg⟩

/-- Typing is functorial on composition, given read-support of the second
relation: the mid-assignments stitch. -/
theorem ofTotal_comp {h₁ : X ⊆ Y} {h₂ : Y ⊆ Z} (hS : ReadsAt Y S) :
    (ofTotal h₁ R).comp (ofTotal h₂ S) =
      ofTotal (h₁.trans h₂) (fun w => Relation.Comp (R w) (S w)) := by
  ext w e e''
  constructor
  · rintro ⟨e', ⟨f, g₁, hf, hg₁, hR⟩, f₂, g, hf₂, hg, hS'⟩
    refine ⟨f, g, hf, hg, g₁, hR, ?_⟩
    rw [← hf₂] at hg₁
    exact (hS (Set.restrict_eq_restrict_iff.mp hg₁)).mpr hS'
  · rintro ⟨f, g, hf, hg, k, hR, hS'⟩
    exact ⟨(↑Y : Set V).restrict k, ⟨f, k, hf, rfl, hR⟩,
      ⟨k, g, rfl, hg, hS'⟩⟩

end OfTotal

/-! ### Repackaging along base equalities

The substrate-safe form of `eqToHom` conjugation (mathlib's `Filter.copy`
pattern): composites whose indices differ by `Finset` identities — e.g.
`(X ∪ U₁) ∪ U₂` against `X ∪ (U₁ ∪ U₂)` — are equated through `copy`,
keeping cast-free statements everywhere below the category layer. -/

/-- Repackage a transition along equalities of its bases. -/
def copy (u : Transition W M X Y) {X' Y' : Finset V} (hX : X = X')
    (hY : Y = Y') : Transition W M X' Y' :=
  hX ▸ hY ▸ u

@[simp] theorem copy_rfl (u : Transition W M X Y) : u.copy rfl rfl = u := rfl

@[simp] theorem copy_copy (u : Transition W M X Y)
    {X' Y' X'' Y'' : Finset V} (hX : X = X') (hY : Y = Y')
    (hX' : X' = X'') (hY' : Y' = Y'') :
    (u.copy hX hY).copy hX' hY' = u.copy (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

/-- Repackaged transitions compose to the repackaged composite. -/
theorem copy_comp_copy (u : Transition W M X Y) (v : Transition W M Y Z)
    {X' Y' Z' : Finset V} (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (u.copy hX hY).comp (v.copy hY hZ) = (u.comp v).copy hX hZ := by
  subst hX hY hZ
  rfl

/-- Application is invariant under repackaging. -/
@[simp] theorem apply_copy (u : Transition W M X Y) {X' Y' : Finset V}
    (hX : X = X') (hY : Y = Y') (T : Set (W × ((↑X' : Set V) → M))) :
    (u.copy hX hY).apply T = (by subst hX hY; exact u.apply T) := by
  subst hX hY
  rfl

/-! ### Information growth (Def. 27) -/

/-- A transition is an *extension* when outputs restrict to their inputs:
established referents persist, only new ones are assigned. -/
def IsExtension (u : Transition W M X Y) : Prop :=
  ∀ ⦃w e e'⦄, u.rel w e e' → e = fun v => e' ⟨v.1, u.grow v.2⟩

/-- The identity is an extension. -/
theorem isExtension_id : (id X : Transition W M X X).IsExtension :=
  fun _ _ _ h => h

/-- Extensions compose. -/
theorem IsExtension.comp {u : Transition W M X Y} {v : Transition W M Y Z}
    (hu : u.IsExtension) (hv : v.IsExtension) : (u.comp v).IsExtension := by
  rintro w e e' ⟨k, hek, hke⟩
  rw [hu hek, hv hke]

end Transition

end DynamicSemantics
