import Linglib.Semantics.Dynamic.State

/-!
# Transitions between context fibers
[kamp-vangenabith-reyle-2011] (Defs. 24, 27)

The hom type of indexed dynamic semantics: a `Transition W M X Y` is a
world-indexed relation between an `X`-assignment and a `Y`-assignment,
`Y ⊇ X`. Objects are bases; a DRS denotes an arrow `X ⟶ X ∪ U`;
sequencing is world-pointwise relational composition. The predecessor of
this file stated transitions on total assignments and carried
`supported_left`/`supported_right` invariants; typing the relation at the
assignments dissolves both, and the identity transition becomes plain
equality rather than agreement-on-`X`.

Applying a transition acts fiberwise on sets of possibilities — the
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

variable {W V M : Type*} {X Y Z : Set V}

/-- A transition: a world-indexed relation from `X`-assignments to
`Y`-assignments. The `grow` field makes arrows context-extending —
bases never shrink. -/
@[ext] structure Transition (W M : Type*) {V : Type*} (X Y : Set V) where
  /-- The world-indexed relation between input and output assignments. -/
  rel : W → (X → M) → (Y → M) → Prop
  /-- Bases only grow along an update. -/
  grow : X ⊆ Y

namespace Transition

/-- The identity transition at `X`: equality of assignments. -/
def id (X : Set V) : Transition W M X X where
  rel _ e e' := e = e'
  grow := subset_rfl

@[simp] theorem rel_id {w : W} {e e' : X → M} :
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
    {Z' : Set V} (t : Transition W M Z Z') :
    (u.comp v).comp t = u.comp (v.comp t) := by
  ext w e e'
  exact ⟨fun ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    fun ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-! ### Application to fibers -/

/-- Context change ([kamp-vangenabith-reyle-2011], Def. 24), on the
presheaf fibers: relate assignments through the transition, worlds
preserved. -/
def apply (u : Transition W M X Y)
    (T : Set (W × (X → M))) :
    Set (W × (Y → M)) :=
  {e' | ∃ e, (e'.1, e) ∈ T ∧ u.rel e'.1 e e'.2}

theorem mem_apply {u : Transition W M X Y}
    {T : Set (W × (X → M))} {w : W} {g : Y → M} :
    (w, g) ∈ u.apply T ↔ ∃ e, (w, e) ∈ T ∧ u.rel w e g := Iff.rfl

/-- Applying the identity transition is the identity. -/
@[simp] theorem apply_id (T : Set (W × (X → M))) :
    (id X).apply T = T := by
  ext ⟨w, e⟩
  exact ⟨fun ⟨k, hk, hke⟩ => (show k = e from hke) ▸ hk, fun h => ⟨e, h, rfl⟩⟩

/-- `apply` is functorial: sequencing then applying is applying twice. -/
theorem apply_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (T : Set (W × (X → M))) :
    (u.comp v).apply T = v.apply (u.apply T) := by
  ext ⟨w, h⟩
  constructor
  · rintro ⟨e, he, k, hek, hkh⟩
    exact ⟨k, ⟨e, he, hek⟩, hkh⟩
  · rintro ⟨k, ⟨e, he, hek⟩, hkh⟩
    exact ⟨e, he, k, hek, hkh⟩

/-! ### Application to root states -/

section ApplyState

/-- Context change on root states ([kamp-vangenabith-reyle-2011],
Def. 24 — the regular CCP): points of the `X`-stratum step to points of
the `Y`-stratum through the transition, worlds preserved. Index-free:
both sides are plain states. -/
def applyState (u : Transition W M X Y) (I : State W V M) :
    State W V M :=
  {q | q.domain = Y ∧ ∃ p ∈ I, p.domain = X ∧
    p.world = q.world ∧
    ∃ (e : X → M) (e' : Y → M),
      (∀ v : X, e v ∈ p.assignment v.1) ∧
      (∀ v : Y, e' v ∈ q.assignment v.1) ∧
      u.rel q.world e e'}

/-- Application lands in the target stratum. -/
theorem uniformAt_applyState (u : Transition W M X Y) (I : State W V M) :
    State.UniformAt Y (u.applyState I) := fun _ hq => hq.1

/-- The point of the `Y`-stratum carrying a given world and assignment. -/
private def ptOf (Y : Set V) (w : W) (e : Y → M) :
    Possibility W V (Part M) :=
  ⟨w, fun v => ⟨v ∈ Y, fun hv => e ⟨v, hv⟩⟩⟩

private theorem domain_ptOf (Y : Set V) (w : W) (e : Y → M) :
    (ptOf Y w e).domain = Y := rfl

/-- Root application is functorial. -/
theorem applyState_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (I : State W V M) :
    (u.comp v).applyState I = v.applyState (u.applyState I) := by
  ext q
  constructor
  · rintro ⟨hq, p, hpI, hp, hw, e, e'', he, he'', k, huk, hkv⟩
    exact ⟨hq, ptOf Y q.world k, ⟨domain_ptOf .., p, hpI, hp, hw, e, k, he,
      fun x => ⟨x.2, rfl⟩, huk⟩, domain_ptOf .., rfl, k, e'',
      fun x => ⟨x.2, rfl⟩, he'', hkv⟩
  · rintro ⟨hq, m, ⟨hm, p, hpI, hp, hw, e, k, he, hk, huk⟩, -, hmw, k', e'',
      hk', he'', hvk⟩
    have hkk' : k = k' := funext fun x => Part.mem_unique (hk x) (hk' x)
    refine ⟨hq, p, hpI, hp, hw.trans hmw, e, e'', he, he'', k, ?_, ?_⟩
    · rw [← hmw]
      exact huk
    · rw [hkk']
      exact hvk

/-- Root and fiber semantics agree under the classification: on the
`X`-stratum, the regular CCP `applyState` is `apply`, transported along
`State.uniformEquiv` — the relational collapse computes the root-state
update. -/
theorem uniformEquiv_applyState (u : Transition W M X Y)
    {I : State W V M} (hI : State.UniformAt X I) :
    State.uniformEquiv Y ⟨u.applyState I, uniformAt_applyState u I⟩ =
      u.apply (State.uniformEquiv X ⟨I, hI⟩) := by
  ext f
  constructor
  · intro hf
    obtain ⟨-, p, hp, hpX, hw, e, f', hpe, hqf, hrel⟩ :
        ptOf Y f.1 f.2 ∈ u.applyState I := State.mem_uniformEquiv.mp hf
    have hf' : f' = f.2 := funext fun v => by
      obtain ⟨hv, hval⟩ := hqf v
      exact hval.symm
    subst hf'
    refine ⟨e, State.mem_uniformEquiv.mpr ?_, by exact hrel⟩
    show ptOf X f.1 e ∈ I
    have hpeq : ptOf X f.1 e = p :=
      Possibility.ext hw.symm <| funext fun v =>
        Part.ext' ⟨fun hv => hpX.superset hv, fun hd => hpX.subset hd⟩
          fun hv hd => Part.mem_unique (hpe ⟨v, hv⟩) (Part.get_mem hd)
    rw [hpeq]; exact hp
  · rintro ⟨e, hmem, hrel⟩
    have hpI : ptOf X f.1 e ∈ I := State.mem_uniformEquiv.mp hmem
    refine State.mem_uniformEquiv.mpr ?_
    show ptOf Y f.1 f.2 ∈ u.applyState I
    exact ⟨domain_ptOf .., ptOf X f.1 e, hpI, domain_ptOf .., rfl, e,
      f.2, fun v => ⟨v.2, rfl⟩, fun v => ⟨v.2, rfl⟩, by exact hrel⟩

end ApplyState

/-! ### Random assignment -/

/-- The random-assignment transition ([groenendijk-stokhof-1991]'s random
reset `k[x]g`, [heim-1982]'s indefinite widening): preserve the input off
`x`, leave the output free at `x` — the generating arrow
`X ⟶ insert x X` of context extension. -/
def randomAssign (X : Set V) (x : V) :
    Transition W M X (insert x X) where
  rel _ e e' := ∀ (v : V) (hv : v ∈ X), v ≠ x →
    e ⟨v, hv⟩ = e' ⟨v, Set.mem_insert_of_mem x hv⟩
  grow := Set.subset_insert x X

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
def ReadsAt (X : Set V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f f' g⦄, Set.EqOn f f' X → (R w f g ↔ R w f' g)

/-- The relation constrains its output only at `Y`. -/
def WritesAt (Y : Set V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f g g'⦄, Set.EqOn g g' Y → (R w f g ↔ R w f g')

/-- Type a total-assignment relation at contexts, by existential
extension of the assignments. -/
def ofTotal (h : X ⊆ Y) (R : W → (V → M) → (V → M) → Prop) :
    Transition W M X Y where
  rel w e e' := ∃ f g : V → M, X.restrict f = e ∧
    Y.restrict g = e' ∧ R w f g
  grow := h

/-- Under the support hypotheses, the typing is faithful: related
assignments are exactly the restrictions of related assignments. -/
theorem ofTotal_rel_restrict {h : X ⊆ Y} (hR : ReadsAt X R)
    (hW : WritesAt Y R) {w : W} {f g : V → M} :
    (ofTotal h R).rel w (X.restrict f)
      (Y.restrict g) ↔ R w f g := by
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
    exact ⟨Y.restrict k, ⟨f, k, hf, rfl, hR⟩,
      ⟨k, g, rfl, hg, hS'⟩⟩

end OfTotal

/-! ### Repackaging along base equalities

The substrate-safe form of `eqToHom` conjugation (mathlib's `Filter.copy`
pattern): composites whose indices differ by base identities — e.g.
`(X ∪ U₁) ∪ U₂` against `X ∪ (U₁ ∪ U₂)` — are equated through `copy`,
keeping cast-free statements everywhere below the category layer. -/

/-- Repackage a transition along equalities of its bases. -/
def copy (u : Transition W M X Y) {X' Y' : Set V} (hX : X = X')
    (hY : Y = Y') : Transition W M X' Y' :=
  hX ▸ hY ▸ u

@[simp] theorem copy_rfl (u : Transition W M X Y) : u.copy rfl rfl = u := rfl

@[simp] theorem copy_copy (u : Transition W M X Y)
    {X' Y' X'' Y'' : Set V} (hX : X = X') (hY : Y = Y')
    (hX' : X' = X'') (hY' : Y' = Y'') :
    (u.copy hX hY).copy hX' hY' = u.copy (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

/-- Typing respects relation equality; the growth proof is irrelevant. -/
theorem ofTotal_congr {R R' : W → (V → M) → (V → M) → Prop}
    (h h' : X ⊆ Y) (hR : R = R') : ofTotal h R = ofTotal h' R' := by
  subst hR
  rfl

/-- Typed relations repackage by re-proving the growth. -/
theorem ofTotal_copy {R : W → (V → M) → (V → M) → Prop} {h : X ⊆ Y}
    {Y' : Set V} (hY : Y = Y') :
    (ofTotal h R).copy rfl hY = ofTotal (hY ▸ h) R := by
  subst hY
  rfl

/-- Repackaged transitions compose to the repackaged composite. -/
theorem copy_comp_copy (u : Transition W M X Y) (v : Transition W M Y Z)
    {X' Y' Z' : Set V} (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (u.copy hX hY).comp (v.copy hY hZ) = (u.comp v).copy hX hZ := by
  subst hX hY hZ
  rfl

/-- Application is invariant under repackaging. -/
@[simp] theorem apply_copy (u : Transition W M X Y) {X' Y' : Set V}
    (hX : X = X') (hY : Y = Y') (T : Set (W × ((↑X' : Set V) → M))) :
    (u.copy hX hY).apply T = (by subst hX hY; exact u.apply T) := by
  subst hX hY
  rfl

/-- Root application is invariant under repackaging. -/
@[simp] theorem applyState_copy (u : Transition W M X Y)
    {X' Y' : Set V} (hX : X = X') (hY : Y = Y') (I : State W V M) :
    (u.copy hX hY).applyState I = u.applyState I := by
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
