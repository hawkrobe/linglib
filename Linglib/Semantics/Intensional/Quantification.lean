import Linglib.Semantics.Intensional.Defs

/-!
# IL Quantification, Modality, and Identity

[dowty-wall-peters-1981] Ch. 6, Semantic Rules B.5, B.9–B.13

Completes the IL semantic rule toolkit with:
- `impl`, `biconditional` — material implication and biconditional (B.9–B.10)
- `forallEntity`, `existsEntity` — quantification over entities (B.11–B.12)
- `ident` — typed identity (B.5)
- `box`, `diamond` — necessity and possibility as IL primitives (B.13)

These are the *IL-level* operators — the primitives from which Kratzer's modal
semantics, tense operators, and PTQ translations are all derived. Kratzer's
richer framework (modal base + ordering source) in `Semantics/Modality/`
generalizes `box`/`diamond` here.
-/

namespace Intensional

variable {E W : Type}

-- ════════════════════════════════════════════════════════════════
-- § Material Implication and Biconditional (DWP B.9–B.10)
-- ════════════════════════════════════════════════════════════════

/-- Material implication. DWP Semantic Rule B.9. -/
def impl (p q : Denot E W .t) : Denot E W .t := p → q

/-- Material biconditional. DWP Semantic Rule B.10. -/
def biconditional (p q : Denot E W .t) : Denot E W .t := p ↔ q

theorem impl_neg_disj (p q : Denot E W .t) :
    impl p q = disj (neg p) q := by
  simp only [impl, disj, neg]
  exact propext ⟨fun h => Or.elim (Classical.em p) (fun hp => .inr (h hp)) .inl,
                  fun h hp => h.elim (absurd hp) id⟩

theorem biconditional_conj_impl (p q : Denot E W .t) :
    biconditional p q = conj (impl p q) (impl q p) := by
  simp only [biconditional, conj, impl]
  exact propext ⟨fun h => ⟨h.mp, h.mpr⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

theorem impl_refl (p : Denot E W .t) : impl p p := id

theorem impl_trans {p q r : Denot E W .t}
    (hpq : impl p q) (hqr : impl q r) : impl p r :=
  hqr ∘ hpq

theorem contrapositive {p q : Denot E W .t}
    (h : impl p q) : impl (neg q) (neg p) :=
  fun hnq hp => hnq (h hp)

theorem biconditional_comm (p q : Denot E W .t) :
    biconditional p q = biconditional q p := by
  simp only [biconditional]; exact propext Iff.comm

-- ════════════════════════════════════════════════════════════════
-- § Entity Quantification (DWP B.11–B.12)
-- ════════════════════════════════════════════════════════════════

/-- Universal quantification over entities.
    `⟦∀x.φ⟧ = 1` iff `⟦φ⟧^{g[x↦a]} = 1` for all `a ∈ A`.
    DWP Semantic Rule B.11. -/
def forallEntity (body : E → Denot E W .t) : Denot E W .t :=
  ∀ x, body x

/-- Existential quantification over entities.
    `⟦∃x.φ⟧ = 1` iff `⟦φ⟧^{g[x↦a]} = 1` for some `a ∈ A`.
    DWP Semantic Rule B.12. -/
def existsEntity (body : E → Denot E W .t) : Denot E W .t :=
  ∃ x, body x

/-- Duality: `∀x.φ ↔ ¬∃x.¬φ`. -/
theorem forallEntity_neg_existsEntity (body : E → Denot E W .t) :
    forallEntity body = neg (existsEntity (fun x => neg (body x))) := by
  simp only [forallEntity, existsEntity, neg, not_exists_not]

/-- Duality: `∃x.φ ↔ ¬∀x.¬φ`. -/
theorem existsEntity_neg_forallEntity (body : E → Denot E W .t) :
    existsEntity body = neg (forallEntity (fun x => neg (body x))) := by
  simp only [existsEntity, forallEntity, neg, not_forall_not]

/-- `∀x.φ → φ[a/x]` — universal instantiation. -/
theorem forallEntity_instantiate (body : E → Denot E W .t)
    (a : E) (h : forallEntity body) : body a :=
  h a

/-- `φ[a/x] → ∃x.φ` — existential generalization. -/
theorem existsEntity_generalize (body : E → Denot E W .t)
    (a : E) (h : body a) : existsEntity body :=
  ⟨a, h⟩

/-- `∀` distributes over `∧`. -/
theorem forallEntity_conj (p q : E → Denot E W .t) :
    forallEntity (fun x => conj (p x) (q x)) =
    conj (forallEntity p) (forallEntity q) := by
  simp only [forallEntity, conj, forall_and]

-- ════════════════════════════════════════════════════════════════
-- § Typed Identity (DWP B.5)
-- ════════════════════════════════════════════════════════════════

/-- Typed identity: `α = β` is a formula whenever α, β have the same type.
    DWP Semantic Rule B.5.

    In IL, identity is extensional: `⟦α = β⟧^{M,w,t,g} = 1` iff
    α and β have the same extension at ⟨w,t⟩. For intensional
    identity (same intension at all indices), use `identIntens`. -/
def ident {a : Ty} (x y : Denot E W a) : Denot E W .t := x = y

/-- Intensional identity: two expressions have the same intension
    (agree at every index). Stronger than `ident` at a single index.
    `^α = ^β` in DWP notation. -/
def identIntens {a : Ty} (x y : Denot E W (.intens a)) : Denot E W .t :=
  ∀ i : W, x i = y i

theorem ident_refl {a : Ty} (x : Denot E W a) : ident (E := E) (W := W) x x := rfl

theorem ident_symm {a : Ty} {x y : Denot E W a}
    (h : ident (E := E) (W := W) x y) : ident y x :=
  h.symm

theorem ident_trans {a : Ty} {x y z : Denot E W a}
    (hxy : ident (E := E) (W := W) x y) (hyz : ident y z) : ident x z :=
  hxy.trans hyz

/-- Intensional identity implies extensional identity at every index. -/
theorem identIntens_implies_ident {a : Ty}
    (x y : Denot E W (.intens a)) (i : W)
    (h : identIntens (E := E) (W := W) x y) : ident (x i) (y i) :=
  h i

/-- Intensional identity of `up` — rigid intensions of the same value
    are intensionally identical. -/
theorem identIntens_up {a : Ty} (x y : Denot E W a)
    (h : ident (E := E) (W := W) x y) : identIntens (up x) (up y) :=
  fun _ => h

-- ════════════════════════════════════════════════════════════════
-- § Necessity and Possibility (DWP B.13)
-- ════════════════════════════════════════════════════════════════

/-- Necessity (□): a proposition (intension of type t) is necessary
    iff it is true at every index.

    `⟦□φ⟧^{M,w,t,g} = 1` iff `⟦φ⟧^{M,w',t',g} = 1` for all w' ∈ W, t' ∈ T.

    DWP Semantic Rule B.13. In Montague's original IL, □ quantifies
    over *all* indices — it is S5 necessity. Kratzer's framework
    (`Semantics/Modality/Kratzer/`) restricts quantification
    to accessible worlds via a modal base and ordering source. -/
def box (p : Denot E W .prop) : Denot E W .t :=
  ∀ i : W, p i

/-- Possibility (◇): a proposition is possible iff it is true at
    some index. Dual of `box`. -/
def diamond (p : Denot E W .prop) : Denot E W .t :=
  ∃ i : W, p i

/-- □ and ◇ are duals: `□p ↔ ¬◇¬p`. -/
theorem box_neg_diamond (p : Denot E W .prop) :
    box (E := E) (W := W) p = neg (diamond (fun i => neg (p i))) := by
  simp only [box, diamond, neg, not_exists_not]

/-- `◇p ↔ ¬□¬p`. -/
theorem diamond_neg_box (p : Denot E W .prop) :
    diamond (E := E) (W := W) p = neg (box (fun i => neg (p i))) := by
  simp only [diamond, box, neg, not_forall_not]

/-- **K axiom**: `□(p → q) → (□p → □q)`.
    The fundamental distribution axiom of normal modal logic. -/
theorem box_K (p q : Denot E W .prop) :
    impl (box (E := E) (W := W) (fun i => impl (p i) (q i)))
         (impl (box p) (box q)) :=
  fun hpq hp i => hpq i (hp i)

/-- **T axiom**: `□p → p` at index `i`.
    Reflexivity — what is necessary is actual. Requires evaluating
    at a specific index (since `box` eliminates the index). -/
theorem box_T (p : Denot E W .prop) (i : W)
    (h : box (E := E) (W := W) p) : p i :=
  h i

/-- **Necessitation**: if `p` holds at all indices, then `□p`. -/
theorem necessitation (p : Denot E W .prop)
    (h : ∀ i : W, p i) : box (E := E) (W := W) p :=
  h

/-- □ distributes over ∧. -/
theorem box_conj (p q : Denot E W .prop) :
    box (E := E) (W := W) (fun i => conj (p i) (q i)) =
    conj (box p) (box q) := by
  simp only [box, conj, forall_and]

/-- ◇ distributes over ∨. -/
theorem diamond_disj (p q : Denot E W .prop) :
    diamond (E := E) (W := W) (fun i => disj (p i) (q i)) =
    disj (diamond p) (diamond q) := by
  simp only [diamond, disj, exists_or]

/-- `□p → ◇p` (seriality — holds vacuously when Index is inhabited). -/
theorem box_implies_diamond [Inhabited W]
    (p : Denot E W .prop)
    (h : box (E := E) (W := W) p) : diamond p :=
  ⟨default, h default⟩

/-- Necessity of identity: if `^α = ^β` necessarily (rigid intensions
    agree), this is itself necessary. Connects to `Rigidity.lean`'s
    `rigid_identity_necessary`. -/
theorem box_ident_rigid {a : Ty} (x y : Denot E W a)
    (h : ident (E := E) (W := W) x y) :
    box (fun i => ident (E := E) (W := W) (up (a := a) x i) (up y i)) :=
  fun _ => h

-- ════════════════════════════════════════════════════════════════
-- § Connections: box/diamond and up/down
-- ════════════════════════════════════════════════════════════════

/-- A rigid proposition (formed by `up`) is either necessarily true
    or necessarily false. -/
theorem box_or_box_neg_of_up (p : Denot E W .t) :
    box (E := E) (W := W) (up p) ∨ box (fun i => neg (up (E := E) (W := W) p i)) := by
  by_cases h : p
  · left; intro _; exact h
  · right; intro _; exact h

/-- `down (up p) i` is the same as `p` — restated via `box` to show
    that `up` followed by `box` is equivalent to the original proposition. -/
theorem box_up_iff [Inhabited W] (p : Denot E W .t) :
    box (E := E) (W := W) (up p) = p := by
  simp only [box, up]
  exact propext ⟨fun h => h default, fun h _ => h⟩

/-- `□` applied to the intension of `p` is `p` evaluated at every index.
    When `p` is already an intension, `box p` is just `∀ i, p i`. -/
theorem box_down (p : Denot E W .prop) (i : W) :
    down (up (box (E := E) (W := W) p)) i = box p := rfl

end Intensional
