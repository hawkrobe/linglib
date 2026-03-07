import Linglib.Core.Context.Tower

/-!
# Iconological Semantics
@cite{schlenker-lamberton-2024}

Core types for Iconological Semantics: a framework combining compositional
logical semantics with pictorial semantics for sign language classifier
predicates. Classifiers have both a logical component (predicate over entities)
and an iconic component (projection from a viewpoint).

Viewpoints may be static (a fixed observation point) or dynamic (varying with
time and world), following @cite{schlenker-lamberton-lamberton-2026}'s
extension.

## Key Types

- `StaticViewpoint P` — a fixed observation point in position space `P`
- `DynamicViewpoint W T P` — a viewpoint that varies with time and world
- `ViewpointVar` — a viewpoint variable: free (π_i) or context-bound (π*)
- `ClassifierPred E P` — a classifier predicate with logical + iconic content
- `dynamicProjection` — evaluate projection from a dynamic viewpoint at (w, t)
-/

namespace Semantics.Iconic

-- ════════════════════════════════════════════════════════════════
-- § Viewpoints
-- ════════════════════════════════════════════════════════════════

/-- A static viewpoint: a fixed observation point in some position space.
    In Iconological Semantics, this is the point from which a classifier's
    iconic content is evaluated via geometric projection. -/
structure StaticViewpoint (P : Type*) where
  position : P

/-- A dynamic viewpoint: a function from time-world pairs to static
    viewpoints. This is @cite{schlenker-lamberton-lamberton-2026}'s key
    generalization: viewpoints can move, modeling traveling camera shots
    in sign language narrative. -/
def DynamicViewpoint (W : Type*) (T : Type*) (P : Type*) :=
  W → T → StaticViewpoint P

/-- Lift a static viewpoint to a dynamic one (constant function). -/
def DynamicViewpoint.static {W : Type*} {T : Type*} {P : Type*}
    (sv : StaticViewpoint P) : DynamicViewpoint W T P :=
  fun _ _ => sv

/-- A dynamic viewpoint is static iff it is constant across all
    time-world pairs. Standard (non-traveling) viewpoints satisfy this. -/
def DynamicViewpoint.isStatic {W : Type*} {T : Type*} {P : Type*}
    (vp : DynamicViewpoint W T P) : Prop :=
  ∀ (w₁ w₂ : W) (t₁ t₂ : T), vp w₁ t₁ = vp w₂ t₂

/-- A static viewpoint lifted to dynamic is indeed static. -/
theorem static_isStatic {W : Type*} {T : Type*} {P : Type*}
    (sv : StaticViewpoint P) :
    (DynamicViewpoint.static sv : DynamicViewpoint W T P).isStatic :=
  fun _ _ _ _ => rfl

-- ════════════════════════════════════════════════════════════════
-- § Viewpoint Variables
-- ════════════════════════════════════════════════════════════════

/-- A viewpoint variable: determines how a classifier's viewpoint is
    resolved.

    - `.free i`: the variable π_i, whose value comes from the assignment
      function. Different classifiers in the same sentence can have
      distinct free viewpoint variables.
    - `.contextBound`: the variable π*, whose value is the dynamic
      viewpoint associated with the context's agent. Introduced by
      Role Shift. -/
inductive ViewpointVar where
  | free (i : Nat)
  | contextBound
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════════════════
-- § Projection
-- ════════════════════════════════════════════════════════════════

/-- Dynamic projection: evaluate projection from a viewpoint that varies
    with time and world.

    At time t in world w, the object is projected from the static
    viewpoint π(w, t). This captures the traveling shot: as the viewpoint
    moves, different spatial configurations are visible.

    When the viewpoint is static (constructed via `DynamicViewpoint.static`),
    this reduces to plain function application at the fixed viewpoint. -/
def dynamicProjection {W : Type*} {T : Type*} {E : Type*} {P : Type*}
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (vp : DynamicViewpoint W T P) (w : W) (t : T) : Bool :=
  projects d (vp w t)

/-- Dynamic projection at a static viewpoint is time-invariant. -/
theorem dynamicProjection_static {W : Type*} {T : Type*} {E : Type*} {P : Type*}
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (sv : StaticViewpoint P) (w : W) (t₁ t₂ : T) :
    dynamicProjection projects d (DynamicViewpoint.static sv) w t₁ =
    dynamicProjection projects d (DynamicViewpoint.static sv) w t₂ := rfl

-- ════════════════════════════════════════════════════════════════
-- § Classifier Predicates
-- ════════════════════════════════════════════════════════════════

/-- A classifier predicate: the lexical entry for a sign language
    classifier, combining logical and iconic content.

    The logical component is a standard predicate (e.g., "is a tree").
    The iconic component specifies how entities project to the classifier
    form from a viewpoint. The viewpoint variable determines which
    viewpoint the iconic component is evaluated relative to.

    This corresponds to the paper's (25):
    ⟦P^π⟧ = λx. ⟦P⟧(x) = 1 and proj(x, s(π), t, w) = P -/
structure ClassifierPred (E : Type*) (P : Type*) where
  /-- The logical predicate (e.g., tree', pole', person') -/
  logical : E → Bool
  /-- The iconic projection function -/
  projects : E → StaticViewpoint P → Bool
  /-- The viewpoint variable this classifier is evaluated relative to -/
  viewpointVar : ViewpointVar
  /-- The classifier label (for transcription) -/
  label : String

/-- Evaluate a classifier predicate at a dynamic viewpoint.
    Returns true iff the logical predicate holds AND the object
    projects to the classifier from the viewpoint at (w, t). -/
def ClassifierPred.eval {E : Type*} {P : Type*} {W : Type*} {T : Type*}
    (cl : ClassifierPred E P) (d : E)
    (vp : DynamicViewpoint W T P) (w : W) (t : T) : Bool :=
  cl.logical d && dynamicProjection cl.projects d vp w t

/-- At a static viewpoint, classifier evaluation is time-invariant. -/
theorem ClassifierPred.eval_static {E : Type*} {P : Type*} {W : Type*} {T : Type*}
    (cl : ClassifierPred E P) (d : E) (sv : StaticViewpoint P)
    (w : W) (t₁ t₂ : T) :
    cl.eval d (DynamicViewpoint.static sv) w t₁ =
    cl.eval d (DynamicViewpoint.static sv) w t₂ := rfl

end Semantics.Iconic
