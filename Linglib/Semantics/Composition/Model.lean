import Linglib.Semantics.Composition.Tree
import Mathlib.ModelTheory.Basic

/-!
# Model-theoretic semantics for type-driven composition

A **composition model** is a mathlib first-order `Structure` over an entity domain, indexed by a
world set (constant-domain intensional first-order). Content-predicate denotations are *sourced
from* the model via `Structure.RelMap`, exactly as DRT sources atomic-condition truth
(`Semantics/Dynamic/DRS/`); higher-order denotations (GQs, type-shifts) and worlds ride on top
in Lean and in the `.intens` types, so the existing `Tree.interp` engine composes a
model-sourced lexicon **unchanged**.

API objects (`Pronoun`, …) and `Fragments/` stay **minimal data**: the engine *projects* them
into typed terms — a pronoun occurrence to a trace valued by the assignment over the model's
entity domain, φ-features to restrictions read off the model — and the model interprets those
terms. Nothing model-theoretic lives on the objects or in the lexicon data.

## Main declarations

* `Model` — entity domain `E`, worlds `W`, and a world-indexed family `interp : W → L.Structure E`
* `Model.pred₁` / `Model.pred₂` — model-sourced predicate denotations
* `interp_model_sourced` — the real `Tree.interp` composes a model-sourced lexicon to a
  world-threading proposition, truth bottoming out in `RelMap`
* `barbara` — cross-model logical consequence (truth in all models), the payoff over a fixed
  entity/world frame
* `interp_pronoun_trace`, `genderRestriction` — the projection discipline for API objects
-/

set_option autoImplicit false

open FirstOrder Language
open Core.Logic.Intensional
open Semantics.Montague (Lexicon)
open Semantics.Composition.Tree
open Syntax (Tree)

namespace Semantics.Composition

universe u v

/-- A composition model: a constant entity domain `E`, a world set `W`, and a world-indexed
family of first-order `L`-structures (the lexicon interpretation), with the content lexicon
as a mathlib `Language` signature (constant-domain intensional first-order). -/
structure Model (L : Language.{u, v}) where
  /-- Entity domain. -/
  E : Type
  /-- World/index set. -/
  W : Type
  /-- World-indexed interpretation of the lexical signature. -/
  interp : W → L.Structure E

variable {L : Language.{u, v}}

/-- A unary content predicate's denotation, *sourced from the model*: world-relativized,
bottoming out in `Structure.RelMap`. Type `e ⇒ ⟨s,t⟩` — an intensional one-place predicate. -/
def Model.pred₁ (m : Model L) (R : L.Relations 1) : Denot m.E m.W (.e ⇒ .intens .t) :=
  fun x w => (m.interp w).RelMap R (fun _ => x)

/-- A binary content predicate's denotation, sourced from the model (`e ⇒ e ⇒ ⟨s,t⟩`,
object-first then subject, matching `Frame`'s `eet` convention). -/
def Model.pred₂ (m : Model L) (R : L.Relations 2) :
    Denot m.E m.W (.e ⇒ .e ⇒ .intens .t) :=
  fun y x w => (m.interp w).RelMap R (fun i => if i = 0 then x else y)

/-! ### Engine integration: the real `Tree.interp` composes a model-sourced lexicon -/

/-- A minimal model-sourced lexicon: `"subj"` denotes `subj`, and the intransitive verb `"V"`
has the model's interpretation of a unary symbol `R` as its (intensional) denotation. -/
def lexFromModel (m : Model L) (subj : m.E) (R : L.Relations 1) : Lexicon m.E m.W :=
  fun s => match s with
  | "subj" => some ⟨.e, subj⟩
  | "V" => some ⟨.e ⇒ .intens .t, m.pred₁ R⟩
  | _ => none

/-- "subj V" — a one-place predication. -/
def predicationTree : Tree Unit String :=
  .node () [.terminal () "subj", .terminal () "V"]

/-- **Engine integration**: the actual `Tree.interp` composes the model-sourced lexicon (via real
backward FA) to a proposition `⟨s,t⟩`, threading worlds through the `.intens` type; its truth at a
world bottoms out in `Structure.RelMap`. The engine needs no model-specific machinery. -/
theorem interp_model_sourced (m : Model L) (subj : m.E) (R : L.Relations 1)
    (g : Core.Assignment m.E) :
    interp m.E m.W (lexFromModel m subj R) g predicationTree
      = some ⟨.intens .t, fun w => (m.interp w).RelMap R (fun _ => subj)⟩ :=
  rfl

/-! ### Cross-model logical consequence -/

/-- **Cross-model consequence** (the payoff over a fixed frame): with content predicates sourced
from the model and the quantifier in Lean, the syllogism *every Q is R, every P is Q ⊨ every P
is R* holds in **every** model `m` and world `w` — genuine logical consequence, ∀ models. -/
theorem barbara (m : Model L) (w : m.W) (P Q R : L.Relations 1)
    (hQR : ∀ x, (m.interp w).RelMap Q (fun _ => x) → (m.interp w).RelMap R (fun _ => x))
    (hPQ : ∀ x, (m.interp w).RelMap P (fun _ => x) → (m.interp w).RelMap Q (fun _ => x)) :
    ∀ x, (m.interp w).RelMap P (fun _ => x) → (m.interp w).RelMap R (fun _ => x) :=
  fun x hP => hQR x (hPQ x hP)

/-! ### Projection discipline for API objects

API objects carry minimal data; the engine projects them into model-theoretic terms. A pronoun
occurrence projects to a trace, interpreted as the assignment value over the model's entity
domain; its φ-features project to restrictions read off the model. Nothing model-theoretic is
stored on the `Pronoun` object (which has "no denotation of its own"). -/

/-- A pronoun occurrence projects to a trace term: the engine interprets `heₙ` as the assignment
value `g n`, an entity in the model's domain. The object supplies only the index. -/
theorem interp_pronoun_trace (m : Model L) (lex : Lexicon m.E m.W)
    (g : Core.Assignment m.E) (n : Nat) :
    interp m.E m.W lex g (.trace n () : Tree Unit String) = some ⟨.e, g n⟩ :=
  rfl

/-- A φ-feature (here masculine gender) projects to a restriction on the referent, *read off the
model*: `masc(g n)` at world `w`. The pronoun carries the feature; the model interprets it. -/
def genderRestriction (m : Model L) (masc : L.Relations 1) (w : m.W)
    (g : Core.Assignment m.E) (n : Nat) : Prop :=
  (m.interp w).RelMap masc (fun _ => g n)

end Semantics.Composition
