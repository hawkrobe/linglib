import Linglib.Syntax.HPSG.Signature
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Relation.ReflTransGen

/-!
# RSRL interpretations
@cite{richter-2000}, @cite{richter-2024}

A native Lean rendering of an RSRL **interpretation** of a `Signature`
(@cite{richter-2000}, Def. 48): a universe of entities `U`, a species assignment `S`, an
attribute interpretation `A` (each attribute a *partial* function on entities), and a
relation interpretation `R`.

## Main declarations

* `HPSG.RSRL.Interpretation` — the structure `⟨U, S, A, R⟩` (Def. 48).
* `HPSG.RSRL.Interpretation.denot` — term/path denotation (Def. 53): follow each attribute of
  a path in turn, partially (`Option`-Kleisli composition).
* `HPSG.RSRL.Interpretation.WellTyped` — the totally-well-typed, sort-resolved condition a
  model must satisfy (Def. 48), as a `structure` with named fields.

## Implementation notes

* Attributes are interpreted as `A : Attr → U → Option U` (partial functions, Def. 48), via
  `Option`, so denotation and well-typedness reduce by `decide` on finite models.
* `WellTyped.appropSort` uses `Option` membership (`∀ τ ∈ Sig.approp …`) rather than a
  `Fintype`-search over all sorts for the one appropriate value.
* `R` is carried for faithfulness to Def. 48 but unused until the description language gains
  relational formulae (RSRL is strictly richer than first-order logic).
* `U` shares the signature's universe; full universe polymorphism is deferred.
-/

namespace HPSG.RSRL

universe u

/-- An RSRL interpretation of a signature (@cite{richter-2000}, Def. 48). -/
structure Interpretation {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- The universe of entities `U`. -/
  U : Type u
  /-- The species assignment `S` — every entity has a (maximally specific) sort. -/
  S : U → Srt
  /-- The attribute interpretation `A`: each attribute a partial function on entities. -/
  A : Sig.Attr → U → Option U
  /-- The relation interpretation `R` (unused until relational formulae are added). -/
  R : Sig.Rel → Set (List U)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- Path denotation (@cite{richter-2000}, Def. 53): the empty path denotes the entity itself;
`α :: rest` follows attribute `α` (partially) and then the rest of the path. -/
def denot (I : Interpretation Sig) : Path Sig → I.U → Option I.U
  | [], u => some u
  | a :: rest, u => (I.A a u).bind (denot I rest)

@[simp] theorem denot_nil (I : Interpretation Sig) (u : I.U) : I.denot [] u = some u := rfl

@[simp] theorem denot_cons (I : Interpretation Sig) (a : Sig.Attr) (rest : Path Sig)
    (u : I.U) : I.denot (a :: rest) u = (I.A a u).bind (denot I rest) := rfl

/-- Term denotation under a variable assignment (@cite{richter-2000}, Def. 53): `colon`
denotes the described entity `u`, `var n` the assigned entity `ass n`, and `feat t α` follows
attribute `α` (partially) from `t`'s denotation. -/
def termDenot (I : Interpretation Sig) (ass : Nat → I.U) : Term Sig → I.U → Option I.U
  | .colon, u => some u
  | .var n, _ => some (ass n)
  | .feat t a, u => (termDenot I ass t u).bind (I.A a)

/-- The attribute-successor relation: `y` is an attribute value of `x`. Its
reflexive-transitive closure is the *component-of* relation that bounds quantification. -/
def attrSucc (I : Interpretation Sig) (x y : I.U) : Prop := ∃ α : Sig.Attr, I.A α x = some y

instance (I : Interpretation Sig) [Fintype Sig.Attr] [DecidableEq I.U] :
    DecidableRel I.attrSucc := fun _ _ => by unfold attrSucc; infer_instance

/-- `v` is a **component of** `u` — reachable from `u` by following attributes (reflexively).
RSRL component quantification ranges over exactly these (@cite{richter-2024}, Ch. 3). -/
abbrev IsComponentOf (I : Interpretation Sig) (u v : I.U) : Prop :=
  Relation.ReflTransGen I.attrSucc u v

/-- Component-of is decidable on a finite interpretation (so `∃`-component quantification
reduces by `decide`). Reuses the finite-carrier reachability decision procedure. -/
instance (I : Interpretation Sig) [Fintype I.U] [DecidableEq I.U] [Fintype Sig.Attr]
    (u v : I.U) : Decidable (I.IsComponentOf u v) :=
  Relation.ReflTransGen.decidable_of_fintype u v

/-- The totally-well-typed, sort-resolved condition on a model (@cite{richter-2000}, Def. 48):
the species assignment lands in species, and every attribute is defined exactly on the
entities whose species licenses it, with an appropriately-specific value. -/
structure WellTyped (I : Interpretation Sig) : Prop where
  /-- Every entity's sort is a species (maximally specific). -/
  species : ∀ u, IsSpecies (I.S u)
  /-- An attribute is defined on an entity exactly when appropriate to its species. -/
  appropDefined : ∀ (α : Sig.Attr) (u : I.U), (I.A α u).isSome = (Sig.approp (I.S u) α).isSome
  /-- A defined attribute value's sort is at least as specific as the appropriate value sort. -/
  appropSort : ∀ (α : Sig.Attr) (u v : I.U), I.A α u = some v →
    ∀ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ

end Interpretation

end HPSG.RSRL
