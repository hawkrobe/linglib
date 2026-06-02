import Linglib.Syntax.HPSG.Signature
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Relation.ReflTransGen

/-!
# RSRL interpretations
[richter-2000], [richter-2024]

An RSRL **interpretation** of a `Signature` (Def. 48): a universe `U`, a species assignment
`S`, partial attribute functions `A`, and a relation interpretation `R`. `WellTyped` is the
totally-well-typed, sort-resolved condition a model must meet. `ex`/`all` quantification ranges
over the components of an entity (`IsComponentOf`).
-/

namespace HPSG.RSRL

universe u

-- TODO: generalise `U : Type v` (currently tied to the signature's universe `u`).
/-- An RSRL interpretation of a signature ([richter-2000], Def. 48). -/
structure Interpretation {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- The universe of entities. -/
  U : Type u
  /-- Species assignment — every entity has a (maximally specific) sort. -/
  S : U → Srt
  /-- Attribute interpretation: each attribute a partial function on entities. -/
  A : Sig.Attr → U → Option U
  /-- Relation interpretation. -/
  R : Sig.Rel → Set (List U)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- Term denotation under an assignment (Def. 53): `colon ↦ u`, `var n ↦ ass n` (the anchor `u`
is intentionally ignored for variables), `feat t α ↦` follow `α` from `t`. -/
def termDenot (I : Interpretation Sig) (ass : Nat → I.U) : Term Sig → I.U → Option I.U
  | .colon, u => some u
  | .var n, _ => some (ass n)
  | .feat t a, u => (termDenot I ass t u).bind (I.A a)

/-- `y` is an attribute value of `x`; its reflexive-transitive closure is `IsComponentOf`. -/
def attrSucc (I : Interpretation Sig) (x y : I.U) : Prop := ∃ α : Sig.Attr, I.A α x = some y

instance (I : Interpretation Sig) [Fintype Sig.Attr] [DecidableEq I.U] :
    DecidableRel I.attrSucc := fun _ _ => by unfold attrSucc; infer_instance

/-- `v` is a **component of** `u` — reachable from `u` by following attributes. RSRL bounds
quantification to these ([richter-2024], Ch. 3). -/
abbrev IsComponentOf (I : Interpretation Sig) (u v : I.U) : Prop :=
  Relation.ReflTransGen I.attrSucc u v

instance (I : Interpretation Sig) [Fintype I.U] [DecidableEq I.U] [Fintype Sig.Attr]
    (u v : I.U) : Decidable (I.IsComponentOf u v) :=
  Relation.ReflTransGen.decidable_of_fintype u v

/-- Totally-well-typed, sort-resolved (Def. 48): `S` species-valued, and `A` defined exactly
where appropriate, with appropriate value sorts. -/
structure WellTyped (I : Interpretation Sig) : Prop where
  /-- Every entity's sort is a species. -/
  species : ∀ u, IsSpecies (I.S u)
  /-- An attribute is defined exactly when appropriate to the entity's species. -/
  appropDefined : ∀ (α : Sig.Attr) (u : I.U), (I.A α u).isSome = (Sig.approp (I.S u) α).isSome
  /-- A defined value's sort is at least as specific as the appropriate value sort. -/
  appropSort : ∀ (α : Sig.Attr) (u v : I.U), I.A α u = some v →
    ∀ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ

end Interpretation

end HPSG.RSRL
