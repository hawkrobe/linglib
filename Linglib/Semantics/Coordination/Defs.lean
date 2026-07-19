import Mathlib.Order.BooleanAlgebra.Basic
import Linglib.Features.Formative

/-!
# The Coordinator unit — marking + operation

A coordinator (*and* / *or* / *but* / *nor*) is **one** thing: a lexical marking whose
`role` selects a Boolean operation. This file is the carrier-agnostic core of the
`Coordinator` API — it needs only `Mathlib.Order.BooleanAlgebra`, so Fragments import it
directly to type their lexical coordinators (the `Semantics/Verb/Defs.lean` precedent: a
word-class lexical-entry type at `Semantics/{class}/Defs`). The Denot-specific bridges
(`genConj = op`, `engineOp`, the `BooleanAlgebra (Denot)` instances) live downstream in
`Semantics/Coordination/Basic.lean`.

`op` is the *at-issue* truth-conditional operation: the role selects the Boolean method
(`⊓` / `⊔` / `(·⊔·)ᶜ`), the instance supplies the algebra. It is faithful for *and* (`.j`),
*or* (`.disj`), *nor* (`.negDisj`/`.negCoord`); the additive `.mu` and adversative `.advers`
collapse onto *and*'s meet here (`op_mu_eq_j`/`op_advers_eq_j`), their surplus content (M&S
additive/focus, adversative contrast) diverging to the relevant studies / the discourse layer.

## Main definitions

* `Coordinator.Role` — which Boolean operation a coordinator denotes.
* `Coordinator.op` — the operation a role denotes, polymorphic over `[BooleanAlgebra α]`.
* `Coordinator` — a lexical coordinator's marking (decidable data Fragments configure).
-/

namespace Coordinator

/-- The role of a coordinator — which Boolean operation it denotes. -/
inductive Role where
  /-- J particle: set intersection / conjunction proper
      (English "and", Hungarian "es", Georgian "da"). -/
  | j
  /-- MU particle: subset/additive (Hungarian "is", Georgian "-c", Japanese "mo");
      at-issue identical to `j`. -/
  | mu
  /-- Disjunction (English "or", Hungarian "vagy"). -/
  | disj
  /-- Adversative (English "but", Hungarian "de"); at-issue identical to `j`. -/
  | advers
  /-- Negative disjunction (Irish "na" = "nor"). -/
  | negDisj
  /-- Negative coordination (Latin "neque/nec" = "neither...nor"). -/
  | negCoord
  deriving DecidableEq, Repr, BEq

/-- **THE operation** a role denotes, polymorphic over any Boolean carrier: the role selects
    the Boolean method (`⊓` / `⊔` / `(·⊔·)ᶜ`), the instance supplies the algebra. Faithful for
    *and* (`.j`), *or* (`.disj`), *nor* (`.negDisj`/`.negCoord`); the additive `.mu` and
    adversative `.advers` give only the at-issue meet — `{j, mu, advers}` all collapse onto
    `⊓` here, the surplus diverging (see `op_mu_eq_j`/`op_advers_eq_j`). -/
def op {α : Type*} [BooleanAlgebra α] : Role → α → α → α
  | .j | .mu | .advers => (· ⊓ ·)
  | .disj => (· ⊔ ·)
  | .negDisj | .negCoord => fun p q => (p ⊔ q)ᶜ

/-- Additive `.mu` has the same at-issue denotation as *and*; its M&S additive/focus
    dimension diverges (see `Studies/MitrovicSauerland2016`). -/
theorem op_mu_eq_j {α : Type*} [BooleanAlgebra α] : (op .mu : α → α → α) = op .j := rfl

/-- Adversative `.advers` (*but*) has the same at-issue denotation as *and*; its contrast is a
    discourse relation outside `op` (and non-commutative there, which the commutative `⊓`
    cannot represent). -/
theorem op_advers_eq_j {α : Type*} [BooleanAlgebra α] : (op .advers : α → α → α) = op .j := rfl

end Coordinator

/-- A coordination morpheme's **marking** — decidable data Fragments configure. The
    denotation is not stored: it is `Coordinator.op` of `role`. -/
structure Coordinator where
  /-- Surface form of the morpheme. -/
  form : String
  /-- Gloss / translation. -/
  gloss : String
  /-- Which Boolean operation it denotes. -/
  role : Coordinator.Role
  /-- Free word vs bound clitic/suffix. -/
  boundness : Features.Boundness
  /-- Does this morpheme also serve as an additive/focus particle? -/
  alsoAdditive : Bool := false
  /-- Does this morpheme also serve as a quantifier particle?
      Japanese "mo" and "ka" both do — tracks the coordination-quantification connection. -/
  alsoQuantifier : Bool := false
  /-- Can this morpheme be used in correlative (bisyndetic) patterns?
      Latin "et...et", "aut...aut". -/
  correlative : Bool := false
  /-- Notes on usage or distribution. -/
  note : String := ""
  deriving DecidableEq, Repr, BEq
