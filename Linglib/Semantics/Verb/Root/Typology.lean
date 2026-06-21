import Linglib.Semantics.Verb.Root.Basic

/-!
# Bifurcation and Manner/Result Complementarity for Roots

The two conjectures [beavers-koontz-garboden-2020] argue against,
stated for roots by delegation to the signature level
(`Roots/Signature.lean`):

- **Bifurcation Thesis of Roots** ([embick-2009]; the assumption of
  [arad-2005]): meaning introduced by a functional head — change,
  cause — can never be part of a root's meaning. As an order
  statement: every root's signature lies below
  `Root.Kinds.ontological`.
- **Manner/Result Complementarity** ([rappaport-hovav-levin-2010]): a
  single root entails a manner *or* a result, never both. As an order
  statement: no root's signature lies above `{manner, result}`.

Falsifying witnesses live in `Studies/BeaversKoontzGarboden2020.lean`.

## Main declarations

* `Root.ViolatesBifurcation`, `Root.HasMannerAndResult`, and their
  negations `Root.RespectsBifurcation`,
  `Root.RespectsMannerResultComplementarity`
-/

namespace Verb

namespace Root

/-- A root *violates* Bifurcation iff it itself carries templatic
    (eventive) meaning — change of state or cause
    (`Root.Kinds.violatesBifurcation_iff`). The Bifurcation
    Thesis ([embick-2009]; [arad-2005]) is the universal claim that no
    root does. (The ditransitive prepositional heads P_loc and P_have,
    which [beavers-koontz-garboden-2020] also treat as templatic, are
    not modeled here.) -/
def ViolatesBifurcation (r : Root) : Prop :=
  r.kinds.ViolatesBifurcation

instance (r : Root) : Decidable r.ViolatesBifurcation :=
  inferInstanceAs (Decidable (Root.Kinds.ViolatesBifurcation _))

/-- Negation of `ViolatesBifurcation`: the root carries only
    ontological entailments (state, manner). -/
def RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation :=
  inferInstanceAs (Decidable (¬ _))

/-- The thesis as an order statement: a root respects Bifurcation iff
    its signature is bounded by the ontological kinds. -/
theorem respectsBifurcation_iff_le {r : Root} :
    r.RespectsBifurcation ↔
      r.kinds ≤ Root.Kinds.ontological :=
  not_not

/-- A root has both manner and result entailments — Manner/Result
    Complementarity ([rappaport-hovav-levin-2010]) is the universal
    claim that no root does. -/
def HasMannerAndResult (r : Root) : Prop :=
  r.kinds.HasMannerAndResult

instance (r : Root) : Decidable r.HasMannerAndResult :=
  inferInstanceAs (Decidable (Root.Kinds.HasMannerAndResult _))

/-- Negation of `HasMannerAndResult`. -/
def RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity :=
  inferInstanceAs (Decidable (¬ _))

end Root

end Verb
