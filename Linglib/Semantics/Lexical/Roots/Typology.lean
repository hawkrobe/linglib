import Linglib.Semantics.Lexical.Roots.Basic

/-!
# B&K-G Typology, Bifurcation, and Manner/Result Complementarity

The four-feature classification of roots (±state, ±manner, ±result,
±cause) of [beavers-koontz-garboden-2020], *derived* from
`Root.entailments` rather than stipulated as a separate enum, together
with the two conjectures the book argues against:

- **Bifurcation Thesis of Roots** ([embick-2009]; the assumption of
  [arad-2005]): meaning introduced by a functional head — change,
  cause — can never be part of a root's meaning.
- **Manner/Result Complementarity** ([rappaport-hovav-levin-2010]): a
  single root entails a manner *or* a result, never both.

Falsifying witnesses live in `Studies/BeaversKoontzGarboden2020.lean`.

## Main declarations

* `FeatureSignature`, `Root.featureSignature`
* `Root.ViolatesBifurcation`, `Root.HasMannerAndResult`, and their
  negations `Root.RespectsBifurcation`,
  `Root.RespectsMannerResultComplementarity`
-/

namespace Semantics.Lexical.Roots

/-! ### Feature signature -/

/-- The four-feature classification of a root (the root typology of
    [beavers-koontz-garboden-2020] ch. 5). All four features are
    *derived* from `Root.entailments`, so the 16-cell typology falls
    out of which kinds of atoms a root carries. -/
structure FeatureSignature where
  state  : Bool
  manner : Bool
  result : Bool
  cause  : Bool
  deriving DecidableEq, Repr

namespace Root

/-- The B&K-G feature signature of a root, derived from its
    entailment list. -/
def featureSignature (r : Root) : FeatureSignature :=
  { state  := r.hasState
  , manner := r.hasManner
  , result := r.hasResult
  , cause  := r.hasCause }

end Root

/-! ### Bifurcation Thesis of Roots -/

/-- A root *violates* Bifurcation iff it itself carries templatic
    (eventive) meaning — change of state or cause. The Bifurcation
    Thesis ([embick-2009]; [arad-2005]) is the universal claim that no
    root does. (The ditransitive prepositional heads P_loc and P_have,
    which [beavers-koontz-garboden-2020] also treat as templatic, are
    not modeled here.) -/
def Root.ViolatesBifurcation (r : Root) : Prop :=
  r.hasResult = true ∨ r.hasCause = true

instance (r : Root) : Decidable r.ViolatesBifurcation := by
  unfold Root.ViolatesBifurcation; infer_instance

/-- Negation of `ViolatesBifurcation`: the root carries only
    ontological entailments (state, manner). -/
def Root.RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation := by
  unfold Root.RespectsBifurcation; infer_instance

/-! ### Manner/Result Complementarity -/

/-- A root has both manner and result entailments — Manner/Result
    Complementarity ([rappaport-hovav-levin-2010]) is the universal
    claim that no root does. -/
def Root.HasMannerAndResult (r : Root) : Prop :=
  r.hasManner = true ∧ r.hasResult = true

instance (r : Root) : Decidable r.HasMannerAndResult := by
  unfold Root.HasMannerAndResult; infer_instance

/-- Negation of `HasMannerAndResult`. -/
def Root.RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity := by
  unfold Root.RespectsMannerResultComplementarity; infer_instance

end Semantics.Lexical.Roots
