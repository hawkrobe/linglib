import Linglib.Theories.Semantics.Verb.Roots.Template

/-!
# B&K-G Typology, Bifurcation, and Manner/Result Complementarity

@cite{beavers-koontz-garboden-2020} @cite{rappaport-hovav-levin-2010}

The four-feature typology of @cite{beavers-koontz-garboden-2020}
(±state, ±manner, ±result, ±cause) classifies roots by which kinds of
atomic entailments they carry. Crucially, this classification is
*derived* from `Root.entailments` — not stipulated as a separate enum.

Two long-standing conjectures restrict which feature combinations are
allowed:

- **Bifurcation Thesis of Roots**: roots only carry "ontological"
  entailments (state, manner). Eventive structure (result, cause) is
  contributed by templatic heads, never by roots.
- **Manner/Result Complementarity**
  (@cite{rappaport-hovav-levin-2010}): a single root entails manner
  *or* result, never both.

@cite{beavers-koontz-garboden-2020} argue both fail. Here we encode them
as Boolean predicates on roots and provide witnesses (in
`BeaversKoontzGarboden2020.lean`) that falsify the universal closures.
-/

namespace Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Feature Signature
-- ════════════════════════════════════════════════════

/-- The four-feature classification of a root
    (@cite{beavers-koontz-garboden-2020} table 13). All four features
    are *derived* from `Root.entailments`, so the 16-cell typology
    falls out of which kinds of atoms a root carries. -/
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

-- ════════════════════════════════════════════════════
-- § 2. Bifurcation Thesis of Roots
-- ════════════════════════════════════════════════════

/-- A root *violates* Bifurcation iff it carries both an ontological
    entailment (state or manner) and an eventive one (result or cause).
    The Bifurcation Thesis (@cite{beavers-koontz-garboden-2020}) is the
    universal claim that no root violates this. -/
def Root.ViolatesBifurcation (r : Root) : Prop :=
  (r.hasState = true ∨ r.hasManner = true) ∧
  (r.hasResult = true ∨ r.hasCause = true)

instance (r : Root) : Decidable r.ViolatesBifurcation := by
  unfold Root.ViolatesBifurcation; infer_instance

/-- Dual of `ViolatesBifurcation`. A root respects the thesis iff it
    has only ontological *or* only eventive entailments. -/
def Root.RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation := by
  unfold Root.RespectsBifurcation; infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Manner/Result Complementarity
-- ════════════════════════════════════════════════════

/-- A root has both manner and result entailments — the Manner/Result
    Complementarity thesis (@cite{rappaport-hovav-levin-2010}) is the
    universal claim that no root does. -/
def Root.HasMannerAndResult (r : Root) : Prop :=
  r.hasManner = true ∧ r.hasResult = true

instance (r : Root) : Decidable r.HasMannerAndResult := by
  unfold Root.HasMannerAndResult; infer_instance

/-- Dual of `HasMannerAndResult`. -/
def Root.RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity := by
  unfold Root.RespectsMannerResultComplementarity; infer_instance

end Semantics.Verb.Roots
