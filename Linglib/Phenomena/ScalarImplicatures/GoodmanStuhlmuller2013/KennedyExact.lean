import Linglib.Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.Bridge

/-!
# Kennedy (2015) exact semantics → G&S (2013) numeral implicatures
@cite{kennedy-2015} @cite{goodman-stuhlmuller-2013}

Applies Kennedy's (2015) de-Fregean exact numeral semantics with Partee
(1987) type-shifting to the numeral interpretation data from Goodman &
Stuhlmüller (2013). This connection is not made in either paper.

**Data source**: `GoodmanStuhlmuller2013.Data`
**Theory source**: `Theories.Semantics.Lexical.Numeral.Semantics` (Kennedy 2015)
**Infrastructure reused**: `GoodmanStuhlmuller2013.Bridge` (observation model,
  quality filter, speaker belief)

## Key insight

Kennedy's exact semantics assigns bare numerals a bilateral meaning:
"two" is true iff max count = 2. Kennedy (2015, §3.1) also derives a
lower-bound meaning via Partee's (1987) type-shifting (BE + iota +
existential closure). Both meanings are grammatically available.

We model this as interpretation ambiguity (cf. Scontras & Pearl 2021 for
scope): the listener marginalizes over both the speaker's observation
(epistemic state) and the interpretation (exact vs lower-bound).
`Latent = Obs × KennedyInterp`.

The quality filter selects interpretations based on the speaker's knowledge:
under partial access, the exact interpretation is blocked (false at some
believed worlds), leaving only the lower-bound reading. Under full access,
the exact interpretation is viable and more informative, so L1 selects it.

This derives the Experiment 2 numeral findings from Kennedy exact semantics
without abandoning bilateral truth conditions.

## References

- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified
  numerals. *Semantics & Pragmatics* 8(10), 1–44.
- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and implicature.
  *TopiCS* 5(1): 173-184.
- Partee, B. (1987). Noun phrase interpretation and type-shifting
  principles. In *Studies in Discourse Representation Theory*.
- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments. *Glossa* 6(1): 110.
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013

-- ============================================================================
-- §14. Kennedy Exact Semantics with Type-Shifting Ambiguity
-- ============================================================================

/-- Kennedy interpretation dimension: de-Fregean exact vs type-lowered. -/
inductive KennedyInterp where
  | exact      -- max{d : D(d)} = m  (basic de-Fregean meaning)
  | lowerBound -- ∃x[P(x) ∧ #(x) = m] (type-lowered via BE + iota)
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- Kennedy's Class A/B alternative structure for numeral m.
    The alternatives are: the bare numeral, "more than m", "at least m". -/
inductive KennedyUtt where
  | bare     -- the bare numeral (ambiguous between exact and lower-bound)
  | moreThan -- "more than m" (Class B modifier)
  | atLeast  -- "at least m" (Class A modifier)
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- Kennedy meaning for numeral m, parametrized by interpretation.
    Under exact interp: bare = max{d | P(d)} = m (bilateral).
    Under lower-bound interp: bare = max{d | P(d)} ≥ m (type-lowered).
    moreThan and atLeast are unambiguous across interpretations. -/
def kennedyMeaning (m : Nat) (interp : KennedyInterp) : KennedyUtt → WorldState → Bool
  | .bare, s => match interp with
    | .exact => s.toNat == m
    | .lowerBound => s.toNat ≥ m
  | .moreThan, s => s.toNat ≥ m + 1
  | .atLeast, s => s.toNat ≥ m

open RSA in
/-- Kennedy-ambiguity RSA model. L1 marginalizes over both the speaker's
    observation and the interpretation (exact vs lower-bound).
    The quality filter checks truth under the interpretation-specific meaning,
    so exact readings are blocked when the speaker considers worlds where the
    exact count differs from the stated numeral. -/
noncomputable abbrev gsCfgK (m : Nat) (a : Access) : RSAConfig KennedyUtt WorldState where
  Latent := Obs × KennedyInterp
  meaning ol u w := if kennedyMeaning m ol.2 u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α ol _w u :=
    if qualityOk (kennedyMeaning m ol.2) ol.1 u then
      Real.exp (α * ∑ s : WorldState, speakerBelief ol.1 s * Real.log (l0 u s))
    else 0
  s1Score_nonneg _ _ _ _ _ _ _ := by
    split
    · exact le_of_lt (Real.exp_pos _)
    · exact le_refl 0
  α := 1
  α_pos := one_pos
  latentPrior w ol := obsPriorTable a w ol.1
  latentPrior_nonneg w ol := by
    obtain ⟨obs, _⟩ := ol
    unfold obsPriorTable
    split
    · exact le_refl 0
    · (repeat' split) <;> positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §15. Kennedy "two" — Findings 4–5
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Full access: Kennedy exact semantics → bare "two" gets exact reading (s2 > s3).
    The exact interpretation is viable and more informative, so L1 selects it. -/
theorem kennedy_two_full_exact :
    (gsCfgK 2 .a3).L1 .bare .s2 > (gsCfgK 2 .a3).L1 .bare .s3 := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Partial access: exact interpretation is quality-blocked → lower-bound only.
    The quality filter blocks bare "two" under exact semantics when the speaker
    considers worlds with count ≠ 2. Only the type-lowered reading survives. -/
theorem kennedy_two_partial_weakened :
    ¬((gsCfgK 2 .a2).L1 .bare .s2 > (gsCfgK 2 .a2).L1 .bare .s3) := by
  rsa_predict

-- ============================================================================
-- §16. Kennedy "one" — Findings 6–11
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Full access: bare "one" → s1 > s2 (exact interpretation dominates). -/
theorem kennedy_one_full_1v2 :
    (gsCfgK 1 .a3).L1 .bare .s1 > (gsCfgK 1 .a3).L1 .bare .s2 := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Full access: bare "one" → s1 > s3. -/
theorem kennedy_one_full_1v3 :
    (gsCfgK 1 .a3).L1 .bare .s1 > (gsCfgK 1 .a3).L1 .bare .s3 := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Minimal access (a=1): s1 does not exceed s2 (exact blocked, lower-bound only). -/
theorem kennedy_one_minimal_1v2_canceled :
    ¬((gsCfgK 1 .a1).L1 .bare .s1 > (gsCfgK 1 .a1).L1 .bare .s2) := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Minimal access (a=1): s1 does not exceed s3. -/
theorem kennedy_one_minimal_1v3_canceled :
    ¬((gsCfgK 1 .a1).L1 .bare .s1 > (gsCfgK 1 .a1).L1 .bare .s3) := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Partial access (a=2): s1 > s3 (partial implicature persists). -/
theorem kennedy_one_partial_1v3 :
    (gsCfgK 1 .a2).L1 .bare .s1 > (gsCfgK 1 .a2).L1 .bare .s3 := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Partial access (a=2): s1 does not exceed s2 (still canceled). -/
theorem kennedy_one_partial_1v2_canceled :
    ¬((gsCfgK 1 .a2).L1 .bare .s1 > (gsCfgK 1 .a2).L1 .bare .s2) := by
  rsa_predict

-- ============================================================================
-- §17. Both semantics account for all numeral findings
-- ============================================================================

/-- The numeral findings (4–11) formalized under Kennedy exact + type-shifting. -/
def formalizeKennedy : Finding → Prop
  | .two_full_upper_bounded =>
      (gsCfgK 2 .a3).L1 .bare .s2 > (gsCfgK 2 .a3).L1 .bare .s3
  | .two_partial_weakened =>
      ¬((gsCfgK 2 .a2).L1 .bare .s2 > (gsCfgK 2 .a2).L1 .bare .s3)
  | .one_full_1v2 =>
      (gsCfgK 1 .a3).L1 .bare .s1 > (gsCfgK 1 .a3).L1 .bare .s2
  | .one_full_1v3 =>
      (gsCfgK 1 .a3).L1 .bare .s1 > (gsCfgK 1 .a3).L1 .bare .s3
  | .one_minimal_1v2_canceled =>
      ¬((gsCfgK 1 .a1).L1 .bare .s1 > (gsCfgK 1 .a1).L1 .bare .s2)
  | .one_minimal_1v3_canceled =>
      ¬((gsCfgK 1 .a1).L1 .bare .s1 > (gsCfgK 1 .a1).L1 .bare .s3)
  | .one_partial_1v3 =>
      (gsCfgK 1 .a2).L1 .bare .s1 > (gsCfgK 1 .a2).L1 .bare .s3
  | .one_partial_1v2_canceled =>
      ¬((gsCfgK 1 .a2).L1 .bare .s1 > (gsCfgK 1 .a2).L1 .bare .s2)
  -- Quantifier findings are not in scope for the Kennedy numeral model
  | .some_full_implicature | .some_minimal_canceled | .some_partial_canceled => True

/-- Kennedy exact semantics with type-shifting accounts for all 8 numeral findings. -/
theorem kennedy_numeral_findings_verified : ∀ f : Finding, formalizeKennedy f := by
  intro f; cases f
  · trivial
  · trivial
  · trivial
  · exact kennedy_two_full_exact
  · exact kennedy_two_partial_weakened
  · exact kennedy_one_full_1v2
  · exact kennedy_one_full_1v3
  · exact kennedy_one_minimal_1v2_canceled
  · exact kennedy_one_minimal_1v3_canceled
  · exact kennedy_one_partial_1v3
  · exact kennedy_one_partial_1v2_canceled

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013
