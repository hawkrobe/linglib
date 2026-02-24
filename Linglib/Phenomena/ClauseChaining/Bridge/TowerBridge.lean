import Linglib.Phenomena.ClauseChaining.Data
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Clause Chaining: ContextTower Bridge @cite{sarvasy-aikhenvald-2025}

End-to-end derivation chain connecting the ContextTower infrastructure to
clause chaining phenomena. The core insight: in a medial-final chain, the
final verb establishes the root context and each medial clause pushes a
`.clauseChain` shift. TAM values absent on medial verbs are inherited from
the origin (the final verb's context).

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, origin, innermost, ShiftLabel.clauseChain)
    ↓
Core.Context.Shifts (temporalShift: medial clauses with temporal shift)
    ↓
This file: tower depth = chain length, origin access = TAM scope
    ↓
Phenomena.ClauseChaining.Data (nungon, korean, turkish, etc.)
```

## Key Results

1. **Tower depth = chain length**: N medial clauses → tower depth N
2. **TAM scope = origin access**: the final verb's tense/mood at `.origin`
   scopes over medial clauses that lack their own tense/mood
3. **Tense inheritance**: languages with `tenseFromFinalVerb = true` (Nungon)
   read tense from origin; languages with medial tense (Turkish) read locally
4. **SR as agent comparison**: SS = `.agent` same across adjacent tower levels;
   DS = `.agent` differs

## References

- Sarvasy, H. S. & A. Y. Aikhenvald (eds.) (2025). Clause Chaining in the
  Languages of the World. IRL Press at Oxford University Press.
- Foley, W. A. & R. D. Van Valin, Jr. (1984). Functional Syntax and Universal
  Grammar. Cambridge University Press.
-/

namespace Phenomena.ClauseChaining.Bridge.TowerBridge

open Core.Context
open Phenomena.ClauseChaining.Typology
open Phenomena.ClauseChaining.Data

-- ============================================================================
-- § Chain Context Type
-- ============================================================================

/-- A minimal clause chain context: world (event structure), agent (subject),
    position (clause index), and time (event time). -/
inductive ChainAgent where | subjectA | subjectB | subjectC
  deriving DecidableEq, Repr, BEq

abbrev ChainCtx := KContext Unit ChainAgent Unit ℤ

/-- The final verb's context: subject A speaking at time 0.
    This is the "root" of the chain — the final verb's TAM values. -/
def finalCtx : ChainCtx :=
  { world := (), agent := .subjectA, addressee := .subjectA, time := 0, position := () }

/-- A clauseChain shift: changes agent and time for a medial clause.
    The medial clause has its own subject and event time. -/
def chainShift (newAgent : ChainAgent) (eventTime : ℤ) : ContextShift ChainCtx where
  apply := λ c => { c with agent := newAgent, time := eventTime }
  label := .clauseChain

-- ============================================================================
-- § Tower Depth = Chain Length
-- ============================================================================

/-- Root tower: just the final verb, no medial clauses. -/
def finalOnly : ContextTower ChainCtx := ContextTower.root finalCtx

/-- A 1-medial chain: one medial clause (subject B, time -3) + final. -/
def chain1 : ContextTower ChainCtx :=
  finalOnly.push (chainShift .subjectB (-3))

/-- A 2-medial chain: two medial clauses + final. -/
def chain2 : ContextTower ChainCtx :=
  chain1.push (chainShift .subjectC (-5))

/-- Final-only chain has depth 0. -/
theorem finalOnly_depth : finalOnly.depth = 0 := rfl

/-- 1-medial chain has depth 1. -/
theorem chain1_depth : chain1.depth = 1 := rfl

/-- 2-medial chain has depth 2. -/
theorem chain2_depth : chain2.depth = 2 := rfl

-- ============================================================================
-- § TAM Scope = Origin Access
-- ============================================================================

/-- The final verb's tense is always accessible at the origin,
    regardless of how many medial clauses are pushed.
    This is why the final verb's TAM "scopes over" the chain. -/
theorem final_tense_at_origin_1 :
    chain1.origin.time = 0 := rfl

theorem final_tense_at_origin_2 :
    chain2.origin.time = 0 := rfl

/-- The innermost medial clause has its own event time. -/
theorem medial_has_own_time_1 :
    chain1.innermost.time = -3 := rfl

theorem medial_has_own_time_2 :
    chain2.innermost.time = -5 := rfl

-- ============================================================================
-- § Tense Inheritance via DepthSpec
-- ============================================================================

/-- Origin access pattern: reads tense from the final verb. This models
    languages like Nungon where medial verbs lack tense entirely
    (`tenseFromFinalVerb = true`). The medial verb inherits tense from
    the final verb's context. -/
def originTenseAccess : AccessPattern ChainCtx ℤ :=
  { depth := .origin, project := KContext.time }

/-- Local access pattern: reads tense from the medial verb's own context.
    This models languages like Turkish where medial verbs retain some
    tense distinctions. -/
def localTenseAccess : AccessPattern ChainCtx ℤ :=
  { depth := .local, project := KContext.time }

/-- In a Nungon-style chain (tenseFromFinalVerb = true), medial verb
    reads final verb's tense (0) via origin access. -/
theorem nungon_style_reads_final_tense :
    originTenseAccess.resolve chain1 = 0 := rfl

/-- In a Turkish-style chain, medial verb reads its own event time (-3)
    via local access. -/
theorem turkish_style_reads_local_tense :
    localTenseAccess.resolve chain1 = -3 := rfl

/-- Origin tense access is stable: adding more medial clauses doesn't
    change the final verb's tense. This is the scope property: the
    final verb's TAM values are invariant under chain extension. -/
theorem tense_scope_stable :
    originTenseAccess.resolve chain1 =
    originTenseAccess.resolve chain2 := by
  exact originTenseAccess.origin_stable rfl chain1 (chainShift .subjectC (-5))

-- ============================================================================
-- § Tense Inheritance ↔ Data
-- ============================================================================

/-- Nungon's `tenseFromFinalVerb = true` is consistent with origin access:
    the medial verb's tense dimension is absent, so it reads from origin. -/
theorem nungon_tense_absent_means_origin :
    nungon.tenseFromFinalVerb = true := rfl

/-- Turkish's `tenseFromFinalVerb = false` is consistent with local access:
    the medial verb has restricted tense, so it reads locally. -/
theorem turkish_tense_retained_means_local :
    turkish.tenseFromFinalVerb = false := rfl

/-- Korean's `tenseFromFinalVerb = false` matches local access. -/
theorem korean_tense_retained_means_local :
    korean.tenseFromFinalVerb = false := rfl

/-- Ku Waru's `tenseFromFinalVerb = true` matches origin access (like Nungon). -/
theorem kuWaru_tense_absent_means_origin :
    kuWaru.tenseFromFinalVerb = true := rfl

-- ============================================================================
-- § SR as Agent Comparison Across Tower Levels
-- ============================================================================

/-- Same-subject (SS): adjacent medial clause has the same agent. -/
def sameSubjectChain : ContextTower ChainCtx :=
  finalOnly.push (chainShift .subjectA (-3))

/-- Different-subject (DS): adjacent medial clause has a different agent. -/
def diffSubjectChain : ContextTower ChainCtx :=
  finalOnly.push (chainShift .subjectB (-3))

/-- SS: the medial clause's agent equals the final verb's agent. -/
theorem ss_agent_match :
    sameSubjectChain.innermost.agent = sameSubjectChain.origin.agent := rfl

/-- DS: the medial clause's agent differs from the final verb's agent. -/
theorem ds_agent_mismatch :
    diffSubjectChain.innermost.agent ≠ diffSubjectChain.origin.agent := by decide

/-- SR-bearing languages in the sample all have SR systems. -/
theorem sr_languages_use_tower_agent_tracking :
    [nungon, manambu, kuWaru, korowai].all (·.hasSR) = true := by native_decide

/-- Non-SR languages don't track agent continuity morphologically. -/
theorem nonsr_languages_no_agent_tracking :
    [korean, turkish].all (λ p => !p.hasSR) = true := by native_decide

-- ============================================================================
-- § Chain Label = clauseChain
-- ============================================================================

/-- The chain shift carries the `.clauseChain` label, connecting it to the
    `ShiftLabel` taxonomy in Tower.lean. -/
theorem chain_shift_label :
    (chainShift .subjectB (-3)).label = ShiftLabel.clauseChain := rfl

/-- Chain shifts are distinct from attitude shifts (subordination). This
    reflects the cosubordination ≠ subordination distinction: clause chaining
    uses a different shift label than attitude embedding. -/
theorem chain_is_not_attitude :
    (chainShift .subjectB (-3)).label ≠ ShiftLabel.attitude := by decide

end Phenomena.ClauseChaining.Bridge.TowerBridge
