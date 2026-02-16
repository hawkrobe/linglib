import Linglib.Theories.Syntax.DependencyGrammar.Formal.MemorySurprisal.Basic
import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength

/-!
# Study 1: Artificial Language Learning (Fedzechkina et al. 2013/2017)

Hahn et al. (2021) Study 1 reanalyzes Fedzechkina, Jaeger & Newport (2012,
2017): learners of an artificial language with flexible word order converge
toward orders that minimize dependency length — and these orders also
achieve more efficient memory-surprisal trade-offs.

## Setup

Two mini-languages with identical lexicons but different word orders:
- **Language A**: complex NP placed sentence-initially (short dependencies)
- **Language B**: complex NP placed sentence-finally (long dependencies)

Mixed-complexity sentences (one simple NP + one complex NP) create the
critical contrast. Language A's order minimizes dependency length because
the verb is closer to both arguments.

## Key Result

Learners exposed to a 50/50 mixture of both orders converge toward
Language A's order (~67% use by end of training), showing a learning
bias for dependency-length-minimizing (= memory-efficient) orders.

## References

- Fedzechkina, M., Jaeger, T. F. & Newport, E. L. (2012). Language
  learners restructure their input to facilitate efficient communication.
  *PNAS* 109:17897–17902.
- Fedzechkina, M., Jaeger, T. F. & Newport, E. L. (2017). Balancing
  effort and information transmission during language acquisition.
  *Cognitive Science* 41:416–446.
- Hahn, M., Degen, J. & Futrell, R. (2021). Study 1 (§4).
-/

namespace DepGrammar.MemorySurprisal.FedzechkinaEtAl2017

open DepGrammar DependencyLength MemorySurprisal

-- ============================================================================
-- Mini-Language Setup
-- ============================================================================

/-- The two mini-languages in the experiment. -/
inductive MiniLanguage where
  | langA  -- Short-dependency order (complex NP first)
  | langB  -- Long-dependency order (complex NP last)
  deriving DecidableEq, Repr, BEq

/-- Word order for a transitive sentence. -/
inductive WordOrder where
  | SOV  -- Subject-Object-Verb
  | OSV  -- Object-Subject-Verb
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Dependency Trees: Language A vs Language B
-- ============================================================================

/-! ### Concrete examples

"The big cat chased the dog" with complex NP = "the big cat" (3 words)
and simple NP = "the dog" (2 words).

Language A (SOV, complex first): the big cat | the dog | chased
Language B (SOV, complex last): the dog | the big cat | chased -/

/-- Language A SOV: "the-big-cat the-dog chased"
Words: the(0) big(1) cat(2) the(3) dog(4) chased(5)
Dependencies:
- det: cat(2) ← the(0)       length 2
- amod: cat(2) ← big(1)      length 1
- nsubj: chased(5) ← cat(2)  length 3
- det: dog(4) ← the(3)       length 1
- obj: chased(5) ← dog(4)    length 1
Total = 8 -/
def langA_SOV : DepTree :=
  { words := [ Word.mk' "the" .DET, Word.mk' "big" .ADJ, Word.mk' "cat" .NOUN
             , Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "chased" .VERB ]
    deps := [ ⟨2, 0, .det⟩, ⟨2, 1, .amod⟩, ⟨5, 2, .nsubj⟩
            , ⟨4, 3, .det⟩, ⟨5, 4, .obj⟩ ]
    rootIdx := 5 }

/-- Language B SOV: "the-dog the-big-cat chased"
Words: the(0) dog(1) the(2) big(3) cat(4) chased(5)
Dependencies:
- det: dog(1) ← the(0)        length 1
- nsubj: chased(5) ← dog(1)   length 4  (long!)
- det: cat(4) ← the(2)        length 2
- amod: cat(4) ← big(3)       length 1
- obj: chased(5) ← cat(4)     length 1
Total = 9 -/
def langB_SOV : DepTree :=
  { words := [ Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "the" .DET
             , Word.mk' "big" .ADJ, Word.mk' "cat" .NOUN, Word.mk' "chased" .VERB ]
    deps := [ ⟨1, 0, .det⟩, ⟨5, 1, .nsubj⟩, ⟨4, 2, .det⟩
            , ⟨4, 3, .amod⟩, ⟨5, 4, .obj⟩ ]
    rootIdx := 5 }

-- ============================================================================
-- Dependency Length Comparison
-- ============================================================================

/-- Language A has total dep length 8. -/
example : totalDepLength langA_SOV = 8 := by native_decide

/-- Language B has total dep length 9. -/
example : totalDepLength langB_SOV = 9 := by native_decide

/-- Language A has shorter total dependency length than Language B. -/
theorem langA_shorter_deps :
    totalDepLength langA_SOV < totalDepLength langB_SOV := by native_decide

-- ============================================================================
-- Trade-off Curves (approximate from Figure 7)
-- ============================================================================

/-- Language A trade-off curve (5 points, from Figure 7).
Lower AUC = more efficient. -/
def langACurve : TradeoffCurve :=
  { name := "Language A"
    points := [ ⟨0, 4200⟩, ⟨500, 3800⟩, ⟨1000, 3200⟩, ⟨2000, 2800⟩, ⟨3000, 2600⟩ ] }

/-- Language B trade-off curve (5 points, from Figure 7).
Higher AUC = less efficient. -/
def langBCurve : TradeoffCurve :=
  { name := "Language B"
    points := [ ⟨0, 4500⟩, ⟨500, 4100⟩, ⟨1000, 3600⟩, ⟨2000, 3200⟩, ⟨3000, 3000⟩ ] }

/-- Language A has lower AUC (more efficient trade-off). -/
theorem langA_more_efficient :
    langACurve.auc < langBCurve.auc := by native_decide

/-- Language A satisfies the efficient trade-off hypothesis vs B. -/
theorem langA_efficient_vs_B :
    efficientTradeoffHypothesis langACurve langBCurve = true := by native_decide

-- ============================================================================
-- Learner Convergence
-- ============================================================================

/-- Learner convergence rate: proportion choosing Language A's order × 1000.

By end of training, ~67% of productions used the short-dependency order
(Fedzechkina et al. 2012, Figure 2). This exceeds chance (50%). -/
def learnerConvergenceRate : Nat := 670

/-- Learners converge above chance toward the efficient order. -/
theorem learners_prefer_efficient :
    learnerConvergenceRate > 500 := by native_decide

-- ============================================================================
-- Bridge: Short Dependencies → Efficient Trade-off
-- ============================================================================

/-- Bridge theorem: the language with shorter dependencies also has the
more efficient memory-surprisal trade-off.

This connects DLM (structural) to information-theoretic efficiency:
shorter dependencies concentrate predictive information locally,
yielding steeper I_t decay and better trade-off curves. -/
theorem short_deps_implies_efficient :
    totalDepLength langA_SOV < totalDepLength langB_SOV ∧
    langACurve.auc < langBCurve.auc :=
  ⟨by native_decide, by native_decide⟩

end DepGrammar.MemorySurprisal.FedzechkinaEtAl2017
