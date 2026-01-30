import Linglib.Theories.Montague.Questions.Basic
import Linglib.Theories.Montague.Questions.Partition
import Linglib.Theories.Montague.Questions.PragmaticAnswerhood
import Linglib.Theories.Montague.Questions.DecisionTheory
import Linglib.Theories.Montague.Questions.SignalingGames
import Linglib.Theories.Montague.Questions.Polarity
import Linglib.Theories.Montague.Questions.ConjoinableTypes
import Linglib.Theories.Montague.Questions.Coordination
import Linglib.Theories.Montague.Questions.MentionSome
import Linglib.Theories.Montague.Questions.ScopeReadings
import Linglib.Theories.Montague.Questions.GSVanRooyBridge

/-!
# Montague/Questions.lean

Formal Semantics for Questions.

This module re-exports all question semantics components:

1. **Basic**: Core types (Question, Answer, Cell)
2. **Partition**: G&S partition semantics (GSQuestion, refinement ⊑)
3. **PragmaticAnswerhood**: G&S Ch.IV pragmatic answerhood (information sets J)
4. **DecisionTheory**: Van Rooy's decision-theoretic semantics (Blackwell)
5. **SignalingGames**: Credibility and strategic communication (RSA bridge)
6. **Polarity**: Van Rooy & Šafářová on polar question pragmatics (PPQ/NPQ/Alt)
7. **ConjoinableTypes**: G&S Ch.VI conjoinable types and CONJ/DISJ schemata
8. **Coordination**: G&S Ch.VI interrogative coordination (Q₁ ∧ Q₂, Q₁ ∨ Q₂)
9. **MentionSome**: G&S Ch.VI Section 5 mention-some interpretations (I-MS rule)
10. **ScopeReadings**: G&S Ch.VI pair-list and choice readings (Sections 2-5)
11. **GSVanRooyBridge**: Cross-theory theorems (Blackwell, mention-some characterization)

## Theoretical Approaches

### Groenendijk & Stokhof (1984): Partition Semantics
Questions denote equivalence relations on worlds. Two worlds are
equivalent iff they give the same answer. This induces a partition.

### Groenendijk & Stokhof (1984), Ch. IV: Pragmatic Answerhood
Semantic answerhood is a limit case of pragmatic answerhood.
Answerhood is relativized to information sets J (questioner's knowledge):
- P **is** a pragmatic answer: P ∩ J ∈ J/Q
- P **gives** a pragmatic answer: P ∩ J ⊆ P' for some P' ∈ J/Q
Term properties (rigidity, definiteness, exhaustiveness) determine answerhood.

### Van Rooy (2003): Decision-Theoretic Semantics
Questions are asked to resolve decision problems. The utility of an
answer depends on how much it helps the questioner choose optimally.

### Blackwell's Theorem
Semantic refinement (⊑) equals universal pragmatic dominance:
```
Q ⊑ Q'  ⟺  ∀DP: EUV_DP(Q) ≥ EUV_DP(Q')
```

### Van Rooy & Šafářová (2003): Polar Question Pragmatics
PPQs, NPQs, and alternative questions are semantically equivalent but
pragmatically distinct. Question type choice depends on answer utility:
- PPQ (?q): UV(q) > UV(¬q)
- NPQ (?¬q): UV(¬q) > UV(q)
- Alt (?q∨¬q): UV(q) ≈ UV(¬q)

### Signaling Games
Questions and answers as moves in a signaling game. Connects to RSA's
speaker-listener recursion. Explains when communication is credible.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Van Rooy (2003). Quality and Quantity of Information Exchange. JoLLI.
- Van Rooy & Šafářová (2003). On Polar Questions. SALT 13.
- Crawford & Sobel (1982). Strategic Information Transmission.
- Lewis (1969). Convention.
- Blackwell (1953). Equivalent Comparisons of Experiments.
-/
