import Linglib.Tactics.CancelFin4

/-! # Fin 4 cancellation: 88 chamber proofs

Each chamber corresponds to a weight vector (w0, w1, w2, w3) with w0 >= w1 >= w2 >= w3
determining which subset-comparison hypotheses hold. `solve_cancellation` derives
all needed ge/nge facts from the weights and applies `cancellation_from_pairs`.
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option maxHeartbeats 400000000 in
theorem chamber_0 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 4 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_1 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 3 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_2 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_3 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 2 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_4 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_5 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 1 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_6 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 3 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_7 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 2 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_8 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 6 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_9 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 5 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_10 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 4 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_11 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 3 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_12 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 7 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_13 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 4 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_14 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 6 4 1

set_option maxHeartbeats 400000000 in
theorem chamber_15 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_16 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 8 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_17 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 5 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_18 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 6 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_19 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 3 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_20 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 7 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_21 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 4 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_22 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 6 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_23 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 3 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_24 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 5 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_25 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_26 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_27 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 3 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_28 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_29 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 2 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_30 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 5 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_31 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 4 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_32 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_33 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 2 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_34 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_35 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 1 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_36 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 3 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_37 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    (hf6r : sys.ge {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 2 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_38 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 5 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_39 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 4 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_40 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_41 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 2 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_42 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 6 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_43 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf4r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 3 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_44 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 7 6 2

set_option maxHeartbeats 400000000 in
theorem chamber_45 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 4 4 1

set_option maxHeartbeats 400000000 in
theorem chamber_46 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 6 5 2

set_option maxHeartbeats 400000000 in
theorem chamber_47 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 3 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_48 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 4 1

set_option maxHeartbeats 400000000 in
theorem chamber_49 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : ¬sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 4 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_50 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 6 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_51 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 3 3

set_option maxHeartbeats 400000000 in
theorem chamber_52 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_53 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_54 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 7 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_55 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_56 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_57 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 2 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_58 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 10 8 6 3

set_option maxHeartbeats 400000000 in
theorem chamber_59 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : ¬sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 9 7 5 3

set_option maxHeartbeats 400000000 in
theorem chamber_60 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 6 5 2

set_option maxHeartbeats 400000000 in
theorem chamber_61 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_62 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 6 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_63 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 5 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_64 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_65 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf3r : sys.ge {(1 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    (hf5r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(1 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 3 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_66 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 8 6 5 4

set_option maxHeartbeats 400000000 in
theorem chamber_67 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 4 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_68 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 3 3

set_option maxHeartbeats 400000000 in
theorem chamber_69 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 2 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_70 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 5 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_71 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_72 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : ¬sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 3 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_73 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 2 1 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_74 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 7 6 5 3

set_option maxHeartbeats 400000000 in
theorem chamber_75 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_76 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_77 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 2 2 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_78 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 5 4 3

set_option maxHeartbeats 400000000 in
theorem chamber_79 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 3 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_80 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 3 2 2

set_option maxHeartbeats 400000000 in
theorem chamber_81 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : ¬sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 1 1 1 1

set_option maxHeartbeats 400000000 in
theorem chamber_82 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 6 5 4 2

set_option maxHeartbeats 400000000 in
theorem chamber_83 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 5 4 3 2

set_option maxHeartbeats 400000000 in
theorem chamber_84 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 4 3 3 1

set_option maxHeartbeats 400000000 in
theorem chamber_85 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : ¬sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : ¬sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf1r : sys.ge {(1 : Fin 4), (2 : Fin 4)} {(0 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 2 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_86 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : ¬sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : ¬sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 3 3 2 1

set_option maxHeartbeats 400000000 in
theorem chamber_87 (sys : EpistemicSystemFA (Fin 4))
    (hpos : ∀ i : Fin 4, ¬sys.ge (∅ : Set (Fin 4)) {i})
    (h01 : sys.ge {(0 : Fin 4)} {1}) (h12 : sys.ge {(1 : Fin 4)} {2})
    (h23 : sys.ge {(2 : Fin 4)} {3})
    (h10 : sys.ge {(1 : Fin 4)} {(0 : Fin 4)})
    (h21 : ¬sys.ge {(2 : Fin 4)} {(1 : Fin 4)})
    (h32 : sys.ge {(3 : Fin 4)} {(2 : Fin 4)})
    (hf1 : sys.ge {(0 : Fin 4), (3 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf2 : sys.ge {(0 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf3 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (3 : Fin 4)})
    (hf4 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4)})
    (hf5 : sys.ge {(1 : Fin 4)} {(2 : Fin 4), (3 : Fin 4)})
    (hf6 : ¬sys.ge {(0 : Fin 4)} {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})
    (hf2r : sys.ge {(2 : Fin 4), (3 : Fin 4)} {(0 : Fin 4)})
    : Cancellation 4 sys.ge := by
  solve_cancellation 2 2 1 1


end Core.Scale
