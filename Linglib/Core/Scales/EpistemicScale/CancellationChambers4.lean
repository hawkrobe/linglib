import Linglib.Tactics.CancelFin4

/-! # Chamber proofs group 4: chambers 66-87 -/

namespace Core.Scale

attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

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