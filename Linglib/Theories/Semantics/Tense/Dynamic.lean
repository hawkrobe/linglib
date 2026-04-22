import Linglib.Theories.Semantics.Dynamic.Core.ContextFilter

/-!
# Dynamic Tense Operators on Situation Variables

`dynPAST`/`dynPRES`/`dynFUT` impose `<`/`=`/`>` constraints on the
times of two situation variables (event time vs reference time). Each
is definitionally a `dynRelation` instance — see the three
`*_eq_dynRelation` `rfl` lemmas — so the algebraic facts in
`Semantics.Dynamic.Core.ContextFilter` (idempotence, contradictory
pairs, transitivity, trichotomy) discharge their per-tense corollaries
directly.

The trichotomy result `temporal_partition` is the marquee theorem:
`dynPAST ∪ dynPRES ∪ dynFUT = id` on any linearly-ordered `Time`.

Sibling of `Tense/Basic.lean` (static intensional tense) and
`Tense/Compositional.lean` (extensional tense). Used by
`Phenomena/TenseAspect/Studies/Mendes2025.lean`'s analysis of the
Subordinate Future.
-/

namespace Semantics.Tense

open _root_.Core (Assignment WorldTimeIndex)
open Semantics.Dynamic.Core

/--
Dynamic PAST: Constrains event time to precede reference time.

Works with situation drefs: τ(s_event) < τ(s_ref)
-/
def dynPAST {W Time : Type*} [LT Time]
    (eventVar refVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | (gs.1 eventVar).time < (gs.1 refVar).time }

/--
Dynamic PRES: Constrains event time to equal reference time.
-/
def dynPRES {W Time : Type*}
    (eventVar refVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | (gs.1 eventVar).time = (gs.1 refVar).time }

/--
Dynamic FUT: Constrains event time to follow reference time.
-/
def dynFUT {W Time : Type*} [LT Time]
    (eventVar refVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | (gs.1 eventVar).time > (gs.1 refVar).time }


-- ════════════════════════════════════════════════════════════════
-- Temporal operators as dynRelation instances
-- ════════════════════════════════════════════════════════════════

theorem dynPAST_eq_dynRelation {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time) :
    dynPAST e r c =
    dynRelation (fun s₁ s₂ : WorldTimeIndex W Time => s₁.time < s₂.time) e r c := rfl

theorem dynPRES_eq_dynRelation {W Time : Type*}
    (e r : SVar) (c : SitContext W Time) :
    dynPRES e r c =
    dynRelation (fun s₁ s₂ : WorldTimeIndex W Time => s₁.time = s₂.time) e r c := rfl

theorem dynFUT_eq_dynRelation {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time) :
    dynFUT e r c =
    dynRelation (fun s₁ s₂ : WorldTimeIndex W Time => s₁.time > s₂.time) e r c := rfl


-- ════════════════════════════════════════════════════════════════
-- Temporal algebra (derived from dynRelation + order theory)
-- ════════════════════════════════════════════════════════════════

/-- PAST ∪ PRES ∪ FUT = identity. Derived from trichotomy on Time. -/
theorem temporal_partition {W Time : Type*} [LinearOrder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ c ∪ dynPRES v₁ v₂ c ∪ dynFUT v₁ v₂ c = c := by
  rw [dynPAST_eq_dynRelation, dynPRES_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_trichotomy (fun s => s.time) v₁ v₂ c

/-- PAST and FUT are contradictory on the same variables. -/
theorem dynPAST_dynFUT_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  rw [dynPAST_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time < s₂.time) (h2 : s₂.time < s₁.time) =>
      lt_asymm h1 h2) v₁ v₂ c

/-- PAST and PRES are contradictory on the same variables. -/
theorem dynPAST_dynPRES_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ (dynPRES v₁ v₂ c) = ∅ := by
  rw [dynPAST_eq_dynRelation, dynPRES_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time < s₂.time) (h2 : s₁.time = s₂.time) =>
      absurd h1 (by rw [h2]; exact lt_irrefl _)) v₁ v₂ c

/-- PRES and FUT are contradictory on the same variables. -/
theorem dynPRES_dynFUT_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPRES v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  rw [dynPRES_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time = s₂.time) (h2 : s₂.time < s₁.time) =>
      absurd h2 (by rw [h1]; exact lt_irrefl _)) v₁ v₂ c

/-- Chained PAST constraints compose: e < r ∧ r < s → e < s. -/
theorem dynPAST_transitive {W Time : Type*} [Preorder Time]
    (e r s : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynPAST r s (dynPAST e r c)) :
    (gs.1 e).time < (gs.1 s).time := by
  rw [dynPAST_eq_dynRelation, dynPAST_eq_dynRelation] at h
  exact dynRelation_transitive _ _ _
    (fun s₁ s₂ s₃ (h1 : s₁.time < s₂.time) (h2 : s₂.time < s₃.time) =>
      lt_trans h1 h2) e r s c gs h

end Semantics.Tense
