import Linglib.Theories.Discourse.Centering.Transition
import Linglib.Theories.Discourse.Centering.Rule1

/-!
# Centering Theory — Rule 2 (Transition Preference)
@cite{grosz-joshi-weinstein-1995} §3

Rule 2 of Centering Theory:

* **Rule 2** (transition preference): a *pair* of transitions is
  preferred over another when its constituent transitions have higher
  rank. The paper specifies the canonical case (CONT-CONT > RET-RET >
  SHIFT-SHIFT); the general pair preference uses sum-of-ranks.

Rule 1 (and its variants per @cite{poesio-stevenson-eugenio-hitzeman-2004}
§2.3.2) lives in the sibling file `Rule1.lean`. This file imports it
as a courtesy re-export so the historical `import Rules.lean` keeps
both available; future code should `import Centering.Rule1` and
`import Centering.Rule2` directly.

Rule 2 variants per PSDH §2.3.3 (BFP 87 single-transition; Strube 1998
cheap/expensive) will land in `Rule2.lean` (next commit).
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. Rule 2 (pair preference)
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** is stated at the
    *pair-of-transitions* level: a pair `(t₁, t₂)` is preferred over a
    pair `(s₁, s₂)` when its constituent transitions have higher rank.
    Implemented as sum-of-ranks (the discriminating measure consistent
    with the paper's stated CONT-CONT > RET-RET > SHIFT-SHIFT case;
    `min` is a coarser alternative). -/
def pairRank (t₁ t₂ : Transition) : Nat := t₁.rank + t₂.rank

theorem rule2_continuations_preferred_over_retentions :
    pairRank .continuation .continuation > pairRank .retaining .retaining := by decide

theorem rule2_retentions_preferred_over_shifts :
    pairRank .retaining .retaining > pairRank .shifting .shifting := by decide

theorem rule2_continuations_preferred_over_shifts :
    pairRank .continuation .continuation > pairRank .shifting .shifting := by decide

end Discourse.Centering
