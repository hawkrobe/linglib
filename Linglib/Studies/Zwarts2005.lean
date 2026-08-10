import Linglib.Semantics.Spatial.Trace

/-!
# [zwarts-2005] *Prepositional Aspect and the Algebra of Paths*

Directional-PP denotations are sets of paths; what distinguishes telic PPs
(*to the house*) from atelic PPs (*towards the house*) is closure under the
**partial** concatenation operation: atelic PPs are cumulative, telic PPs are
not (21). The paper's Appendix A path algebra — `Spatial.Path` with
`Path.IsConcat` (67) and the subpath order (68) — lives in
`Semantics/Spatial/Path.lean`; this file formalizes the aspectual system
built on it.

## Main definitions

* `Cumulative` (17b, with the existence clause of fn. 7), `Bounded` (21) —
  stated over any ternary concatenation relation, since Appendix A pairs the
  path algebra with an event algebra of the same shape.
* `weakTo` (30c), `toPP`/`fromPP` (endpoint content of the strict (36)),
  `towardsPP` (45), `awayFromPP` (48), `loops`, `Star` (58).
* `IsTraceHom`, `vpp` (25) — §3.2 aspect transfer from PP to VP.

## Main statements

* `weakTo_cumulative` vs `toPP_bounded` — the §4.1.1 argument: the weak
  goal-PP denotation is cumulative (wrong aspect), the strict one bounded.
* `fromPP_bounded` — source PPs are bounded like goal PPs: no aspectual
  source/goal asymmetry (12a), grounding the telic marking of
  source-directionality PPs (`Spatial.Path.Directionality`).
* `towardsPP_concat_closed`, `awayFromPP_concat_closed`,
  `towardsPP_cumulative` — the comparative definitions (45)/(48) are
  cumulative, grounding `.unbounded ↦ .atelic`.
* `toPP_not_quantized` — bounded PPs are **not** quantized (23)–(24):
  a *to x* path has proper *to x* subpaths, so `Mereology.QUA` fails.
* `quantized_telicK`, `loops_telicK`, `loops_cumulative` — quantization
  implies Krifka-telicity (22b), but the round-and-round loop set is
  (22b)-telic yet cumulative, so neither Krifka notion characterizes
  boundedness (§3.1).
* `star_cumulative` — the plural closure (58) is cumulative.
* `vpp_concat_closed`, `vpp_bounded_of_no_pairs`, `toPP_no_pairs` — §3.2:
  a trace homomorphism transfers PP closure to VP closure, and *walk to the
  house* is bounded because no two *to the house* traces concatenate.

## TODO

* The full single-phase strict definitions (35)–(36), (39)–(40) and the
  minimality/grinder operators (63)–(64).
* Reconciling `Spatial.Trace`'s `IsSumHom` law with this study's trace
  homomorphism: Zwarts (§3.2) follows Rothstein in using partial event
  concatenation, not the unrestricted mereological sum.
-/

namespace Zwarts2005

open Mereology (QUA)
open Spatial
open scoped Spatial.Path

variable {Loc α : Type*}

/-! ### Cumulativity and boundedness (17b), (21)

Stated over an arbitrary ternary concatenation relation: Appendix A pairs the
path algebra with an event algebra of the same shape, and §3.2 transfers
closure properties along a homomorphism between the two. -/

/-- (17b): a set is cumulative iff some concatenation exists within it
    (fn. 7's non-vacuity clause) and it is closed under concatenation. -/
def Cumulative (C : α → α → α → Prop) (X : Set α) : Prop :=
  (∃ p ∈ X, ∃ q ∈ X, ∃ r, C p q r) ∧
    ∀ p ∈ X, ∀ q ∈ X, ∀ r, C p q r → r ∈ X

/-- (21): bounded = non-cumulative. This, not quantization, is what
    characterizes telic PPs. -/
def Bounded (C : α → α → α → Prop) (X : Set α) : Prop :=
  ¬ Cumulative C X

/-- A set with no concatenable pairs at all is bounded. -/
theorem bounded_of_no_pairs {C : α → α → α → Prop} {X : Set α}
    (h : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, C p q r) : Bounded C X :=
  fun hc => h hc.1

/-! ### Quantization and Krifka-telicity are the wrong notions (§3.1)

(22) transplants [krifka-1998]'s quantization and telicity to path sets;
Zwarts shows neither characterizes boundedness. Quantization is
`Mereology.QUA` over the subpath order. -/

/-- (22b): Krifka-style telicity for path sets — comparable members share
    both endpoints. -/
def TelicK (X : Set (Path Loc)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, p ≤ q → p.source = q.source ∧ p.goal = q.goal

/-- Quantized sets are Krifka-telic (§3.1: "Being quantized implies being
    telic"). -/
theorem quantized_telicK {X : Set (Path Loc)} (h : QUA (· ∈ X)) :
    TelicK X := by
  intro p hp q hq hle
  rcases eq_or_ne p q with rfl | hne
  · exact ⟨rfl, rfl⟩
  · exact absurd hle (h hp hq hne)

/-- The *round and round the block* set: non-constant loops at a fixed
    location. -/
def loops (A : Loc) : Set (Path Loc) :=
  {p | p.source = A ∧ p.goal = A ∧ p.steps ≠ []}

/-- Loop sets are Krifka-telic: all members share both endpoints. -/
theorem loops_telicK (A : Loc) : TelicK (loops (Loc := Loc) A) :=
  fun _ hp _ hq _ => ⟨hp.1.trans hq.1.symm, hp.2.1.trans hq.2.1.symm⟩

/-- Loop sets are cumulative — so Krifka-telicity (22b) does not
    characterize boundedness (§3.1: *round and round the block* is telic in
    Krifka's sense but behaves unboundedly). -/
theorem loops_cumulative (A : Loc) :
    Cumulative Path.IsConcat (loops (Loc := Loc) A) := by
  constructor
  · have h : (⟨A, [A]⟩ : Path Loc) ∈ loops A := ⟨rfl, rfl, by simp⟩
    exact ⟨_, h, _, h, _, ⟨rfl, rfl⟩⟩
  · rintro p hp q hq r hr
    exact ⟨hr.source_eq.trans hp.1, hr.goal_eq.trans hq.2.1,
      by rw [hr.2]; simp [hq.2.2]⟩

/-! ### Goal and source prepositions (§4.1.1) -/

/-- (30c): the weak goal-PP denotation — paths ending at the reference
    object. -/
def weakTo (x : Loc) : Set (Path Loc) := {p | p.goal = x}

/-- The weak definition (30c) is cumulative — the wrong aspect for telic
    *to*/*into*, which is Zwarts's argument for the strict single-phase
    definitions (34)–(35). -/
theorem weakTo_cumulative (x : Loc) : Cumulative Path.IsConcat (weakTo x) :=
  ⟨⟨_, Path.goal_const x, _, Path.goal_const x, _, Path.isConcat_const x⟩,
    fun _ _ _ hq _ hr => hr.goal_eq.trans hq⟩

/-- The endpoint content of the strict goal PP (36): the path ends at the
    reference object and does not start there. -/
def toPP (x : Loc) : Set (Path Loc) := {p | p.goal = x ∧ p.source ≠ x}

/-- The endpoint content of the strict source PP (36): the path starts at
    the reference object and does not end there. -/
def fromPP (x : Loc) : Set (Path Loc) := {p | p.source = x ∧ p.goal ≠ x}

/-- No two *to x* paths concatenate: the first ends at `x`, the second never
    starts there (§3.1). -/
theorem toPP_no_pairs (x : Loc) :
    ¬ ∃ p ∈ toPP x, ∃ q ∈ toPP x, ∃ r, Path.IsConcat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hq.2 (hr.1 ▸ hp.1)

/-- Strict goal PPs are bounded (21): *to the house* is telic. -/
theorem toPP_bounded (x : Loc) : Bounded Path.IsConcat (toPP x) :=
  bounded_of_no_pairs (toPP_no_pairs x)

/-- Strict source PPs are bounded, exactly like goal PPs — there is no
    aspectual source/goal asymmetry (12a). Grounds the telic marking of
    source-directionality PPs (`Spatial.Path.Directionality`). -/
theorem fromPP_bounded (x : Loc) : Bounded Path.IsConcat (fromPP x) := by
  rintro ⟨⟨p, hp, q, hq, r, hr⟩, -⟩
  exact hp.2 (hr.1.trans hq.1)

/-! ### Towards and away from (§4.1.3)

The comparative definitions over a distance measure `d` to the reference
object: cumulative, hence unbounded — grounding the atelic marking of the
comparative prepositions in the fragments' directionality × telicity data. -/

/-- (45): *towards x* — the path ends nearer to the reference object than it
    starts, measured by `d`. -/
def towardsPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.goal < d p.source}

/-- (48): *away from x* — the path ends further from the reference object
    than it starts. -/
def awayFromPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.source < d p.goal}

/-- (45) is closed under concatenation: distance decreases across each
    concatenant. -/
theorem towardsPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ towardsPP d, ∀ q ∈ towardsPP d, ∀ r, Path.IsConcat p q r →
      r ∈ towardsPP d := by
  intro p hp q hq r hr
  show d r.goal < d r.source
  rw [hr.goal_eq, hr.source_eq]
  exact hq.trans_le (hr.1 ▸ hp.le)

/-- (48) is closed under concatenation, mirroring (45). -/
theorem awayFromPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ awayFromPP d, ∀ q ∈ awayFromPP d, ∀ r, Path.IsConcat p q r →
      r ∈ awayFromPP d := by
  intro p hp q hq r hr
  show d r.source < d r.goal
  rw [hr.goal_eq, hr.source_eq]
  exact hp.trans_le (hr.1 ▸ hq.le)

/-- On the rational line with the reference object at the origin, *towards*
    is fully cumulative (45): closure plus a concrete concatenable pair. -/
theorem towardsPP_cumulative :
    Cumulative Path.IsConcat (towardsPP (abs : ℚ → ℚ)) := by
  refine ⟨⟨⟨2, [1]⟩, ?_, ⟨1, [0]⟩, ?_, _, ⟨rfl, rfl⟩⟩,
    towardsPP_concat_closed abs⟩
  · show |(1 : ℚ)| < |(2 : ℚ)|
    norm_num
  · show |(0 : ℚ)| < |(1 : ℚ)|
    norm_num

/-- Bounded PPs are **not** quantized (23)–(24): a *to x* path has proper
    subpaths that are also *to x*, so `Mereology.QUA` fails — against the
    [krifka-1998] characterization of telicity, and against this library's
    earlier docstring folklore. -/
theorem toPP_not_quantized : ¬ QUA (· ∈ toPP (0 : ℚ)) := by
  intro h
  have hp : (⟨1, [0]⟩ : Path ℚ) ∈ toPP 0 := ⟨rfl, by norm_num⟩
  have hq : (⟨2, [1, 0]⟩ : Path ℚ) ∈ toPP 0 := ⟨rfl, by norm_num⟩
  have hle : (⟨1, [0]⟩ : Path ℚ) ≤ ⟨2, [1, 0]⟩ :=
    Path.subpath_iff_infix.mpr ⟨[2], [], rfl⟩
  exact h hp hq (by simp) hle

/-! ### Plural PPs: the star operator (§4.2.2) -/

/-- (58): closure of a path set under concatenations — prepositional
    plurality (*round and round the house*). -/
inductive Star (X : Set (Path Loc)) : Path Loc → Prop
  | base {p} (hp : p ∈ X) : Star X p
  | concat {p q r} (hp : Star X p) (hq : Star X q) (h : Path.IsConcat p q r) :
      Star X r

/-- (58): the star closure is cumulative, given any concatenable pair to
    seed it. -/
theorem star_cumulative {X : Set (Path Loc)}
    (h : ∃ p ∈ X, ∃ q ∈ X, ∃ r, Path.IsConcat p q r) :
    Cumulative Path.IsConcat {p | Star X p} := by
  obtain ⟨p, hp, q, hq, r, hr⟩ := h
  exact ⟨⟨p, .base hp, q, .base hq, r, hr⟩,
    fun _ hp' _ hq' _ hr' => .concat hp' hq' hr'⟩

/-! ### Aspect transfer to the VP (§3.2) -/

section Transfer

variable {E : Type*} (C : E → E → E → Prop) (tr : E → Path Loc)

/-- §3.2: the trace function is a homomorphism for concatenation — the trace
    of a fused event is the concatenation of the traces. Zwarts follows
    Rothstein's partial event concatenation, not the unrestricted
    mereological sum. -/
def IsTraceHom : Prop :=
  ∀ e e' f, C e e' f → Path.IsConcat (tr e) (tr e') (tr f)

/-- (25): `⟦V PP⟧` — the verb's events whose trace lies in the PP
    denotation. -/
def vpp (V : Set E) (X : Set (Path Loc)) : Set E :=
  {e ∈ V | tr e ∈ X}

/-- §3.2 transfer, positive half: closure of the verb and of the PP
    denotation transfers to the VP (*walk along the river* is cumulative
    because *walk* and *along the river* are). -/
theorem vpp_concat_closed (hhom : IsTraceHom C tr) {V : Set E}
    {X : Set (Path Loc)}
    (hV : ∀ e ∈ V, ∀ e' ∈ V, ∀ f, C e e' f → f ∈ V)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ r, Path.IsConcat p q r → r ∈ X) :
    ∀ e ∈ vpp tr V X, ∀ e' ∈ vpp tr V X, ∀ f, C e e' f → f ∈ vpp tr V X :=
  fun e he e' he' f hf =>
    ⟨hV e he.1 e' he'.1 f hf, hX _ he.2 _ he'.2 _ (hhom e e' f hf)⟩

/-- §3.2 transfer, negative half: if no two PP paths concatenate, no two VP
    events fuse — *walk to the house* is bounded because *to the house* has
    no concatenable pairs. -/
theorem vpp_bounded_of_no_pairs (hhom : IsTraceHom C tr) {V : Set E}
    {X : Set (Path Loc)}
    (hX : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, Path.IsConcat p q r) :
    Bounded C (vpp tr V X) :=
  bounded_of_no_pairs fun ⟨e, he, e', he', f, hf⟩ =>
    hX ⟨tr e, he.2, tr e', he'.2, tr f, hhom e e' f hf⟩

/-- *Walk to the house* is bounded (26), (§3.2): instantiates the negative
    transfer at the strict goal PP. -/
theorem vpp_toPP_bounded (hhom : IsTraceHom C tr) {V : Set E} (x : Loc) :
    Bounded C (vpp tr V (toPP x)) :=
  vpp_bounded_of_no_pairs C tr hhom (toPP_no_pairs x)

end Transfer

end Zwarts2005
