import Mathlib.Data.Finset.Card
import Linglib.Semantics.Plurality.Cumulativity
import Linglib.Semantics.Plurality.Reciprocal
import Linglib.Studies.Beck2001

/-!
# Sternefeld (1998): Reciprocity and Cumulative Predication
[sternefeld-1998]

*Natural Language Semantics* 6(3): 303–337. doi:10.1023/A:1008352502939.

[sternefeld-1998] extends [langendoen-1978]'s
reciprocity-as-cumulativity insight into a fully compositional theory.
Distinct readings of plural and reciprocal sentences arise from
different placements of the pluralization operators (`*` and `**`) at
Logical Form. The reciprocal NP itself denotes "the others", with the
non-identity statement injected into the LF as semantic glue.

## Headline analysis (paper §3, eq 26b)

Sternefeld's WR analysis: `⟨A, A⟩ ∈ **λxy[R(x, y) ∧ x ≠ y]`. The
distinctness condition `x ≠ y` is **inside** the `**`'s relation
argument — NOT a separate asserted clause as some readings of the
literature suggest.

In bivalent semantics this is structurally identical to
[beck-2001]'s eq 120 (`**(λxλy.[R(x,y) ∧ @(x ≠ y)])(A,A)`). The
two analyses agree on the bivalent predicate — `Plurality.Reciprocal.WeakReciprocity`
— and diverge only on:

1. **Status of distinctness**: Sternefeld asserts; Beck presupposes
   (`@`). Visible only in trivalent semantics (truth-value gap when R
   holds with x = y).
2. **Status of SR**: [sternefeld-1998] §3.5 argues SR is
   *expressible* in his framework but defends in §3.6 (the
   Geach-Kaplan sentence) that SR is "probably a special case of WR"
   plus *only*-focus on the non-identity statement. [beck-2001]
   takes SR as a basic reading.
3. **`**` operator shape**: [sternefeld-1998] eq 5 uses
   [krifka-1989]'s closure form (smallest relation closed under
   `⟨a,b⟩+⟨c,d⟩ → ⟨a∪c, b∪d⟩`); [beck-sauerland-2000] use
   bidirectional coverage (`(∀a∈x. ∃b∈y. R(a,b)) ∧ (∀b∈y. ∃a∈x. R(a,b))`).
   Equivalent on Quine-innovation domains where individuals are
   identified with singletons.

## What is formalized

| Paper §  | Topic                                                    | Lean encoding              |
|----------|----------------------------------------------------------|----------------------------|
| §2 eq 5  | `**` operator ([krifka-1989] closure form)          | `sternefeldStarStar` (inductive) |
| §2.4 eq 12 | WD analysis (Scha 1981 cumulative)                     | (deferred)                 |
| §3 eq 26b | WR analysis (distinctness inside relation)              | `sternefeldWR`             |
| §3 eq 25b | Langendoen-style WR (existence-witnessed)               | `langendoenWR`             |
| §3.5 eq 48b | SR expressed as iterated `*` distribution             | `sternefeldSR_iff_stronglyReciprocal` |

The `**` closure-form ↔ bidirectional-coverage equivalence is proved
in the easy direction (`sternefeldStarStar_implies_cumulative`).
The reverse direction is a substantial inductive argument that would
properly belong in `Semantics/Plurality/Cumulativity.lean` as
substrate justification for treating the two `**` formulations as
interchangeable; not in this study file.

## Out of scope

- §2.5 Plural Predication at LF (Augmented Logical Forms with
  freely-inserted `*` operators) — purely representational; would
  require Tree.lean syntactic-tree machinery.
- §3.1 Three-place relations (`***` operator, paper eq 29) — small
  extension of `**`; substrate-deferred.
- §3.2–3.3 dependent plurals + Heim's inner/outer indices — would
  require inner/outer-index distinction substrate.
- §3.4 LF-movement crossover constraint — syntax, not semantics.
- §3.6 Geach-Kaplan sentence with [rooth-1985] focus — would
  require Focus substrate; the SR-derivation step is recorded in
  prose but not as a Lean theorem.
- §4.1–4.2 [schwarzschild-1996] covers as pragmatic supplement —
  substrate exists in `Plurality.Cover`; the closure-of-`**` ↔
  Schwarzschild-PPart(PCov) reduction is a separate effort.

## Connection to [beck-2001] and [haug-dalrymple-2020]

[beck-2001] cites Sternefeld 1998 as the immediate predecessor
and at one point characterises Sternefeld's analysis as bare-`**(R)(A,A)`
(i.e., without distinctness in the relation). Reading Sternefeld 1998
directly: bare `**(R)(A,A)` does NOT appear in his analysis; his
actual eq 26b *has* distinctness inside the relation. The
Beck-vs-Sternefeld difference is therefore presupposition-vs-assertion
of the distinctness clause, not structural placement.

[haug-dalrymple-2020] consumes the same `**` machinery via the
PPCDRT bridge `groupIdentityCond_iff_cumulative_eq`. The three-paper
convergence on `**`-cumulation as the heart of reciprocity is the
linglib interconnection-density payoff: Sternefeld's WR ↔ Beck's
eq 120 ↔ H&D's group identity all factor through
`Plurality.Cumulativity.Cumulative`.
-/

namespace Sternefeld1998

open Semantics.Plurality.Cumulativity
open Semantics.Plurality.Reciprocal

variable {α : Type*} [DecidableEq α]

-- ════════════════════════════════════════════════════════════════
-- § 1: Sternefeld's `**` Operator (paper eq 5, [krifka-1989])
-- ════════════════════════════════════════════════════════════════

/-- **Sternefeld eq 5 / [krifka-1989]**: the smallest relation
    `Q` over `Finset α × Finset α` such that `R ⊆ Q` (lifted to
    singletons) and `Q` is closed under `⟨a,b⟩ + ⟨c,d⟩ → ⟨a∪c, b∪d⟩`.

    On Quine-innovation domains, this is equivalent to
    [beck-sauerland-2000]'s bidirectional-coverage `Cumulative`
    — see `sternefeldStarStar_implies_cumulative` for the easy
    direction. The reverse direction holds on nonempty pluralities
    but the inductive proof is non-trivial; substrate-deferred. -/
inductive sternefeldStarStar (R : α → α → Prop) : Finset α → Finset α → Prop
  | base {a b : α} (h : R a b) : sternefeldStarStar R {a} {b}
  | union {a b c d : Finset α}
      (hab : sternefeldStarStar R a b) (hcd : sternefeldStarStar R c d) :
      sternefeldStarStar R (a ∪ c) (b ∪ d)

/-- **Sternefeld closure form `**` entails [beck-sauerland-2000]
    bidirectional coverage** (the easy direction of the equivalence
    `sternefeldStarStar R x y ↔ Cumulative R x y`).

    Proof: induction on the closure derivation. Base case
    `⟨{a},{b}⟩` from `R a b`: both quantifiers reduce to the witness
    pair. Union case: bidirectional coverage of `⟨a∪c, b∪d⟩` follows
    from coverage of `⟨a,b⟩` and `⟨c,d⟩` by case-splitting on the
    union membership. -/
theorem sternefeldStarStar_implies_cumulative
    (R : α → α → Prop) (x y : Finset α)
    (h : sternefeldStarStar R x y) :
    Cumulative R x y := by
  induction h with
  | base hab =>
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨_, Finset.mem_singleton_self _, hab⟩
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact ⟨_, Finset.mem_singleton_self _, hab⟩
  | @union a b c d _ _ ihab ihcd =>
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [Finset.mem_union] at hp
      cases hp with
      | inl hpa =>
        obtain ⟨q, hqb, hRpq⟩ := ihab.1 p hpa
        exact ⟨q, Finset.mem_union_left d hqb, hRpq⟩
      | inr hpc =>
        obtain ⟨q, hqd, hRpq⟩ := ihcd.1 p hpc
        exact ⟨q, Finset.mem_union_right b hqd, hRpq⟩
    · intro q hq
      rw [Finset.mem_union] at hq
      cases hq with
      | inl hqb =>
        obtain ⟨p, hpa, hRpq⟩ := ihab.2 q hqb
        exact ⟨p, Finset.mem_union_left c hpa, hRpq⟩
      | inr hqd =>
        obtain ⟨p, hpc, hRpq⟩ := ihcd.2 q hqd
        exact ⟨p, Finset.mem_union_right a hpc, hRpq⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Sternefeld's WR Analysis (paper §3, eq 26b)
-- ════════════════════════════════════════════════════════════════

/-- **Sternefeld 1998 eq 26b**: WR truth conditions are
    `⟨A, A⟩ ∈ **λxy[R(x, y) ∧ x ≠ y]`. The distinctness clause is
    INSIDE the `**`'s relation argument, NOT a separate asserted
    clause.

    Encoding choice: we use [beck-sauerland-2000]'s bidirectional
    coverage `Cumulative` for `**` (see
    `sternefeldStarStar_implies_cumulative` for the connection to
    Sternefeld's closure-form `**`).

    In bivalent semantics this is structurally identical to
    `Plurality.Reciprocal.WeakReciprocity` (and to Beck eq 120). The
    two analyses diverge only on the trivalent assertion-vs-
    presupposition status of `x ≠ y` (Sternefeld asserts;
    [beck-2001] eq 120 presupposes via `@`). -/
def sternefeldWR (A : Finset α) (R : α → α → Prop) : Prop :=
  Cumulative (fun x y => R x y ∧ x ≠ y) A A

instance sternefeldWR.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (sternefeldWR A R) := by
  unfold sternefeldWR; infer_instance

/-- **Sternefeld 1998 ↔ Beck 2001 (bivalent collapse)**: in bivalent
    encoding, the two reciprocity analyses produce identical
    predicates. The cumulation-with-distinctness shape is the
    *common ground* of both papers; they only diverge at the
    trivalent (presupposition projection) layer. Substrate form
    `Plurality.Reciprocal.WeakReciprocity`. -/
theorem sternefeldWR_iff_WeakReciprocity
    (A : Finset α) (R : α → α → Prop) :
    sternefeldWR A R ↔ WeakReciprocity R A :=
  (weakReciprocity_iff_cumulative_strict R A).symm

-- ════════════════════════════════════════════════════════════════
-- § 3: Langendoen-style WR (paper §1, eq 25b — equivalent on
-- nonempty A but historically attributed to [langendoen-1978])
-- ════════════════════════════════════════════════════════════════

/-- **[langendoen-1978] WR** (paper eq 25b): for each `x ∈ A`,
    there are `y, z ∈ A` with `x ≠ y`, `x ≠ z`, `xRy`, `zRx`. This is
    the existence-witnessed form Sternefeld attributes to Langendoen.

    Sternefeld notes (paper p. 316) that this form does not entail his
    eq 26b for non-D-based relations; in particular, in the
    "problematic situation" `f(R) = {⟨⟨a,b⟩, c⟩, ⟨c, a⟩, ⟨c, b⟩}`,
    eq 25b cannot apply but eq 26b is still true. For D-based
    relations on Quine-innovation domains, the two coincide and both
    reduce to `Plurality.Reciprocal.WeakReciprocity`. -/
def langendoenWR (A : Finset α) (R : α → α → Prop) : Prop :=
  ∀ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ x ≠ z ∧ R x y ∧ R z x

instance langendoenWR.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (langendoenWR A R) := by
  unfold langendoenWR; infer_instance

/-- For symmetric, distinctness-bearing R, [langendoen-1978] WR
    entails `Plurality.Reciprocal.WeakReciprocity`: the existence-
    witnesses on each side are the y and z of the Langendoen formula. -/
theorem langendoenWR_implies_WeakReciprocity
    (A : Finset α) (R : α → α → Prop)
    (h : langendoenWR A R) :
    WeakReciprocity R A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, _, _, hxy, _, hRxy, _⟩ := h x hx
    exact ⟨y, hy, hRxy, hxy⟩
  · intro x hx
    obtain ⟨_, _, z, hz, _, hxz, _, hRzx⟩ := h x hx
    exact ⟨z, hz, hRzx, hxz.symm⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Strong Reciprocity Expressibility (paper §3.5, eq 48b)
-- ════════════════════════════════════════════════════════════════

/-- **Sternefeld §3.5 eq 48b** (SR via iterated distribution):
    `A ∈ *λx[{y: y ∈ A ∧ y ≠ x} ∈ *λy.R(x, y)]`. The outer `*`
    distributes over A; the inner `*` quantifies universally over
    `{y ∈ A : y ≠ x}`. Assuming R is D-based (applies only to atoms),
    this unfolds to `∀x ∈ A. ∀y ∈ A. y ≠ x → R(x,y)` — exactly
    `Plurality.Reciprocal.StrongReciprocity`.

    Sternefeld's point (paper §3.5–3.6): SR is *expressible* in his
    framework but is not a basic reading; it falls out of more
    general WR + focus mechanisms (the Geach-Kaplan analysis,
    paper §3.6). This contrasts with [beck-2001], who takes SR
    as a basic reading. -/
theorem sternefeldSR_iff_StrongReciprocity
    (A : Finset α) (R : α → α → Prop) :
    (∀ x ∈ A, ∀ y ∈ A, y ≠ x → R x y) ↔
    StrongReciprocity R A := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § 5: Cross-paper Cumulation Bridges
-- ════════════════════════════════════════════════════════════════

/-- **Sternefeld 1998 ↔ [beck-2001] ↔ [haug-dalrymple-2020]
    (bivalent)**: chain `sternefeldWR → Cumulative` via the substrate
    `WeakReciprocity` bridge — the meeting point of all three analyses
    at the cumulation substrate.

    The three-paper convergence makes
    `Plurality.Cumulativity.Cumulative` the substrate consumed by all
    three Studies files; the implementation choice (BS form vs Krifka
    closure form) is invisible from the consumer side modulo the
    easy-direction equivalence `sternefeldStarStar_implies_cumulative`. -/
theorem sternefeldWR_implies_cumulative_R
    (A : Finset α) (R : α → α → Prop)
    (hWR : sternefeldWR A R) :
    Cumulative R A A := by
  rw [sternefeldWR_iff_WeakReciprocity] at hWR
  exact weakReciprocity_imp_cumulative R A hWR

end Sternefeld1998
