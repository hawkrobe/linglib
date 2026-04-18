import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition
import Linglib.Core.Mood.InquisitiveContent
import Linglib.Core.Mood.PartitionAsInquiry

/-!
# Theiler, Roelofsen & Aloni (2018) — A Uniform Semantics for Declarative and Interrogative Complements
@cite{theiler-etal-2018}

*Journal of Semantics* 35(3): 409–466, doi:10.1093/jos/ffy003.

This study formalizes Section 2 of the paper (semantic framework:
inquisitive sentence meanings) plus the **forcing** mention-some
example from Section 3.1, which justifies the existence of
`Core/Mood/InquisitiveContent.lean` as a sibling structure to
`Setoid W`.

## What this file establishes

1. **Figure 2** examples (Section 2.1, p. 415): the polar interrogative
   `Did Amy leave?` and the declarative `Amy left.` constructed via the
   `polar` and `declarative` constructors of `InquisitiveContent`. We
   prove the four characteristic properties from the paper's prose
   discussion (Section 2.2):
   - `amyLeft` is informative and non-inquisitive (declarative).
   - `didAmyLeave` is non-informative and inquisitive (polar question).

2. **Mention-some forcing** (Section 3.1, ex. (13)): the `Janna knows
   where one can buy an Italian newspaper` scenario adapted from
   @cite{george-2011} requires alternatives that **overlap**
   (a world where two stores both sell Italian newspapers belongs to
   multiple alternatives). We construct a minimal `mentionSome`
   inquisitive content and prove `mentionSome_not_partition_derived`:
   *no* `Setoid W` produces this content via `fromSetoid`.

   This is the forcing theorem for the architectural decision in the
   "Architectural note" docstring of `Core/Mood/POSWQ.lean` (added
   0.229.922) — it shows that `Setoid → InquisitiveContent` is a
   strictly weaker representation, and so the sibling-structure
   architecture is necessary rather than redundant.

## Scope

This file does **not** formalize the rest of the paper:
- Section 3 (false-answer-sensitive truthful resolutions, Definition 3
  in §3.3) requires a richer `E` operator over the inquisitive
  meaning, which we leave for a follow-up.
- Sections 4–6 (verb meanings, predicates of relevance, constraints
  on responsive verb meanings) require a full Fragment of attitude
  verbs typed against `InquisitiveContent`, also future work.
- Appendices A–B (comparison with @cite{uegaki-2015} inverse reductive
  approach; formal proofs).

The point of this file is the existence theorem for the "more
expressive than partitions" claim, which is what the
`InquisitiveContent.lean`/`PartitionAsInquiry.lean` pair was built
to support.
-/

namespace Phenomena.Complementation.Studies.TheilerRoelofsenAloni2018

open Core.Mood InquisitiveContent

/-! ### Section 2.1: Figure 2 — Did Amy leave? / Amy left. -/

/-- Worlds: `0, 1` are worlds where Amy left; `2, 3` are worlds where
    Amy didn't leave. Following @cite{theiler-etal-2018} Figure 2
    (`w₁, w₂` = Amy left, `w₃, w₄` = Amy didn't leave). -/
abbrev W : Type := Fin 4

/-- The proposition *Amy left* — true at worlds `w₁, w₂` (= `0, 1`). -/
def amyLeft : Set W := {0, 1}

/-- (6b) **Amy left.** — Figure 2(b). -/
def amyLeftMeaning : InquisitiveContent W := declarative amyLeft

/-- (6a) **Did Amy leave?** — Figure 2(a). -/
def didAmyLeaveMeaning : InquisitiveContent W := polar amyLeft

theorem amyLeftMeaning_info : amyLeftMeaning.info = amyLeft :=
  info_declarative amyLeft

theorem didAmyLeaveMeaning_info : didAmyLeaveMeaning.info = Set.univ :=
  info_polar amyLeft

/-- Figure 2(b): *Amy left* is **informative** — its informative content
    excludes the worlds where Amy didn't leave. -/
theorem amyLeftMeaning_isInformative : amyLeftMeaning.isInformative := by
  show amyLeftMeaning.info ≠ Set.univ
  rw [amyLeftMeaning_info]
  intro h
  have h2 : (2 : W) ∈ amyLeft := h ▸ Set.mem_univ 2
  simp [amyLeft] at h2

/-- Figure 2(b): *Amy left* is **non-inquisitive** — declaratives never
    raise an issue beyond what they assert. -/
theorem amyLeftMeaning_not_isInquisitive : ¬ amyLeftMeaning.isInquisitive :=
  not_isInquisitive_declarative amyLeft

/-- Figure 2(a): *Did Amy leave?* is **non-informative** — its
    informative content covers all worlds (the speaker rules nothing
    out by asking). -/
theorem didAmyLeaveMeaning_not_isInformative :
    ¬ didAmyLeaveMeaning.isInformative :=
  not_isInformative_polar amyLeft

/-- Figure 2(a): *Did Amy leave?* is **inquisitive** — it has two
    alternatives (`amyLeft` and `amyLeftᶜ`), neither of which alone
    covers the universe. -/
theorem didAmyLeaveMeaning_isInquisitive : didAmyLeaveMeaning.isInquisitive := by
  apply (isInquisitive_polar_iff amyLeft).mpr
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : (0 : W) ∈ amyLeft := by simp [amyLeft]
    rw [h] at h0; exact h0
  · intro h
    have h2 : (2 : W) ∉ amyLeft := by simp [amyLeft]
    apply h2
    rw [h]; exact Set.mem_univ 2

/-! ### Mention-some readings force overlapping alternatives

The Janna/Rupert scenario from @cite{george-2011} (cited in
@cite{theiler-etal-2018} ex. (13)): there are stores Newstopia,
Paperworld, and Cellulose City; Newstopia and Paperworld sell Italian
newspapers, Cellulose City does not. *Janna knows where one can buy an
Italian newspaper* under a mention-some reading is true if Janna knows
of any one such store. Critically, in worlds where multiple stores
sell, those worlds belong to multiple alternatives (one per store) —
the alternatives **overlap**.

The structural feature — non-disjoint alternatives — is what
@cite{theiler-etal-2018} §2 (Figure 5(b), the non-exhaustive *Who
left?*) and the broader inquisitive-semantics tradition (e.g.,
@cite{ciardelli-groenendijk-roelofsen-2018}) use to motivate the move
beyond partition theory. We model the irreducible structural feature
with three worlds and two overlapping alternatives. The forcing
theorem `mentionSome_not_partition_derived` shows that no `Setoid` on
these three worlds can generate this content via `fromSetoid`. -/

/-- World universe for the mention-some example: three worlds. -/
abbrev MS : Type := Fin 3

/-- Alternative 1: *Newstopia sells Italian newspapers* — true in
    worlds `0` and `1`. -/
def msNewstopia : Set MS := {0, 1}

/-- Alternative 2: *Paperworld sells Italian newspapers* — true in
    worlds `1` and `2`. World `1` is where **both** stores sell, so it
    sits in both alternatives — this is the structural feature that
    a `Setoid` cannot represent. -/
def msPaperworld : Set MS := {1, 2}

/-- The mention-some inquisitive content for *where one can buy an
    Italian newspaper*: a state resolves the issue iff every world in
    it agrees on at least one of the two stores selling. The
    alternatives are `msNewstopia` and `msPaperworld`, which **overlap**
    at world `1`. -/
def mentionSome : InquisitiveContent MS where
  props := {q | q ⊆ msNewstopia ∨ q ⊆ msPaperworld}
  contains_empty := Or.inl (Set.empty_subset _)
  downward_closed := fun _ hp _ hr => by
    rcases hp with h | h
    · exact Or.inl (hr.trans h)
    · exact Or.inr (hr.trans h)

/-- **Forcing theorem** (the architectural justification for
    `InquisitiveContent`). The mention-some content is **not** in the
    image of `fromSetoid` for any `Setoid` on the three worlds.

    Proof: `msNewstopia = {0, 1}` and `msPaperworld = {1, 2}` both lie
    in `mentionSome.props`. If `fromSetoid r = mentionSome`, each must
    be contained in some equivalence class of `r`. Since both contain
    world `1`, those classes coincide; so worlds `0`, `1`, and `2` all
    lie in one class. Then `{0, 2}` is also in
    `(fromSetoid r).props = mentionSome.props`, but `{0, 2}` is not a
    subset of `msNewstopia` (missing `2`) nor of `msPaperworld`
    (missing `0`) — contradiction.

    This is the standard partition-theory limitation that motivates
    inquisitive semantics' move to non-disjoint alternatives
    (@cite{ciardelli-groenendijk-roelofsen-2018}; @cite{theiler-etal-2018}
    §2 Figure 5(b)). -/
theorem mentionSome_not_partition_derived (r : Setoid MS) :
    fromSetoid r ≠ mentionSome := by
  intro heq
  have hms1 : msNewstopia ∈ mentionSome.props := Or.inl subset_rfl
  have hms2 : msPaperworld ∈ mentionSome.props := Or.inr subset_rfl
  have hms1' : msNewstopia ∈ (fromSetoid r).props := heq ▸ hms1
  have hms2' : msPaperworld ∈ (fromSetoid r).props := heq ▸ hms2
  -- Extract class containment for msNewstopia
  rcases hms1' with hempty | ⟨c1, hc1, hsub1⟩
  · have h0 : (0 : MS) ∈ msNewstopia := by simp [msNewstopia]
    rw [hempty] at h0; exact h0.elim
  -- Extract class containment for msPaperworld
  rcases hms2' with hempty | ⟨c2, hc2, hsub2⟩
  · have h1 : (1 : MS) ∈ msPaperworld := by simp [msPaperworld]
    rw [hempty] at h1; exact h1.elim
  -- Worlds 0, 1 ∈ c1; worlds 1, 2 ∈ c2
  have h0c1 : (0 : MS) ∈ c1 := hsub1 (by simp [msNewstopia])
  have h1c1 : (1 : MS) ∈ c1 := hsub1 (by simp [msNewstopia])
  have h1c2 : (1 : MS) ∈ c2 := hsub2 (by simp [msPaperworld])
  have h2c2 : (2 : MS) ∈ c2 := hsub2 (by simp [msPaperworld])
  -- c1 = c2 since both contain world 1
  have hcc : c1 = c2 := Setoid.eq_of_mem_classes hc1 h1c1 hc2 h1c2
  -- So world 2 ∈ c1
  have h2c1 : (2 : MS) ∈ c1 := hcc ▸ h2c2
  -- Now {0, 2} ⊆ c1, so {0, 2} ∈ (fromSetoid r).props
  have h02_sub : ({0, 2} : Set MS) ⊆ c1 := by
    intro x hx
    rcases hx with rfl | hx
    · exact h0c1
    · rcases hx with rfl | _
      · exact h2c1
  have h02_props : ({0, 2} : Set MS) ∈ (fromSetoid r).props :=
    Or.inr ⟨c1, hc1, h02_sub⟩
  -- By heq, {0, 2} ∈ mentionSome.props
  have h02_ms : ({0, 2} : Set MS) ∈ mentionSome.props := heq ▸ h02_props
  -- But {0, 2} is not ⊆ msNewstopia (missing 2) nor ⊆ msPaperworld (missing 0)
  rcases h02_ms with hsub_n | hsub_c
  · have : (2 : MS) ∈ msNewstopia := hsub_n (by simp)
    simp [msNewstopia] at this
  · have : (0 : MS) ∈ msPaperworld := hsub_c (by simp)
    simp [msPaperworld] at this

end Phenomena.Complementation.Studies.TheilerRoelofsenAloni2018
