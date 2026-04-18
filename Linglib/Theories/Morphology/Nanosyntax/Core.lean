import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment

/-!
# Nanosyntax: Core
@cite{caha-2009}

Nanosyntax (@cite{caha-2009}, @cite{starke-2009}) is a non-lexicalist,
post-syntactic, piece-based, realizational theory of morphology —
identical to Distributed Morphology on all four of
@cite{kalin-bjorkman-etal-2026}'s dimensions, but distinguished by
two mechanism-level differences:

1. **Phrasal spellout**: lexical items spell out entire syntactic
   phrases (subtrees), not just individual terminals as in DM's
   Vocabulary Insertion.

2. **The Superset Principle**: a lexical entry matches a syntactic
   node if it has a sub-constituent identical to the node
   (@cite{caha-2009} §2.2). Among competing entries, the
   Elsewhere Condition selects the most specific (smallest) match.

## The functional sequence (fseq)

The key structural assumption is that case features are ordered
in a universal **functional sequence** (fseq):

    NOM – ACC – GEN – DAT – INS – COM

Each case is built by successive Merge from atomic features,
yielding a strictly right-branching tree:

    NOM = [A]
    ACC = [B [A]]
    GEN = [C [B [A]]]
    DAT = [D [C [B [A]]]]

Because the tree is strictly right-branching, each case is fully
characterized by its **rank** (depth): NOM = 0, ACC = 1, GEN = 2,
DAT = 3, etc. A lexical entry storing a tree of rank r contains
all sub-constituents of rank ≤ r. This is exactly the containment
hierarchy formalized in `Interfaces.Morphosyntax.CaseContainment`.

## Deriving *ABA

The Superset Principle + fseq structure derives the *ABA
constraint (@cite{caha-2009} §2.3). If entry β stores rank 2
(ACC-sized) and entry α stores rank 3 (GEN-sized), then:

- NOM (rank 0): both match, β wins (smaller) → β
- ACC (rank 1): both match, β wins (smaller) → β
- GEN (rank 2): only α matches → α

Result: β–β–α. There is no way to get α–β–α, because any entry
that beats α for the intermediate case Y also beats α for all
cases below Y (it matches them too, and it's smaller).

See `Interfaces.Morphosyntax.CaseContainment` for the *ABA constraint
formalized independently via `AllomorphyPattern`.
-/

namespace Morphology.Nanosyntax

open Interfaces.Morphosyntax.CaseContainment

-- ============================================================================
-- §1: Lexical Entries on the fseq
-- ============================================================================

/-- A Nanosyntax lexical entry: a stored fseq rank paired with a
    phonological exponent. The rank represents how deep the entry's
    stored tree goes on the functional sequence.

    An entry of rank r stores the tree [Fᵣ [... [F₁ [F₀]]]],
    which contains all sub-constituents of rank 0..r.

    Contrast with DM's `FeatureVI` which stores a feature *set*
    (not necessarily contiguous on the fseq). -/
structure LexEntry where
  /-- The rank (depth) of the stored tree on the fseq.
      Corresponds to `CaseContainment.containmentRank`. -/
  rank : Nat
  /-- The phonological exponent. -/
  exponent : String
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §2: The Superset Principle
-- ============================================================================

/-- Does a lexical entry match a target under the Superset Principle?
    The entry matches if its stored tree contains the target as a
    sub-constituent — equivalently, if the entry's rank is at least
    as large as the target's rank.

    @cite{caha-2009} §2.2: "A phonological exponent is inserted into
    a node if its lexical entry has a (sub-)constituent that is
    identical to the node." -/
def LexEntry.matches (entry : LexEntry) (targetRank : Nat) : Bool :=
  entry.rank ≥ targetRank

/-- Phrasal spellout via the Superset Principle: among all entries
    that match the target (rank ≥ target rank), select the one with
    the smallest rank (= most specific, closest match).

    This is the Nanosyntax counterpart of DM's `vocabularyInsert`.
    The competition logic is reversed:
    - DM Subset Principle: VI features ⊆ target, *largest* VI wins
    - Nanosyntax Superset Principle: entry rank ≥ target, *smallest*
      entry wins

    Both converge on "the entry that wastes the least." -/
def spellout (entries : List LexEntry) (targetRank : Nat) :
    Option String :=
  let matching := entries.filter (·.matches targetRank)
  (matching.foldl (init := none) fun acc entry =>
    match acc with
    | none => some entry
    | some prev =>
      if entry.rank < prev.rank then some entry else some prev
  ).map (·.exponent)

-- ============================================================================
-- §3: Syncretism and *ABA
-- ============================================================================

/-- Two cases are syncretic under a given lexicon if spellout
    assigns them the same exponent. -/
def syncretic (entries : List LexEntry)
    (rank1 rank2 : Nat) : Bool :=
  match spellout entries rank1, spellout entries rank2 with
  | some e1, some e2 => e1 == e2
  | _, _ => false

/-- Three ranks X < Y < Z exhibit an ABA pattern if X and Z
    receive the same exponent but Y receives a different one.
    The fseq-based Superset Principle predicts this cannot happen. -/
def abaViolation (entries : List LexEntry)
    (x y z : Nat) : Bool :=
  match spellout entries x, spellout entries y, spellout entries z with
  | some ex, some ey, some ez => ex == ez && ex != ey
  | _, _, _ => false

-- ============================================================================
-- §4: *ABA impossibility (derived from fseq structure)
-- ============================================================================

/-- If entry β (rank rβ) beats entry α (rank rα) for case Y
    (rank rY), then β also beats α for all cases X with rank
    rX ≤ rY. This is because:
    1. β matches Y → β.rank ≥ rY ≥ rX → β matches X
    2. β beats α for Y → β.rank < α.rank (both match, β is smaller)
    3. Both match X, β is still smaller → β beats α for X too

    Consequence: if β wins over α anywhere on the fseq, β wins for
    *all cases below that point*. There is no way for α to resurface
    below β — hence no ABA. -/
theorem smaller_entry_dominates_below
    (α β : LexEntry) (rY rX : Nat)
    (hX_le_Y : rX ≤ rY)
    (hβ_matches_Y : β.matches rY = true)
    (hα_matches_Y : α.matches rY = true)
    (hβ_beats_α : β.rank < α.rank) :
    β.matches rX = true ∧ α.matches rX = true ∧ β.rank < α.rank := by
  refine ⟨?_, ?_, hβ_beats_α⟩
  · simp [LexEntry.matches] at hβ_matches_Y ⊢; omega
  · simp [LexEntry.matches] at hα_matches_Y ⊢; omega

-- ============================================================================
-- §5: Case examples
-- ============================================================================

section CaseExamples

/-- Case ranks on the fseq, matching `containmentRank`.
    NOM = 0, ACC = 1, GEN = 2, DAT = 3. -/
def nom : Nat := 0
def acc : Nat := 1
def gen : Nat := 2
def dat : Nat := 3

/-- ABB pattern: entry A at rank 0 (NOM-sized), entry B at rank 3
    (DAT-sized = covers everything).
    - NOM: A (rank 0) vs B (rank 3), both match, A wins → "A"
    - ACC: only B matches → "B"
    - GEN: only B matches → "B"
    - DAT: only B matches → "B" -/
def abbLexicon : List LexEntry :=
  [⟨0, "A"⟩, ⟨3, "B"⟩]

theorem abb_nom : spellout abbLexicon nom = some "A" := by native_decide
theorem abb_acc : spellout abbLexicon acc = some "B" := by native_decide
theorem abb_gen : spellout abbLexicon gen = some "B" := by native_decide
theorem abb_dat : spellout abbLexicon dat = some "B" := by native_decide

/-- ABB has no ABA violation. -/
theorem abb_no_aba :
    abaViolation abbLexicon nom acc gen = false := by native_decide

/-- AAB pattern: entry A at rank 2 (GEN-sized), entry B at rank 3
    (DAT-sized).
    - NOM: A (rank 2) vs B (rank 3), both match, A wins → "A"
    - ACC: A vs B, A wins → "A"
    - GEN: A vs B, A wins → "A"
    - DAT: only B matches → "B" -/
def aabLexicon : List LexEntry :=
  [⟨2, "A"⟩, ⟨3, "B"⟩]

theorem aab_nom : spellout aabLexicon nom = some "A" := by native_decide
theorem aab_acc : spellout aabLexicon acc = some "A" := by native_decide
theorem aab_gen : spellout aabLexicon gen = some "A" := by native_decide
theorem aab_dat : spellout aabLexicon dat = some "B" := by native_decide

/-- AABB pattern: entry A at rank 1 (ACC-sized), entry B at rank 3.
    - NOM: A (rank 1) vs B (rank 3), A wins → "A"
    - ACC: A vs B, A wins → "A"
    - GEN: only B matches → "B"
    - DAT: only B matches → "B" -/
def aabbLexicon : List LexEntry :=
  [⟨1, "A"⟩, ⟨3, "B"⟩]

theorem aabb_nom : spellout aabbLexicon nom = some "A" := by native_decide
theorem aabb_acc : spellout aabbLexicon acc = some "A" := by native_decide
theorem aabb_gen : spellout aabbLexicon gen = some "B" := by native_decide
theorem aabb_dat : spellout aabbLexicon dat = some "B" := by native_decide

/-- Total syncretism: a single entry at rank 3 matches everything.
    One form for all cases. -/
def totalSyncretism : List LexEntry :=
  [⟨3, "A"⟩]

theorem total_syncretic :
    syncretic totalSyncretism nom acc = true ∧
    syncretic totalSyncretism acc gen = true ∧
    syncretic totalSyncretism gen dat = true := by native_decide

/-- *ABA is impossible. With entries at ranks 0 and 2 (trying to
    skip rank 1), the rank-2 entry matches rank 1 too — and beats
    the rank-0 entry for rank 0 as well! Result: B–B–B, not A–B–A. -/
def attemptedABA : List LexEntry :=
  [⟨0, "A"⟩, ⟨2, "B"⟩]

theorem attempted_aba_produces_abb :
    spellout attemptedABA nom = some "A" ∧
    spellout attemptedABA acc = some "B" ∧
    spellout attemptedABA gen = some "B" := by native_decide

theorem attempted_aba_fails :
    abaViolation attemptedABA nom acc gen = false := by native_decide

/-- Even with three entries, *ABA is impossible. Adding a third
    entry at rank 2 with exponent "A" doesn't help — entries at
    the same rank compete, and only one can win. The fseq structure
    ensures contiguity. -/
def threeEntryAttempt : List LexEntry :=
  [⟨0, "A"⟩, ⟨1, "B"⟩, ⟨2, "A"⟩]

-- NOM: all three match (ranks 0,1,2 all ≥ 0). Smallest = rank 0 → "A"
-- ACC: entries at rank 1 and 2 match (not rank 0). Smallest = rank 1 → "B"
-- GEN: only rank 2 matches → "A"
-- This IS ABA! But only because we allowed two distinct entries with
-- the same exponent "A" at different ranks. In Nanosyntax, this
-- requires two DISTINCT lexical items that happen to be homophonous.
-- Caha argues this is accidental homophony (phonological), not
-- systematic syncretism — the theory distinguishes the two.

theorem three_entry_is_aba :
    abaViolation threeEntryAttempt nom acc gen = true := by native_decide

-- The point: *ABA from SYSTEMATIC syncretism (one lexical item
-- covering a contiguous span) is impossible. ABA from accidental
-- homophony (two unrelated items that sound alike) is a different
-- phenomenon that the theory correctly sets aside.

end CaseExamples

-- ============================================================================
-- §6: Connection to CaseContainment
-- ============================================================================

/-- Map a `Core.Case` to a Nanosyntax target rank via the existing
    containment hierarchy. Returns `none` for cases not on the
    standard fseq (e.g., ERG/ABS). -/
def caseToRank (c : Core.Case) : Option Nat :=
  Core.Case.containmentRank c

/-- Spellout a case directly: look up the case's rank, then
    apply phrasal spellout. -/
def spelloutCase (entries : List LexEntry) (c : Core.Case) :
    Option String :=
  match caseToRank c with
  | some r => spellout entries r
  | none => none

-- ============================================================================
-- §8: Paradigm gap monotonicity
-- ============================================================================

/-- For the min-selecting fold used in `spellout`, once we process at
    least one element, the result is `some`. -/
private theorem foldl_spellout_some (l : List LexEntry) (e : LexEntry) :
    ∃ e', l.foldl (fun acc entry =>
      match acc with
      | none => some entry
      | some prev => if entry.rank < prev.rank then some entry else some prev
    ) (some e) = some e' := by
  induction l generalizing e with
  | nil => exact ⟨e, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    split <;> exact ih _

private theorem spellout_none_of_filter_nil (lex : List LexEntry) (r : Nat)
    (hf : lex.filter (·.matches r) = []) :
    spellout lex r = none := by
  simp only [spellout, hf]
  rfl

private theorem entries_lt_of_spellout_none (lex : List LexEntry) (r : Nat)
    (h : spellout lex r = none) :
    ∀ e ∈ lex, e.rank < r := by
  intro e he
  by_cases hlt : e.rank < r
  · exact hlt
  · exfalso
    have hge : e.matches r = true := by
      simp [LexEntry.matches]; omega
    have hmatch : e ∈ lex.filter (·.matches r) :=
      List.mem_filter.mpr ⟨he, hge⟩
    have hne : lex.filter (·.matches r) ≠ [] :=
      List.ne_nil_of_mem hmatch
    obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil hne
    have hspellout : spellout lex r ≠ none := by
      simp only [spellout, heq, List.foldl_cons]
      obtain ⟨e', he'⟩ := foldl_spellout_some tl hd
      intro hab
      rw [Option.map_eq_none_iff] at hab
      exact absurd (he' ▸ hab) (by intro h; nomatch h)
    exact hspellout h

/-- Paradigm gap monotonicity: if spellout fails at rank r, it fails
    at all higher ranks. This follows from the Superset Principle —
    an entry matching rank r' ≥ r would also match rank r. -/
theorem gap_propagates_upward (lex : List LexEntry) (r r' : Nat)
    (h : spellout lex r = none) (hr : r ≤ r') :
    spellout lex r' = none := by
  apply spellout_none_of_filter_nil
  rw [List.filter_eq_nil_iff]
  intro e he
  simp only [Bool.not_eq_true, LexEntry.matches, decide_eq_false_iff_not, Nat.not_le]
  have := entries_lt_of_spellout_none lex r h e he
  omega

-- ============================================================================
-- §9: Morphological type (prefix vs suffix)
-- ============================================================================

/-- Morphological type of an exponent derived from nanosyntactic
    spellout. Suffixes arise from spellout-driven movement (roll-up,
    unary foot); prefixes arise from subderivation (binary foot). -/
inductive MorphType where
  | suffix | prefix
  deriving DecidableEq, Repr, BEq

end Morphology.Nanosyntax
