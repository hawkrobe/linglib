import Linglib.Features.WordOrder
import Linglib.Syntax.Tree.Cat
import Linglib.Fragments.English.WordOrder
import Mathlib.Data.Finset.Basic

/-!
# Bruening and Al Khalaf 2020: category mismatches in coordination

Coordination is supposed to conjoin like with like, and the counterexamples fall into two kinds.
Predicates and modifiers of different categories coordinate freely but never violate a selectional
restriction — *Danny became a political radical and very antisocial* is fine, *and under suspicion*
is not — because what is selected there is a supercategory that several categories belong to.
Arguments and prenominal modifiers, by contrast, do violate selection, and only in two
configurations: a clause coordinated with a noun phrase where clauses are banned, and one of the
non-*ly* adverbs coordinated with an adjective phrase prenominally. Those are exactly the two that
displacement and ellipsis also permit, so the file derives the pair from distribution rather than
listing it.

The paper's mechanism is that the conjunct which has to satisfy the selectional requirement is the
one linearly closest to the selecting head, against the rival accounts on which it is the
structurally prominent first conjunct. The two are the same rule applied to different choices of
conjunct, and they coincide exactly where the head precedes the coordination. English subjects and
verb-final complements are where they part company, and the judgements there — a clause must come
first when the coordination precedes its verb — are the linear ones.

## Main definitions

* `FeaturePercolation`, `selectedSlot` — which conjunct must satisfy selection, on each account
* `predictOrder` — the conjunct order each account predicts at a position
* `coordExtension` — the categories a category can also appear as, outside coordination
* `Supercategory` — the predicative and modifier supercategories over `Cat`

## Main results

* `agree_iff_head_precedes` — the accounts coincide exactly where the head precedes the
  coordination, and diverge everywhere else
* `english_subject_diverges`, `ov_complement_diverges` — the two configurations that adjudicate
* `coordExtension_exhaustive`, `extension_to_violation` — only clauses and adverb phrases extend,
  which is where the two permitted violations come from

## References

* [bruening-alkhalaf-2020]
* [munn-1993]
* [sag-etal-1985]
* [zhang-2010]
-/
namespace BrueningAlKhalaf2020

open Syntax (Cat)
open Syntax.Cat (NP VP AdjP AdvP PP)
open WordOrder

/-! ### Shared types for selection-violating coordination -/

/-- Preferred order of conjuncts in DP-CP selection-violating coordination. -/
inductive ConjunctOrder where
  /-- DP conjunct precedes CP conjunct. -/
  | dpFirst
  /-- CP conjunct precedes DP conjunct. -/
  | cpFirst
  deriving DecidableEq, Repr

-- `VerbPosition` and the `OVOrder → Option VerbPosition` projection
-- live in `WordOrder` substrate; consumed via `open` above.

/-! ### Which conjunct must satisfy selection -/

/-- A conjunct's position in the coordination. -/
inductive ConjunctSlot where
  /-- The specifier conjunct. -/
  | first
  /-- The complement conjunct. -/
  | last
  deriving DecidableEq, Repr

/-- Which conjunct's features reach the selecting head. The accounts differ in this alone. -/
inductive FeaturePercolation where
  /-- The features of the structurally prominent conjunct, whatever the surface order
      ([munn-1993], [zhang-2010]). -/
  | structural
  /-- The features of the conjunct linearly closest to the selecting head. -/
  | linear
  deriving DecidableEq, Repr

/-- The conjunct adjacent to the selecting head: the first when the head precedes the coordination,
the last when it follows it. -/
def adjacent : VerbPosition → ConjunctSlot
  | .postverbal => .first
  | .preverbal => .last

/-- The conjunct that has to satisfy the head's selectional requirement: the adjacent one on the
linear account, the prominent one — always the first — on the structural account. -/
def selectedSlot : FeaturePercolation → VerbPosition → ConjunctSlot
  | .linear, pos => adjacent pos
  | .structural, _ => .first

/-- The order predicted for a coordination of a selected noun phrase with a clause: the noun phrase
takes the selected slot, so the clause takes the other. -/
def predictOrder (fp : FeaturePercolation) (pos : VerbPosition) : ConjunctOrder :=
  match selectedSlot fp pos with
  | .first => .dpFirst
  | .last => .cpFirst

/-- **The accounts coincide exactly where the head precedes the coordination**, since only there is
the adjacent conjunct the prominent one. Everywhere else — an English subject, a verb-final
complement, a postpositional complement — they make opposite predictions. -/
theorem agree_iff_head_precedes (pos : VerbPosition) :
    predictOrder .structural pos = predictOrder .linear pos ↔ pos = .postverbal := by
  cases pos <;> simp [predictOrder, selectedSlot, adjacent]

/-! ### Permitted selection violations -/

/-- The two category mismatches a coordination may use to violate selection. Both are mismatches
that displacement and ellipsis also permit: a clause has the distribution of a noun phrase under
topicalization and pseudoclefting, and a non-*ly* adverb has that of an adjective prenominally. -/
inductive SelectionViolationType where
  /-- CP appearing in an NP-selecting position. -/
  | cpAsNp
  /-- Non-*ly* adverb appearing in an adjective position. -/
  | advAsAdj
  deriving DecidableEq, Repr

/-! ### The configurations that adjudicate -/

/-- English complements follow the verb. -/
theorem english_complement_postverbal :
    OVOrder.verbPosition English.wordOrder.ovOrder = some .postverbal := rfl

/-- With the head preceding, both accounts predict the selected noun phrase first, and that is what
is found: *you can depend on my assistant and that he will be on time* ((3a), from
[sag-etal-1985]). -/
theorem english_complement_agree :
    predictOrder .structural .postverbal = predictOrder .linear .postverbal :=
  (agree_iff_head_precedes .postverbal).mpr rfl

/-- An English subject precedes the verb even though complements follow it, so the accounts part
company there. The judgement is the linear one: *that he was late all the time and his constant
harassment of coworkers resulted in his being dismissed* is good and the reverse order is not
((41)). The same holds of a complement of a postposition, which likewise precedes its head
(*that she got third place and her injury in the final round notwithstanding*, (43)). -/
theorem english_subject_diverges :
    predictOrder .structural .preverbal ≠ predictOrder .linear .preverbal := by
  simpa using (agree_iff_head_precedes .preverbal).not.mpr (by simp)

/-- A verb-final language puts every complement before its verb, so the accounts diverge there
too — the cross-linguistic version of the subject test. -/
theorem ov_complement_diverges :
    (OVOrder.verbPosition .ov).map (predictOrder .structural)
      ≠ (OVOrder.verbPosition .ov).map (predictOrder .linear) := by
  simp [OVOrder.verbPosition, predictOrder, selectedSlot, adjacent]

/-! ### Supercategories -/

/-- The supercategories a position may select, under which apparently mismatched predicates and
modifiers turn out to be alike. Selection is finer-grained than the supercategory coordination
cares about: *become* selects predicates but admits only noun and adjective phrases, so
*became a political radical and under suspicion* is still out ((1)). -/
inductive Supercategory where
  /-- Predicative: NP, VP, AP, PP can all serve as predicates. -/
  | pred
  /-- Modifier: AP, AdvP can both serve as (prenominal) modifiers. -/
  | mod
  deriving DecidableEq, Repr

/-- Categories belonging to each supercategory, grounded in the `Cat` category
    system from `Syntax`. `Pred` is the full predicative supercategory (B&AK's
    (84): `Pred:{NP,AP}` and friends); `Mod` is restricted here to the
    prenominal modifier categories. The inclusion order on `Finset Cat` gives
    the lattice structure. -/
def Supercategory.cats : Supercategory → Finset Cat
  | .pred => {NP, VP, AdjP, PP}
  | .mod  => {AdjP, AdvP}

/-- The two supercategories overlap in the adjective phrase alone, which is why an adjective is
the category that can be coordinated both with a predicate and with a modifier. -/
theorem supercats_overlap :
    Supercategory.cats .pred ∩ Supercategory.cats .mod = {AdjP} := by decide

/-- Extended distributional compatibility for coordination (§3.2). Categories
    that `c` can appear as in non-coordination contexts (displacement, ellipsis),
    beyond its native category.

    - CP → NP: CPs can be topicalized, pseudoclefted, and pro-form replaced —
      NP-like distributional properties
    - AdvP → AdjP: non-*ly* adverbs appear prenominally — AdjP-like
      distributional properties (only with a non-*ly* adverb conjoined to an
      AP in prenominal position, AP last; this coarse map drops those
      conditions)

    All other categories have no extended compatibility. Combined with
    `Supercategory.cats`, this derives B&AK's "exactly two permitted violations"
    (§3.2). -/
def coordExtension : Cat → Finset Cat
  | .CP        => {NP}
  | .proj .ADV => {AdjP}
  | _          => ∅

/-- CP extends to NP positions. -/
theorem cp_extends_np : NP ∈ coordExtension .CP :=
  Finset.mem_singleton.mpr rfl

/-- AdvP extends to AdjP positions. -/
theorem advp_extends_adjp : AdjP ∈ coordExtension (.proj .ADV) :=
  Finset.mem_singleton.mpr rfl

/-- Only CP and AdvP have non-empty coordination extensions. This structurally
    derives B&AK's "exactly two permitted violations" (§3.2) from distributional
    profiles rather than stipulating them as a list. -/
theorem coordExtension_exhaustive (c : Cat) :
    coordExtension c ≠ ∅ → c = .CP ∨ c = AdvP := by
  cases c with
  | CP => intro _; exact Or.inl rfl
  | S => intro h; exact absurd rfl h
  | head _ => intro h; exact absurd rfl h
  | proj u =>
    cases u <;> intro h <;>
      first | exact Or.inr rfl | exact absurd rfl h

/-- Map each violation type to its source and target categories. The source
    category can appear in a position selecting the target via coordination. -/
def SelectionViolationType.cats : SelectionViolationType → Cat × Cat
  | .cpAsNp   => (.CP, NP)
  | .advAsAdj => (AdvP, AdjP)

/-- Each permitted violation corresponds to a non-empty `coordExtension`: the
    target category appears in the extension of the source. -/
theorem violation_from_extension (v : SelectionViolationType) :
    v.cats.2 ∈ coordExtension v.cats.1 := by
  cases v <;> exact Finset.mem_singleton.mpr rfl

/-- Every non-empty `coordExtension` corresponds to a permitted violation. This,
    together with `violation_from_extension`, establishes a bijection between
    `SelectionViolationType` and non-empty extensions, proving the enumeration
    is not stipulated but derived from distributional profiles. -/
theorem extension_to_violation (c : Cat) (h : coordExtension c ≠ ∅) :
    ∃ v : SelectionViolationType, v.cats.1 = c := by
  rcases coordExtension_exhaustive c h with rfl | rfl
  · exact ⟨.cpAsNp, rfl⟩
  · exact ⟨.advAsAdj, rfl⟩

end BrueningAlKhalaf2020
