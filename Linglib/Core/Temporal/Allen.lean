import Linglib.Core.Temporal.Time
import Mathlib.Tactic.Order

/-!
# Allen's Interval Relations
@cite{allen-1983}

The thirteen jointly-exhaustive, pairwise-disjoint relations that can hold
between two intervals on a linear order. Originally introduced by James F.
Allen for temporal reasoning in AI, this is the canonical relation algebra
that Reichenbach, Klein, Pancheva, and Declerck all draw from — every
temporal predicate in linglib is a (possibly singleton) subset of these
thirteen atomic relations.

| Atom         | Symbol | Inverse        | Defining inequality              |
|--------------|--------|----------------|----------------------------------|
| precedes     | p      | precededBy     | i.finish < j.start               |
| meets        | m      | metBy          | i.finish = j.start               |
| overlaps     | o      | overlappedBy   | i.start < j.start < i.finish < j.finish |
| finishedBy   | F      | finishes       | i.start < j.start, i.finish = j.finish |
| contains     | D      | during         | i.start < j.start, j.finish < i.finish |
| starts       | s      | startedBy      | i.start = j.start, i.finish < j.finish |
| equal        | e      | equal          | i.start = j.start, i.finish = j.finish |
| startedBy    | S      | starts         | i.start = j.start, j.finish < i.finish |
| during       | d      | contains       | j.start < i.start, i.finish < j.finish |
| finishes     | f      | finishedBy     | j.start < i.start, i.finish = j.finish |
| overlappedBy | O      | overlaps       | j.start < i.start < j.finish < i.finish |
| metBy        | M      | meets          | i.start = j.finish               |
| precededBy   | P      | precedes       | j.finish < i.start               |

For any two intervals on a linear order, at least one atomic relation
holds (`holds_exists`). When both intervals are non-degenerate
(`start < finish`), **exactly** one holds (`holds_unique`). The
non-degeneracy hypothesis matches @cite{allen-1983}'s original setup: on
point intervals at the same location, `meets`, `metBy`, and `equal` all
hold simultaneously, so uniqueness genuinely fails on degenerate inputs.
Both proofs use mathlib's `order` decision procedure for `LinearOrder`.

Existing `Interval` predicates (`subinterval`, `isBefore`, `finalSubinterval`,
…) are *unions* of atomic Allen relations — see the **Predicate Bridges**
section.

The Allen algebra also has a 13×13 composition table giving, for each
pair `(r, s)`, the set of relations consistent with `i r j ∧ j s k`. We
provide identity laws and the principal compositions used by tense theory;
the full table is left as a TODO.

`TemporalRelation` (in `Time.lean`) is the **point** analogue (operating on
`Time × Time`); on point intervals it collapses to `{precedes, equal,
precededBy}` (the only three Allen relations consistent with zero-length
intervals).
-/

namespace Core.Time

-- ════════════════════════════════════════════════════
-- § The Thirteen Atoms
-- ════════════════════════════════════════════════════

/-- The thirteen atomic Allen relations between two intervals on a linear
    order (@cite{allen-1983}). Naming follows Allen 1983; each atom has an
    inverse obtained by swapping the two interval arguments — see
    `AllenRelation.inverse`. -/
inductive AllenRelation where
  /-- `i.finish < j.start` — i ends strictly before j starts. -/
  | precedes
  /-- `i.finish = j.start` — i's right endpoint is j's left endpoint. -/
  | meets
  /-- `i.start < j.start < i.finish < j.finish` — proper overlap on the right of i. -/
  | overlaps
  /-- `i.start < j.start ∧ i.finish = j.finish` — j is a final subinterval of i. -/
  | finishedBy
  /-- `i.start < j.start ∧ j.finish < i.finish` — j strictly inside i. -/
  | contains
  /-- `i.start = j.start ∧ i.finish < j.finish` — i is a proper initial subinterval of j. -/
  | starts
  /-- `i.start = j.start ∧ i.finish = j.finish` — identical intervals. -/
  | equal
  /-- `i.start = j.start ∧ j.finish < i.finish` — j is a proper initial subinterval of i. -/
  | startedBy
  /-- `j.start < i.start ∧ i.finish < j.finish` — i strictly inside j. -/
  | during
  /-- `j.start < i.start ∧ i.finish = j.finish` — i is a final subinterval of j. -/
  | finishes
  /-- `j.start < i.start < j.finish < i.finish` — proper overlap on the left of i. -/
  | overlappedBy
  /-- `i.start = j.finish` — i's left endpoint is j's right endpoint. -/
  | metBy
  /-- `j.finish < i.start` — j ends strictly before i starts. -/
  | precededBy
  deriving DecidableEq, Repr, Inhabited

namespace AllenRelation

/-- The inverse of an atom: the relation that holds when the two intervals
    are swapped. `equal` is the unique self-inverse atom. -/
def inverse : AllenRelation → AllenRelation
  | .precedes     => .precededBy
  | .meets        => .metBy
  | .overlaps     => .overlappedBy
  | .finishedBy   => .finishes
  | .contains     => .during
  | .starts       => .startedBy
  | .equal        => .equal
  | .startedBy    => .starts
  | .during       => .contains
  | .finishes     => .finishedBy
  | .overlappedBy => .overlaps
  | .metBy        => .meets
  | .precededBy   => .precedes

@[simp] theorem inverse_inverse (r : AllenRelation) : r.inverse.inverse = r := by
  cases r <;> rfl

/-- `equal` is the unique self-inverse atom. -/
theorem inverse_eq_self_iff (r : AllenRelation) : r.inverse = r ↔ r = .equal := by
  cases r <;> simp [inverse]

/-- The set of all thirteen atoms — useful for stating exhaustiveness. -/
def all : List AllenRelation :=
  [.precedes, .meets, .overlaps, .finishedBy, .contains, .starts, .equal,
   .startedBy, .during, .finishes, .overlappedBy, .metBy, .precededBy]

theorem all_length : all.length = 13 := rfl

theorem mem_all (r : AllenRelation) : r ∈ all := by
  cases r <;> simp [all]

end AllenRelation

-- ════════════════════════════════════════════════════
-- § Holds Predicate
-- ════════════════════════════════════════════════════

variable {Time : Type*} [LinearOrder Time]

namespace AllenRelation

/-- `r.holds i j` is true iff atomic Allen relation `r` is the one that
    holds between intervals `i` and `j`. The defining inequalities follow
    @cite{allen-1983}. -/
def holds : AllenRelation → Interval Time → Interval Time → Prop
  | .precedes,     i, j => i.finish < j.start
  | .meets,        i, j => i.finish = j.start
  | .overlaps,     i, j => i.start < j.start ∧ j.start < i.finish ∧ i.finish < j.finish
  | .finishedBy,   i, j => i.start < j.start ∧ i.finish = j.finish
  | .contains,     i, j => i.start < j.start ∧ j.finish < i.finish
  | .starts,       i, j => i.start = j.start ∧ i.finish < j.finish
  | .equal,        i, j => i.start = j.start ∧ i.finish = j.finish
  | .startedBy,    i, j => i.start = j.start ∧ j.finish < i.finish
  | .during,       i, j => j.start < i.start ∧ i.finish < j.finish
  | .finishes,     i, j => j.start < i.start ∧ i.finish = j.finish
  | .overlappedBy, i, j => j.start < i.start ∧ i.start < j.finish ∧ j.finish < i.finish
  | .metBy,        i, j => i.start = j.finish
  | .precededBy,   i, j => j.finish < i.start

/-- Holds is symmetric under inversion: r holds of (i, j) iff r⁻¹ holds of
    (j, i). This is the central algebraic property of the inverse operation. -/
theorem holds_inverse (r : AllenRelation) (i j : Interval Time) :
    r.holds i j ↔ r.inverse.holds j i := by
  cases r <;> simp [holds, inverse, and_comm, and_left_comm, eq_comm]

/-- **Exhaustiveness** (existence half): every interval pair satisfies at
    least one atomic Allen relation. Proved by case-splitting on the
    trichotomy of `i.finish vs j.start`, `i.start vs j.finish`, then
    refining via `i.start vs j.start` and `i.finish vs j.finish`. -/
theorem holds_exists (i j : Interval Time) : ∃ r : AllenRelation, r.holds i j := by
  rcases lt_trichotomy i.finish j.start with h₁ | h₁ | h₁
  · exact ⟨.precedes, h₁⟩
  · exact ⟨.meets, h₁⟩
  · rcases lt_trichotomy i.start j.finish with h₂ | h₂ | h₂
    · rcases lt_trichotomy i.start j.start with h₃ | h₃ | h₃
      · rcases lt_trichotomy i.finish j.finish with h₄ | h₄ | h₄
        · exact ⟨.overlaps, h₃, h₁, h₄⟩
        · exact ⟨.finishedBy, h₃, h₄⟩
        · exact ⟨.contains, h₃, h₄⟩
      · rcases lt_trichotomy i.finish j.finish with h₄ | h₄ | h₄
        · exact ⟨.starts, h₃, h₄⟩
        · exact ⟨.equal, h₃, h₄⟩
        · exact ⟨.startedBy, h₃, h₄⟩
      · rcases lt_trichotomy i.finish j.finish with h₄ | h₄ | h₄
        · exact ⟨.during, h₃, h₄⟩
        · exact ⟨.finishes, h₃, h₄⟩
        · exact ⟨.overlappedBy, h₃, h₂, h₄⟩
    · exact ⟨.metBy, h₂⟩
    · exact ⟨.precededBy, h₂⟩

end AllenRelation

-- ════════════════════════════════════════════════════
-- § Signature and Uniqueness
-- ════════════════════════════════════════════════════

/-! Each non-degenerate interval pair `(i, j)` has a four-tuple
    *signature*: the pairwise `sgn` (lt/eq/gt) of every endpoint of `i`
    with every endpoint of `j`. The thirteen Allen atoms correspond
    bijectively to thirteen of the 81 possible signature tuples (the
    other 68 are excluded by `i.start < i.finish` and `j.start < j.finish`).
    Factoring uniqueness through this signature reduces the 169-case
    cross-product `cases r₁ <;> cases r₂` (which needs 6× the default
    heartbeat budget) into two 13-case lemmas. -/

/-- Three-way sign of `a vs b` on a linear order. -/
def sgn (a b : Time) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

theorem sgn_lt {a b : Time} (h : a < b) : sgn a b = .lt := if_pos h

theorem sgn_eq {a b : Time} (h : a = b) : sgn a b = .eq := by
  subst h; simp [sgn]

theorem sgn_gt {a b : Time} (h : b < a) : sgn a b = .gt := by
  unfold sgn; rw [if_neg (lt_asymm h), if_neg (ne_of_gt h)]

/-- The 4-tuple signature of an interval pair: pairwise comparisons of
    `(i.start vs j.start, i.start vs j.finish, i.finish vs j.start,
    i.finish vs j.finish)`. -/
def signature (i j : Interval Time) : Ordering × Ordering × Ordering × Ordering :=
  (sgn i.start j.start, sgn i.start j.finish, sgn i.finish j.start, sgn i.finish j.finish)

namespace AllenRelation

/-- The expected signature of each Allen atom — the unique 4-tuple of
    pairwise endpoint comparisons forced by the atom's defining
    inequalities together with non-degeneracy of both intervals. -/
def expectedSig : AllenRelation → Ordering × Ordering × Ordering × Ordering
  | .precedes     => (.lt, .lt, .lt, .lt)
  | .meets        => (.lt, .lt, .eq, .lt)
  | .overlaps     => (.lt, .lt, .gt, .lt)
  | .finishedBy   => (.lt, .lt, .gt, .eq)
  | .contains     => (.lt, .lt, .gt, .gt)
  | .starts       => (.eq, .lt, .gt, .lt)
  | .equal        => (.eq, .lt, .gt, .eq)
  | .startedBy    => (.eq, .lt, .gt, .gt)
  | .during       => (.gt, .lt, .gt, .lt)
  | .finishes     => (.gt, .lt, .gt, .eq)
  | .overlappedBy => (.gt, .lt, .gt, .gt)
  | .metBy        => (.gt, .eq, .gt, .gt)
  | .precededBy   => (.gt, .gt, .gt, .gt)

/-- The thirteen expected signatures are pairwise distinct: any two atoms
    with the same signature are equal. (13-case diagonal + 156 trivial
    `simp` contradictions on `Ordering` constructor mismatch.) -/
theorem expectedSig_injective (r₁ r₂ : AllenRelation)
    (h : r₁.expectedSig = r₂.expectedSig) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> first | rfl | (simp [expectedSig] at h)

/-- If atom `r` holds of a non-degenerate interval pair, the pair's
    signature is exactly `r.expectedSig`. (13 cases, each computing
    four `sgn` components via `Prod.ext` + the appropriate `sgn_*`
    lemma + `order`.) -/
theorem signature_of_holds (r : AllenRelation) (i j : Interval Time)
    (hi : i.start < i.finish) (hj : j.start < j.finish) (h : r.holds i j) :
    signature i j = r.expectedSig := by
  cases r <;> simp only [holds] at h
  all_goals (
    try obtain ⟨_, _, _⟩ := h
    try obtain ⟨_, _⟩ := h
    simp only [signature, expectedSig]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      first
      | (apply sgn_lt; order)
      | (apply sgn_eq; order)
      | (apply sgn_gt; order))

/-- **Uniqueness** (pairwise disjointness): on non-degenerate intervals
    (`i.start < i.finish` and `j.start < j.finish`), at most one atom
    holds of a given pair. Combined with `holds_exists`, this gives the
    key property of Allen's algebra: the thirteen atoms partition the
    space of (proper) interval pairs into thirteen exhaustive,
    pairwise-disjoint cases.

    The non-degeneracy hypothesis is essential: at a single time point
    `t`, taking `i = j = ⟨t, t, le_refl t⟩` makes `meets` (`t = t`),
    `metBy` (`t = t`), and `equal` (`t = t ∧ t = t`) all hold
    simultaneously. @cite{allen-1983} sidesteps this by assuming strict
    intervals throughout.

    Proof: factor through the 4-tuple `signature`. Both `r₁` and `r₂`
    force the same signature (`signature_of_holds`), and distinct atoms
    have distinct signatures (`expectedSig_injective`). -/
theorem holds_unique (i j : Interval Time)
    (hi : i.start < i.finish) (hj : j.start < j.finish)
    (r₁ r₂ : AllenRelation)
    (h₁ : r₁.holds i j) (h₂ : r₂.holds i j) : r₁ = r₂ :=
  expectedSig_injective _ _
    ((signature_of_holds r₁ i j hi hj h₁).symm.trans
     (signature_of_holds r₂ i j hi hj h₂))

end AllenRelation

-- ════════════════════════════════════════════════════
-- § Atom Sets and `holdsIn`
-- ════════════════════════════════════════════════════

/-! Many natural temporal predicates correspond to **unions** of Allen
    atoms — "at least one of these atoms holds." We express this
    uniformly via `holdsIn`, and name the atom-sets that appear in the
    `Interval` predicate API. Each existing `Interval` predicate is
    then a *projection* from a named atom-set: this exposes the
    algebraic structure (`S₁ ⊆ S₂ ⇒ holdsIn S₁ ⇒ holdsIn S₂`) and
    grounds each predicate in the Allen algebra by construction.

    Singleton sets (`precedesSet`, `meetsSet`) recover individual atoms
    as predicates; longer sets give the union predicates that linguistic
    theory typically works with. The atom sets are first-class data, so
    later modules (`Domain`, `RelationOrigin`, …) can manipulate them
    uniformly without committing to a specific predicate at the
    type level. -/

namespace AllenRelation

/-- "`holdsIn S i j`" iff some atom in the list `S` is the relation
    holding between `i` and `j`. Singleton lists yield exact-atom
    predicates; longer lists yield union predicates. -/
def holdsIn (S : List AllenRelation) (i j : Interval Time) : Prop :=
  ∃ r ∈ S, r.holds i j

@[simp] theorem holdsIn_nil (i j : Interval Time) :
    holdsIn [] i j ↔ False := by simp [holdsIn]

@[simp] theorem holdsIn_singleton (r : AllenRelation) (i j : Interval Time) :
    holdsIn [r] i j ↔ r.holds i j := by simp [holdsIn]

theorem holdsIn_cons (r : AllenRelation) (S : List AllenRelation)
    (i j : Interval Time) :
    holdsIn (r :: S) i j ↔ r.holds i j ∨ holdsIn S i j := by
  simp [holdsIn, or_and_right, exists_or]

/-- Subset monotonicity: enlarging the atom set weakens the predicate. -/
theorem holdsIn_mono {S₁ S₂ : List AllenRelation} (h : ∀ r ∈ S₁, r ∈ S₂)
    (i j : Interval Time) : holdsIn S₁ i j → holdsIn S₂ i j := by
  rintro ⟨r, hr, hrij⟩; exact ⟨r, h r hr, hrij⟩

-- ──── Named atom-sets corresponding to existing `Interval` predicates ────

/-- `{precedes}` — i.e., `Interval.precedes`. -/
def precedesSet : List AllenRelation := [.precedes]

/-- `{equal}` — interval coincidence; on point intervals collapses to
    point equality, the relation behind Reichenbach's `R = P` etc. -/
def equalSet : List AllenRelation := [.equal]

/-- `{meets}` — i.e., `Interval.meets`. -/
def meetsSet : List AllenRelation := [.meets]

/-- `{precedes, meets}` — i.e., `Interval.isBefore`: strict precedence
    plus meeting (the conflation `i.finish ≤ j.start` represents). -/
def beforeSet : List AllenRelation := [.precedes, .meets]

/-- `{precededBy, metBy}` — i.e., `Interval.isAfter`. -/
def afterSet : List AllenRelation := [.precededBy, .metBy]

/-- `{starts, equal, finishes, during}` — i.e., `Interval.subinterval`:
    every way `i` can be contained in `j`. -/
def containmentSet : List AllenRelation := [.starts, .equal, .finishes, .during]

/-- `{starts, finishes, during}` — i.e., `Interval.properSubinterval`:
    proper containment (excludes `equal`). -/
def properContainmentSet : List AllenRelation := [.starts, .finishes, .during]

/-- `{finishes, equal}` — i.e., `Interval.finalSubinterval`: contained
    and sharing the right endpoint. -/
def finalContainmentSet : List AllenRelation := [.finishes, .equal]

/-- `{startedBy, equal, finishedBy, contains}` — the **inverse** of
    `containmentSet`: every way `i` can contain `j`. -/
def reverseContainmentSet : List AllenRelation :=
  [.startedBy, .equal, .finishedBy, .contains]

/-- Eleven atoms — every relation except strict precedence in either
    direction — i.e., `Interval.overlaps`'s union characterization. -/
def overlapSet : List AllenRelation :=
  [.meets, .overlaps, .finishedBy, .contains, .starts, .equal,
   .startedBy, .during, .finishes, .overlappedBy, .metBy]

end AllenRelation

-- ════════════════════════════════════════════════════
-- § Predicate Bridges
-- ════════════════════════════════════════════════════

/-! Existing `Interval` predicates equated to projections from named
    Allen atom-sets via `holdsIn`. The singleton-atom predicates
    (`precedes`, `meets`) collapse to `Iff.rfl`; the union predicates
    require structural-form ↔ disjunction-form translations. These are
    the only place where the structural definitions in
    `Core/Temporal/Time.lean` meet the Allen algebra; downstream
    modules should depend on the Allen side. -/

namespace Interval

variable (i j : Interval Time)

/-- `Interval.precedes` is exactly the Allen `precedes` atom. -/
theorem precedes_iff_allen : i.precedes j ↔ AllenRelation.holdsIn AllenRelation.precedesSet i j := by
  simp [AllenRelation.precedesSet, AllenRelation.holds]; rfl

/-- `Interval.meets` is exactly the Allen `meets` atom. -/
theorem meets_iff_allen : i.meets j ↔ AllenRelation.holdsIn AllenRelation.meetsSet i j := by
  simp [AllenRelation.meetsSet, AllenRelation.holds]; rfl

/-- `Interval.isBefore` (≤) is the union `{precedes, meets}` — Allen's
    strict `precedes` plus `meets`. This conflation of two atoms into
    one weakened predicate is exactly the kind of imprecision the
    Allen algebra removes. -/
theorem isBefore_iff_allen :
    i.isBefore j ↔ AllenRelation.holdsIn AllenRelation.beforeSet i j := by
  simp [AllenRelation.beforeSet, AllenRelation.holdsIn, AllenRelation.holds, isBefore]
  exact le_iff_lt_or_eq

/-- `Interval.isAfter` is the inverse of `isBefore`: `{precededBy, metBy}`. -/
theorem isAfter_iff_allen :
    i.isAfter j ↔ AllenRelation.holdsIn AllenRelation.afterSet i j := by
  simp [AllenRelation.afterSet, AllenRelation.holdsIn, AllenRelation.holds, isAfter]
  rw [le_iff_lt_or_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm

/-- `Interval.subinterval` (i ⊆ j) is the union
    `{starts, equal, finishes, during}` — every way `i` can be contained
    in `j` without sharing the wrong boundary. -/
theorem subinterval_iff_allen :
    i.subinterval j ↔ AllenRelation.holdsIn AllenRelation.containmentSet i j := by
  simp [AllenRelation.containmentSet, AllenRelation.holdsIn, AllenRelation.holds]
  constructor
  · intro ⟨h₁, h₂⟩
    rcases lt_or_eq_of_le h₁ with hs | hs
    · rcases lt_or_eq_of_le h₂ with hf | hf
      · exact Or.inr (Or.inr (Or.inr ⟨hs, hf⟩))   -- during
      · exact Or.inr (Or.inr (Or.inl ⟨hs, hf⟩))   -- finishes
    · rcases lt_or_eq_of_le h₂ with hf | hf
      · exact Or.inl ⟨hs.symm, hf⟩                  -- starts
      · exact Or.inr (Or.inl ⟨hs.symm, hf⟩)         -- equal
  · rintro (⟨hs, hf⟩ | ⟨hs, hf⟩ | ⟨hs, hf⟩ | ⟨hs, hf⟩)
    · exact ⟨le_of_eq hs.symm, le_of_lt hf⟩         -- starts
    · exact ⟨le_of_eq hs.symm, le_of_eq hf⟩         -- equal
    · exact ⟨le_of_lt hs, le_of_eq hf⟩              -- finishes
    · exact ⟨le_of_lt hs, le_of_lt hf⟩              -- during

/-- `Interval.finalSubinterval` is the union `{finishes, equal}` —
    contained in `j` and sharing `j`'s right endpoint. -/
theorem finalSubinterval_iff_allen :
    i.finalSubinterval j ↔ AllenRelation.holdsIn AllenRelation.finalContainmentSet i j := by
  simp [AllenRelation.finalContainmentSet, AllenRelation.holdsIn, AllenRelation.holds]
  constructor
  · intro ⟨⟨h₁, _⟩, hf⟩
    rcases lt_or_eq_of_le h₁ with hs | hs
    · exact Or.inl ⟨hs, hf⟩
    · exact Or.inr ⟨hs.symm, hf⟩
  · rintro (⟨hs, hf⟩ | ⟨hs, hf⟩)
    · exact ⟨⟨le_of_lt hs, le_of_eq hf⟩, hf⟩
    · exact ⟨⟨le_of_eq hs.symm, le_of_eq hf⟩, hf⟩

/-- `Interval.properSubinterval` is the union `{starts, finishes, during}`
    — containment that excludes the `equal` case. -/
theorem properSubinterval_iff_allen :
    i.properSubinterval j ↔ AllenRelation.holdsIn AllenRelation.properContainmentSet i j := by
  simp [AllenRelation.properContainmentSet, AllenRelation.holdsIn, AllenRelation.holds,
        properSubinterval]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hstrict⟩
    rcases hstrict with hs | hf
    · -- j.start < i.start ⇒ during or finishes
      rcases lt_or_eq_of_le h₂ with hf' | hf'
      · exact Or.inr (Or.inr ⟨hs, hf'⟩)            -- during
      · exact Or.inr (Or.inl ⟨hs, hf'⟩)            -- finishes
    · -- i.finish < j.finish ⇒ starts or during
      rcases lt_or_eq_of_le h₁ with hs' | hs'
      · exact Or.inr (Or.inr ⟨hs', hf⟩)            -- during
      · exact Or.inl ⟨hs'.symm, hf⟩                  -- starts
  · rintro (⟨hs, hf⟩ | ⟨hs, hf⟩ | ⟨hs, hf⟩)
    · exact ⟨⟨le_of_eq hs.symm, le_of_lt hf⟩, Or.inr hf⟩  -- starts
    · exact ⟨⟨le_of_lt hs, le_of_eq hf⟩, Or.inl hs⟩       -- finishes
    · exact ⟨⟨le_of_lt hs, le_of_lt hf⟩, Or.inl hs⟩        -- during

end Interval

-- ════════════════════════════════════════════════════
-- § Decidability
-- ════════════════════════════════════════════════════

namespace AllenRelation

/-- `holds` is decidable on a linear order (provided `<` and `=` are). -/
instance holds_decidable [DecidableEq Time] [DecidableRel (α := Time) (· < ·)]
    (r : AllenRelation) (i j : Interval Time) : Decidable (r.holds i j) := by
  cases r <;> unfold holds <;> infer_instance

end AllenRelation

-- ════════════════════════════════════════════════════
-- § Identity Compositions and Principal Transitives
-- ════════════════════════════════════════════════════

/-! The full Allen composition table assigns to each pair `(r, s)` the set
    of relations consistent with `i r j ∧ j s k`. The table has 169 entries
    and is left as a TODO. We provide the identity laws plus the principal
    transitive closures used by tense theory.

    Convention: `holds_*_trans` reads "if r holds of (i, j) and r holds
    of (j, k), then r holds of (i, k)" for the relations that are transitive. -/

namespace AllenRelation

variable {i j k : Interval Time}

/-- `equal` is a left identity: if i = j and j r k, then i r k. -/
theorem holds_equal_left (r : AllenRelation)
    (h₁ : AllenRelation.equal.holds i j) (h₂ : r.holds j k) : r.holds i k := by
  obtain ⟨hs, hf⟩ := h₁
  cases r <;> simp_all [holds]

/-- `equal` is a right identity: if i r j and j = k, then i r k. -/
theorem holds_equal_right (r : AllenRelation)
    (h₁ : r.holds i j) (h₂ : AllenRelation.equal.holds j k) : r.holds i k := by
  obtain ⟨hs, hf⟩ := h₂
  cases r <;> simp_all [holds]

/-- `precedes` is transitive: i p j ∧ j p k → i p k. (The composition table
    entry `precedes ∘ precedes` is the singleton `{precedes}`.) The proof
    chains `i.finish < j.start ≤ j.finish < k.start` via `j.valid`. -/
theorem holds_precedes_trans
    (h₁ : AllenRelation.precedes.holds i j) (h₂ : AllenRelation.precedes.holds j k) :
    AllenRelation.precedes.holds i k := by
  simp only [holds] at h₁ h₂ ⊢
  exact lt_of_lt_of_le h₁ (le_trans j.valid (le_of_lt h₂))

/-- The `during` relation is transitive: i ⊏ j ∧ j ⊏ k → i ⊏ k. (Composition
    entry `during ∘ during = {during}`.) -/
theorem holds_during_trans
    (h₁ : AllenRelation.during.holds i j) (h₂ : AllenRelation.during.holds j k) :
    AllenRelation.during.holds i k := by
  simp only [holds] at h₁ h₂ ⊢
  exact ⟨lt_trans h₂.1 h₁.1, lt_trans h₁.2 h₂.2⟩

/-- The `contains` relation is transitive (mirror of `during`). -/
theorem holds_contains_trans
    (h₁ : AllenRelation.contains.holds i j) (h₂ : AllenRelation.contains.holds j k) :
    AllenRelation.contains.holds i k := by
  simp only [holds] at h₁ h₂ ⊢
  exact ⟨lt_trans h₁.1 h₂.1, lt_trans h₂.2 h₁.2⟩

end AllenRelation

-- ════════════════════════════════════════════════════
-- § The Projection Function `Interval.allenRel`
-- ════════════════════════════════════════════════════

/-! The projection from interval pairs to Allen atoms — the inverse
    direction of `holds`. By `holds_exists`, every pair stands in at
    least one Allen relation, so we can use `Classical.choose` to
    extract a canonical atom. By `holds_unique`, on non-degenerate
    intervals the choice is forced — any atom that holds equals the
    projection. Together with `holdsIn`, this gives a full
    abstraction-and-projection layer over the algebra. -/

namespace Interval

/-- The unique Allen atom currently holding between two intervals
    (noncomputable, extracted from `holds_exists`). For non-degenerate
    intervals this is well-defined: `allenRel_unique` proves every
    witness equals the projection. -/
noncomputable def allenRel (i j : Interval Time) : AllenRelation :=
  Classical.choose (AllenRelation.holds_exists i j)

/-- The projected atom does hold between the intervals. -/
theorem allenRel_holds (i j : Interval Time) : (allenRel i j).holds i j :=
  Classical.choose_spec (AllenRelation.holds_exists i j)

/-- For non-degenerate intervals, the projection is **unique**: every
    atom that holds equals `allenRel i j`. This is the core "well-
    definedness" theorem for the projection — it justifies treating
    `allenRel i j` as **the** Allen relation between the two intervals. -/
theorem allenRel_unique (i j : Interval Time)
    (hi : i.start < i.finish) (hj : j.start < j.finish)
    {r : AllenRelation} (h : r.holds i j) : r = allenRel i j :=
  AllenRelation.holds_unique i j hi hj r (allenRel i j) h (allenRel_holds i j)

/-- The projection lands in the named atom-set iff the corresponding
    `holdsIn` predicate holds. (For non-degenerate intervals; uses
    uniqueness to convert membership to existence.) -/
theorem allenRel_mem_iff_holdsIn (i j : Interval Time)
    (hi : i.start < i.finish) (hj : j.start < j.finish)
    (S : List AllenRelation) :
    allenRel i j ∈ S ↔ AllenRelation.holdsIn S i j := by
  constructor
  · intro h
    exact ⟨allenRel i j, h, allenRel_holds i j⟩
  · rintro ⟨r, hrS, hrij⟩
    rwa [allenRel_unique i j hi hj hrij] at hrS

end Interval

end Core.Time
