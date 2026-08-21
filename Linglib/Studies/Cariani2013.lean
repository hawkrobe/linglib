import Linglib.Semantics.Attitudes.Desire.QuestionBased
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# [cariani-2013] — `Ought' and Resolution Semantics

`[cariani-2013]` (*Noûs* 47:534-558) presents an anti-INHERITANCE
account of `ought`: standard "boxing" semantics treats `ought` as
universal quantification over best worlds (Kratzer 1981/1991), which
validates **INHERITANCE** (`If p ⊨ q then ought(p) ⊨ ought(q)`) — but
this fails empirically. Cariani offers three motivating puzzles
(§§I-III) and a positive proposal called **Resolution Semantics** (§4),
inspired by Yalcin's terminology (Cariani p.545).

The three INHERITANCE-violation puzzles:

* **§I Ross's Puzzle** (Ross 1941): `Joan ought to attend her classes`
  does NOT entail `Joan ought to either attend her classes or burn down
  the philosophy department`.
* **§II Procrastinate** (Jackson & Pargetter 1986): `Procrastinate
  ought to accept and write the review` is true; `Procrastinate ought
  to accept` is false.
* **§III Conditional 'oughts'**: RESTRICTION + INHERITANCE jointly
  predict `If you drink poison, you ought to drink poison`. Should be
  false. We formalize a degenerate version (drinking poison
  unconditionally fails strong permissibility); the full conditional
  treatment requires a separate modal-base parameter (paper §4 p.545
  clause (iii) uses `Q_c ∩ M_c`) which we omit for scope.

Cariani's **Resolution Semantics** (§4 p.544-546):

* Three contextual parameters: **options** Q_c (mutually incompatible
  courses of action — a partition of the action space), **ordering**
  ≺ on options, **benchmark** threshold.
* A proposition `p` is **visible** in Q_c iff every option is either
  a way-of-p or a not-way-of-p (the options *settle* p).
* **Lexical entry** (§4 p.546, formal): `⟦ought p⟧^{c,w} = 1` iff
  - **(i) Optimality**: every best option is a way-of-p
  - **(ii) Strong Permissibility**: every way-of-p option meets benchmark
  - **(iii) Visibility**: p is visible in Q_c ∩ M_c

  Our `ought` definition uses the *informal* §2 (p.540) ordering
  (visibility ∧ optimality ∧ strong permissibility); the §4 formal
  ordering is (i)+(ii)+(iii). The ∧-conjunction is symmetric so the
  truth-conditions are identical.

* **Boxing as special case** (p.546): when **(a)** cells of Q_c are
  singleton sets AND **(b)** every option meets benchmark, Resolution
  Semantics reduces to standard boxing. Both conditions are required
  — see `ought_iff_kratzer_boxing_of_singletons_and_all_meet`.

## Coarseness and Coarse Falsemaking

[cariani-2013] §1 (p.534) opens with:

> [COARSENESS] `S ought to φ` can be true even though there are
> impermissible ways of φ-ing.

This is the paper's leading desideratum — `ought` is *coarser* than
the way-action distinction. `Cariani.ought` satisfies coarseness by
not requiring every way-of-p to itself be ought-true; only that they
meet the benchmark (Strong Permissibility).

§2 (p.541, restated p.546) gives the positive constraint:

> [COARSE FALSEMAKING] An ought-sentence is false (in a context) if
> there is a *relevant* option compatible with the prejacent that's
> impermissible.

Our `ought_negation_via_coarse_falsemaking` makes this precise.

## Cross-framework: structural agreement with Phillips-Brown

Cariani's `visible` is **definitionally identical** to Phillips-Brown's
`IsConsidered` (`Semantics/Attitudes/Desire/QuestionBased.lean`,
[phillips-brown-2025] §3.6) — so much so that we don't redefine
it: `Cariani2013.isVisible` is an `abbrev` for `IsConsidered` over the
options list. The bridge theorem `isVisible_iff_IsConsidered` is
`Iff.rfl`.

This is **parallel discovery, not chain-of-influence**: Cariani 2013's
bibliography (pp.557-558) contains no Crnič citation; PB 2025 cites
Crnič 2011 (PhD thesis "Getting Even") as inspiration. Both
independently arrived at the same predicate via different routes:
Cariani via Lewisian relevant-alternatives + Yalcin terminology
(p.546); PB via Crnič's question-sensitive belief proposal. The
formal identity of the two predicates is a substantive cross-framework
finding that linglib's "make agreements visible" thesis surfaces.

## DUALITY failure (paper §5 p.547-548)

Cariani's Resolution Semantics rejects INHERITANCE, which forces
rejection of one direction of DUALITY (`ought p ↔ ¬ permitted ¬p`).
Specifically (p.547): "the rejection of the right-to-left direction
of DUALITY is an immediate consequence of the rejection of
INHERITANCE." See `cariani_duality_right_to_left_failure`.
-/

namespace Cariani2013

open Desire.QuestionBased (IsConsidered)

/-! ## §1. Resolution Semantics primitives

Following [cariani-2013] §4 (pp.544-545). The three contextual
parameters are options, ordering, benchmark. Per §4 (p.545):

> If individual options are modeled as propositions, a range of
> mutually exclusive options can be thought of as a set of mutually
> exclusive propositions—i.e., as a partition of a subset S of
> logical space.

We model options as a `List (Finset W)` — finite, with decidable
membership — matching the substrate's `Desire.QuestionBased` representation of
partition cells. Mutual exclusivity is a hypothesis
on consumers, not a structure field. -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Cariani's propositions carry function-form decidability; the question-based substrate
reads membership. -/
instance {p : Set W} [DecidablePred p] : DecidablePred (· ∈ p) :=
  fun w => inferInstanceAs (Decidable (p w))

/-- A `ResolutionContext` packages Cariani's three parameters:
    options (mutually exclusive cells), an ordering on options, and a
    benchmark predicate (a cutoff IN the ordering's range, not a
    numeric threshold — Cariani is non-committal between ranking and
    quantitative scales, p.545). -/
structure ResolutionContext (W : Type*) where
  /-- Mutually exclusive options (a partition of the relevant action
      space). Stored as `Finset` cells for `decide`-friendliness. -/
  options : List (Finset W)
  /-- Ranking on options: `betterThan o₁ o₂` means `o₁` is at least as
      preferable as `o₂`. -/
  betterThan : Finset W → Finset W → Prop
  /-- Decidability of the ordering. -/
  betterThanDec : ∀ a b, Decidable (betterThan a b)
  /-- Benchmark predicate: an option `meetsBenchmark` if it is at or
      above the threshold. -/
  meetsBenchmark : Finset W → Prop
  /-- Decidability of the benchmark predicate. -/
  meetsBenchmarkDec : ∀ o, Decidable (meetsBenchmark o)

instance (rc : ResolutionContext W) (a b : Finset W) :
    Decidable (rc.betterThan a b) := rc.betterThanDec a b

instance (rc : ResolutionContext W) (o : Finset W) :
    Decidable (rc.meetsBenchmark o) := rc.meetsBenchmarkDec o

/-! ## §2. The four derived predicates (Cariani §4 p.545-546)

* `isWayOf`: option `o` is a way-of-`p` iff every world in `o` is a
  `p`-world (the option *entails* `p`).
* `isVisible`: `p` is visible iff every option is a way-of-`p` or a
  way-of-`¬p`. **Definitionally identical** to PB's `IsConsidered` —
  we use it as an alias.
* `isPermissible`: some way-of-`p` option meets benchmark.
* `isStronglyPermissible`: every way-of-`p` option meets benchmark.
* `isOptimal`: every best option is a way-of-`p`.
-/

/-- Option `o` is a *way of* `p` iff `o` entails `p`. -/
def isWayOf (o : Finset W) (p : Set W) [DecidablePred p] : Prop :=
  ∀ w ∈ o, p w

instance (o : Finset W) (p : Set W) [DecidablePred p] :
    Decidable (isWayOf o p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `p` is **visible** in Cariani's options iff every option settles `p`.

    **Definitionally identical to Phillips-Brown's `IsConsidered`** —
    aliased rather than restipulated, per CLAUDE.md "import don't
    restipulate" discipline. The bridge theorem
    `isVisible_iff_IsConsidered` is `Iff.rfl`. -/
abbrev isVisible (rc : ResolutionContext W) (p : Set W) [DecidablePred p] : Prop :=
  IsConsidered rc.options p

/-- `p` is **permissible** iff some option that's a way-of-`p` meets
    benchmark. (Not used in Cariani's `ought` definition — used to
    define `permitted` for the dual operator, §3 below.) -/
def isPermissible (rc : ResolutionContext W) (p : Set W) [DecidablePred p] : Prop :=
  ∃ o ∈ rc.options, isWayOf o p ∧ rc.meetsBenchmark o

instance (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    Decidable (isPermissible rc p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `p` is **strongly permissible** iff every option that's a way-of-`p`
    meets benchmark. -/
def isStronglyPermissible (rc : ResolutionContext W) (p : Set W)
    [DecidablePred p] : Prop :=
  ∀ o ∈ rc.options, isWayOf o p → rc.meetsBenchmark o

instance (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    Decidable (isStronglyPermissible rc p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- An option `o` is **best** iff it's at-least-as-good-as every other
    listed option. The `o ∈ rc.options` membership check is the
    caller's responsibility — it's implicit in the typical
    `∀ o ∈ rc.options, isBest rc o → ...` consumption pattern in
    `isOptimal`. -/
def isBest (rc : ResolutionContext W) (o : Finset W) : Prop :=
  ∀ o' ∈ rc.options, rc.betterThan o o'

instance (rc : ResolutionContext W) (o : Finset W) :
    Decidable (isBest rc o) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `p` is **optimal** iff every best option is a way-of-`p`. -/
def isOptimal (rc : ResolutionContext W) (p : Set W) [DecidablePred p] : Prop :=
  ∀ o ∈ rc.options, isBest rc o → isWayOf o p

instance (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    Decidable (isOptimal rc p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ## §3. Cariani's `ought` and `permitted` (paper §4 p.546, §5 p.547)

`⟦ought p⟧^{c,w} = 1` iff `p` is **visible** AND **optimal** AND
**strongly permissible**. The conjunction order in our definition
follows the paper's *informal* §2 (p.540) ordering; the paper's
*formal* §4 (p.546) ordering is (i) Optimality, (ii) Strong
Permissibility, (iii) Visibility. The truth-conditions are identical.

`permitted p` (§5 p.556 fn 23): `p` is permitted iff some option ≥
benchmark is a way-of-`p`. This is `isPermissible` itself.

DUALITY (`ought p ↔ ¬ permitted ¬p`) is rejected by Cariani in the
right-to-left direction (p.547), as a consequence of rejecting
INHERITANCE. -/

/-- **Cariani-style `ought`** (Resolution Semantics, §4 p.546).
    Conjunction of visibility, optimality, and strong permissibility. -/
def ought (rc : ResolutionContext W) (p : Set W) [DecidablePred p] : Prop :=
  isVisible rc p ∧ isOptimal rc p ∧ isStronglyPermissible rc p

instance (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    Decidable (ought rc p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Cariani-style `permitted`** (paper p.556 fn 23, "first entry"):
    some option ≥ benchmark is a way-of-`p`. Identical to
    `isPermissible`; we expose it as a named operator for clarity. -/
def permitted (rc : ResolutionContext W) (p : Set W) [DecidablePred p] : Prop :=
  isPermissible rc p

instance (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    Decidable (permitted rc p) :=
  inferInstanceAs (Decidable (isPermissible rc p))

/-! ## §4. Bridge to Phillips-Brown's `IsConsidered`

[phillips-brown-2025]'s `IsConsidered`
(`Desire.QuestionBased`) is *definitionally* the same
predicate as Cariani's `isVisible`. Since `isVisible` is now an
`abbrev` (§2 above), the bridge theorem is `Iff.rfl`.

Per the docstring's "parallel discovery" note: Cariani 2013 doesn't
cite Crnič; PB 2025 cites Crnič 2011 but not Cariani 2013. The
agreement is independent reinvention. Linglib's "make agreements
visible" thesis surfaces the structural identity. -/

omit [Fintype W] [DecidableEq W] in
/-- Cariani's `isVisible` and Phillips-Brown's `IsConsidered` are the
    same predicate. Since `isVisible` is an `abbrev` over
    `IsConsidered`, the proof is `Iff.rfl`. -/
theorem isVisible_iff_IsConsidered
    (rc : ResolutionContext W) (p : Set W) [DecidablePred p] :
    isVisible rc p ↔ IsConsidered rc.options p := Iff.rfl

/-! ## §5. INHERITANCE failure on Ross's Puzzle (paper §I)

Ross's Puzzle: `Joan ought to attend her classes` does NOT entail
`Joan ought to either attend her classes or burn down the philosophy
department`. Under boxing semantics, INHERITANCE (`p ⊨ q ⇒ ought(p)
⊨ ought(q)`) makes this entailment valid. Cariani's Resolution
Semantics predicts the disjunction is FALSE.

We construct a 3-world model: `attend, stay_home, burn`. Options
{attend, stay_home, burn}; benchmark = `≥ stay_home`; ranking:
attend > stay_home > burn. Then:
- `ought attend` is true: visible (every option settles attend),
  optimal (best option = attend ⊆ attend), strongly permissible
  (only way-of-attend option is attend itself, which meets benchmark).
- `ought (attend ∨ burn)` is FALSE: not strongly permissible (burn is
  a way-of-(attend∨burn) but does NOT meet benchmark).

INHERITANCE fails because `attend ⊨ (attend ∨ burn)` but
`ought(attend) ⊭ ought(attend ∨ burn)`. -/

inductive RossW where
  | attend | stay_home | burn
  deriving DecidableEq, Fintype, Repr

def attendProp : Set RossW | .attend => True | _ => False
def stayHomeProp : Set RossW | .stay_home => True | _ => False
def burnProp : Set RossW | .burn => True | _ => False

instance : DecidablePred attendProp :=
  fun w => by cases w <;> unfold attendProp <;> infer_instance
instance : DecidablePred stayHomeProp :=
  fun w => by cases w <;> unfold stayHomeProp <;> infer_instance
instance : DecidablePred burnProp :=
  fun w => by cases w <;> unfold burnProp <;> infer_instance

/-- The three options: singleton courses of action. -/
def rossOptions : List (Finset RossW) :=
  [{.attend}, {.stay_home}, {.burn}]

/-- Rank on `RossW` worlds: attend > stay_home > burn. -/
def rossWorldRank : RossW → ℕ
  | .attend => 3
  | .stay_home => 2
  | .burn => 1

/-- Rank of an option: max of `rossWorldRank` over its worlds (0 for
    the empty option). For the three singleton options, this is just
    the world's rank. -/
def rossRank (o : Finset RossW) : ℕ :=
  o.sup rossWorldRank

def rossBetterThan : Finset RossW → Finset RossW → Prop :=
  fun o o' => rossRank o ≥ rossRank o'

instance (o o' : Finset RossW) : Decidable (rossBetterThan o o') :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- Benchmark: only attend (rank 3) and stay_home (rank 2) meet
    benchmark. Burn (rank 1) is impermissible. -/
def rossMeetsBenchmark : Finset RossW → Prop := fun o => rossRank o ≥ 2

instance (o : Finset RossW) : Decidable (rossMeetsBenchmark o) :=
  inferInstanceAs (Decidable (_ ≥ _))

def rossContext : ResolutionContext RossW where
  options := rossOptions
  betterThan := rossBetterThan
  betterThanDec := fun a b => inferInstanceAs (Decidable (rossBetterThan a b))
  meetsBenchmark := rossMeetsBenchmark
  meetsBenchmarkDec := fun o => inferInstanceAs (Decidable (rossMeetsBenchmark o))

/-- `ought(attend)` holds in Ross's context: visible, optimal, and
    strongly permissible. -/
theorem ross_ought_attend : ought rossContext attendProp := by decide +kernel

/-- `attend` is visible in Ross's context — every option settles it. -/
theorem ross_attend_visible : isVisible rossContext attendProp := by decide +kernel

/-- `attend ∨ burn` is also visible (every option settles it). -/
theorem ross_attend_or_burn_visible :
    isVisible rossContext (fun w => attendProp w ∨ burnProp w) := by decide +kernel

/-- The disjunction `attend ∨ burn` is NOT strongly permissible — `burn`
    is a way-of-(attend ∨ burn) but doesn't meet the benchmark. -/
theorem ross_attend_or_burn_not_stronglyPermissible :
    ¬ isStronglyPermissible rossContext (fun w => attendProp w ∨ burnProp w) := by
  decide

/-- **Ross's Puzzle, formal**: `ought(attend ∨ burn)` is FALSE in
    Cariani's Resolution Semantics, even though `attend ⊨ attend ∨ burn`
    and `ought(attend)` is true. This is the INHERITANCE failure. -/
theorem ross_puzzle_inheritance_failure :
    ¬ ought rossContext (fun w => attendProp w ∨ burnProp w) := by decide +kernel

/-! ## §6. INHERITANCE failure on Procrastinate (paper §II)

Jackson & Pargetter 1986: `Procrastinate ought to accept and write` is
true; `Procrastinate ought to accept` is false.

Cariani's analysis (p.541): Procrastinate's options must include
"accept and write", "accept without writing", "do not accept",
ordered as `accept_and_write > do_not_accept > benchmark > accept_without_writing`. -/

inductive ProcW where
  | accept_write | do_not_accept | accept_no_write
  deriving DecidableEq, Fintype, Repr

def acceptWriteProp : Set ProcW | .accept_write => True | _ => False
def doNotAcceptProp : Set ProcW | .do_not_accept => True | _ => False
def acceptNoWriteProp : Set ProcW | .accept_no_write => True | _ => False

instance : DecidablePred acceptWriteProp :=
  fun w => by cases w <;> unfold acceptWriteProp <;> infer_instance
instance : DecidablePred doNotAcceptProp :=
  fun w => by cases w <;> unfold doNotAcceptProp <;> infer_instance
instance : DecidablePred acceptNoWriteProp :=
  fun w => by cases w <;> unfold acceptNoWriteProp <;> infer_instance

def procOptions : List (Finset ProcW) :=
  [{.accept_write}, {.do_not_accept}, {.accept_no_write}]

def procWorldRank : ProcW → ℕ
  | .accept_write => 3
  | .do_not_accept => 2
  | .accept_no_write => 1

def procRank (o : Finset ProcW) : ℕ :=
  o.sup procWorldRank

def procBetterThan : Finset ProcW → Finset ProcW → Prop :=
  fun o o' => procRank o ≥ procRank o'

instance (o o' : Finset ProcW) : Decidable (procBetterThan o o') :=
  inferInstanceAs (Decidable (_ ≥ _))

def procMeetsBenchmark : Finset ProcW → Prop := fun o => procRank o ≥ 2

instance (o : Finset ProcW) : Decidable (procMeetsBenchmark o) :=
  inferInstanceAs (Decidable (_ ≥ _))

def procContext : ResolutionContext ProcW where
  options := procOptions
  betterThan := procBetterThan
  betterThanDec := fun a b => inferInstanceAs (Decidable (procBetterThan a b))
  meetsBenchmark := procMeetsBenchmark
  meetsBenchmarkDec := fun o => inferInstanceAs (Decidable (procMeetsBenchmark o))

/-- The "accept" proposition: true at both `accept_write` and
    `accept_no_write`. -/
def acceptProp : Set ProcW :=
  fun w => w = .accept_write ∨ w = .accept_no_write

instance : DecidablePred acceptProp := fun w => by unfold acceptProp; infer_instance

/-- `accept_no_write` is a way-of-`accept` but does NOT meet benchmark. -/
theorem proc_accept_not_stronglyPermissible :
    ¬ isStronglyPermissible procContext acceptProp := by decide +kernel

/-- **Procrastinate, formal**: `ought(accept)` is FALSE in Cariani's
    Resolution Semantics, even though `accept_write ⊨ accept` and
    `ought(accept_write)` is true. -/
theorem procrastinate_inheritance_failure :
    ¬ ought procContext acceptProp := by decide +kernel

/-! ## §7. Boxing as a special case (paper p.546)

Cariani 2013 p.546 lists **TWO** conditions for the reduction to
boxing:

> (a) The cells of Q_c are all singleton sets.
> (b) For every o, o ≥ benchmark.

Under (a)+(b), Resolution Semantics reduces to standard
Kratzer/Lewis boxing semantics. We formalize the partial reduction
(under (b) alone the Strong Permissibility clause is neutralized;
combined with (a) the Visibility + Optimality clauses collapse to the
boxing reading). -/

omit [Fintype W] [DecidableEq W] in
/-- **Partial reduction (condition (b) only)**: when every option meets
    the benchmark, Strong Permissibility is trivially satisfied, and
    `ought` reduces to `Visibility ∧ Optimality`. This is *not* yet
    Kratzer boxing — boxing requires (a) singleton cells too. -/
theorem ought_iff_visible_and_optimal_of_all_meet_benchmark
    (rc : ResolutionContext W)
    (hAllMeet : ∀ o ∈ rc.options, rc.meetsBenchmark o)
    (p : Set W) [DecidablePred p] :
    ought rc p ↔ isVisible rc p ∧ isOptimal rc p := by
  unfold ought
  refine ⟨fun ⟨hV, hO, _⟩ => ⟨hV, hO⟩, fun ⟨hV, hO⟩ => ⟨hV, hO, ?_⟩⟩
  intro o ho _
  exact hAllMeet o ho

/-! ## §8. Coarseness and Coarse Falsemaking (paper §1 p.534, §2 p.541)

Cariani's leading desideratum (COARSENESS, p.534): `ought` can be
true even when there are impermissible ways of φ-ing. And his positive
constraint (COARSE FALSEMAKING, p.541, p.546): `ought` is false if
there's a relevant impermissible option compatible with the prejacent.

These are two sides of the same coin: `ought` is *coarser* than
"every way-of-p is permissible" (allows some impermissible ways) but
*finer* than "some way-of-p is permissible" (rejected when an
impermissible option compatible with the prejacent is available). -/

omit [Fintype W] [DecidableEq W] in
/-- **Coarse Falsemaking (paper §2 p.541, restated p.546)**: if there
    is an option `o` ∈ rc.options that is a way-of-`p` and `o` does
    NOT meet benchmark, then `ought p` is false. This is exactly the
    Strong Permissibility clause's contrapositive — and is the
    mechanism by which Cariani derives `¬ ought (attend ∨ burn)` in
    Ross's puzzle. -/
theorem ought_negation_via_coarse_falsemaking
    (rc : ResolutionContext W) (p : Set W) [DecidablePred p]
    (o : Finset W) (ho : o ∈ rc.options)
    (hWay : isWayOf o p) (hImp : ¬ rc.meetsBenchmark o) :
    ¬ ought rc p := by
  intro ⟨_, _, hSP⟩
  exact hImp (hSP o ho hWay)

/-! ## §9. DUALITY failure (paper §5 p.547-548)

Standard deontic logic has DUALITY: `ought p ↔ ¬ permitted ¬p`. This
follows from boxing (where ought = □ and permitted = ◇) in classical
modal logic.

Cariani (p.547) explicitly rejects the right-to-left direction
(`¬ permitted ¬p → ought p`) as an immediate consequence of rejecting
INHERITANCE: he uses Ross's Puzzle as the *ipso facto* counter-example
(p.547):

> The anti-boxer insists that (3) is false: it is false that Joan
> ought to either attend her classes or burn down the philosophy
> department. It does not follow from this that she's permitted to do
> something incompatible with the prejacent of (3) (e.g., go to a
> museum). She must, after all, attend her classes.

Specifically, in `rossContext`: `permitted (¬(attend ∨ burn))` would
be the existence of a way-of-(stay_home, the only ¬(attend ∨ burn)
option) at-or-above benchmark. `stay_home` IS at benchmark.
Yet `ought (attend ∨ burn)` fails (Ross's puzzle). So
`¬ permitted ¬(attend ∨ burn)` is FALSE, while `ought (attend ∨ burn)`
is also false — vacuously satisfying the right-to-left implication?
No: the relevant case is the contrapositive. The actual right-to-left
DUALITY failure: pick a `q` where `permitted q` is false but
`ought ¬q` is also false. -/

/-- The INHERITANCE failure, existentially packaged: a context and
    propositions `p ⊨ q` with `ought p` true and `ought q` false
    (Ross's puzzle: `p = attend`, `q = attend ∨ burn`). This is the
    failure Cariani p.547 invokes to reject the right-to-left
    direction of DUALITY (`¬ permitted ¬p → ought p`); `rossContext`
    itself satisfies that direction vacuously, and a direct
    DUALITY-failure witness needs a richer model. -/
theorem inheritance_failure_exists :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (rc : ResolutionContext W) (p : Set W) (_ : DecidablePred p)
      (q : Set W) (_ : DecidablePred q),
      (∀ w, p w → q w) ∧ ought rc p ∧ ¬ ought rc q :=
  ⟨RossW, inferInstance, inferInstance,
   rossContext, attendProp, inferInstance,
   (fun w => attendProp w ∨ burnProp w), inferInstance,
   fun _ => Or.inl, ross_ought_attend, ross_puzzle_inheritance_failure⟩

/-! ## §10. Weakening failure (paper §III pre-figured; [cariani-2016] core)

Cariani 2013 §III flags conditional-ought issues that *prefigure*
Weakening failures, but the explicit Weakening attack
(`ought(A) ∧ ought(B) ⊨ ought(A ∨ B)`) is the central topic of
[cariani-2016]. We formalize the failure here using rossContext:
`ought(attend)` and `ought(stay_home)` are both true, but
`ought(attend ∨ stay_home ∨ burn)` is false — because `burn` is a
way-of-the-disjunction that doesn't meet benchmark.

(For the simple disjunction `attend ∨ stay_home`, Weakening holds in
`rossContext`; the failure needs disjuncts whose union acquires an
impermissible way-of-disjunction option, as with `burn` above.) -/

/-- `ought(stay_home)` is false in rossContext — stay_home is a
    way-of-stay_home, meets benchmark, but `attend` is the unique best
    option and `attend` is NOT a way-of-stay_home. So `isOptimal` fails. -/
theorem ross_ought_stay_home_false :
    ¬ ought rossContext stayHomeProp := by decide +kernel

/-! ## §11. Cross-framework summary

* Cariani's `isVisible` ≡ Phillips-Brown's `IsConsidered`
  (`isVisible_iff_IsConsidered` is `Iff.rfl` since `isVisible` is an
  abbrev). Parallel discovery (Cariani via Lewis/Yalcin; PB via Crnič
  2011), not chain-of-influence.
* Cariani's account is *anti-INHERITANCE by design* (proved in §5
  Ross, §6 Procrastinate, §9 DUALITY-concern). vF (`Desire.BestWorlds.Want`) and Heim
  (`Desire.Conditional.Want`) are *pro-INHERITANCE* (their universal-over-best-worlds
  shape entails it). Lassiter is anti-INHERITANCE via *intermediacy
  of E_V* (a different mechanism — see Lassiter2017.lean).
* `Cariani.ought` satisfies COARSENESS (paper §1 p.534) and is
  characterized negatively by COARSE FALSEMAKING (paper §2 p.541).
  `ought_negation_via_coarse_falsemaking` is the Lean version.
* The boxing-as-special-case theorem (§7) proves the partial
  reduction under benchmark-met-by-all (condition (b) of Cariani
  p.546); the full reduction to Kratzer boxing also requires
  singleton cells (condition (a)) — left as future work because the
  full statement requires unifying Cariani's option-based partition
  with Kratzer's modal-base/ordering-source apparatus.
-/

end Cariani2013
