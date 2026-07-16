import Linglib.Semantics.Dynamic.State
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# [abramsky-sadrzadeh-2014]: Semantic Unification, sheaf-theoretically

[abramsky-sadrzadeh-2014] present a presheaf of basic DRSs over
vocabulary–variable contexts and cast anaphora resolution as sheaf
*gluing*: local literal-theories over parts of a discourse unify into a
global theory when a cover — the choice of which referents to merge —
admits a section restricting onto each part. The paper's Proposition 1
asserts that gluings are unique when they exist.

The formalization confirms the framework and sharpens the proposition.
Uniqueness holds for covers in which every literal of the glued context
factors through a single cover map (`isGluing_unique_of_factors`) — as
in all the paper's examples, where one map carries each semantic unit.
Without that hypothesis it fails: a binary literal whose arguments are
hit by *different* cover maps is invisible to every restriction, so two
theories differing by such a mixed literal glue the same family
(`exists_isGluing_ne` — a two-singleton cover of a two-variable
context). Existence can also fail, as the paper's negative-literal
example shows: merging *it* with *John* forces `Man` and `¬Man` on one
referent (`noGluing_merged`).

The closing section reads the substrate's information states
(`Semantics/Dynamic/State.lean`) through the paper's contextuality
frame: three pairwise-compatible anticorrelation states on a triangle of
bases admit no gluing at all (`no_gluing_triangle`) — local consistency
without a global section, in the model-theoretic fibers. Together with
the substrate's `exists_ne_of_restrict_eq` (non-uniqueness from
correlation), this locates the two sheaf-condition failures that
separate model-theoretic information from the paper's syntactic
theories.

## Main results

- `Theory.restrict_restrict`: functoriality of the paper's `F`.
- `subset_of_isGluing`: the pushforward union is the least gluing.
- `isGluing_unique_of_factors`: Proposition 1, under the factorization
  hypothesis its proof uses.
- `exists_isGluing_ne`: uniqueness fails without it.
- `noGluing_merged`: the paper's consistency-violation example.
- `no_gluing_triangle`: contextuality in the `State` fibers.
-/

namespace AbramskySadrzadeh2014

/-! ### Literals and theories -/

/-- A relational signature: symbols with arities. -/
structure Signature where
  /-- The relation symbols. -/
  Rel : Type
  /-- The arity of each symbol. -/
  ar : Rel → ℕ

variable {σ : Signature}

/-- A literal: a signed atomic formula, variables drawn from `ℕ`. -/
structure Literal (σ : Signature) where
  /-- The relation symbol. -/
  rel : σ.Rel
  /-- The argument variables. -/
  args : Fin (σ.ar rel) → ℕ
  /-- The sign. -/
  pos : Bool

/-- Substitution along a variable map. -/
def Literal.map (f : ℕ → ℕ) (l : Literal σ) : Literal σ :=
  ⟨l.rel, f ∘ l.args, l.pos⟩

@[simp] theorem Literal.map_id (l : Literal σ) : l.map id = l := rfl

theorem Literal.map_map (f g : ℕ → ℕ) (l : Literal σ) :
    (l.map f).map g = l.map (g ∘ f) := rfl

/-- The complementary literal. -/
def Literal.neg (l : Literal σ) : Literal σ := ⟨l.rel, l.args, !l.pos⟩

@[simp] theorem Literal.neg_map (f : ℕ → ℕ) (l : Literal σ) :
    (l.map f).neg = l.neg.map f := rfl

/-- The literal draws its symbol from `L` and its variables from `X`. -/
def Literal.Over (L : Finset σ.Rel) (X : Finset ℕ) (l : Literal σ) : Prop :=
  l.rel ∈ L ∧ ∀ i, l.args i ∈ X

/-- The paper's fibers `F(L, X)`: consistent theories of literals over
the context. The paper takes deductive closures of consistent *finite*
sets; for literal-only theories closure adds nothing and finiteness is
not load-bearing — the paper's own "could be finessed if necessary". -/
@[ext] structure Theory (σ : Signature) (L : Finset σ.Rel) (X : Finset ℕ) where
  /-- The literals held true. -/
  lits : Set (Literal σ)
  /-- Every literal is over the context. -/
  over : ∀ l ∈ lits, l.Over L X
  /-- No literal occurs with both signs. -/
  consistent : ∀ l ∈ lits, l.neg ∉ lits

variable {L L' : Finset σ.Rel} {X X' : Finset ℕ}

instance : Membership (Literal σ) (Theory σ L X) := ⟨fun s l => l ∈ s.lits⟩

/-- Restriction along a context morphism (the paper's `F(ι, f)`), by
substitution-preimage: `F(f)(s) ⊨ ±A(x̄) ⟺ s ⊨ ±A(f(x̄))`. -/
def Theory.restrict (f : ℕ → ℕ) (s : Theory σ L' X') (L : Finset σ.Rel)
    (X : Finset ℕ) : Theory σ L X where
  lits := {l | l.Over L X ∧ l.map f ∈ s.lits}
  over _ hl := hl.1
  consistent l hl hneg := s.consistent (l.map f) hl.2 hneg.2

@[simp] theorem Theory.mem_restrict {f : ℕ → ℕ} {s : Theory σ L' X'}
    {l : Literal σ} :
    l ∈ s.restrict f L X ↔ l.Over L X ∧ l.map f ∈ s.lits := Iff.rfl

/-- Functoriality of restriction, along composable context morphisms. -/
theorem Theory.restrict_restrict {L'' : Finset σ.Rel} {X'' : Finset ℕ}
    {f g : ℕ → ℕ} (hL : L ⊆ L') (hf : ∀ x ∈ X, f x ∈ X')
    (s : Theory σ L'' X'') :
    (s.restrict g L' X').restrict f L X = s.restrict (g ∘ f) L X := by
  ext l
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, ⟨⟨hL h1.1, fun i => hf _ (h1.2 i)⟩, h3⟩⟩

/-! ### Covers and gluing -/

variable {ι : Type*}

/-- The paper's covers: jointly surjective families of context
morphisms into `(L, X)`. -/
structure Cover (σ : Signature) (L : Finset σ.Rel) (X : Finset ℕ)
    (ι : Type*) where
  /-- The component vocabularies. -/
  Lpart : ι → Finset σ.Rel
  /-- The component variable contexts. -/
  Xpart : ι → Finset ℕ
  /-- The component variable maps. -/
  map : ι → ℕ → ℕ
  /-- Joint surjectivity on variables. -/
  jointlySurj : ∀ x ∈ X, ∃ i, ∃ y ∈ Xpart i, map i y = x

/-- `s` glues the family `F` over the cover: it restricts onto every
member (`F(fᵢ)(s) = sᵢ`). -/
def IsGluing (c : Cover σ L X ι)
    (F : ∀ i, Theory σ (c.Lpart i) (c.Xpart i)) (s : Theory σ L X) : Prop :=
  ∀ i, s.restrict (c.map i) (c.Lpart i) (c.Xpart i) = F i

/-- Any gluing contains every pushed-forward literal: the union of
pushforwards is the least gluing — the candidate of the paper's
Proposition 1. -/
theorem subset_of_isGluing {c : Cover σ L X ι}
    {F : ∀ i, Theory σ (c.Lpart i) (c.Xpart i)} {s : Theory σ L X}
    (hs : IsGluing c F s) (i : ι) {l : Literal σ} (hl : l ∈ F i) :
    l.map (c.map i) ∈ s.lits := by
  rw [← hs i] at hl
  exact hl.2

/-- **Proposition 1, with its implicit hypothesis**: gluings are unique
provided every literal over the glued context factors through a single
cover map — as in all the paper's examples. Membership of a factoring
literal is decided by the restriction it factors through. -/
theorem isGluing_unique_of_factors {c : Cover σ L X ι}
    {F : ∀ i, Theory σ (c.Lpart i) (c.Xpart i)} {s s' : Theory σ L X}
    (hFac : ∀ m : Literal σ, m.Over L X →
      ∃ i, ∃ l : Literal σ, l.Over (c.Lpart i) (c.Xpart i) ∧
        l.map (c.map i) = m)
    (hs : IsGluing c F s) (hs' : IsGluing c F s') : s = s' := by
  have key : ∀ (t t' : Theory σ L X), IsGluing c F t → IsGluing c F t' →
      t.lits ⊆ t'.lits := by
    intro t t' ht ht' m hm
    obtain ⟨i, l, hlover, hlm⟩ := hFac m (t.over m hm)
    have hlF : l ∈ F i := by
      rw [← ht i]
      exact ⟨hlover, hlm ▸ hm⟩
    have := subset_of_isGluing ht' i hlF
    rwa [hlm] at this
  exact Theory.ext (Set.Subset.antisymm (key s s' hs hs') (key s' s hs' hs))

/-! ### Uniqueness fails without factorization -/

/-- One binary relation symbol. -/
private abbrev sigB : Signature := ⟨Unit, fun _ => 2⟩

/-- The empty theory. -/
private def emptyTheory (L : Finset sigB.Rel) (X : Finset ℕ) :
    Theory sigB L X :=
  ⟨∅, fun _ h => h.elim, fun _ h => h.elim⟩

/-- The two-singleton cover of the two-variable context: each map hits
one variable. -/
private def twoCover : Cover sigB {()} {0, 1} Bool where
  Lpart _ := {()}
  Xpart _ := {0}
  map b := fun _ => if b then 1 else 0
  jointlySurj x hx := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨false, 0, by simp, rfl⟩
    · exact ⟨true, 0, by simp, (Finset.mem_singleton.mp hx).symm⟩

/-- The mixed literal `A(0, 1)`: its two arguments are hit by different
cover maps. -/
private abbrev mixed : Literal sigB := ⟨(), ![0, 1], true⟩

private def mixedTheory : Theory sigB {()} {0, 1} where
  lits := {mixed}
  over l hl := by
    rw [Set.mem_singleton_iff] at hl
    subst hl
    refine ⟨Finset.mem_singleton_self _, fun i => ?_⟩
    have h2 : ∀ i : Fin 2, (![0, 1] : Fin 2 → ℕ) i ∈ ({0, 1} : Finset ℕ) := by
      decide
    exact h2 i
  consistent l hl hneg := by
    rw [Set.mem_singleton_iff] at hl hneg
    subst hl
    simp [Literal.neg] at hneg

/-- The binary argument tuple of a `sigB`-literal. -/
private def bargs (m : Literal sigB) : Fin 2 → ℕ := m.args

/-- No literal over a single variable substitutes to the mixed literal:
its constant image cannot produce two distinct arguments. -/
private theorem not_map_eq_mixed (b : Bool) (l : Literal sigB)
    (hover : l.Over ({()} : Finset sigB.Rel) {0}) : l.map (twoCover.map b) ≠ mixed := by
  intro h
  have h0 := congrFun (congrArg bargs h) 0
  have h1 := congrFun (congrArg bargs h) 1
  simp only [bargs, Literal.map, Function.comp] at h0 h1
  rw [Finset.mem_singleton.mp (hover.2 0)] at h0
  rw [Finset.mem_singleton.mp (hover.2 1)] at h1
  rcases b <;> simp [twoCover] at h0 h1

/-- **Uniqueness fails without factorization**: the empty theories on
the two-singleton cover are glued both by the empty theory and by the
mixed-literal theory. Proposition 1's uniqueness claim needs the
factorization hypothesis. -/
theorem exists_isGluing_ne :
    ∃ s s' : Theory sigB {()} {0, 1},
      IsGluing twoCover (fun _ => emptyTheory {()} {0}) s ∧
      IsGluing twoCover (fun _ => emptyTheory {()} {0}) s' ∧ s ≠ s' := by
  refine ⟨emptyTheory _ _, mixedTheory, fun b => ?_, fun b => ?_, ?_⟩
  · ext l
    simp [Theory.restrict, emptyTheory]
  · ext l
    simp only [mixedTheory]
    constructor
    · rintro ⟨hover, hmap⟩
      exact absurd hmap (not_map_eq_mixed b l hover)
    · intro h
      exact absurd h (by simp [emptyTheory])
  · intro h
    have hmem : mixed ∈ (emptyTheory {()} ({0, 1} : Finset ℕ)).lits := by
      rw [h]
      exact rfl
    exact hmem

/-! ### Existence fails on inconsistency: the paper's example 3 -/

/-- Unary symbols for the paper's negative-literal example. -/
private inductive R3 | john | man | donkey
  deriving DecidableEq

private abbrev sigU : Signature := ⟨R3, fun _ => 1⟩

/-- `{John(x), Man(x)}`. -/
private def johnSection : Theory sigU {R3.john, R3.man} {0} where
  lits := {⟨R3.john, fun _ => 0, true⟩, ⟨R3.man, fun _ => 0, true⟩}
  over l hl := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by simp, fun _ => Finset.mem_singleton_self 0⟩
  consistent l hl hneg := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl hneg
    rcases hl with rfl | rfl <;> rcases hneg with h | h <;>
      simp [Literal.neg] at h

/-- `{donkey(y), ¬Man(y)}` — the pronoun *it* does not refer to men. -/
private def donkeySection : Theory sigU {R3.donkey, R3.man} {0} where
  lits := {⟨R3.donkey, fun _ => 0, true⟩, ⟨R3.man, fun _ => 0, false⟩}
  over l hl := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by simp, fun _ => Finset.mem_singleton_self 0⟩
  consistent l hl hneg := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl hneg
    rcases hl with rfl | rfl <;> rcases hneg with h | h <;>
      simp [Literal.neg] at h

/-- The cover that merges the two referents. -/
private def mergedCover :
    Cover sigU {R3.john, R3.man, R3.donkey} {5} Bool where
  Lpart b := if b then {R3.donkey, R3.man} else {R3.john, R3.man}
  Xpart _ := {0}
  map _ := fun _ => 5
  jointlySurj _ hx :=
    ⟨false, 0, Finset.mem_singleton_self 0, (Finset.mem_singleton.mp hx).symm⟩

private def mergedFamily : ∀ b : Bool,
    Theory sigU (mergedCover.Lpart b) (mergedCover.Xpart b)
  | true => donkeySection
  | false => johnSection

/-- **Existence fails on inconsistency** (the paper's example 3): the
cover merging *it* with *John* has no gluing — it would hold both
`Man` and `¬Man` of the merged referent. "A cover which merged x and y
would not have a gluing, since the consistency condition would be
violated." -/
theorem noGluing_merged : ¬ ∃ s, IsGluing mergedCover mergedFamily s := by
  rintro ⟨s, hs⟩
  have hMan : (⟨R3.man, fun _ => 0, true⟩ : Literal sigU).map (fun _ => 5) ∈
      s.lits :=
    subset_of_isGluing hs false (Set.mem_insert_of_mem _ rfl)
  have hNeg : (⟨R3.man, fun _ => 0, false⟩ : Literal sigU).map (fun _ => 5) ∈
      s.lits :=
    subset_of_isGluing hs true (Set.mem_insert_of_mem _ rfl)
  exact s.consistent _ hMan hNeg

/-! ### Contextuality in the model-theoretic fibers -/

open DynamicSemantics

/-- The anticorrelation state on two referents: points defining exactly
`{i, j}`, with distinct values. -/
private def anti (i j : Fin 3) : State Unit (Fin 3) Bool :=
  {p | p.dom = ({i, j} : Set (Fin 3)) ∧
    p.assignment i ≠ p.assignment j}

/-- A two-referent point. -/
private def pt2 (i j : Fin 3) (a b : Bool) :
    Possibility Unit (Fin 3) (Option Bool) :=
  ⟨(), fun v => if v = i then some a else if v = j then some b else none⟩

private theorem pt2_mem_anti {i j : Fin 3} (hij : i ≠ j) (a b : Bool)
    (hab : a ≠ b) : pt2 i j a b ∈ anti i j := by
  refine ⟨?_, ?_⟩
  · ext v
    by_cases hvi : v = i
    · simp [pt2, Possibility.dom, hvi]
    · by_cases hvj : v = j <;>
        simp [pt2, Possibility.dom, hvi, hvj, hij.symm]
  · simp only [pt2, if_neg hij.symm]
    exact fun h => hab (Option.some.injEq .. ▸ h :)

/-- Adjacent anticorrelation states are consistent: their Def. 26 merge
is inhabited — the pair glues. -/
private theorem merge_anti_nonempty {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    ((anti i j).merge (anti j k)).Nonempty := by
  refine ⟨(pt2 i j false true).union (pt2 j k true false),
    pt2 i j false true, pt2_mem_anti hij false true (by simp),
    pt2 j k true false, pt2_mem_anti hjk true false (by simp), ?_, rfl⟩
  refine ⟨rfl, fun v e e' he he' => ?_⟩
  simp only [pt2] at he he'
  split at he
  · rename_i hvi
    subst hvi
    rw [if_neg hij, if_neg hik] at he'
    exact absurd he' (by simp)
  · split at he
    · rename_i hvi hvj
      subst hvj
      rw [if_pos rfl] at he'
      have h1 : e = true := by
        have := he.symm
        simpa using this
      have h2 : e' = true := by
        have := he'.symm
        simpa using this
      rw [h1, h2]
    · exact absurd he (by simp)

/-- **Contextuality in the states** ([abramsky-sadrzadeh-2014]'s frame,
model-theoretically): the three anticorrelation constraints are pairwise
consistent — each pair merges (`merge_anti_nonempty`) — but no state
restricts onto all three: Boolean anticorrelation cannot hold on three
referents at once. Local consistency without a global section. -/
theorem no_gluing_triangle :
    ¬ ∃ S : State Unit (Fin 3) Bool,
      S.restrict {0, 1} = anti 0 1 ∧ S.restrict {1, 2} = anti 1 2 ∧
      S.restrict {0, 2} = anti 0 2 := by
  rintro ⟨S, h01, h12, h02⟩
  -- the target states are inhabited, so S is
  have hne : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with rfl | h
    · have : (∅ : State Unit (Fin 3) Bool) = anti 0 1 := by
        simpa [State.restrict] using h01
      exact absurd (this ▸ pt2_mem_anti (by decide) false true (by simp) :
        pt2 0 1 false true ∈ (∅ : State Unit (Fin 3) Bool)) (by simp)
    · exact h
  obtain ⟨r, hr⟩ := hne
  -- r's restrictions land in each anticorrelation state
  have key : ∀ (i j : Fin 3), S.restrict {i, j} = anti i j →
      ∃ a b : Bool, r.assignment i = some a ∧ r.assignment j = some b ∧
        a ≠ b := by
    intro i j hS
    have hmem : r.restrict {i, j} ∈ anti i j := by
      rw [← hS]
      exact ⟨r, hr, rfl⟩
    obtain ⟨hdom, hne⟩ := hmem
    rw [Possibility.dom_restrict] at hdom
    have hi : (r.assignment i).isSome := by
      have : i ∈ ({i, j} : Set (Fin 3)) ∩
          Possibility.dom r := by
        rw [hdom]
        simp
      exact this.2
    have hj : (r.assignment j).isSome := by
      have : j ∈ ({i, j} : Set (Fin 3)) ∩
          Possibility.dom r := by
        rw [hdom]
        simp
      exact this.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hi
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hj
    refine ⟨a, b, ha, hb, fun hab => ?_⟩
    subst hab
    apply hne
    have hri : (r.restrict {i, j}).assignment i = some a := by
      simpa [Possibility.restrict] using ha
    have hrj : (r.restrict {i, j}).assignment j = some a := by
      simpa [Possibility.restrict] using hb
    rw [hri, hrj]
  obtain ⟨a, b, ha, hb, hab⟩ := key 0 1 h01
  obtain ⟨b', c, hb', hc, hbc⟩ := key 1 2 h12
  obtain ⟨a', c', ha', hc', hac⟩ := key 0 2 h02
  rw [hb] at hb'
  rw [ha] at ha'
  rw [hc] at hc'
  obtain rfl := (Option.some.injEq .. ▸ hb' :)
  obtain rfl := (Option.some.injEq .. ▸ ha' :)
  obtain rfl := (Option.some.injEq .. ▸ hc' :)
  cases a <;> cases b <;> cases c <;> simp_all

end AbramskySadrzadeh2014
