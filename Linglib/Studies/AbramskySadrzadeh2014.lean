import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.ModelTheory.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Linglib.Data.Examples.AbramskySadrzadeh2014

/-!
# Semantic unification as sheaf gluing

Abramsky and Sadrzadeh model basic Discourse Representation Structures as a presheaf on a
category of contexts — a finite vocabulary of relation symbols with a finite set of variables —
and read anaphora resolution as sheaf gluing: the local theories of the parts of a discourse glue
along a cover (the choice of which discourse referents to identify) exactly when some global theory
restricts to each of them. `presheaf` is that functor, `Theory.restrict` its action on context
morphisms, and `Cover.IsGluing` the gluing condition for a jointly surjective family of context
morphisms, whose presieve is `Cover.presieve`.

The paper's Proposition 1 says gluings are unique when they exist, its proof building the candidate
`Cover.pushforward`. Uniqueness holds when every literal of the glued context factors through a
cover map (`Cover.IsGluing.unique`, `Cover.isSeparatedFor_of_factors`), as in the first example
(`snores_unique`), but fails on the paper's own second example, where `John(b)` is invisible to
every restriction and may be added to the listed gluing (`isGluing_beats_insert`,
`not_isSeparatedFor_beats`). What is unique is the least gluing: every gluing contains the
pushforward (`Cover.IsGluing.pushforward_subset`), which glues whenever the vocabularies are
pairwise disjoint and the cover maps injective (`Cover.isGluing_glue`). The two obstructions
otherwise both occur in the paper: overlapping vocabularies in the discussion example
(`not_exists_isGluing_overlap`) and inconsistency when *it* is merged with *John*
(`not_exists_isGluing_merged`); the four linguistic examples are decided by kernel computation
(`isGluing_snores`, `isGluing_beats`, `isGluing_grey`, `isGluing_broke`).

The probabilistic half composes the presheaf with the distribution functor `distribution R` of a
semiring `R`, whose gluing is `Cover.IsGluing (presheaf 𝓛 V ⋙ distribution R)`. The bananas
discourse instantiates the paper's ranking of covers by corpus frequencies: pushing the covering
distribution forward along the gluing map (`gluingDistribution`) makes *ripe bananas, cheeky
monkeys* the most likely resolution (`gluingDistribution_ripe`).

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
* [geach-1962]
-/

namespace AbramskySadrzadeh2014

open CategoryTheory FirstOrder

universe u v w r

section General

/-! ### Contexts and the presheaf of basic DRS -/

/-- A context `(L, X)`: a finite vocabulary of relation symbols and a finite set of variables. -/
structure Context (𝓛 : Language.{u, v}) (V : Type w) where
  /-- The vocabulary. -/
  vocab : Finset (Σ n, 𝓛.Relations n)
  /-- The variables. -/
  vars : Finset V

variable {𝓛 : Language.{u, v}} {V : Type w}

/-- A context morphism: an inclusion of vocabularies together with a map of variables. -/
structure Context.Hom (c c' : Context 𝓛 V) where
  /-- The vocabulary inclusion. -/
  incl : c.vocab ⊆ c'.vocab
  /-- The variable map. -/
  map : c.vars → c'.vars

instance : Category (Context 𝓛 V) where
  Hom := Context.Hom
  id c := ⟨subset_rfl, id⟩
  comp f g := ⟨f.incl.trans g.incl, g.map ∘ f.map⟩

/-- A literal over a context: a signed atomic formula `±A(x̄)`. -/
structure Literal (c : Context 𝓛 V) where
  /-- The relation symbol. -/
  rel : c.vocab
  /-- The argument variables. -/
  args : Fin rel.1.1 → c.vars
  /-- The sign. -/
  pos : Bool

namespace Literal

variable {c c' c'' : Context 𝓛 V}

/-- Literals as dependent triples. -/
def equivSigma (c : Context 𝓛 V) : Literal c ≃ Σ r : c.vocab, (Fin r.1.1 → c.vars) × Bool where
  toFun l := ⟨l.rel, l.args, l.pos⟩
  invFun l := ⟨l.1, l.2.1, l.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Substitution along a context morphism. -/
def map (f : c ⟶ c') (l : Literal c) : Literal c' :=
  ⟨⟨l.rel.1, f.incl l.rel.2⟩, f.map ∘ l.args, l.pos⟩

@[simp] theorem map_id (l : Literal c) : l.map (𝟙 c) = l := rfl

@[simp] theorem map_comp (f : c ⟶ c') (g : c' ⟶ c'') (l : Literal c) :
    l.map (f ≫ g) = (l.map f).map g := rfl

theorem map_injective {f : c ⟶ c'} (hf : Function.Injective f.map) :
    Function.Injective (map f) := by
  rintro ⟨⟨r, hr⟩, a, p⟩ ⟨⟨r', hr'⟩, a', p'⟩ h
  obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj h
  obtain rfl := Subtype.mk.inj h₁
  cases funext fun i => hf (congrFun (eq_of_heq h₂) i)
  rfl

/-- The complementary literal. -/
def neg (l : Literal c) : Literal c := ⟨l.rel, l.args, !l.pos⟩

@[simp] theorem neg_neg (l : Literal c) : l.neg.neg = l := by cases l; simp [neg]

@[simp] theorem neg_map (f : c ⟶ c') (l : Literal c) : (l.map f).neg = l.neg.map f := rfl

end Literal

/-- A consistent finite set of literals over a context — the paper's `F(L, X)`, whose deductive
closure adds no literals. -/
@[ext] structure Theory (c : Context 𝓛 V) where
  /-- The literals held true. -/
  lits : Finset (Literal c)
  /-- No literal occurs with both signs. -/
  consistent : ∀ l ∈ lits, l.neg ∉ lits

namespace Theory

variable {c c' : Context 𝓛 V}

instance : Bot (Theory c) := ⟨⟨∅, by simp⟩⟩

@[simp] theorem lits_bot : (⊥ : Theory c).lits = ∅ := rfl

end Theory

variable [DecidableEq V] [∀ n, DecidableEq (𝓛.Relations n)]

-- Compared through non-dependent data, which kernel `decide` evaluates on enumerated literals.
instance (c : Context 𝓛 V) : DecidableEq (Literal c) := fun l l' =>
  decidable_of_iff (l.rel.1 = l'.rel.1 ∧ List.ofFn l.args = List.ofFn l'.args ∧ l.pos = l'.pos) (by
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨⟨r, hr⟩, a, p⟩ := l
      obtain ⟨⟨r', hr'⟩, a', p'⟩ := l'
      obtain rfl : r = r' := h₁
      obtain rfl := List.ofFn_injective h₂
      obtain rfl := h₃
      rfl
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩)

instance (c : Context 𝓛 V) : Fintype (Literal c) := Fintype.ofEquiv _ (Literal.equivSigma c).symm

namespace Theory

variable {c c' : Context 𝓛 V}

instance : DecidableEq (Theory c) := fun _ _ => decidable_of_iff _ Theory.ext_iff.symm

/-- Restriction along a context morphism: `F(f)(s) ⊢ ±A(x̄) ⟺ s ⊢ ±A(f(x̄))`. -/
def restrict (f : c ⟶ c') (s : Theory c') : Theory c where
  lits := Finset.univ.filter fun l => l.map f ∈ s.lits
  consistent _ hl hn := s.consistent _ (Finset.mem_filter.1 hl).2 (Finset.mem_filter.1 hn).2

@[simp] theorem mem_restrict {f : c ⟶ c'} {s : Theory c'} {l : Literal c} :
    l ∈ (s.restrict f).lits ↔ l.map f ∈ s.lits := by simp [restrict]

end Theory

variable (𝓛 V) in
/-- The presheaf of basic DRS: theories at each context, restriction along context morphisms. -/
def presheaf : (Context 𝓛 V)ᵒᵖ ⥤ Type (max v w) where
  obj c := Theory c.unop
  map f := TypeCat.ofHom fun s => s.restrict f.unop

@[simp] theorem presheaf_obj (c : (Context 𝓛 V)ᵒᵖ) : (presheaf 𝓛 V).obj c = Theory c.unop := rfl

@[simp] theorem presheaf_map {c c' : (Context 𝓛 V)ᵒᵖ} (f : c ⟶ c') (s : Theory c.unop) :
    (presheaf 𝓛 V).map f s = s.restrict f.unop := rfl

/-! ### Covers and gluing -/

/-- A cover of a context: a jointly surjective family of context morphisms into it
(`⋃ Im fᵢ = X` and `L = ⋃ Lᵢ`). -/
structure Cover (c : Context 𝓛 V) (ι : Type*) where
  /-- The covering contexts. -/
  part : ι → Context 𝓛 V
  /-- The covering morphisms. -/
  map : ∀ i, part i ⟶ c
  exists_map_eq : ∀ x : c.vars, ∃ i y, (map i).map y = x
  exists_mem_vocab : ∀ r ∈ c.vocab, ∃ i, r ∈ (part i).vocab

namespace Cover

variable {c : Context 𝓛 V} {ι : Type*} (C : Cover c ι)

/-- The presieve of the covering morphisms. -/
abbrev presieve : Presieve c := Presieve.ofArrows C.part C.map

/-- `s` glues the family `x` over the cover: `P(fᵢ)(s) = xᵢ` for every `i`. -/
def IsGluing (P : (Context 𝓛 V)ᵒᵖ ⥤ Type*) (x : ∀ i, P.obj (Opposite.op (C.part i)))
    (s : P.obj (Opposite.op c)) : Prop :=
  ∀ i, P.map (C.map i).op s = x i

variable {C} {x : ∀ i, Theory (C.part i)} {s s' : Theory c}

instance [Fintype ι] : Decidable (C.IsGluing (presheaf 𝓛 V) x s) :=
  inferInstanceAs (Decidable (∀ i, s.restrict (C.map i) = x i))

/-- The paper's candidate gluing `{±A(fᵢ(x̄)) | ±A(x̄) ∈ sᵢ}`. -/
def pushforward [Fintype ι] (C : Cover c ι) (x : ∀ i, Theory (C.part i)) : Finset (Literal c) :=
  Finset.univ.biUnion fun i => (x i).lits.image (Literal.map (C.map i))

@[simp] theorem mem_pushforward [Fintype ι] {l : Literal c} :
    l ∈ C.pushforward x ↔ ∃ i, ∃ m ∈ (x i).lits, m.map (C.map i) = l := by
  simp [pushforward]

theorem IsGluing.pushforward_subset [Fintype ι] (hs : C.IsGluing (presheaf 𝓛 V) x s) :
    C.pushforward x ⊆ s.lits := by
  intro l hl
  obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
  rw [← hs i] at hm
  exact Theory.mem_restrict.1 hm

/-- Every literal over the glued context is the image of a literal over some part. -/
def Factors (C : Cover c ι) : Prop :=
  ∀ l : Literal c, ∃ i, ∃ m : Literal (C.part i), m.map (C.map i) = l

instance [Fintype ι] : Decidable C.Factors :=
  inferInstanceAs (Decidable (∀ l : Literal c, ∃ i, ∃ m : Literal (C.part i), m.map (C.map i) = l))

theorem IsGluing.lits_eq_pushforward [Fintype ι] (hC : C.Factors)
    (hs : C.IsGluing (presheaf 𝓛 V) x s) : s.lits = C.pushforward x :=
  subset_antisymm (fun l hl => by
      obtain ⟨i, m, rfl⟩ := hC l
      exact mem_pushforward.2 ⟨i, m, by rw [← hs i]; exact Theory.mem_restrict.2 hl, rfl⟩)
    hs.pushforward_subset

/-- Proposition 1, for covers through which every literal factors. -/
theorem IsGluing.unique [Fintype ι] (hC : C.Factors) (hs : C.IsGluing (presheaf 𝓛 V) x s)
    (hs' : C.IsGluing (presheaf 𝓛 V) x s') : s = s' :=
  Theory.ext ((hs.lits_eq_pushforward hC).trans (hs'.lits_eq_pushforward hC).symm)

/-- Proposition 1 in sheaf-theoretic terms: the presheaf is separated for a factoring cover. -/
theorem isSeparatedFor_of_factors [Fintype ι] (hC : C.Factors) :
    C.presieve.IsSeparatedFor (presheaf 𝓛 V) := fun x _ _ h h' =>
  IsGluing.unique hC (x := fun i => x _ (.mk i))
    ((Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows _ _ x _).1 h)
    ((Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows _ _ x _).1 h')

omit [DecidableEq V] [∀ n, DecidableEq (𝓛.Relations n)] in
theorem eq_of_map_eq (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    {i j : ι} {m : Literal (C.part i)} {m' : Literal (C.part j)}
    (h : m.map (C.map i) = m'.map (C.map j)) : i = j :=
  by_contra fun hij => Finset.disjoint_left.1 (hdisj hij) m.rel.2
    (by rw [show m.rel.1 = m'.rel.1 from congrArg (fun l : Literal c => l.rel.1) h]; exact m'.rel.2)

/-- With pairwise disjoint vocabularies and injective cover maps the pushforward is consistent. -/
def glue [Fintype ι] (C : Cover c ι)
    (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, Theory (C.part i)) : Theory c where
  lits := C.pushforward x
  consistent _ hl hn := by
    obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
    obtain ⟨j, m', hm', h⟩ := mem_pushforward.1 hn
    rw [Literal.neg_map] at h
    obtain rfl : i = j := (C.eq_of_map_eq hdisj h).symm
    exact (x i).consistent m hm (Literal.map_injective (hinj i) h ▸ hm')

/-- Under disjoint vocabularies and injective cover maps the pushforward glues: the only
obstruction to gluing is consistency, and it does not arise. -/
theorem isGluing_glue [Fintype ι]
    (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, Theory (C.part i)) :
    C.IsGluing (presheaf 𝓛 V) x (C.glue hdisj hinj x) := fun i =>
  Theory.ext (Finset.ext fun l => by
    simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict, glue, mem_pushforward]
    constructor
    · rintro ⟨j, m, hm, h⟩
      obtain rfl : i = j := (C.eq_of_map_eq hdisj h).symm
      exact Literal.map_injective (hinj i) h ▸ hm
    · exact fun hl => ⟨i, l, hl, rfl⟩)

end Cover

/-! ### The distribution functor -/

/-- Finitely supported `R`-weightings of `S` summing to `1` — the paper's `D_R(S)`. -/
def Distribution (R : Type r) [AddCommMonoid R] [One R] (S : Type u) : Type (max u r) :=
  {d : S →₀ R // d.sum (fun _ m => m) = 1}

namespace Distribution

variable {R : Type r} [AddCommMonoid R] [One R] {S T : Type u}

/-- The image distribution along a map. -/
noncomputable def map (f : S → T) (d : Distribution R S) : Distribution R T :=
  ⟨Finsupp.mapDomain f d.1, by
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]; exact d.2⟩

@[simp] theorem map_id (d : Distribution R S) : map id d = d := Subtype.ext Finsupp.mapDomain_id

theorem map_comp {U : Type u} (f : S → T) (g : T → U) (d : Distribution R S) :
    map (g ∘ f) d = map g (map f d) :=
  Subtype.ext Finsupp.mapDomain_comp

/-- The distribution proportional to a weighting with nonzero total. -/
noncomputable def ofWeights {ι : Type u} [Fintype ι] (w : ι → ℕ) (h : ∑ i, w i ≠ 0) :
    Distribution ℚ ι :=
  ⟨Finsupp.equivFunOnFinite.symm fun i => (w i : ℚ) / ∑ i, w i, by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp only [Finsupp.coe_equivFunOnFinite_symm, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 h)⟩

end Distribution

variable (R : Type r) [AddCommMonoid R] [One R] in
/-- The distribution functor `D_R`. -/
noncomputable def distribution : Type u ⥤ Type (max u r) where
  obj := Distribution R
  map f := TypeCat.ofHom (Distribution.map f)
  map_id _ := congrArg TypeCat.ofHom (funext fun d => by rw [hom_id]; exact Distribution.map_id d)
  map_comp f g := congrArg TypeCat.ofHom (funext fun d => by
    rw [hom_comp]; exact Distribution.map_comp f g d)

end General

/-! ### The paper's examples -/

/-- Relation symbols of the paper's examples, by arity. -/
inductive Rel : ℕ → Type
  | R : Rel 1
  | S : Rel 1
  | john : Rel 1
  | man : Rel 1
  | sleeps : Rel 1
  | snores : Rel 1
  | donkey : Rel 1
  | grey : Rel 1
  | cup : Rel 1
  | plate : Rel 1
  | banana : Rel 1
  | monkey : Rel 1
  | ripe : Rel 1
  | cheeky : Rel 1
  | owns : Rel 2
  | beats : Rel 2
  | broke : Rel 2
  | putOn : Rel 3
  | gave : Rel 3
  deriving DecidableEq

/-- The relational language of the examples. -/
abbrev lang : Language := ⟨fun _ => Empty, Rel⟩

/-- Variables of the paper's examples. -/
inductive Var | x | y | z | u | v | w | a | b
  deriving DecidableEq

/-- The literal `A(x̄)`, or `¬A(x̄)` for `pos := false`. -/
def lit {c : Context lang Var} {n : ℕ} (r : Rel n) (args : Fin n → Var) (pos : Bool := true)
    (hr : ⟨n, r⟩ ∈ c.vocab := by decide +kernel) (h : ∀ i, args i ∈ c.vars := by decide +kernel) :
    Literal c :=
  ⟨⟨⟨n, r⟩, hr⟩, fun i => ⟨args i, h i⟩, pos⟩

/-- The context morphism acting as `f` on variables. -/
def hom {c c' : Context lang Var} (f : Var → Var)
    (hf : ∀ t ∈ c.vars, f t ∈ c'.vars := by decide +kernel)
    (hL : c.vocab ⊆ c'.vocab := by decide +kernel) : c ⟶ c' :=
  ⟨hL, fun t => ⟨f t, hf t t.2⟩⟩

/-! #### Example 1: *John sleeps. He snores.* -/

/-- The glued context of the first example. -/
abbrev snoresCtx : Context lang Var := ⟨{⟨1, .john⟩, ⟨1, .sleeps⟩, ⟨1, .snores⟩}, {.z}⟩

/-- The cover `{x} ↦ z ↤ {y}` merging *he* with *John*. -/
def snoresCover : Cover snoresCtx (Fin 2) where
  part := ![⟨{⟨1, .john⟩, ⟨1, .sleeps⟩}, {.x}⟩, ⟨{⟨1, .snores⟩}, {.y}⟩]
  map
    | 0 => hom fun _ => .z
    | 1 => hom fun _ => .z
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- `s₁ = {John(x), sleeps(x)}`, `s₂ = {snores(y)}`. -/
def snoresSections : ∀ i, Theory (snoresCover.part i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .sleeps (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .snores (fun _ => .y)}, by decide +kernel⟩

/-- `s = {John(z), sleeps(z), snores(z)}`. -/
def snoresGluing : Theory snoresCtx :=
  ⟨{lit .john (fun _ => .z), lit .sleeps (fun _ => .z), lit .snores (fun _ => .z)},
    by decide +kernel⟩

theorem isGluing_snores : snoresCover.IsGluing (presheaf lang Var) snoresSections snoresGluing := by
  decide +kernel

/-- Every literal over `{z}` factors through the cover, so the gluing is unique. -/
theorem snores_unique {s : Theory snoresCtx}
    (hs : snoresCover.IsGluing (presheaf lang Var) snoresSections s) : s = snoresGluing :=
  hs.unique (by decide +kernel) isGluing_snores

/-! #### Example 2: *John beats his donkey.* -/

/-- The glued context of the second example. -/
abbrev beatsCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .donkey⟩, ⟨2, .owns⟩, ⟨2, .beats⟩}, {.a, .b}⟩

/-- The cover `x ↦ a`, `y ↦ b`, `u ↦ a, v ↦ b`. -/
def beatsCover : Cover beatsCtx (Fin 3) where
  part := ![⟨{⟨1, .john⟩}, {.x}⟩, ⟨{⟨1, .donkey⟩}, {.y}⟩, ⟨{⟨2, .owns⟩, ⟨2, .beats⟩}, {.u, .v}⟩]
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .b
    | 2 => hom fun | .u => .a | _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- `s₁ = {John(x)}`, `s₂ = {donkey(y)}`, `s₃ = {owns(u, v), beats(u, v)}`. -/
def beatsSections : ∀ i, Theory (beatsCover.part i)
  | 0 => ⟨{lit .john (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .donkey (fun _ => .y)}, by decide +kernel⟩
  | 2 => ⟨{lit .owns ![.u, .v], lit .beats ![.u, .v]}, by decide +kernel⟩

/-- `s = {John(a), donkey(b), owns(a, b), beats(a, b)}`. -/
def beatsGluing : Theory beatsCtx :=
  ⟨{lit .john (fun _ => .a), lit .donkey (fun _ => .b), lit .owns ![.a, .b], lit .beats ![.a, .b]},
    by decide +kernel⟩

theorem isGluing_beats : beatsCover.IsGluing (presheaf lang Var) beatsSections beatsGluing := by
  decide +kernel

/-- `s ∪ {John(b)}`: `John(b)` factors through no cover map, so adding it changes no
restriction and the listed gluing is not unique. -/
def beatsGluing' : Theory beatsCtx :=
  ⟨insert (lit .john (fun _ => .b)) beatsGluing.lits, by decide +kernel⟩

theorem isGluing_beats_insert :
    beatsCover.IsGluing (presheaf lang Var) beatsSections beatsGluing' := by
  decide +kernel

theorem not_isSeparatedFor_beats : ¬ beatsCover.presieve.IsSeparatedFor (presheaf lang Var) :=
  fun h => absurd (h.ext (t₁ := beatsGluing) (t₂ := beatsGluing') fun _ _ ⟨i⟩ =>
    (isGluing_beats i).trans (isGluing_beats_insert i).symm)
    (show beatsGluing ≠ beatsGluing' by decide +kernel)

/-! #### Example 3: *John owns a donkey. It is grey.* -/

/-- The glued context of the third example. -/
abbrev greyCtx : Context lang Var := ⟨{⟨1, .john⟩, ⟨1, .man⟩, ⟨1, .donkey⟩, ⟨1, .grey⟩}, {.a, .b}⟩

/-- The covering contexts of the third example. -/
def greyParts : Fin 3 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .man⟩}, {.x}⟩, ⟨{⟨1, .donkey⟩, ⟨1, .man⟩}, {.y}⟩, ⟨{⟨1, .grey⟩}, {.z}⟩]

/-- `s₁ = {John(x), Man(x)}`, `s₂ = {donkey(y), ¬Man(y)}`, `s₃ = {grey(z)}`. -/
def greySections : ∀ i, Theory (greyParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .man (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .donkey (fun _ => .y), lit .man (fun _ => .y) false}, by decide +kernel⟩
  | 2 => ⟨{lit .grey (fun _ => .z)}, by decide +kernel⟩

/-- The cover merging *it* with *John*: `x ↦ a`, `y ↦ a`, `z ↦ b`. -/
def mergedCover : Cover greyCtx (Fin 3) where
  part := greyParts
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .a
    | 2 => hom fun _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- Merging `x` and `y` forces `Man` and `¬Man` of one referent. -/
theorem not_exists_isGluing_merged :
    ¬ ∃ s, mergedCover.IsGluing (presheaf lang Var) greySections s := by
  rintro ⟨s, hs⟩
  exact s.consistent _
    (hs.pushforward_subset
      (Cover.mem_pushforward.2 ⟨0, lit .man (fun _ => .x), by decide +kernel, rfl⟩))
    (hs.pushforward_subset
      (Cover.mem_pushforward.2 ⟨1, lit .man (fun _ => .y) false, by decide +kernel, rfl⟩))

/-- The cover merging *it* with the donkey: `x ↦ a`, `y ↦ b`, `z ↦ b`. -/
def greyCover : Cover greyCtx (Fin 3) where
  part := greyParts
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .b
    | 2 => hom fun _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- `s = {John(a), Man(a), donkey(b), ¬Man(b), grey(b)}`. -/
def greyGluing : Theory greyCtx :=
  ⟨{lit .john (fun _ => .a), lit .man (fun _ => .a), lit .donkey (fun _ => .b),
    lit .man (fun _ => .b) false, lit .grey (fun _ => .b)}, by decide +kernel⟩

theorem isGluing_grey : greyCover.IsGluing (presheaf lang Var) greySections greyGluing := by
  decide +kernel

/-! #### Example 4: *John put the cup on the plate. He broke it.* -/

/-- The glued context of the fourth example. -/
abbrev brokeCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .cup⟩, ⟨1, .plate⟩, ⟨3, .putOn⟩, ⟨2, .broke⟩}, {.x, .y, .z}⟩

/-- The covering contexts of the fourth example. -/
def brokeParts : Fin 2 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .cup⟩, ⟨1, .plate⟩, ⟨3, .putOn⟩}, {.x, .y, .z}⟩, ⟨{⟨2, .broke⟩}, {.u, .v}⟩]

/-- `s₁ = {John(x), Cup(y), Plate(z), PutOn(x, y, z)}`, `s₂ = {Broke(u, v)}`. -/
def brokeSections : ∀ i, Theory (brokeParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .cup (fun _ => .y), lit .plate (fun _ => .z),
      lit .putOn ![.x, .y, .z]}, by decide +kernel⟩
  | 1 => ⟨{lit .broke ![.u, .v]}, by decide +kernel⟩

/-- The two plausible antecedents of *it*. -/
inductive Broken | cup | plate
  deriving DecidableEq, Fintype

/-- The referent of each antecedent. -/
def Broken.var : Broken → Var
  | cup => .y
  | plate => .z

theorem Broken.var_mem (b : Broken) : b.var ∈ brokeCtx.vars := by cases b <;> decide +kernel

/-- The cover extending the identity on `{x, y, z}` by `u ↦ x` and `v ↦` the chosen antecedent. -/
def brokeCover (b : Broken) : Cover brokeCtx (Fin 2) where
  part := brokeParts
  map
    | 0 => hom id
    | 1 => hom (fun | .u => .x | _ => b.var) fun t _ => by cases t <;> cases b <;> decide +kernel
  exists_map_eq := by cases b <;> decide +kernel
  exists_mem_vocab := by decide +kernel

/-- `{John(x), Cup(y), Plate(z), PutOn(x, y, z), Broke(x, ·)}` with the chosen antecedent. -/
def brokeGluing (b : Broken) : Theory brokeCtx :=
  ⟨{lit .john (fun _ => .x), lit .cup (fun _ => .y), lit .plate (fun _ => .z),
    lit .putOn ![.x, .y, .z],
    lit .broke ![.x, b.var] (h := Fin.forall_fin_two.2 ⟨by cases b <;> decide +kernel, b.var_mem⟩)},
    by cases b <;> decide +kernel⟩

/-- Either choice of antecedent yields a gluing. -/
theorem isGluing_broke :
    ∀ b, (brokeCover b).IsGluing (presheaf lang Var) brokeSections (brokeGluing b) := by
  decide +kernel

/-! #### The discussion example: overlapping vocabularies -/

/-- The glued context of the discussion example. -/
abbrev overlapCtx : Context lang Var := ⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.z, .w}⟩

/-- The cover `x ↦ z, u ↦ w` and `y ↦ z, v ↦ w`, both parts carrying the whole vocabulary. -/
def overlapCover : Cover overlapCtx (Fin 2) where
  part := ![⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.x, .u}⟩, ⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.y, .v}⟩]
  map
    | 0 => hom fun | .x => .z | _ => .w
    | 1 => hom fun | .y => .z | _ => .w
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- `s₁ = {R(x), S(u)}`, `s₂ = {S(y), R(v)}`. -/
def overlapSections : ∀ i, Theory (overlapCover.part i)
  | 0 => ⟨{lit .R (fun _ => .x), lit .S (fun _ => .u)}, by decide +kernel⟩
  | 1 => ⟨{lit .S (fun _ => .y), lit .R (fun _ => .v)}, by decide +kernel⟩

/-- The sections are consistent but do not glue: `S(z)` restricts to `S(x) ∉ s₁`. -/
theorem not_exists_isGluing_overlap :
    ¬ ∃ s, overlapCover.IsGluing (presheaf lang Var) overlapSections s := by
  rintro ⟨s, hs⟩
  have h : lit .S (fun _ => .z) ∈ s.lits :=
    hs.pushforward_subset
      (Cover.mem_pushforward.2 ⟨1, lit .S (fun _ => .y), by decide +kernel, rfl⟩)
  have h' : lit .S (fun _ => .x) ∈ (overlapSections 0).lits := by
    rw [← hs 0]; exact Theory.mem_restrict.2 h
  exact absurd h' (by decide +kernel)

/-! #### Probabilistic anaphora: *John gave the bananas to the monkeys. They were ripe. They were
cheeky.* -/

/-- The glued context of the bananas discourse. -/
abbrev ripeCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .banana⟩, ⟨1, .monkey⟩, ⟨3, .gave⟩, ⟨1, .ripe⟩, ⟨1, .cheeky⟩}, {.x, .y, .z}⟩

/-- The covering contexts of the bananas discourse. -/
def ripeParts : Fin 3 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .banana⟩, ⟨1, .monkey⟩, ⟨3, .gave⟩}, {.x, .y, .z}⟩,
    ⟨{⟨1, .ripe⟩}, {.u}⟩, ⟨{⟨1, .cheeky⟩}, {.v}⟩]

/-- `s₁ = {John(x), Banana(y), Monkey(z), Gave(x, y, z)}`, `s₂ = {Ripe(u)}`, `s₃ = {Cheeky(v)}`. -/
def ripeSections : ∀ i, Theory (ripeParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .banana (fun _ => .y), lit .monkey (fun _ => .z),
      lit .gave ![.x, .y, .z]}, by decide +kernel⟩
  | 1 => ⟨{lit .ripe (fun _ => .u)}, by decide +kernel⟩
  | 2 => ⟨{lit .cheeky (fun _ => .v)}, by decide +kernel⟩

/-- The antecedents available to each *they*. -/
inductive Antecedent | banana | monkey
  deriving DecidableEq, Fintype

/-- The referent of each antecedent. -/
def Antecedent.var : Antecedent → Var
  | banana => .y
  | monkey => .z

theorem Antecedent.var_mem (a : Antecedent) : a.var ∈ ripeCtx.vars := by
  cases a <;> decide +kernel

/-- The covering `c` extending the identity on `{x, y, z}` by `u ↦ c.1` and `v ↦ c.2`. -/
def ripeCover (c : Antecedent × Antecedent) : Cover ripeCtx (Fin 3) where
  part := ripeParts
  map
    | 0 => hom id
    | 1 => hom (fun _ => c.1.var) fun _ _ => c.1.var_mem
    | 2 => hom (fun _ => c.2.var) fun _ _ => c.2.var_mem
  exists_map_eq := by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The candidate global section `t_c` induced by the covering `c`. -/
def ripeGluing (c : Antecedent × Antecedent) : Theory ripeCtx :=
  ⟨{lit .john (fun _ => .x), lit .banana (fun _ => .y), lit .monkey (fun _ => .z),
    lit .gave ![.x, .y, .z], lit .ripe (fun _ => c.1.var) (h := fun _ => c.1.var_mem),
    lit .cheeky (fun _ => c.2.var) (h := fun _ => c.2.var_mem)},
    by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> decide +kernel⟩

theorem isGluing_ripe :
    ∀ c, (ripeCover c).IsGluing (presheaf lang Var) ripeSections (ripeGluing c) := by
  decide +kernel

theorem ripeGluing_injective : Function.Injective ripeGluing := by decide +kernel

/-- British News corpus frequencies of *ripe banana* and *ripe monkey*. -/
def ripeFrequency : Antecedent → ℕ
  | .banana => 14
  | .monkey => 0

/-- British News corpus frequencies of *cheeky banana* and *cheeky monkey*. -/
def cheekyFrequency : Antecedent → ℕ
  | .banana => 0
  | .monkey => 10

/-- Each covering weighted by the summed frequencies of its mergings, normalised. -/
noncomputable def coveringDistribution : Distribution ℚ (Antecedent × Antecedent) :=
  Distribution.ofWeights (fun c => ripeFrequency c.1 + cheekyFrequency c.2) (by decide)

/-- The distribution `d` over global sections: the covering distribution pushed forward along
`c ↦ t_c`. -/
noncomputable def gluingDistribution : Distribution ℚ (Theory ripeCtx) :=
  (distribution ℚ).map (TypeCat.ofHom ripeGluing) coveringDistribution

theorem coveringDistribution_apply (c : Antecedent × Antecedent) :
    coveringDistribution.1 c = (ripeFrequency c.1 + cheekyFrequency c.2 : ℚ) / 48 := by
  simp [coveringDistribution, Distribution.ofWeights,
    show ∑ c : Antecedent × Antecedent, (ripeFrequency c.1 + cheekyFrequency c.2) = 48 from rfl]

theorem gluingDistribution_apply (c : Antecedent × Antecedent) :
    gluingDistribution.1 (ripeGluing c) = (ripeFrequency c.1 + cheekyFrequency c.2 : ℚ) / 48 := by
  rw [← coveringDistribution_apply]
  exact Finsupp.mapDomain_apply ripeGluing_injective _ _

/-- *Ripe bananas, cheeky monkeys* (`t₂`) is the most likely resolution, with probability `1/2`. -/
theorem gluingDistribution_ripe :
    gluingDistribution.1 (ripeGluing (.banana, .monkey)) = 1 / 2 ∧
      ∀ c, gluingDistribution.1 (ripeGluing c) ≤ 1 / 2 := by
  simp only [gluingDistribution_apply]
  exact ⟨by norm_num [ripeFrequency, cheekyFrequency],
    fun ⟨a, b⟩ => by cases a <;> cases b <;> norm_num [ripeFrequency, cheekyFrequency]⟩

end AbramskySadrzadeh2014
