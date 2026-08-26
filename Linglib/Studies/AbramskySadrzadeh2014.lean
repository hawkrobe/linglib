import Linglib.Semantics.Dynamic.DRS.Gluing
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
restricts to each of them. The presheaf is `DRT.presheaf`, covers and gluing are `DRT.Cover` and
`DRT.Cover.IsGluing`, and the paper's reading of a cover as DRT's merge followed by unification of
referents is `DRT.Cover.coe_conditions_toDRS_glue`.

The paper's Proposition 1 says gluings are unique when they exist, its proof building the candidate
`DRT.Cover.pushforward`. Uniqueness holds when every literal of the glued context factors through
a cover map (`DRT.Cover.IsGluing.unique`), as in the first example (`snores_unique`), but fails on
the paper's own second example, where `John(b)` is invisible to every restriction and may be added
to the listed gluing (`isGluing_beats_insert`, `not_isSeparatedFor_beats`). What is unique is the
least gluing, which glues whenever the vocabularies are pairwise disjoint and the cover maps
injective (`DRT.Cover.isGluing_glue`); the two obstructions otherwise both occur in the paper:
overlapping vocabularies in the discussion example (`not_exists_isGluing_overlap`) and
inconsistency when *it* is merged with *John* (`not_exists_isGluing_merged`). The four linguistic
examples are decided by kernel computation (`isGluing_snores`, `isGluing_beats`, `isGluing_grey`,
`isGluing_broke`).

The probabilistic half composes the presheaf with the distribution functor `distribution R` of a
semiring `R`, whose gluing is `DRT.Cover.IsGluing (DRT.presheaf L V ⋙ distribution R)`. The
bananas discourse instantiates the paper's ranking of covers by corpus frequencies: pushing the
covering distribution forward along the gluing map (`gluingDistribution`) makes *ripe bananas,
cheeky monkeys* the most likely resolution (`gluingDistribution_ripe`).

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
* [geach-1962]
-/

namespace AbramskySadrzadeh2014

open CategoryTheory FirstOrder DRT

universe u r

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
