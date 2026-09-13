import Linglib.Phonology.Prosody.Grid

/-!
# Prince (1983): Relating to the Grid

This file formalizes [prince-1983]'s case that the metrical grid alone, without the labelled
tree, carries the theory of stress. The Relative Prominence Projection Rule of
[liberman-prince-1977] reads a grid off an s/w-labelled tree, and for a uniformly labelled tree
it says exactly what the End Rule says, that the rightmost (leftmost) terminal of every
constituent is the strongest, so the labelling does no work (`SWTree.uniformWS_rppr_iff`). On the
grid two entries clash when they are adjacent at a level with no entry one level down between
them, and the Rhythm Rule is Move x, the sliding of a clashing entry within its level to the
nearest landing site; that the peak of a phrase never moves follows from the continuity of
columns, since sliding an entry out from under a taller column leaves a hole
(`Marks.not_isContinuous_move`, `moveXL_getD_peak`). The universal theory of word stress is
built from the End Rule at an edge and a level, extrametricality, Perfect Grid Construction
sweeping in a direction from a peak or a trough, and the bipositional representation of heavy
syllables. The four alternating patterns of (62) are the clash-free sweeps over an unstressed
word (`pg_replicate_getD`, `noClash_pg_replicate`); Garawa's stress never falls directly after
the initial main stress because the sweep is blocked by clash (`garawa_second`); Winnebago's
stress on the third syllable is the extrametricality variant of a trough-first sweep, and no
other setting of the parameters gives it (`third_syllable_iff`); heavy syllables never clash
(`noClash_qs`); and the three kinds of quantity-sensitive system without alternation of (97),
at both edges, give the main-stress theorems for the seven systems of (98) and §3.7, from
Khalkha (`khalkha_heavy`) to Malayalam, whose second-syllable stress is the End Rule blocked by
clash (`malayalam_second`).

## Implementation notes

A grid is the substrate's `Prosody.Grid`, a list of column heights, so the Continuous Column
Constraint holds by construction; the rendered rows of marks enter only in the argument that Move
x cannot move a peak. The End Rule is indexed by the level it maps into and applies to the highest
level present below it, the reading the paper settles on in §3.7; without Forward Clash Override
it withholds a promotion that would clash. Perfect Grid Construction is a greedy sweep that
raises a column when neither neighbour is stressed, the paper's maximal organization up to
clash, a trough start being a sweep that behaves as if a stress preceded the edge. Right-to-left
sweeps, the final edge of extrametricality, and rightward Move x are the mirror images of the
left-to-right versions. Syllable weights are the substrate's mora counts, and a syllable of two
or more moras is bipositional.

## TODO

The Hawaiian derivation (64), Mora Sluicing, the Forward Clash Override option of Perfect Grid
Construction, the bounding of Move x in §2.2, the feet of §4, and the pitch-accent systems of §5
are not formalized.

## References

* [prince-1983]
* [liberman-prince-1977]
-/

namespace Prince1983

open Prosody Prosody.Grid

/-! ### Trees, the Relative Prominence Projection Rule, and the End Rule (§1.3, §2.1) -/

/-- An s/w-labelled binary metrical tree whose terminals carry their grid column heights. -/
inductive SWTree
  | leaf (h : ℕ)
  | ws (w s : SWTree)
  | sw (s w : SWTree)
  deriving DecidableEq, Repr

namespace SWTree

/-- The column heights of the terminals, left to right: the grid over the tree. -/
def heights : SWTree → Grid
  | leaf h => [h]
  | ws w s => heights w ++ heights s
  | sw s w => heights s ++ heights w

/-- `H(N)`: the height of the head terminal, reached from the root through strong daughters. -/
def headHeight : SWTree → ℕ
  | leaf h => h
  | ws _ s => headHeight s
  | sw s _ => headHeight s

/-- The heights of the terminals other than the head. -/
def weakHeights : SWTree → List ℕ
  | leaf _ => []
  | ws w s => heights w ++ weakHeights s
  | sw s w => weakHeights s ++ heights w

theorem mem_heights {t : SWTree} {h : ℕ} :
    h ∈ heights t ↔ h = headHeight t ∨ h ∈ weakHeights t := by
  induction t with
  | leaf x => simp [heights, headHeight, weakHeights]
  | ws w s _ ihs => simp [heights, headHeight, weakHeights, ihs, or_left_comm]
  | sw s w ihs _ => simp [heights, headHeight, weakHeights, ihs, or_assoc]

theorem headHeight_mem (t : SWTree) : headHeight t ∈ heights t := mem_heights.2 (Or.inl rfl)

/-- The terminals are the head and the others. -/
theorem heights_perm (t : SWTree) : (heights t).Perm (headHeight t :: weakHeights t) := by
  induction t with
  | leaf _ => exact List.Perm.refl _
  | ws w s _ ihs =>
    simp only [heights, headHeight, weakHeights]
    exact (ihs.append_left _).trans List.perm_middle
  | sw s w ihs _ =>
    simpa only [heights, headHeight, weakHeights, List.cons_append] using ihs.append_right _

/-- The Relative Prominence Projection Rule (7): in every pair of sisters, `H(s) > H(w)`. -/
def Rppr : SWTree → Prop
  | leaf _ => True
  | ws w s => Rppr w ∧ Rppr s ∧ headHeight w < headHeight s
  | sw s w => Rppr s ∧ Rppr w ∧ headHeight w < headHeight s

/-- The head of a constituent is stronger than each of its other terminals. -/
def HeadStrong (t : SWTree) : Prop := ∀ h ∈ weakHeights t, h < headHeight t

/-- The head is strongest in every constituent. -/
def HeadStrongest : SWTree → Prop
  | leaf _ => True
  | ws w s => HeadStrongest w ∧ HeadStrongest s ∧ HeadStrong (ws w s)
  | sw s w => HeadStrongest s ∧ HeadStrongest w ∧ HeadStrong (sw s w)

theorem HeadStrong.le {t : SWTree} (ht : HeadStrong t) {h : ℕ} (hh : h ∈ heights t) :
    h ≤ headHeight t := by
  rcases mem_heights.1 hh with rfl | hw
  · exact le_rfl
  · exact (ht h hw).le

theorem HeadStrongest.headStrong {t : SWTree} (h : HeadStrongest t) : HeadStrong t := by
  cases t with
  | leaf _ => simp [HeadStrong, weakHeights]
  | ws _ _ => exact h.2.2
  | sw _ _ => exact h.2.2

/-- The RPPR, a condition on sisters, says that the head is strongest in every constituent. -/
theorem rppr_iff_headStrongest (t : SWTree) : Rppr t ↔ HeadStrongest t := by
  induction t with
  | leaf _ => exact Iff.rfl
  | ws w s ihw ihs =>
    simp only [Rppr, HeadStrongest, ihw, ihs, HeadStrong, weakHeights, headHeight,
      List.mem_append]
    refine and_congr_right λ hw => and_congr_right λ hs => ⟨λ hlt h hh => ?_, λ h => ?_⟩
    · rcases hh with hh | hh
      · exact (hw.headStrong.le hh).trans_lt hlt
      · exact hs.headStrong h hh
    · exact h _ (Or.inl (headHeight_mem w))
  | sw s w ihs ihw =>
    simp only [Rppr, HeadStrongest, ihw, ihs, HeadStrong, weakHeights, headHeight,
      List.mem_append]
    refine and_congr_right λ hs => and_congr_right λ hw => ⟨λ hlt h hh => ?_, λ h => ?_⟩
    · rcases hh with hh | hh
      · exact hs.headStrong h hh
      · exact (hw.headStrong.le hh).trans_lt hlt
    · exact h _ (Or.inr (headHeight_mem w))

/-- Under the RPPR the grid is culminative: the head terminal is its unique peak. -/
theorem isCulminative_of_rppr {t : SWTree} (h : Rppr t) : IsCulminative (heights t) := by
  have hs := ((rppr_iff_headStrongest t).1 h).headStrong
  have hpeak : peak (heights t) = headHeight t :=
    le_antisymm (peak_le λ x hx => hs.le hx) (le_peak (headHeight_mem t))
  rw [IsCulminative, hpeak, (heights_perm t).countP_eq, List.countP_cons_of_pos (by simp),
    List.countP_eq_zero.2 λ x hx => by simpa using (hs x hx).ne]

/-- The height of the rightmost terminal. -/
def lastHeight : SWTree → ℕ
  | leaf h => h
  | ws _ s => lastHeight s
  | sw _ w => lastHeight w

/-- The heights of all terminals but the rightmost. -/
def initHeights : SWTree → List ℕ
  | leaf _ => []
  | ws w s => heights w ++ initHeights s
  | sw s w => heights s ++ initHeights w

theorem heights_eq (t : SWTree) : heights t = initHeights t ++ [lastHeight t] := by
  induction t with
  | leaf _ => rfl
  | ws w s _ ihs => simp [heights, initHeights, lastHeight, ihs]
  | sw s w _ ihw => simp [heights, initHeights, lastHeight, ihw]

/-- The End Rule (13), right-hand version: in every constituent the rightmost terminal is
stronger than every other terminal. -/
def EndRuleRight : SWTree → Prop
  | leaf _ => True
  | ws w s => EndRuleRight w ∧ EndRuleRight s ∧
      ∀ h ∈ initHeights (ws w s), h < lastHeight (ws w s)
  | sw s w => EndRuleRight s ∧ EndRuleRight w ∧
      ∀ h ∈ initHeights (sw s w), h < lastHeight (sw s w)

/-- Uniform `[w s]` labelling: every constituent is strong on the right. -/
def UniformWS : SWTree → Prop
  | leaf _ => True
  | ws w s => UniformWS w ∧ UniformWS s
  | sw _ _ => False

theorem UniformWS.headHeight_eq {t : SWTree} (h : UniformWS t) :
    headHeight t = lastHeight t := by
  induction t with
  | leaf _ => rfl
  | ws w s _ ihs => exact ihs h.2
  | sw _ _ _ _ => exact h.elim

theorem UniformWS.weakHeights_eq {t : SWTree} (h : UniformWS t) :
    weakHeights t = initHeights t := by
  induction t with
  | leaf _ => rfl
  | ws w s _ ihs => simp [weakHeights, initHeights, ihs h.2]
  | sw _ _ _ _ => exact h.elim

/-- Under uniform `[w s]` labelling the RPPR says exactly what the End Rule says, so the
labelling of nonterminals does no work. -/
theorem uniformWS_rppr_iff {t : SWTree} (h : UniformWS t) : Rppr t ↔ EndRuleRight t := by
  rw [rppr_iff_headStrongest]
  induction t with
  | leaf _ => exact Iff.rfl
  | ws w s ihw ihs =>
    simp only [HeadStrongest, EndRuleRight, ihw h.1, ihs h.2, HeadStrong, weakHeights,
      initHeights, headHeight, lastHeight, h.2.weakHeights_eq, h.2.headHeight_eq]
  | sw _ _ _ _ => exact h.elim

/-- The mirror image of a tree. -/
def reverse : SWTree → SWTree
  | leaf h => leaf h
  | ws w s => sw s.reverse w.reverse
  | sw s w => ws w.reverse s.reverse

@[simp] theorem heights_reverse (t : SWTree) : heights t.reverse = (heights t).reverse := by
  induction t <;> simp [reverse, heights, *]

@[simp] theorem headHeight_reverse (t : SWTree) : headHeight t.reverse = headHeight t := by
  induction t <;> simp [reverse, headHeight, *]

theorem rppr_reverse (t : SWTree) : Rppr t.reverse ↔ Rppr t := by
  induction t <;> simp [reverse, Rppr, *, and_left_comm]

/-- Uniform `[s w]` labelling: every constituent is strong on the left. -/
def UniformSW (t : SWTree) : Prop := UniformWS t.reverse

/-- The End Rule (13), left-hand version: the leftmost terminal is strongest in every
constituent, the mirror image of the right-hand version. -/
def EndRuleLeft (t : SWTree) : Prop := EndRuleRight t.reverse

/-- Uniform `[s w]` labelling under the RPPR is the left-hand End Rule. -/
theorem uniformSW_rppr_iff {t : SWTree} (h : UniformSW t) : Rppr t ↔ EndRuleLeft t :=
  (rppr_reverse t).symm.trans (uniformWS_rppr_iff h)

end SWTree

/-! ### Clash and Move x (§2.2) -/

/-- Columns `i < j` clash at level `n` (27): both reach level `n` and no column between them
reaches level `n - 1`. -/
def Clash (g : Grid) (n i j : ℕ) : Prop :=
  i < j ∧ n ≤ g.getD i 0 ∧ n ≤ g.getD j 0 ∧ ∀ k < j, i < k → g.getD k 0 + 1 < n

instance (g : Grid) (n i j : ℕ) : Decidable (Clash g n i j) := by unfold Clash; infer_instance

/-- A eurhythmic grid: no clash at any level from `2` up to the peak. -/
def NoClash (g : Grid) : Prop :=
  ∀ n ≤ peak g, 2 ≤ n → ∀ i < g.length, ∀ j < g.length, ¬ Clash g n i j

instance (g : Grid) : Decidable (NoClash g) := by unfold NoClash; infer_instance

/-- A grid of stresses and unstressed columns with no two stresses adjacent is eurhythmic. -/
theorem noClash_of_alternating {g : Grid} (h : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2)
    (hadj : ∀ i, i + 1 < g.length → g.getD i 0 < 2 ∨ g.getD (i + 1) 0 < 2) : NoClash g := by
  rintro n hn h2 i hi j hj ⟨hij, hni, hnj, hk⟩
  have hp : peak g ≤ 2 := peak_le λ x hx => (h x hx).2
  obtain rfl : n = 2 := by omega
  rcases Nat.lt_or_ge (i + 1) j with hlt | hge
  · have h1 := hk (i + 1) hlt (Nat.lt_succ_self i)
    have h2 := (h _ (List.getElem_mem (show i + 1 < g.length by omega))).1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i + 1 < g.length by omega)]
      at h1
    simp at h1
    omega
  · obtain rfl : j = i + 1 := by omega
    rcases hadj i hj with h' | h' <;> omega

/-- A direction of sweep or movement, `D = {LR, RL}` of (119). -/
inductive Dir
  | lr
  | rl
  deriving DecidableEq, Repr

/-- The landing site of a leftward move at level `n` from column `i`: the nearest column to the
left with an entry at level `n - 1` and none at level `n`. -/
def landing? (g : Grid) (n i : ℕ) : Option ℕ :=
  (List.range i).reverse.find? λ k => g.getD k 0 == n - 1

/-- The leftmost column that clashes at level `n` with a column to its right. -/
def clashing? (g : Grid) (n : ℕ) : Option ℕ :=
  (List.range g.length).find? λ i => (List.range g.length).any λ j => decide (Clash g n i j)

/-- Leftward Move x at level `n`: the left member of the first clash slides within its level to
the landing site, provided its column has no entry above level `n`. -/
def moveXL (n : ℕ) (g : Grid) : Grid :=
  match clashing? g n with
  | none => g
  | some i =>
    if g.getD i 0 = n then
      match landing? g n i with
      | none => g
      | some k => (g.set i (n - 1)).set k n
    else g

/-- Move x(D;L) ((119f)): the rightward rule is the mirror image of the leftward one. -/
def moveX : Dir → ℕ → Grid → Grid
  | .rl, n, g => moveXL n g
  | .lr, n, g => (moveXL n g.reverse).reverse

/-- Sliding one mark within row `r` from column `i` to column `k`. -/
def Marks.move (r i k : ℕ) (m : Marks) : Marks :=
  m.modify r λ row => (row.set i false).set k true

/-- (32): sliding the level-`n` entry out of a column that reaches above level `n` leaves a
hole, so no such move is available on well-formed grids. -/
theorem Marks.not_isContinuous_move {g : Grid} {n i k : ℕ} (hi : i < g.length) (hn : n < g[i])
    (hn1 : 1 ≤ n) (hk : k ≠ i) : ¬ Marks.IsContinuous (Marks.move (n - 1) i k (rows g)) := by
  intro h
  have hlen : n < peak g := lt_of_lt_of_le hn (le_peak (List.getElem_mem hi))
  have h1 : n - 1 + 1 = n := by omega
  have hm := Marks.isContinuous_iff.1 h (n - 1)
  simp only [Marks.move, List.length_modify, rows, List.length_map, List.length_range, h1,
    List.getElem_modify_ne _ _ (show n - 1 ≠ n by omega), List.getElem_modify_eq,
    List.getElem_map, List.getElem_range, List.length_set] at hm
  have := hm hlen i (by simpa using hi) (by simpa using hi)
  simp [List.getElem_set_ne hk, hn] at this

/-- The absolute peak never moves (31): a clash at the peak's level would need a second peak. -/
theorem moveXL_getD_peak {g : Grid} (hc : IsCulminative g) {i n : ℕ} (hi : i < g.length)
    (hp : g[i] = peak g) : (moveXL n g).getD i 0 = g[i] := by
  have hgi : g.getD i 0 = g[i] := by simp [List.getD_eq_getElem?_getD, hi]
  unfold moveXL
  split
  · exact hgi
  · rename_i i' hi'
    have hmem := List.mem_of_find?_eq_some hi'
    have hp' := List.find?_some hi'
    simp only [List.mem_range] at hmem
    obtain ⟨j, hj, hcl⟩ := List.any_eq_true.1 hp'
    simp only [List.mem_range, decide_eq_true_eq] at hj hcl
    obtain ⟨hij, hni, hnj, -⟩ := hcl
    split
    · rename_i hn
      split
      · exact hgi
      · rename_i k hk
        have hki : k < i' := by
          have := List.mem_of_find?_eq_some hk
          simpa [List.mem_range] using this
        have hkv : g.getD k 0 = n - 1 := by simpa using List.find?_some hk
        have hgj : g.getD j 0 = g[j] := by simp [List.getD_eq_getElem?_getD, hj]
        have hgi' : g.getD i' 0 = g[i'] := by simp [List.getD_eq_getElem?_getD, hmem]
        have hle := le_peak (List.getElem_mem hmem)
        have hii' : i ≠ i' := by
          rintro rfl
          have hj' : g[j] = peak g := le_antisymm (le_peak (List.getElem_mem hj)) (by omega)
          exact absurd (hc.eq_of_eq_peak hi hj hp hj') (by omega)
        have hik : i ≠ k := by
          rintro rfl
          have : g[i'] = peak g := by omega
          exact hii' (hc.eq_of_eq_peak hi hmem hp this)
        simp [List.getD_eq_getElem?_getD, hii'.symm, hik.symm, hi]
    · exact hgi

/-! ### The End Rule, extrametricality, and Perfect Grid Construction (§3.2, §3.3) -/

/-- The edge a rule refers to, `E = {Initial, Final}` of (119). -/
inductive Edge
  | initial
  | final
  deriving DecidableEq, Repr

/-! #### The last index -/

/-- The last index whose element satisfies `p`. -/
def lastIdx? (p : ℕ → Bool) : List ℕ → Option ℕ
  | [] => none
  | x :: l => ((lastIdx? p l).map (· + 1)).or (if p x then some 0 else none)

@[simp] theorem lastIdx?_nil (p : ℕ → Bool) : lastIdx? p [] = none := rfl

theorem lastIdx?_cons (p : ℕ → Bool) (x : ℕ) (l : List ℕ) :
    lastIdx? p (x :: l) = ((lastIdx? p l).map (· + 1)).or (if p x then some 0 else none) := rfl

theorem lastIdx?_cons_of_some {p : ℕ → Bool} {l : List ℕ} {i : ℕ} (h : lastIdx? p l = some i)
    (x : ℕ) : lastIdx? p (x :: l) = some (i + 1) := by
  simp [lastIdx?_cons, h]

theorem lastIdx?_append (p : ℕ → Bool) (l₁ l₂ : List ℕ) :
    lastIdx? p (l₁ ++ l₂) = ((lastIdx? p l₂).map (· + l₁.length)).or (lastIdx? p l₁) := by
  induction l₁ with
  | nil => simp
  | cons x l ih =>
    rw [List.cons_append, lastIdx?_cons, lastIdx?_cons, ih]
    cases lastIdx? p l₂ <;> cases lastIdx? p l <;> simp [Nat.add_assoc]

theorem lastIdx?_eq_some {p : ℕ → Bool} {l : List ℕ} {i : ℕ} (h : lastIdx? p l = some i) :
    ∃ hi : i < l.length, p l[i] = true := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    rw [lastIdx?_cons] at h
    cases hl : lastIdx? p l with
    | none =>
      rw [hl] at h
      split_ifs at h with hx <;> simp only [Option.map_none, Option.none_or,
        Option.some.injEq, reduceCtorEq] at h
      exact ⟨by simp [← h], by simpa [← h] using hx⟩
    | some j =>
      rw [hl] at h
      obtain ⟨hj, hpj⟩ := ih hl
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at h
      exact ⟨by simp; omega, by simpa [← h] using hpj⟩

theorem lastIdx?_eq_none {p : ℕ → Bool} {l : List ℕ} :
    lastIdx? p l = none ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [lastIdx?_cons, Option.or_eq_none_iff, Option.map_eq_none_iff, ih]
    split_ifs with hx <;> simp [hx]

/-! #### The End Rule -/

/-- The edge-most column reaching level `n`. -/
def edgeIdx? : Edge → ℕ → Grid → Option ℕ
  | .initial, n, g => g.findIdx? (n ≤ ·)
  | .final, n, g => lastIdx? (n ≤ ·) g

/-- The End Rule ER(E;L;FCO) ((16), (97), (119a)): the edge-most entry at the highest level
present below `L` is promoted one level, so that the edge-most stress of a constituent becomes
its main stress and, absent stresses, its edge syllable is stressed. Without Forward Clash
Override the promotion is withheld when it would clash. -/
def endRule (e : Edge) (L : ℕ) (fco : Bool) (g : Grid) : Grid :=
  let n := min (L - 1) (peak g)
  match edgeIdx? e n g with
  | none => g
  | some i =>
    let g' := g.set i (max (g.getD i 0) (n + 1))
    if fco ∨ ∀ j < g.length, ¬ Clash g' (n + 1) i j ∧ ¬ Clash g' (n + 1) j i then g' else g

/-- Extrametricality elm(E) ((119c)): the edge column is invisible to the rule applied inside. -/
def elm : Edge → (Grid → Grid) → Grid → Grid
  | .initial, f, [] => f []
  | .initial, f, x :: t => x :: f t
  | .final, f, g => f g.dropLast ++ g.drop (g.length - 1)

/-- One sweep of Perfect Grid Construction: a column rises to the stress level when neither
neighbour reaches it, `prev` being the height of the column just passed. A trough start is a
sweep that behaves as if a stress preceded the edge. -/
def sweep : ℕ → Grid → Grid
  | _, [] => []
  | prev, x :: t =>
    let x' := if x < 2 ∧ prev < 2 ∧ t.headD 0 < 2 then 2 else x
    x' :: sweep x' t

/-- Whether a sweep starts at a peak or a trough, `A` of (119b). -/
inductive Altitude
  | peak
  | trough
  deriving DecidableEq, Repr

/-- The height a sweep pretends to have passed before its first column. -/
def Altitude.start : Altitude → ℕ
  | .peak => 0
  | .trough => 2

/-- Perfect Grid Construction PG(D;A) ((61), (62), (119b)): a clash-free, maximally alternating
stress level laid down by a sweep in direction `D` starting from a peak or a trough. -/
def pg (d : Dir) (a : Altitude) (g : Grid) : Grid :=
  match d with
  | .lr => sweep a.start g
  | .rl => (sweep a.start g.reverse).reverse

/-- The alternating stress level: `2, 1, 2, …` from a peak or `1, 2, 1, …` from a trough. -/
def alt : Bool → ℕ → Grid
  | _, 0 => []
  | b, n + 1 => (if b then 2 else 1) :: alt (!b) n

@[simp] theorem alt_length (b : Bool) (n : ℕ) : (alt b n).length = n := by
  induction n generalizing b <;> simp [alt, *]

theorem alt_getD (b : Bool) (n i : ℕ) :
    (alt b n).getD i 0 = if i < n then (if (i % 2 = 0 ↔ b = true) then 2 else 1) else 0 := by
  induction n generalizing b i with
  | zero => simp [alt]
  | succ n ih =>
    cases i with
    | zero => cases b <;> simp [alt]
    | succ i =>
      rw [alt, List.getD_cons_succ, ih]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> cases b <;>
        simp [h, Nat.succ_mod_two_eq_zero_iff]

theorem sweep_replicate (p n : ℕ) : sweep p (List.replicate n 1) = alt (p < 2) n := by
  induction n generalizing p with
  | zero => simp [sweep, alt]
  | succ n ih =>
    have hd : (List.replicate n 1).headD 0 < 2 := by cases n <;> simp [List.replicate_succ]
    rw [List.replicate_succ, sweep, alt]
    simp only [hd, and_true, Nat.one_lt_ofNat, true_and, ih]
    by_cases hp : p < 2 <;> simp [hp]

theorem sweep_replicate_append (p m : ℕ) :
    sweep p (List.replicate (m + 1) 1 ++ [2]) = alt (p < 2) m ++ [1, 2] := by
  induction m generalizing p with
  | zero => simp [sweep, alt]
  | succ m ih =>
    have h2 := ih 2
    have h1 := ih 1
    rw [List.replicate_succ, List.cons_append] at h1 h2
    rw [List.replicate_succ, List.cons_append, sweep, alt]
    simp only [List.replicate_succ, List.cons_append, List.headD_cons, Nat.one_lt_ofNat,
      true_and, and_true]
    by_cases hp : p < 2
    · simp [hp, h2]
    · simp [hp, h1]

/-- The distance of column `i` from the edge a sweep starts at. -/
def Dir.dist : Dir → ℕ → ℕ → ℕ
  | .lr, _, i => i
  | .rl, n, i => n - 1 - i

private theorem getD_reverse (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    l.reverse.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  simp [List.getD_eq_getElem?_getD, hi, List.getElem_reverse,
    List.getElem?_eq_getElem (show l.length - 1 - i < l.length by omega)]

/-- (62): a sweep over an unstressed word stresses the columns whose distance from the starting
edge has the parity of the start, a peak stressing the even distances. Weri is (62d), sweeping
right to left from a peak; Warao, (62c); Maranungku, (62b); Southern Paiute, (62a). -/
theorem pg_replicate_getD (d : Dir) (a : Altitude) {n i : ℕ} (hi : i < n) :
    (pg d a (List.replicate n 1)).getD i 0 =
      if (d.dist n i % 2 = 0 ↔ a = .peak) then 2 else 1 := by
  cases d with
  | lr =>
    cases a <;> simp only [pg, Altitude.start, sweep_replicate] <;> rw [alt_getD] <;>
      simp [hi, Dir.dist]
  | rl =>
    cases a <;> simp only [pg, Altitude.start, List.reverse_replicate, sweep_replicate] <;>
      rw [getD_reverse _ (by simpa using hi), alt_getD] <;>
      simp [Dir.dist, show n - 1 - i < n by omega]

/-- Perfect Grid Construction is clash-free. -/
theorem noClash_pg_replicate (d : Dir) (a : Altitude) (n : ℕ) :
    NoClash (pg d a (List.replicate n 1)) := by
  have hlen : (pg d a (List.replicate n 1)).length = n := by
    cases d <;> simp [pg, sweep_replicate]
  refine noClash_of_alternating (λ x hx => ?_) λ i hi => ?_
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have := pg_replicate_getD d a (hlen ▸ hi)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this]
    split_ifs <;> omega
  · have hi' : i + 1 < n := hlen ▸ hi
    rw [pg_replicate_getD d a (by omega), pg_replicate_getD d a hi']
    cases d <;> cases a <;> simp [Dir.dist] <;> (try split_ifs) <;> omega

private theorem edgeIdx?_getD {e : Edge} {n : ℕ} {g : Grid} {i : ℕ} (h : edgeIdx? e n g = some i) :
    i < g.length ∧ n ≤ g.getD i 0 := by
  cases e with
  | initial =>
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    exact ⟨hi, by simpa [List.getD_eq_getElem?_getD, hi] using hp⟩
  | final =>
    obtain ⟨hi, hp⟩ := lastIdx?_eq_some h
    exact ⟨hi, by simpa [List.getD_eq_getElem?_getD, hi] using hp⟩

/-- The End Rule at the level just above the peak: the edge-most peak column is promoted, and no
clash can arise. -/
theorem endRule_of_peak {e : Edge} {L : ℕ} {fco : Bool} {g : Grid} (hL : peak g ≤ L - 1)
    {i : ℕ} (hi : edgeIdx? e (peak g) g = some i) :
    endRule e L fco g = g.set i (peak g + 1) := by
  obtain ⟨hil, hpi⟩ := edgeIdx?_getD hi
  have hn : min (L - 1) (peak g) = peak g := min_eq_right hL
  have hgi : g.getD i 0 = peak g :=
    le_antisymm (by simpa [List.getD_eq_getElem?_getD, hil] using le_peak (List.getElem_mem hil))
      hpi
  simp only [endRule, hn, hi, hgi, Nat.max_eq_right (Nat.le_succ _)]
  rw [if_pos]
  refine Or.inr λ j _ => ⟨λ hc => ?_, λ hc => ?_⟩
  · obtain ⟨hij, -, hj, -⟩ := hc
    have hle : g[j]?.getD 0 ≤ peak g := by
      rcases lt_or_ge j g.length with hjl | hjl
      · simpa [List.getElem?_eq_getElem hjl] using le_peak (List.getElem_mem hjl)
      · simp [List.getElem?_eq_none hjl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij.ne] at hj
    omega
  · obtain ⟨hji, hj, -, -⟩ := hc
    have hle : g[j]?.getD 0 ≤ peak g := by
      rcases lt_or_ge j g.length with hjl | hjl
      · simpa [List.getElem?_eq_getElem hjl] using le_peak (List.getElem_mem hjl)
      · simp [List.getElem?_eq_none hjl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hji.ne'] at hj
    omega

theorem peak_replicate_one {n : ℕ} (hn : 0 < n) : peak (List.replicate n 1) = 1 :=
  le_antisymm (peak_le λ x hx => by simp [List.eq_of_mem_replicate hx])
    (le_peak (List.mem_replicate.2 ⟨hn.ne', rfl⟩))

/-- Stressing the first syllable of an unstressed word. -/
theorem endRule_initial_replicate {n : ℕ} (hn : 0 < n) (fco : Bool) :
    endRule .initial 2 fco (List.replicate n 1) = 2 :: List.replicate (n - 1) 1 := by
  rw [endRule_of_peak (by rw [peak_replicate_one hn]) (i := 0), peak_replicate_one hn]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    simp [List.replicate_succ]
  · rw [peak_replicate_one hn]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    simp [edgeIdx?, List.replicate_succ, List.findIdx?_cons]

/-! ### Garawa and Winnebago (63), (65) -/

/-- Garawa (63): the End Rule stresses the initial syllable, Perfect Grid Construction sweeps
right to left from a trough, and the End Rule at word level makes the initial stress the main
stress. -/
def garawa (n : ℕ) : Grid :=
  endRule .initial 3 false (pg .rl .trough (endRule .initial 2 false (List.replicate n 1)))

theorem garawa_eq {n : ℕ} (hn : 2 ≤ n) :
    garawa n = 3 :: 1 :: (alt false (n - 2)).reverse := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : endRule .initial 2 false (List.replicate (m + 2) 1) = 2 :: List.replicate (m + 1) 1 :=
    endRule_initial_replicate (by omega) false
  have h2 : pg .rl .trough (2 :: List.replicate (m + 1) 1) = 2 :: 1 :: (alt false m).reverse := by
    simp [pg, Altitude.start, List.reverse_cons, List.reverse_replicate, sweep_replicate_append]
  have hpeak : peak (2 :: 1 :: (alt false m).reverse) = 2 := by
    refine le_antisymm (peak_le λ x hx => ?_) (le_peak (by simp))
    simp only [List.mem_cons, List.mem_reverse] at hx
    rcases hx with rfl | rfl | hx
    · exact le_rfl
    · exact one_le_two
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
      have := alt_getD false m j
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
      rw [this]; split_ifs <;> omega
  rw [garawa, h1, h2, endRule_of_peak (by rw [hpeak]) (i := 0)]
  · simp [hpeak]
  · simp [hpeak, edgeIdx?, List.findIdx?_cons]

/-- Garawa's main stress is initial. -/
theorem garawa_initial {n : ℕ} (hn : 2 ≤ n) : (garawa n).getD 0 0 = 3 := by
  rw [garawa_eq hn]; rfl

/-- "Nonprimary stress may never occur on syllables directly following the main stress": the
sweep is blocked next to the initial stress by clash. -/
theorem garawa_second {n : ℕ} (hn : 2 ≤ n) : (garawa n).getD 1 0 = 1 := by
  rw [garawa_eq hn]; rfl

/-- Secondary stress on the penult, and alternating back from it. -/
theorem garawa_getD {n i : ℕ} (hi : 2 ≤ i) (hin : i < n) :
    (garawa n).getD i 0 = if (n - 1 - i) % 2 = 1 then 2 else 1 := by
  obtain ⟨i, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [garawa_eq (by omega), List.getD_cons_succ, List.getD_cons_succ,
    getD_reverse _ (by simp; omega), alt_getD, alt_length]
  have h1 : n - 2 - 1 - i < n - 2 := by omega
  have h2 : n - 2 - 1 - i = n - 1 - (i + 2) := by omega
  rw [if_pos h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (n - 1 - (i + 2)) with h | h <;> simp [h]

/-- Winnebago (65): with the initial syllable extrametrical, a trough-first sweep from the left
and the End Rule at word level put main stress on the third syllable. -/
def winnebago (n : ℕ) : Grid :=
  endRule .initial 3 false (elm .initial (pg .lr .trough) (List.replicate n 1))

theorem winnebago_eq {n : ℕ} (hn : 3 ≤ n) :
    winnebago n = 1 :: 1 :: 3 :: alt false (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : elm .initial (pg .lr .trough) (List.replicate (m + 3) 1)
      = 1 :: 1 :: 2 :: alt false m := by
    rw [List.replicate_succ]
    simp only [elm, pg, Altitude.start, sweep_replicate]
    simp [alt]
  have hpeak : peak (1 :: 1 :: 2 :: alt false m) = 2 := by
    refine le_antisymm (peak_le λ x hx => ?_) (le_peak (by simp))
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact one_le_two
    · exact one_le_two
    · exact le_rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
      have := alt_getD false m j
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
      rw [this]; split_ifs <;> omega
  rw [winnebago, h1, endRule_of_peak (by rw [hpeak]) (i := 2)]
  · simp [hpeak]
  · simp [hpeak, edgeIdx?, List.findIdx?_cons]

/-- The stress systems of an unstressed word from Perfect Grid Construction, with or without an
extrametrical initial syllable: the parameter space of §3.2. -/
def alternating (d : Dir) (a : Altitude) (x : Bool) (n : ℕ) : Grid :=
  (if x then elm .initial (pg d a) else pg d a) (List.replicate n 1)

/-- Stress three syllables in, in every word long enough, is the extrametricality variant of a
trough-first sweep from the left and arises from no other setting of the parameters: grid theory
derives postpeninitial stress only as Winnebago has it. -/
theorem third_syllable_iff (d : Dir) (a : Altitude) (x : Bool) :
    (∀ n, 4 ≤ n → (alternating d a x n).findIdx? (2 ≤ ·) = some 2) ↔
      d = .lr ∧ a = .trough ∧ x = true := by
  constructor
  · intro h
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    revert h4 h5
    cases d <;> cases a <;> cases x <;> decide
  · rintro ⟨rfl, rfl, rfl⟩ n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [alternating, if_true]
    rw [List.replicate_succ]
    simp only [elm, pg, Altitude.start, sweep_replicate]
    simp [alt, List.findIdx?_cons]

/-! ### The End Rule at the phrase and Move x (28) to (31) -/

/-- The citation grids of *achromatic*, *lens*, *Dundee*, *marmalade* (28), *antique*, *dealer*,
and *chair* (31). -/
def achromatic : Grid := [2, 1, 3, 1]
def lens : Grid := [3]
def dundee : Grid := [2, 3]
def marmalade : Grid := [3, 1, 2]
def antique : Grid := [2, 3]
def dealer : Grid := [3, 1]
def chair : Grid := [3]

/-- (29a), (30a): phrasal stress on *lens* creates a word-level clash with *-ma-*, which Move x
resolves by sliding the entry to the initial syllable. -/
theorem achromatic_lens :
    moveX .rl 3 (endRule .final 4 false (achromatic ++ lens)) = [3, 1, 2, 1, 4] := by decide

/-- (29b), (30b): *Dundee marmalade*. -/
theorem dundee_marmalade :
    moveX .rl 3 (endRule .final 4 false (dundee ++ marmalade)) = [3, 2, 4, 1, 2] := by decide

/-- (31a): in the compound *antique dealer* the clashing entry sits under the phrasal peak, so
Move x cannot touch it. -/
theorem antique_dealer :
    moveX .rl 3 (endRule .initial 4 false (antique ++ dealer)) = [2, 4, 3, 1] := by decide

/-- (31b): in the phrase *antique chair* the same clash is resolved. -/
theorem antique_chair :
    moveX .rl 3 (endRule .final 4 false (antique ++ chair)) = [3, 2, 4] := by decide

/-! ### Quantity: bipositional heavy syllables (§3.5, §3.7) -/

/-- A heavy syllable, one of two or more moras, occupies two grid positions with its nucleus above
the second, so it is intrinsically stressed (74); a light syllable occupies one. -/
def mora (m : Syllable.Weight) : Grid := if 2 ≤ m then [2, 1] else [1]

/-- Quantity Sensitivity QS ((119d)): the grid of a syllable string. -/
def qs (w : List Syllable.Weight) : Grid := w.flatMap mora

/-- The grid position of the nucleus of syllable `k`. -/
def nucleus (w : List Syllable.Weight) (k : ℕ) : ℕ := (qs (w.take k)).length

theorem mora_of_two_le {m : Syllable.Weight} (h : 2 ≤ m) : mora m = [2, 1] := if_pos h

theorem mora_of_lt {m : Syllable.Weight} (h : m < 2) : mora m = [1] := if_neg (Nat.not_le.2 h)

theorem qs_cons (m : Syllable.Weight) (w : List Syllable.Weight) :
    qs (m :: w) = mora m ++ qs w :=
  List.flatMap_cons ..

theorem qs_append (w v : List Syllable.Weight) : qs (w ++ v) = qs w ++ qs v :=
  List.flatMap_append ..

theorem mem_mora {m x : ℕ} (hx : x ∈ mora m) : 1 ≤ x ∧ x ≤ 2 := by
  unfold mora at hx
  split_ifs at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> omega

theorem mem_qs {w : List Syllable.Weight} {x : ℕ} (hx : x ∈ qs w) : 1 ≤ x ∧ x ≤ 2 := by
  obtain ⟨m, -, hm⟩ := List.mem_flatMap.1 hx
  exact mem_mora hm

theorem qs_le_two (w : List Syllable.Weight) : ∀ x ∈ qs w, x ≤ 2 := λ _ hx => (mem_qs hx).2

theorem qs_singleton (m : Syllable.Weight) : qs [m] = mora m := by simp [qs]

/-- Heavy syllables never clash: their nuclei are separated by their second positions (74). -/
theorem qs_isChain (w : List Syllable.Weight) : (qs w).IsChain (λ a b => a < 2 ∨ b < 2) := by
  induction w with
  | nil => simp [qs]
  | cons m w ih =>
    rw [qs_cons, List.isChain_append]
    refine ⟨?_, ih, ?_⟩ <;> unfold mora <;> split_ifs <;> simp

theorem noClash_qs (w : List Syllable.Weight) : NoClash (qs w) :=
  noClash_of_alternating (λ x hx => mem_qs hx) λ i hi => by
    have := List.isChain_iff_getElem.1 (qs_isChain w) i hi
    simpa [List.getD_eq_getElem?_getD, show i < (qs w).length by omega, hi] using this

theorem qs_eq_nil_iff {w : List Syllable.Weight} : qs w = [] ↔ w = [] := by
  cases w with
  | nil => simp [qs]
  | cons m w => rw [qs_cons, mora]; split_ifs <;> simp

private theorem exists_append_singleton {v : List Syllable.Weight} (hv : v ≠ []) :
    ∃ t m, v = t ++ [m] := by
  obtain ⟨t, m, h⟩ := (List.eq_nil_or_concat v).resolve_left hv
  exact ⟨t, m, by rw [h, List.concat_eq_append]⟩

/-- Every syllable ends in a weak position. -/
theorem exists_qs_eq_append_one {v : List Syllable.Weight} (hv : v ≠ []) :
    ∃ t, qs v = t ++ [1] := by
  obtain ⟨v, m, rfl⟩ := exists_append_singleton hv
  rw [qs_append, qs_singleton]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact ⟨qs v, by rw [mora_of_lt hm]⟩
  · exact ⟨qs v ++ [2], by rw [mora_of_two_le hm, List.append_assoc]; rfl⟩

@[simp] theorem nucleus_zero (w : List Syllable.Weight) : nucleus w 0 = 0 := rfl

theorem nucleus_cons_succ (m : Syllable.Weight) (w : List Syllable.Weight) (k : ℕ) :
    nucleus (m :: w) (k + 1) = (mora m).length + nucleus w k := by
  simp [nucleus, qs_cons]

theorem nucleus_append_length (v : List Syllable.Weight) (m : Syllable.Weight) :
    nucleus (v ++ [m]) v.length = (qs v).length := by
  simp [nucleus]

/-- The first stress of the quantity-sensitive grid is the nucleus of the first heavy syllable. -/
theorem findIdx?_qs (w : List Syllable.Weight) :
    (qs w).findIdx? (2 ≤ ·) = (w.findIdx? (2 ≤ ·)).map (nucleus w) := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, List.findIdx?_append, List.findIdx?_cons, ih]
    by_cases hm : 2 ≤ m
    · simp [mora_of_two_le hm, hm, List.findIdx?_cons]
    · simp [mora_of_lt (Nat.not_le.1 hm), hm, List.findIdx?_cons, nucleus_cons_succ,
        Option.map_map, Function.comp_def, Nat.add_comm]

/-- The last stress of the quantity-sensitive grid is the nucleus of the last heavy syllable. -/
theorem lastIdx?_qs (w : List Syllable.Weight) :
    lastIdx? (2 ≤ ·) (qs w) = (lastIdx? (2 ≤ ·) w).map (nucleus w) := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, lastIdx?_append, lastIdx?_cons, ih]
    by_cases hm : 2 ≤ m
    · cases lastIdx? (2 ≤ ·) w <;>
        simp [mora_of_two_le hm, hm, lastIdx?_cons, nucleus_cons_succ, Nat.add_comm]
    · cases lastIdx? (2 ≤ ·) w <;>
        simp [mora_of_lt (Nat.not_le.1 hm), hm, lastIdx?_cons, nucleus_cons_succ, Nat.add_comm]

/-- A word of light syllables is an unstressed grid. -/
theorem qs_eq_replicate {w : List Syllable.Weight} (h : ∀ m ∈ w, m < 2) :
    qs w = List.replicate w.length 1 := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, mora_of_lt (h m (List.mem_cons_self ..)),
      ih λ x hx => h x (List.mem_cons_of_mem _ hx), List.length_cons, List.replicate_succ]
    rfl

theorem nucleus_of_light {w : List Syllable.Weight} (h : ∀ m ∈ w, m < 2) (k : ℕ) :
    nucleus w k = min k w.length := by
  rw [nucleus, qs_eq_replicate λ x hx => h x (List.mem_of_mem_take hx), List.length_replicate,
    List.length_take]

theorem lastIdx?_replicate_one (n : ℕ) : lastIdx? (2 ≤ ·) (List.replicate n 1) = none :=
  lastIdx?_eq_none.2 λ x hx => by simp [List.eq_of_mem_replicate hx]

theorem lastIdx?_replicate_one_pos (n : ℕ) :
    lastIdx? (1 ≤ ·) (List.replicate (n + 1) 1) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, lastIdx?_cons_of_some ih]

/-! #### The End Rule at the stress level -/

private theorem min_one_peak {g : Grid} {x : ℕ} (hx : x ∈ g) (h1 : 1 ≤ x) :
    min (2 - 1) (peak g) = 1 :=
  Nat.min_eq_left (h1.trans (le_peak hx))

/-- The End Rule at the stress level never raises a column above it. -/
theorem endRule_le_two {e : Edge} {fco : Bool} {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) :
    ∀ x ∈ endRule e 2 fco g, x ≤ 2 := by
  intro x hx
  simp only [endRule] at hx
  split at hx
  · exact h2 x hx
  · rename_i i hi
    split_ifs at hx
    · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h2 x hx
      · have := (edgeIdx?_getD hi).1
        have hgi : g.getD i 0 ≤ 2 := by
          simpa [List.getD_eq_getElem?_getD, this] using h2 _ (List.getElem_mem this)
        omega
    · exact h2 x hx

/-- An already stressed initial syllable is left alone. -/
theorem endRule_initial_of_two_le {x : ℕ} (hx : 2 ≤ x) (t : Grid) (fco : Bool) :
    endRule .initial 2 fco (x :: t) = x :: t := by
  simp only [endRule, min_one_peak (List.mem_cons_self ..) (by omega : 1 ≤ x), edgeIdx?,
    List.findIdx?_cons, decide_eq_true (by omega : 1 ≤ x), ↓reduceIte, List.set_cons_zero,
    List.getD_cons_zero, Nat.max_eq_left hx, ite_self]

theorem endRule_initial_singleton {x : ℕ} (hx : 1 ≤ x) (fco : Bool) :
    endRule .initial 2 fco [x] = [max x 2] := by
  simp only [endRule, min_one_peak (List.mem_cons_self ..) hx, edgeIdx?, List.findIdx?_cons,
    decide_eq_true hx, ↓reduceIte, List.set_cons_zero, List.getD_cons_zero]
  rw [if_pos (Or.inr λ j hj => ?_)]
  simp only [List.length_singleton] at hj
  obtain rfl : j = 0 := by omega
  simp [Clash]

/-- Stressing a light initial syllable, withheld before a stressed second position unless
Forward Clash Override is on. -/
theorem endRule_initial_two {y : ℕ} (hy : 1 ≤ y) (t : Grid) (fco : Bool) :
    endRule .initial 2 fco (1 :: y :: t) = if fco ∨ y < 2 then 2 :: y :: t else 1 :: y :: t := by
  have key : (∀ j < (1 :: y :: t).length,
      ¬ Clash (2 :: y :: t) (1 + 1) 0 j ∧ ¬ Clash (2 :: y :: t) (1 + 1) j 0) ↔ y < 2 := by
    constructor
    · intro h
      have := (h 1 (by simp)).1
      simp [Clash] at this
      omega
    · intro hy2 j _
      constructor
      · rintro ⟨hij, -, h2, hk⟩
        rcases j with _ | _ | j
        · omega
        · simp at h2; omega
        · have := hk 1 (by omega) (by omega)
          simp at this
          omega
      · rintro ⟨hji, -⟩
        omega
  have hidx : edgeIdx? .initial 1 (1 :: y :: t) = some 0 := by simp [edgeIdx?, List.findIdx?_cons]
  simp only [endRule, min_one_peak (List.mem_cons_self ..) le_rfl, hidx, List.set_cons_zero,
    List.getD_cons_zero, Nat.max_eq_right (Nat.le_succ 1), key]

theorem endRule_final_singleton {x : ℕ} (hx : 1 ≤ x) (fco : Bool) :
    endRule .final 2 fco [x] = [max x 2] := by
  have hidx : edgeIdx? .final 1 [x] = some 0 := by simp [edgeIdx?, lastIdx?_cons, hx]
  simp only [endRule, min_one_peak (List.mem_cons_self ..) hx, hidx, List.set_cons_zero,
    List.getD_cons_zero]
  rw [if_pos (Or.inr λ j hj => ?_)]
  simp only [List.length_singleton] at hj
  obtain rfl : j = 0 := by omega
  simp [Clash]

/-- Stressing a light final syllable, withheld after a stressed penultimate position unless
Forward Clash Override is on. -/
theorem endRule_final_two {y : ℕ} (hy : 1 ≤ y) (t : Grid) (fco : Bool) :
    endRule .final 2 fco (t ++ [y, 1]) = if fco ∨ y < 2 then t ++ [y, 2] else t ++ [y, 1] := by
  have hidx : edgeIdx? .final 1 (t ++ [y, 1]) = some (t.length + 1) := by
    simp [edgeIdx?, lastIdx?_append, lastIdx?_cons, Nat.add_comm]
  have hset : (t ++ [y, 1]).set (t.length + 1) (max 1 (1 + 1)) = t ++ [y, 2] := by
    rw [List.set_append_right _ _ (Nat.le_succ _)]
    simp
  have hgy : (t ++ [y, 2]).getD t.length 0 = y := by simp [List.getD_eq_getElem?_getD]
  have hg2 : (t ++ [y, 2]).getD (t.length + 1) 0 = 2 := by simp [List.getD_eq_getElem?_getD]
  have hg1 : (t ++ [y, 1]).getD (t.length + 1) 0 = 1 := by simp [List.getD_eq_getElem?_getD]
  have key : (∀ j < (t ++ [y, 1]).length,
      ¬ Clash (t ++ [y, 2]) (1 + 1) (t.length + 1) j ∧
        ¬ Clash (t ++ [y, 2]) (1 + 1) j (t.length + 1)) ↔ y < 2 := by
    constructor
    · intro h
      by_contra hy2
      refine (h t.length (by simp)).2
        ⟨Nat.lt_succ_self _, ?_, ?_, λ k hk hk' => absurd hk (by omega)⟩
      · rw [hgy]; omega
      · rw [hg2]
    · intro hy2 j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      constructor
      · rintro ⟨hij, -⟩
        omega
      · rintro ⟨hji, h2, -, hk⟩
        rcases Nat.lt_or_ge j t.length with hjt | hjt
        · have := hk t.length (by omega) hjt
          rw [hgy] at this
          omega
        · have : j = t.length := by omega
          subst this
          rw [hgy] at h2
          omega
  have hmin : min (2 - 1) (peak (t ++ [y, 1])) = 1 :=
    min_one_peak (List.mem_append_right _ (by simp)) le_rfl
  simp only [endRule]
  rw [hmin, hidx]
  dsimp only
  rw [hg1, hset]
  simp only [key]

/-! #### Main stress -/

/-- Column `i` carries the main stress: it is strictly taller than every other column. -/
def MainStressAt (g : Grid) (i : ℕ) : Prop :=
  i < g.length ∧ ∀ j < g.length, j ≠ i → g.getD j 0 < g.getD i 0

instance (g : Grid) (i : ℕ) : Decidable (MainStressAt g i) := by
  unfold MainStressAt; infer_instance

theorem MainStressAt.isCulminative {g : Grid} {i : ℕ} (h : MainStressAt g i) :
    IsCulminative g :=
  isCulminative_of_forall_lt h.1 λ j hj hne => by
    simpa [List.getD_eq_getElem?_getD, hj, h.1] using h.2 j hj hne

theorem mainStressAt_set {g : Grid} {m i : ℕ} (h2 : ∀ x ∈ g, x ≤ m) (hi : i < g.length) :
    MainStressAt (g.set i (m + 1)) i := by
  refine ⟨by simpa using hi, λ j hj hne => ?_⟩
  simp only [List.length_set] at hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm,
    List.getElem?_set_self hi, List.getElem?_eq_getElem hj]
  simpa using Nat.lt_succ_of_le (h2 _ (List.getElem_mem hj))

/-- The End Rule at the level above the peak puts the main stress on the edge-most peak. -/
theorem mainStressAt_endRule {e : Edge} {L : ℕ} {fco : Bool} {g : Grid} (hL : peak g ≤ L - 1)
    {i : ℕ} (hi : edgeIdx? e (peak g) g = some i) : MainStressAt (endRule e L fco g) i := by
  rw [endRule_of_peak hL hi]
  exact mainStressAt_set (λ x hx => le_peak hx) (edgeIdx?_getD hi).1

theorem peak_eq_two {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) (hx : 2 ∈ g) : peak g = 2 :=
  le_antisymm (peak_le h2) (le_peak hx)

theorem two_mem_of_findIdx? {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) {i : ℕ}
    (hi : g.findIdx? (2 ≤ ·) = some i) : 2 ∈ g := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have := h2 _ (List.getElem_mem hi)
  simp only [decide_eq_true_eq] at hp
  exact (by omega : g[i] = 2) ▸ List.getElem_mem hi

theorem two_mem_of_lastIdx? {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) {i : ℕ}
    (hi : lastIdx? (2 ≤ ·) g = some i) : 2 ∈ g := by
  obtain ⟨hi, hp⟩ := lastIdx?_eq_some hi
  have := h2 _ (List.getElem_mem hi)
  simp only [decide_eq_true_eq] at hp
  exact (by omega : g[i] = 2) ▸ List.getElem_mem hi

/-- Main stress on the first stress of a grid of stresses and unstressed columns. -/
theorem mainStressAt_of_edgeIdx? {e : Edge} {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) {i : ℕ}
    (hi : edgeIdx? e 2 g = some i) : MainStressAt (endRule e 3 false g) i := by
  have hp : peak g = 2 := by
    cases e with
    | initial => exact peak_eq_two h2 (two_mem_of_findIdx? h2 hi)
    | final => exact peak_eq_two h2 (two_mem_of_lastIdx? h2 hi)
  exact mainStressAt_endRule (by rw [hp]) (by rw [hp]; exact hi)

/-! #### The three kinds of quantity-sensitive system without alternation (97), (98) -/

/-- The opposite edge, `Ē` of (97). -/
def Edge.flip : Edge → Edge
  | .initial => .final
  | .final => .initial

/-- (97) I, fixed stress: QS, ER(E;Σ), ER(E;Wd). The edge syllable is stressed, every heavy
syllable is stressed, and the edge-most stress is the main stress. -/
def fixedStress (e : Edge) (fco : Bool) (w : List Syllable.Weight) : Grid :=
  endRule e 3 fco (endRule e 2 fco (qs w))

/-- (97) II, `E` defaulting to `Ē`: QS, ER(Ē;Σ), ER(E;Wd). Main stress on the `E`-most heavy
syllable or, lacking heavies, on the `Ē` syllable. -/
def defaultOpposite (e : Edge) (w : List Syllable.Weight) : Grid :=
  endRule e 3 false (endRule e.flip 2 false (qs w))

/-- (97) III, `E` defaulting to `E`: QS, ER(E;Wd), which applies to the highest level present.
Main stress on the `E`-most heavy syllable or, lacking heavies, on the `E` syllable. -/
def defaultSame (e : Edge) (w : List Syllable.Weight) : Grid :=
  endRule e 3 false (qs w)

/-- (98) III.i, Khalkha Mongolian, Fore, Yana: main stress on the first heavy syllable. -/
theorem khalkha_heavy {w : List Syllable.Weight} {k : ℕ} (hk : w.findIdx? (2 ≤ ·) = some k) :
    MainStressAt (defaultSame .initial w) (nucleus w k) :=
  mainStressAt_of_edgeIdx? (qs_le_two w) (e := .initial) (by rw [edgeIdx?, findIdx?_qs, hk]; rfl)

/-- (98) III.i: lacking heavy syllables, main stress on the first syllable. -/
theorem khalkha_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultSame .initial w) 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  have hq : qs w = List.replicate (n + 1) 1 := by rw [qs_eq_replicate hl, hn]
  have hp : peak (qs w) = 1 := by rw [hq]; exact peak_replicate_one (Nat.succ_pos n)
  refine mainStressAt_endRule (by rw [hp]; decide) ?_
  rw [hp, hq, edgeIdx?, List.replicate_succ]
  simp [List.findIdx?_cons]

/-- (98) III.ii, Aguacatec, Golin: main stress on the last heavy syllable. -/
theorem aguacatec_heavy {w : List Syllable.Weight} {k : ℕ} (hk : lastIdx? (2 ≤ ·) w = some k) :
    MainStressAt (defaultSame .final w) (nucleus w k) :=
  mainStressAt_of_edgeIdx? (qs_le_two w) (e := .final) (by rw [edgeIdx?, lastIdx?_qs, hk]; rfl)

/-- (98) III.ii: lacking heavy syllables, main stress on the last syllable. -/
theorem aguacatec_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultSame .final w) (nucleus w (w.length - 1)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  have hq : qs w = List.replicate (n + 1) 1 := by rw [qs_eq_replicate hl, hn]
  have hp : peak (qs w) = 1 := by rw [hq]; exact peak_replicate_one (Nat.succ_pos n)
  rw [nucleus_of_light hl, hn, Nat.add_sub_cancel, Nat.min_eq_left (Nat.le_succ n)]
  refine mainStressAt_endRule (by rw [hp]; decide) ?_
  rw [hp, hq, edgeIdx?, lastIdx?_replicate_one_pos]

/-- After the End Rule stresses the initial syllable, the last stress is the last stress of the
rest of the word, or the initial syllable itself. -/
theorem lastIdx?_endRule_initial {g : Grid} (hg : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2) (hne : g ≠ []) :
    lastIdx? (2 ≤ ·) (endRule .initial 2 false g) =
      ((lastIdx? (2 ≤ ·) g.tail).map (· + 1)).or (some 0) := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hx1, hx2⟩ := hg x (List.mem_cons_self ..)
  rcases Nat.lt_or_ge x 2 with hx | hx
  · obtain rfl : x = 1 := by omega
    cases t with
    | nil => simp [endRule_initial_singleton le_rfl, lastIdx?_cons]
    | cons y t =>
      obtain ⟨hy1, -⟩ := hg y (by simp)
      rw [endRule_initial_two hy1]
      by_cases hy2 : y < 2
      · rw [if_pos (Or.inr hy2)]
        simp [lastIdx?_cons]
      · rw [if_neg (by simpa using hy2)]
        simp [lastIdx?_cons, Nat.not_lt.1 hy2]
  · rw [endRule_initial_of_two_le hx]
    simp [lastIdx?_cons, hx]

/-- (98) II.i, Classical Arabic, Eastern Cheremis, Chuvash, Hindi, Huasteco, Dongolese Nubian:
main stress on the last heavy syllable. -/
theorem cheremis_heavy {w : List Syllable.Weight} {k : ℕ} (hk : lastIdx? (2 ≤ ·) w = some k) :
    MainStressAt (defaultOpposite .final w) (nucleus w k) := by
  have h1 : lastIdx? (2 ≤ ·) (qs w) = some (nucleus w k) := by rw [lastIdx?_qs, hk]; rfl
  have hne : qs w ≠ [] := by rintro h; simp [h] at h1
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two w)) ?_
  rw [edgeIdx?, Edge.flip, lastIdx?_endRule_initial (λ x hx => mem_qs hx) hne]
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil hne
  rw [hxt] at h1 ⊢
  rw [lastIdx?_cons] at h1
  cases ht : lastIdx? (2 ≤ ·) t with
  | none =>
    rw [ht] at h1
    simp only [Option.map_none, Option.none_or] at h1
    simp only [List.tail_cons, ht, Option.map_none, Option.none_or]
    split_ifs at h1
    exact h1
  | some j =>
    rw [ht] at h1
    simp only [List.tail_cons, ht]
    simpa using h1

/-- (98) II.i: lacking heavy syllables, main stress on the first syllable. -/
theorem cheremis_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultOpposite .final w) 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  have hq : qs w = List.replicate (n + 1) 1 := by rw [qs_eq_replicate hl, hn]
  have h1 : endRule .initial 2 false (qs w) = 2 :: List.replicate n 1 := by
    rw [hq, endRule_initial_replicate (Nat.succ_pos n), Nat.succ_sub_one]
  rw [defaultOpposite, Edge.flip, h1]
  refine mainStressAt_of_edgeIdx? (λ x hx => ?_) (e := .final) ?_
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · simp [List.eq_of_mem_replicate hx]
  · rw [edgeIdx?, lastIdx?_cons, lastIdx?_replicate_one]
    rfl

/-- The End Rule leaves a heavy final syllable alone and stresses a light one. -/
theorem endRule_final_qs (v : List Syllable.Weight) (m : Syllable.Weight) :
    endRule .final 2 false (qs (v ++ [m])) = if 2 ≤ m then qs (v ++ [m]) else qs v ++ [2] := by
  rw [qs_append, qs_singleton]
  split_ifs with hm
  · rw [mora_of_two_le hm, endRule_final_two (Nat.le_succ 1)]
    simp
  · rw [mora_of_lt (Nat.not_le.1 hm)]
    rcases eq_or_ne v [] with rfl | hv
    · simp [qs, endRule_final_singleton]
    · obtain ⟨t, ht⟩ := exists_qs_eq_append_one hv
      rw [ht, List.append_assoc, List.singleton_append, endRule_final_two le_rfl]
      simp

/-- (98) II.ii, Komi: main stress on the first heavy syllable. -/
theorem komi_heavy {w : List Syllable.Weight} {k : ℕ} (hk : w.findIdx? (2 ≤ ·) = some k) :
    MainStressAt (defaultOpposite .initial w) (nucleus w k) := by
  have h1 : (qs w).findIdx? (2 ≤ ·) = some (nucleus w k) := by rw [findIdx?_qs, hk]; rfl
  have hne : w ≠ [] := by rintro rfl; simp at hk
  obtain ⟨v, m, rfl⟩ := exists_append_singleton hne
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .initial) ?_
  rw [edgeIdx?, Edge.flip, endRule_final_qs]
  split_ifs with hm
  · exact h1
  · rw [qs_append, qs_singleton, mora_of_lt (Nat.not_le.1 hm), List.findIdx?_append] at h1
    rw [List.findIdx?_append]
    cases hv : (qs v).findIdx? (2 ≤ ·) <;> rw [hv] at h1 <;> simp_all [List.findIdx?_cons]

/-- (98) II.ii: lacking heavy syllables, main stress on the last syllable. -/
theorem komi_light {v : List Syllable.Weight} {m : Syllable.Weight}
    (hl : ∀ x ∈ v ++ [m], x < 2) :
    MainStressAt (defaultOpposite .initial (v ++ [m])) (nucleus (v ++ [m]) v.length) := by
  have hm : m < 2 := hl m (by simp)
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .initial) ?_
  rw [edgeIdx?, Edge.flip, endRule_final_qs, if_neg (Nat.not_le.2 hm), nucleus_append_length,
    qs_eq_replicate λ x hx => hl x (List.mem_append_left _ hx), List.findIdx?_append]
  simp [List.findIdx?_cons, List.findIdx?_replicate]

/-- (98) I.ii, West Greenlandic Eskimo: the last syllable is stressed and carries the main
stress, whether heavy or light. -/
theorem westGreenlandic (v : List Syllable.Weight) (m : Syllable.Weight) :
    MainStressAt (fixedStress .final false (v ++ [m])) (nucleus (v ++ [m]) v.length) := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .final) ?_
  rw [edgeIdx?, endRule_final_qs, nucleus_append_length]
  split_ifs with hm
  · rw [qs_append, qs_singleton, mora_of_two_le hm, lastIdx?_append]
    simp [lastIdx?_cons]
  · rw [lastIdx?_append]
    simp [lastIdx?_cons]

/-- The initial syllable is stressed under Forward Clash Override. -/
theorem findIdx?_endRule_initial_fco {g : Grid} (hg : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2) (hne : g ≠ []) :
    (endRule .initial 2 true g).findIdx? (2 ≤ ·) = some 0 := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hx1, hx2⟩ := hg x (List.mem_cons_self ..)
  rcases Nat.lt_or_ge x 2 with hx | hx
  · obtain rfl : x = 1 := by omega
    cases t with
    | nil => simp [endRule_initial_singleton le_rfl, List.findIdx?_cons]
    | cons y t =>
      rw [endRule_initial_two (hg y (by simp)).1, if_pos (Or.inl rfl)]
      simp [List.findIdx?_cons]
  · rw [endRule_initial_of_two_le hx]
    simp [List.findIdx?_cons, hx]

/-- (98) I.i, Koya: the first syllable is stressed, with Forward Clash Override, and carries the
main stress. -/
theorem koya {w : List Syllable.Weight} (hw : w ≠ []) :
    MainStressAt (fixedStress .initial true w) 0 := by
  have hq : qs w ≠ [] := by rwa [Ne, qs_eq_nil_iff]
  have h2 := endRule_le_two (e := .initial) (fco := true) (qs_le_two w)
  have hp : peak (endRule .initial 2 true (qs w)) = 2 :=
    peak_eq_two h2 (two_mem_of_findIdx? h2 (findIdx?_endRule_initial_fco (λ x hx => mem_qs hx) hq))
  exact mainStressAt_endRule (by rw [hp])
    (by rw [hp]; exact findIdx?_endRule_initial_fco (λ x hx => mem_qs hx) hq)

/-- Malayalam (§3.7): the first syllable carries the main stress unless it is light and the
second heavy, the End Rule being blocked by clash there. -/
theorem malayalam_first {m : Syllable.Weight} {w : List Syllable.Weight}
    (h : ¬ (m < 2 ∧ ∃ m₁ ∈ w.head?, 2 ≤ m₁)) :
    MainStressAt (fixedStress .initial false (m :: w)) 0 := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .initial) ?_
  rw [edgeIdx?, qs_cons]
  by_cases hm : 2 ≤ m
  · rw [mora_of_two_le hm, List.cons_append, endRule_initial_of_two_le le_rfl]
    simp [List.findIdx?_cons]
  · have hm' : m < 2 := Nat.not_le.1 hm
    rw [mora_of_lt hm', List.singleton_append]
    cases w with
    | nil => simp [qs, endRule_initial_singleton le_rfl, List.findIdx?_cons]
    | cons m₁ w =>
      have hm₁ : m₁ < 2 := Nat.not_le.1 λ h₁ => h ⟨hm', m₁, rfl, h₁⟩
      rw [qs_cons, mora_of_lt hm₁, List.singleton_append, endRule_initial_two le_rfl,
        if_pos (Or.inr Nat.one_lt_two)]
      simp [List.findIdx?_cons]

/-- Malayalam (§3.7): a heavy second syllable after a light first one carries the main stress. -/
theorem malayalam_second {m₀ m₁ : Syllable.Weight} {w : List Syllable.Weight} (h₀ : m₀ < 2)
    (h₁ : 2 ≤ m₁) : MainStressAt (fixedStress .initial false (m₀ :: m₁ :: w)) 1 := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .initial) ?_
  rw [edgeIdx?, qs_cons, qs_cons, mora_of_lt h₀, mora_of_two_le h₁, List.singleton_append,
    List.cons_append, List.cons_append, List.nil_append, endRule_initial_two (Nat.le_succ 1),
    if_neg (by simp)]
  simp [List.findIdx?_cons]

end Prince1983
