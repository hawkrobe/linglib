import Mathlib.Data.Set.Subsingleton

/-!
# The Russellian iota

The unique satisfier of a predicate, as a partial individual: `russellIota P` is `some e` when
`e` is the only `P`, and `none` when `P` has no satisfier or several ([russell-1905]). Definedness
is unique existence (`russellIota_isSome_iff`), which factors into existence and uniqueness of
the extension (`existsUnique_iff_nonempty_subsingleton`), the two components
[coppock-beaver-2015] separate into an assertion and a presupposition.

## Main definitions

* `Reference.russellIota`: the unique satisfier of a predicate, or `none`.

## Main results

* `russellIota_eq_some_iff`, `russellIota_isSome_iff`, `russellIota_eq_none_iff`.
* `existsUnique_iff_nonempty_subsingleton`: `∃!` is nonemptiness with subsingletonness.

## References

* [russell-1905]
* [coppock-beaver-2015]
-/

variable {α : Type*} {p : α → Prop}

/-- Unique existence is nonemptiness together with subsingletonness of the extension. -/
theorem existsUnique_iff_nonempty_subsingleton :
    (∃! x, p x) ↔ {x | p x}.Nonempty ∧ {x | p x}.Subsingleton :=
  (exists_congr fun _ ↦ Set.eq_singleton_iff_unique_mem.symm).trans
    Set.exists_eq_singleton_iff_nonempty_subsingleton

namespace Reference

variable {E : Type*} (P : E → Prop) {e : E}

/-- The unique satisfier of `P`, or `none` when `P` has no satisfier or several. -/
noncomputable def russellIota : Option E :=
  letI := Classical.dec (∃! x, P x)
  if h : ∃! x, P x then some h.choose else none

theorem russellIota_eq_some_iff : russellIota P = some e ↔ P e ∧ ∀ x, P x → x = e := by
  classical
  unfold russellIota
  split_ifs with h
  · rw [Option.some_inj, h.choose_eq_iff]
    exact ⟨fun he ↦ ⟨he, fun _ hx ↦ h.unique hx he⟩, And.left⟩
  · exact ⟨(nomatch ·), fun he ↦ (h ⟨e, he⟩).elim⟩

theorem russellIota_isSome_iff : (russellIota P).isSome ↔ ∃! x, P x := by
  classical
  unfold russellIota
  split_ifs with h <;> simp [h]

theorem russellIota_eq_none_iff : russellIota P = none ↔ ¬ ∃! x, P x := by
  rw [← Option.not_isSome_iff_eq_none, russellIota_isSome_iff]

end Reference
