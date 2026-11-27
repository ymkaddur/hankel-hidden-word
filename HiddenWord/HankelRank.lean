import Mathlib

/-!
# The indicator of a hidden word has Hankel rank `L + 1`

For a word `w` of length `L` over `{0, 1}`, let `f_w` be its indicator (`f_w x = 1` iff `x = w`).
Its Hankel matrix on finite sets of row words `U` and column words `V` is `H u v = f_w (u ++ v)`.

* `hankel_factor`: `H = P Q` through `L + 1` states, where `P u i = [u = take i w]` is the prefix
  chain and `Q i v = [v = drop i w]` the suffix antidiagonal;
* `rank_le`: hence `rank H ≤ L + 1` on every finite window;
* `rank_ge`, `rank_eq`: on windows that contain every prefix and every suffix of `w`, the
  prefix × suffix block is the identity, so `rank H = L + 1` exactly.

The minimal linear realization of `f_w` is therefore small. `QueryLowerBound` shows that finding it
from value queries still costs `2^L` queries in the worst case.
-/

namespace HiddenWord

open Matrix

variable {K : Type*} [Field K]

/-- The indicator of the hidden word `w`. -/
def hw (w : List Bool) (x : List Bool) : K := if x = w then 1 else 0

/-- `u ++ v = w` iff `u` and `v` are the prefix and suffix of `w` cut at some position `i ≤ |w|`. -/
theorem append_eq_iff (w u v : List Bool) :
    u ++ v = w ↔ ∃ i, i ≤ w.length ∧ u = w.take i ∧ v = w.drop i := by
  constructor
  · rintro rfl
    exact ⟨u.length, by simp, (List.take_left' rfl).symm, (List.drop_left' rfl).symm⟩
  · rintro ⟨i, -, rfl, rfl⟩
    exact List.take_append_drop i w

/-- The cut position is determined by the prefix. -/
theorem take_inj {w : List Bool} {i j : ℕ} (hi : i ≤ w.length) (hj : j ≤ w.length)
    (h : w.take i = w.take j) : i = j := by
  have hl := congrArg List.length h
  simp only [List.length_take] at hl
  omega

/-- The Hankel matrix of `f` on finite sets of words: `H u v = f (u ++ v)`. -/
def hankel (f : List Bool → K) (U V : Finset (List Bool)) : Matrix U V K :=
  fun u v => f (u.1 ++ v.1)

/-- The prefix chain `P u i = [u = take i w]`. -/
def pre (w : List Bool) (U : Finset (List Bool)) : Matrix U (Fin (w.length + 1)) K :=
  fun u i => if u.1 = w.take i then 1 else 0

/-- The suffix antidiagonal `Q i v = [v = drop i w]`. -/
def suf (w : List Bool) (V : Finset (List Bool)) : Matrix (Fin (w.length + 1)) V K :=
  fun i v => if v.1 = w.drop i then 1 else 0

/-- Entries of the product of the prefix chain and the suffix antidiagonal. -/
theorem pre_mul_suf_apply (w : List Bool) (U V : Finset (List Bool)) (u : U) (v : V) :
    (pre w U * suf w V : Matrix U V K) u v =
      ∑ i : Fin (w.length + 1),
        (if u.1 = w.take i then (1 : K) else 0) * (if v.1 = w.drop i then 1 else 0) :=
  rfl

/-- Factorization of the Hankel matrix through `L + 1` states. -/
theorem hankel_factor (w : List Bool) (U V : Finset (List Bool)) :
    hankel (hw w) U V = (pre w U * suf w V : Matrix U V K) := by
  ext u v
  rw [pre_mul_suf_apply]
  simp only [hankel, hw]
  by_cases h : u.1 ++ v.1 = w
  · rw [if_pos h]
    obtain ⟨i, hi, hu, hv⟩ := (append_eq_iff w u.1 v.1).mp h
    rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (w.length + 1))]
    · simp [hu, hv]
    · intro j _ hj
      by_cases hju : u.1 = w.take j
      · exfalso
        apply hj
        ext
        exact take_inj (by have := j.2; omega) hi (hju.symm.trans hu)
      · simp [hju]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hu : u.1 = w.take i
    · by_cases hv : v.1 = w.drop i
      · exfalso; apply h; rw [hu, hv, List.take_append_drop]
      · simp [hu, hv]
    · simp [hu]

/-- Upper bound: the Hankel matrix of a hidden word has rank at most `L + 1` on every window. -/
theorem rank_le (w : List Bool) (U V : Finset (List Bool)) :
    (hankel (hw w) U V : Matrix U V K).rank ≤ w.length + 1 := by
  rw [hankel_factor]
  calc (pre w U * suf w V : Matrix U V K).rank ≤ (pre w U : Matrix U (Fin (w.length + 1)) K).rank :=
        rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin (w.length + 1)) := rank_le_card_width _
    _ = w.length + 1 := Fintype.card_fin _

/-- Lower bound: on a window that contains every prefix (rows) and every suffix (columns), the
prefix × suffix block is the identity, so the rank is at least `L + 1`. -/
theorem rank_ge (w : List Bool) (U V : Finset (List Bool)) (hU : ∀ i ≤ w.length, w.take i ∈ U)
    (hV : ∀ i ≤ w.length, w.drop i ∈ V) :
    w.length + 1 ≤ (hankel (hw w) U V : Matrix U V K).rank := by
  let r : Fin (w.length + 1) → U := fun i => ⟨w.take i, hU i (by have := i.2; omega)⟩
  let c : Fin (w.length + 1) → V := fun j => ⟨w.drop j, hV j (by have := j.2; omega)⟩
  have hsub : (hankel (hw w) U V : Matrix U V K).submatrix r c =
      (1 : Matrix (Fin (w.length + 1)) (Fin (w.length + 1)) K) := by
    ext i j
    simp only [submatrix_apply, hankel, hw, r, c, one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg]
      intro h
      apply hij
      have hl := congrArg List.length h
      simp only [List.length_append, List.length_take, List.length_drop] at hl
      have := i.2
      have := j.2
      ext
      omega
  calc w.length + 1 = Fintype.card (Fin (w.length + 1)) := (Fintype.card_fin _).symm
    _ = (1 : Matrix (Fin (w.length + 1)) (Fin (w.length + 1)) K).rank := rank_one.symm
    _ = ((hankel (hw w) U V : Matrix U V K).submatrix r c).rank := by rw [hsub]
    _ ≤ (hankel (hw w) U V : Matrix U V K).rank := rank_submatrix_le _ _ _

/-- The exact Hankel rank of a hidden word: `L + 1`. -/
theorem rank_eq (w : List Bool) (U V : Finset (List Bool)) (hU : ∀ i ≤ w.length, w.take i ∈ U)
    (hV : ∀ i ≤ w.length, w.drop i ∈ V) :
    (hankel (hw w) U V : Matrix U V K).rank = w.length + 1 :=
  le_antisymm (rank_le w U V) (rank_ge w U V hU hV)

end HiddenWord
