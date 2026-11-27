import Mathlib

/-!
# Finding a hidden word needs `2^L` value queries

A discoverer that may only ask for values `f x` (membership queries), with no equivalence oracle and
no access to operators, runs an adaptive deterministic strategy: the next queried word is a function
of the answers received so far.

* `indistinguishable`: if `T < 2^L`, some word `w` of length `L` produces exactly the same
  transcript as the zero function. If the strategy never queries `w`, the two histories cannot be told
  apart.
* `queries_needed`: a strategy that separates the zero function from every hidden word of length `L`
  makes at least `2^L` queries.

With `HankelRank`, this separates two complexities. The minimal realization has dimension only
`L + 1`, yet discovering it from values costs `2^L` queries. A small minimal dimension does not bound
the cost of finding it.
-/

namespace HiddenWord

/-- An adaptive deterministic strategy: the next queried word as a function of the answers so far. -/
abbrev Strategy := List Bool → List Bool

/-- The answers collected in `t` rounds against the oracle `f`. -/
def run (s : Strategy) (f : List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => run s f t ++ [f (s (run s f t))]

/-- The membership oracle of the hidden word `w`. -/
def member (w : List Bool) (x : List Bool) : Bool := decide (x = w)

/-- The words of length `L`. -/
def words (L : ℕ) : Finset (List Bool) :=
  Finset.univ.image (List.ofFn : (Fin L → Bool) → List Bool)

theorem card_words (L : ℕ) : (words L).card = 2 ^ L := by
  unfold words
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

theorem length_of_mem_words {L : ℕ} {w : List Bool} (h : w ∈ words L) : w.length = L := by
  unfold words at h
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
  exact List.length_ofFn

/-- The words queried during the first `T` rounds against the zero oracle. -/
def queried (s : Strategy) (T : ℕ) : Finset (List Bool) :=
  (Finset.range T).image fun t => s (run s (fun _ => false) t)

theorem card_queried_le (s : Strategy) (T : ℕ) : (queried s T).card ≤ T := by
  unfold queried
  exact Finset.card_image_le.trans (by simp)

/-- A word never queried against the zero oracle produces the zero transcript, round by round. -/
theorem run_eq_of_not_queried (s : Strategy) (w : List Bool) (T : ℕ) (hw : w ∉ queried s T) :
    ∀ t ≤ T, run s (member w) t = run s (fun _ => false) t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (by omega)
    have hans : member w (s (run s (fun _ => false) t)) = false := by
      simp only [member, decide_eq_false_iff_not]
      intro h
      apply hw
      exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), h⟩
    simp only [run, ih', hans]

/-- **Lower bound.** With fewer than `2^L` adaptive value queries, some hidden word of length `L`
gives exactly the transcript of the zero function. -/
theorem indistinguishable (s : Strategy) (L T : ℕ) (hT : T < 2 ^ L) :
    ∃ w, w.length = L ∧ run s (member w) T = run s (fun _ => false) T := by
  have hcard : (queried s T).card < (words L).card := by
    rw [card_words]; exact (card_queried_le s T).trans_lt hT
  obtain ⟨w, hwL, hwq⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨w, length_of_mem_words hwL, run_eq_of_not_queried s w T hwq T le_rfl⟩

/-- A strategy that separates the zero function from every hidden word of length `L` makes at least
`2^L` queries. -/
theorem queries_needed (s : Strategy) (L T : ℕ)
    (h : ∀ w, w.length = L → run s (member w) T ≠ run s (fun _ => false) T) : 2 ^ L ≤ T := by
  by_contra hlt
  obtain ⟨w, hw, heq⟩ := indistinguishable s L T (Nat.lt_of_not_le hlt)
  exact h w hw heq

end HiddenWord
