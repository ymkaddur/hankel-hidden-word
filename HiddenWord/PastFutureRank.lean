import Mathlib

/-!
# The past–future rank bounds the dimension of linear realizations, and nothing more

A system `s_{t+1} = F_t s_t + g_t b_t` with state in `K^r` and readouts `y_t = q_t ⬝ s_t` is cut at
time `c`. The *past–future block* has one column per test past (an initial state and an input
sequence that vanishes from `c` on) and one row per future time `c + i`.

* `state_after_cut`: with no input after the cut, `s_{c+k} = Φ(c, k) s_c`, where `Φ(c, k)` is the
  product of the transitions from `c` to `c + k`;
* `pastFuture_factor`: the block factors as `O R`, with `O` built from the readouts and the
  transitions after the cut, and `R` the states reached at the cut. The pasts are arbitrary: the
  state at the cut may be produced by any mechanism, linear or not;
* `pastFuture_rank_le`: hence its rank is at most `r`. A block of rank `ρ` excludes every
  realization of this form with fewer than `ρ` state coordinates;
* `stack_rank_le_common`, `stack_rank_le_separate`: readers that share one `r`-dimensional memory
  give a stacked block of rank at most `r`; readers with separate `r`-dimensional memories give at
  most `|L| r`;
* `nonlinear_post_cut_exceeds` (**refutation**): with a state-dependent map after the cut the bound
  fails. A one-dimensional state evolved by `σ ↦ σ²` has a past–future block of rank `2`;
* `equality_block_rank`: the `N × N` equality block has rank `N`, while a realization that stores
  the past index uses `⌈log₂ N⌉` bits. Rank bounds a linear dimension, not a number of bits.
-/

namespace HiddenWord.PastFuture

open Matrix

variable {K : Type*} [Field K]

/-- A block that factors through `r` coordinates has rank at most `r`. -/
theorem rank_le_of_factor {F P : Type*} [Fintype F] [Fintype P] {r : ℕ} (H : Matrix F P K)
    (O : Matrix F (Fin r) K) (R : Matrix (Fin r) P K) (h : H = O * R) : H.rank ≤ r := by
  rw [h]
  exact (rank_mul_le_right O R).trans ((rank_le_card_height R).trans_eq (Fintype.card_fin r))

variable {r : ℕ}

/-- The transition over `k` steps from time `c`: `F (c+k-1) ⋯ F c`. -/
def trans (F : ℕ → Matrix (Fin r) (Fin r) K) (c : ℕ) : ℕ → Matrix (Fin r) (Fin r) K
  | 0 => 1
  | k + 1 => F (c + k) * trans F c k

/-- The state of `s_{t+1} = F_t s_t + g_t b_t` started at `s₀`. -/
def state (F : ℕ → Matrix (Fin r) (Fin r) K) (b : ℕ → Fin r → K) (s₀ : Fin r → K) (g : ℕ → K) :
    ℕ → Fin r → K
  | 0 => s₀
  | t + 1 => F t *ᵥ state F b s₀ g t + g t • b t

/-- With no input after the cut, the state evolves by the transitions alone. -/
theorem state_after_cut (F : ℕ → Matrix (Fin r) (Fin r) K) (b : ℕ → Fin r → K)
    (s₀ : Fin r → K) (g : ℕ → K) (c : ℕ) (hg : ∀ i, g (c + i) = 0) :
    ∀ k, state F b s₀ g (c + k) = trans F c k *ᵥ state F b s₀ g c := by
  intro k
  induction k with
  | zero => simp [trans]
  | succ k ih =>
    show state F b s₀ g (c + k + 1) = trans F c (k + 1) *ᵥ state F b s₀ g c
    rw [state, ih, hg k, zero_smul, add_zero, trans, mulVec_mulVec]

/-- The past–future block at cut `c`: future times `c + i` (rows) and test pasts `p` (columns),
each given by an initial state `s₀ p` and an input sequence `γ p`. -/
def block (F : ℕ → Matrix (Fin r) (Fin r) K) (b q : ℕ → Fin r → K) (c m : ℕ) {P : Type*}
    (s₀ : P → Fin r → K) (γ : P → ℕ → K) : Matrix (Fin m) P K :=
  Matrix.of fun i p => q (c + i) ⬝ᵥ state F b (s₀ p) (γ p) (c + i)

/-- **Factorization through the state at the cut.** -/
theorem pastFuture_factor (F : ℕ → Matrix (Fin r) (Fin r) K) (b q : ℕ → Fin r → K) (c m : ℕ)
    {P : Type*} (s₀ : P → Fin r → K) (γ : P → ℕ → K) (hγ : ∀ p i, γ p (c + i) = 0) :
    block F b q c m s₀ γ =
      (Matrix.of fun (i : Fin m) (k : Fin r) => (q (c + i) ᵥ* trans F c i) k) *
        Matrix.of fun (k : Fin r) (p : P) => state F b (s₀ p) (γ p) c k := by
  ext i p
  simp only [block, of_apply, Matrix.mul_apply]
  rw [state_after_cut F b (s₀ p) (γ p) c (hγ p) i, dotProduct_mulVec]
  rfl

/-- **Linear-dimension bound**: the past–future block has rank at most the state dimension. -/
theorem pastFuture_rank_le (F : ℕ → Matrix (Fin r) (Fin r) K) (b q : ℕ → Fin r → K) (c m : ℕ)
    {P : Type*} [Fintype P] (s₀ : P → Fin r → K) (γ : P → ℕ → K)
    (hγ : ∀ p i, γ p (c + i) = 0) : (block F b q c m s₀ γ).rank ≤ r :=
  rank_le_of_factor _ _ _ (pastFuture_factor F b q c m s₀ γ hγ)

/-- The rows of several readers, stacked. -/
def stack {L F P : Type*} (H : L → Matrix F P K) : Matrix (L × F) P K :=
  Matrix.of fun i j => H i.1 i.2 j

/-- **One shared memory**: readers whose blocks factor through the same `r`-dimensional state map
give a stacked block of rank at most `r`. -/
theorem stack_rank_le_common {L F P : Type*} [Fintype L] [Fintype F] [Fintype P]
    (H : L → Matrix F P K) (O : L → Matrix F (Fin r) K) (R : Matrix (Fin r) P K)
    (h : ∀ ℓ, H ℓ = O ℓ * R) : (stack H).rank ≤ r := by
  apply rank_le_of_factor _ (stack O) R
  ext ⟨ℓ, i⟩ j
  simp [stack, h ℓ, Matrix.mul_apply]

/-- **Separate memories**: readers with their own `r`-dimensional states give a stacked block of
rank at most `|L| r`. -/
theorem stack_rank_le_separate {L F P : Type*} [Fintype L] [DecidableEq L] [Fintype F]
    [Fintype P] (H : L → Matrix F P K) (O : L → Matrix F (Fin r) K) (R : L → Matrix (Fin r) P K)
    (h : ∀ ℓ, H ℓ = O ℓ * R ℓ) : (stack H).rank ≤ Fintype.card L * r := by
  have e : stack H =
      (Matrix.of fun (i : L × F) (k : L × Fin r) => if k.1 = i.1 then O i.1 i.2 k.2 else 0) *
        Matrix.of fun (k : L × Fin r) (j : P) => R k.1 k.2 j := by
    ext ⟨ℓ, i⟩ j
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single ℓ]
    · simp [stack, h ℓ, Matrix.mul_apply]
    · intro ℓ' _ hne
      simp [hne]
    · intro h'
      exact absurd (Finset.mem_univ ℓ) h'
  rw [e]
  exact (rank_mul_le_right _ _).trans ((rank_le_card_height _).trans_eq (by simp))

/-- **Refutation**: with a state-dependent map after the cut, the rank bound fails. The state is
one rational number `σ`; the two pasts leave `σ = 1` and `σ = 2` at the cut; after the cut
`σ ↦ σ²` and the readout is `σ`. The block (futures × pasts) is `!![1, 2; 1, 4]`, of rank `2`. -/
theorem nonlinear_post_cut_exceeds :
    let H : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of fun i p => (((p : ℕ) : ℚ) + 1) ^ (2 ^ (i : ℕ))
    H = !![1, 2; 1, 4] ∧ H.rank = 2 := by
  intro H
  have e : H = !![1, 2; 1, 4] := by
    ext i p; fin_cases i <;> fin_cases p <;> norm_num [H]
  refine ⟨e, ?_⟩
  rw [e, rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr
    (by rw [det_fin_two_of]; exact isUnit_iff_ne_zero.mpr (by norm_num)))]
  simp

/-- The `N × N` equality block has full rank `N`. -/
theorem equality_block_rank (N : ℕ) :
    (Matrix.of fun (u v : Fin N) => if u = v then (1 : K) else 0).rank = N := by
  have : (Matrix.of fun (u v : Fin N) => if u = v then (1 : K) else 0) = 1 := by
    ext u v; simp [Matrix.one_apply]
  rw [this, rank_one, Fintype.card_fin]

end HiddenWord.PastFuture
