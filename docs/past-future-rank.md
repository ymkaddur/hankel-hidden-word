# Past–future rank and linear dimension

Status labels: **[L-known]** formalized here, mathematically known or elementary;
**[L]** formalized here, statement new in this form; **refuted** the claim is false and the
counterexample is formalized; **open** not proved.

## Statement

A system `s_{t+1} = F_t s_t + g_t b_t` with state in `K^r` (any field) and readouts
`y_t = q_t ⬝ s_t` is cut at time `c`. The past–future block `H` has one column per test past (an
initial state and an input sequence that vanishes from `c` on) and one row per future time `c + i`.

* `H = O R`, where `O` holds the readouts propagated by the transitions after the cut and `R` holds
  the states reached at the cut. Hence `rank H ≤ r`.
* Readers that share one `r`-dimensional memory give a stacked block of rank at most `r`. Readers
  with separate `r`-dimensional memories give at most `|L| r`.

## Conditions, exactly

The bound holds under these hypotheses, and each one is used:

1. **Fixed schedule after the cut**: `F_t` and `q_t` for `t ≥ c` do not depend on the state or on
   the past (`nonlinear_post_cut_exceeds` shows what fails otherwise).
2. **Linear readout** of the state.
3. **No input after the cut** (with a fixed nonzero future input the response becomes affine in the
   state, and the same argument gives `rank ≤ r + 1`; not formalized).
4. **Exactness** on the tested pasts and futures.

Nothing is assumed about how the state at the cut is produced: the pasts may come from any
mechanism, linear or not. A block of rank `ρ` therefore excludes every realization of this form
with fewer than `ρ` state coordinates, and a stacked rank equal to `|L| r` excludes any shared
memory smaller than the separate ones.

## What it does not say

* It is not a bound on bits. The `N × N` equality block has rank `N`, while a realization that
  stores the past index needs `⌈log₂ N⌉` bits (`equality_block_rank`).
* It is not a bound on nonlinear realizations. A one-dimensional state evolved by `σ ↦ σ²` after the
  cut produces a block of rank `2` (`nonlinear_post_cut_exceeds`).
* It says nothing about approximate realizations (numerical rank) or about the cost of computing
  the transitions.

## Proof

With no input after the cut, `s_{c+k} = Φ(c, k) s_c` by induction on `k`, where `Φ(c, k)` is the
product of the transitions. Each entry is then `q_{c+i} ⬝ Φ(c, i) s_c = (q_{c+i}ᵀ Φ(c, i)) ⬝ s_c`,
a row of `O` times a column of `R`. The rank of a product is at most its inner dimension.

## Background

Kronecker's rank theorem for Hankel matrices; Ho and Kalman (1966) for minimal realizations of
linear systems; Carlyle and Paz (1971) and Fliess (1974) for the equality of Hankel rank and minimal
dimension of weighted automata. This repository's `HankelRank` computes the rank `L + 1` of a hidden
word, and `QueryLowerBound` shows that discovering it from values costs `2^L` queries.

## Formalization

`HiddenWord/PastFutureRank.lean`

| Status | Statement | Lean name |
|--------|-----------|-----------|
| [L-known] | a block that factors through `r` coordinates has rank at most `r` | `rank_le_of_factor` |
| [L-known] | with no input after the cut, the state evolves by the transitions | `state_after_cut` |
| [L-known] | the past–future block factors through the state at the cut, for arbitrary pasts | `pastFuture_factor` |
| [L-known] | its rank is at most the state dimension | `pastFuture_rank_le` |
| [L-known] | shared memory: stacked rank at most `r`; separate memories: at most `|L| r` | `stack_rank_le_common`, `stack_rank_le_separate` |
| **refuted** | "the past–future rank bounds the dimension of every realization" (state-dependent map after the cut) | `nonlinear_post_cut_exceeds` |
| [L-known] | the `N × N` equality block has rank `N` (rank is not a bit count) | `equality_block_rank` |

## Limitations

Exact arithmetic over a field. Certifying the rank of a block computed from floating-point data
needs an exact conversion (for instance dyadic rationals and a nonzero minor modulo a prime); that
step is outside this repository.

## Verification

`scripts/audit.sh` compiles every module with `#print axioms` of each theorem appended, and fails on
`sorry`, on warnings, or on axioms outside `propext`, `Classical.choice` and `Quot.sound`. Pinned
toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.
