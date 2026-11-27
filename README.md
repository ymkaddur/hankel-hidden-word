# hankel-hidden-word

Machine-checked separation between the dimension of a minimal linear realization and the cost of
discovering it from value queries, in Lean 4 with Mathlib.

Fix a word `w ∈ {0,1}^L` and its indicator `f_w` (`f_w x = 1` iff `x = w`). The Hankel matrix
`H u v = f_w(u ++ v)` has rank exactly `L + 1`, so `f_w` has a linear realization with `L + 1`
states. Any adaptive strategy that sees only values `f(x)` still needs `2^L` queries in the worst
case to tell `f_w` apart from the zero function. A small minimal dimension therefore does not bound
the cost of finding the realization.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Labels: **[L]** new theorem or construction proved in Lean; **[L-known]** Lean formalization of a known result; **refuted** counterexample proved in Lean; **open** precise statement not resolved here.

## Contents

| Module | Statement | Status |
|--------|-----------|--------|
| `HankelRank` | `u ++ v = w` iff `u = take i w` and `v = drop i w` for a unique cut `i ≤ L` | [L-known] |
| | `H = P·Q` through `L + 1` states: prefix chain `P u i = [u = take i w]`, suffix antidiagonal `Q i v = [v = drop i w]` | [L-known] |
| | `rank H ≤ L + 1` on every finite window of words | [L-known] |
| | `rank H = L + 1` on windows containing all prefixes (rows) and all suffixes (columns) | [L-known] |
| `QueryLowerBound` | for every adaptive deterministic strategy and `T < 2^L` rounds, some `w` of length `L` gives the same transcript as the zero function | [L-known] |
| | a strategy that separates `0` from every `f_w` with `|w| = L` makes at least `2^L` queries | [L-known] |

Open questions:

- **open**: the matching bound for randomized strategies, where the expected number of queries
  should be about `2^(L-1)`.
- **open**: families of functions with Hankel rank `r` whose value-query discovery cost is polynomial
  in `r`. Structural conditions on the family would be needed, since rank alone is not enough.

## Past–future rank

| Module | Statement | Status |
|--------|-----------|--------|
| `PastFutureRank` | for `s_{t+1} = F_t s_t + g_t b_t` in `K^r` with linear readouts and a fixed schedule after the cut, the past–future block factors through the state at the cut, for arbitrary pasts, so its rank is at most `r` | [L-known] |
| | readers sharing one `r`-dimensional memory: stacked rank at most `r`; separate memories: at most `|L| r` | [L-known] |
| | claim "the past–future rank bounds the dimension of every realization" (`σ ↦ σ²` after the cut gives rank `2` with one coordinate) | **refuted** |
| | the `N × N` equality block has rank `N`, while storing the past needs `⌈log₂ N⌉` bits: rank is not a bit count | [L-known] |

Conditions, proof and limitations: [docs/past-future-rank.md](docs/past-future-rank.md).

## Reproduce

```bash
lake exe cache get
lake build
scripts/audit.sh     # #print axioms for every theorem; fails on sorry, warnings or extra axioms
```

Pinned toolchain: `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`).

## License

MIT
