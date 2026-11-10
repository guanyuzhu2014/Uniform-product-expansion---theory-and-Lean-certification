# Phase 1 Lean formalisation — coprime-degree Frobenius twists

Companion to `Uniform_product_expansion.pdf` (the note proving Assumption 2.1 of the balanced-product
CCZ manuscript). This folder contains the Lean 4 / Mathlib formalisation of the three *new*
ingredients of that note.

## Status (2026-10-27)

`CoprimeFrobenius.lean` (656 lines, 41 declarations, **no `sorry`**) type-checks on
https://live.lean-lang.org with the server's "Latest Mathlib with Lean v4.36.0-rc2". The only
diagnostics are three deprecation warnings (`if_pos`/`if_neg`). No local toolchain was available in
this sandbox, so the check was done through the playground; the file is self-contained
(`import Mathlib`) and should build unchanged in any Mathlib project of comparable age.

## What is proved

| Note | Lean declaration(s) | Content |
|---|---|---|
| Lemma 1.1 | `exists_selector`, `exists_selector_mul`, `pow_pow_mod`, `pow_pow_congr` | CRT selection of Frobenius exponents for pairwise coprime moduli (and the generalised CRT with a common factor `f`); on elements fixed by `x ↦ x^(q^m)`, `x^(q^s)` depends only on `s mod m`. |
| Lemma 2.1 | `not_dvd_tw` (+ `pow_char_pow_eq_expand`) | An irreducible `Q ∈ K[X₀,X₁]` with `deg₀ Q, deg₁ Q ≥ 1` never divides `𝒯Q = Q^σ(X₀, X₁^P)`, for any field automorphism `σ`, `P = p^f`, `f ≥ 1` (`K` perfect of characteristic `p`). Proof via UFD + `dvd_prime_pow` + degree comparison, exactly as in the note. |
| Lemma 4.1 (a) | `twist_eval`, `coord_identity`, `eval_scaleSub_map` | `R(x) = σ(F(x))` on grid points `x` with `x_i^(2^(f m_i)) = x_i`, `σ = Frob^{-e}`. |
| Lemma 4.1 (b) | `pderiv_twist_of_ne_zero`, `pderiv_scaleSub_of_ne_zero` | `∂_i R = 0` for `i ≠ j` (char 2, even exponents). |
| Lemma 4.1 (c) | `pderiv_twist_of_eq_zero`, `pderiv_scaleSub_of_eq_zero` | `∂_j R = twist(∂_j G)`, hence `(∂_j R)(x) = σ(b_j(x))` on the grid. |
| Lemma 4.1 (d) | `degreeOf_twist`, `degreeOf_scaleSub` | `deg_i R = 2^{v_i} deg_i G`, hence `≤ P·deg_i F` (`i ≠ j`) and `deg_j R ≤ deg_j F`. |
| exponents `v, e` | `exists_v`, `exists_twist_exponents` | `v_j = 0`, `1 ≤ v_i ≤ f`, `v_i + e ≡ u_i (mod f m_i)`; uses pairwise coprimality. |
| `b_j` | `totalDegree_scaleSub_pderiv_lt`, `degreeOf_pderiv_le`, `scaleSub_eq_zero_iff` | `b_j ≠ 0`, `totalDegree b_j < totalDegree F`, `deg_i b_j ≤ deg_i F`. |
| **Lemma 4.1 assembled** | `lemma_4_1` | All of the above in one statement. |

Conventions: the grid is given by `x : ι → F` with `x i ^ 2 ^ (f * m i) = x i` (i.e. `x i` in the
subfield of size `P^{m_i}`, `P = 2^f`); `F = scaleSub (fun i => 2 ^ u i) G` plays the role of
`G((X_i^{2^{u_i}})_i)`, and the hypothesis `pderiv j G ≠ 0` says that the 2-power extraction in
direction `j` is maximal (the note's "write `F = P((X_i^{2^{u_i}}))`, extracting the largest power
of two"). Note that only direction `j` needs a maximal extraction; the `u_i` for `i ≠ j` are
arbitrary, which is slightly more general than the note.

## What is *not* in this file (remaining Phase 1 polish)

* The purely combinatorial preprocessing step "every `F` depending on `X_j` can be written as
  `scaleSub (2^u) G` with `pderiv j G ≠ 0`" (divide all `X_j`-exponents by their common 2-power).
  `lemma_4_1` takes `(G, u)` with `pderiv j G ≠ 0` as input.
* The "same zero set" phrasing of (a) is immediate from `twist_eval` and `invFrob_injective`.

## Axiom audit

The file ends with `#print axioms` for the three main theorems and `#eval Lean.versionString`.
Output (identical on "Latest Mathlib", Lean 4.36.0-rc2, and on "Stable Release", Lean 4.35.0;
see `verification_log_2026-10-27.txt` for the full message lists and the SHA-256 of the checked file):

```
'CoprimeFrobenius.lemma_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'CoprimeFrobenius.not_dvd_tw' depends on axioms: [propext, Classical.choice, Quot.sound]
'CoprimeFrobenius.exists_selector_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean's classical logic; `sorryAx` (incomplete proof) and
any user-declared `axiom` are absent. The only `set_option` in the file disables an unused-variable
linter, nothing that affects soundness.

## Reproducing the check

Open https://live.lean-lang.org, choose "Latest Mathlib", paste `CoprimeFrobenius.lean`, and wait for
the `#eval` at the end ("CoprimeFrobenius: all declarations checked") to appear in the message
list; the only other messages should be the three deprecation warnings. `mkjs.py` is the helper
used here to push a file into the playground through the browser console
(`python3 mkjs.py CoprimeFrobenius.lean` writes `/tmp/submit.js`).

In a local Mathlib project: drop the file into the project, `lake build CoprimeFrobenius`.
