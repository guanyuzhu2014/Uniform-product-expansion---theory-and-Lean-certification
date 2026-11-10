import Mathlib

/-!
# Phase 1: coprime-degree Frobenius twists (Lean 4 / Mathlib)

Companion to the note "Uniform product expansion of Reed–Solomon codes on coprime-degree subfield
grids" (v1, Oct 27, 2026). This file formalises the three *new* ingredients of that note:

* Lemma 1.1 (Frobenius selectors): `exists_selector`, `exists_selector_mul`, `pow_pow_congr`;
* Lemma 2.1 (`Q ∤ 𝒯Q`): `not_dvd_tw` (for any field automorphism `σ`, any `P = p ^ f`, `f ≥ 1`);
* Lemma 4.1 (isolating a derivative): `lemma_4_1`, assembled from `twist_eval` (a),
  `pderiv_twist_of_ne_zero` (b), `pderiv_twist_of_eq_zero` (c), `degreeOf_twist` (d),
  `exists_twist_exponents` (the choice of `v`, `e`), and the properties of `b_j`
  (`totalDegree_scaleSub_pderiv_lt`, `degreeOf_pderiv_le`).

Status: the whole file type-checks with **no `sorry`** on live.lean-lang.org
("Latest Mathlib with Lean v4.36.0-rc2", checked 2026-10-27); the only diagnostics are three
deprecation warnings for `if_pos`/`if_neg`.

Layout:
Part A: the substitution `X i ↦ X i ^ w i` ("scale substitution").
Part B: derivatives of twisted polynomials in characteristic two.
Part C: Frobenius selectors (CRT) and grid exponent identities.
Part D: the twist lemma (Lemma 4.1 of the note), core form.
Part E: choice of the exponents `v`, `e`.
Part F: the polynomial `b_j`.
Part G: Lemma 4.1 assembled.
Part H: `Q ∤ 𝒯Q` (Lemma 2.1 of the note).

Conventions: the grid points are `x : ι → F` with `x i ^ 2 ^ (f * m i) = x i`, i.e. `x i` lies in
the subfield with `2 ^ (f * m i) = P ^ (m i)` elements (`P = 2 ^ f`); `m` is pairwise coprime.
`scaleSub (fun i => 2 ^ u i) G` plays the role of `F = G((X_i^{2^{u_i}})_i)`; the hypothesis
`pderiv j G ≠ 0` says that the 2-power extraction in direction `j` is maximal.
-/

open MvPolynomial

namespace CoprimeFrobenius

set_option linter.unusedSectionVars false

/-! ## Part A: scale substitution -/
section Scale

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

/-- Pointwise scaling of an exponent vector: `(scale w s) i = w i * s i`. -/
noncomputable def scale (w : σ → ℕ) (s : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.onFinset s.support (fun i => w i * s i) (by
    intro i hi
    rw [Finsupp.mem_support_iff]
    intro h
    apply hi
    rw [h, mul_zero])

@[simp] lemma scale_apply (w : σ → ℕ) (s : σ →₀ ℕ) (i : σ) : scale w s i = w i * s i := by
  simp [scale]

lemma scale_injective {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) : Function.Injective (scale w) := by
  intro s t hst
  ext i
  have h := congrArg (fun f : σ →₀ ℕ => f i) hst
  simp only [scale_apply] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hw i)) h

lemma scale_support_subset (w : σ → ℕ) (s : σ →₀ ℕ) : (scale w s).support ⊆ s.support := by
  intro i hi
  rw [Finsupp.mem_support_iff] at hi ⊢
  intro h
  apply hi
  simp [h]

/-- The substitution `X i ↦ X i ^ w i`, as an `R`-algebra endomorphism of `MvPolynomial σ R`. -/
noncomputable def scaleSub (w : σ → ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ (fun i => X i ^ w i)

lemma scaleSub_X (w : σ → ℕ) (i : σ) : scaleSub w (X i : MvPolynomial σ R) = X i ^ w i := by
  simp [scaleSub]

lemma scaleSub_monomial (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    scaleSub w (monomial s a) = monomial (scale w s) a := by
  unfold scaleSub
  rw [bind₁_monomial]
  have h1 : (monomial (scale w s) a : MvPolynomial σ R) = C a * monomial (scale w s) 1 := by
    rw [C_mul_monomial, mul_one]
  rw [h1, ← prod_X_pow_eq_monomial]
  congr 1
  rw [← Finset.prod_subset (scale_support_subset w s)]
  · apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, scale_apply]
  · intro i _ hi
    rw [Finsupp.mem_support_iff, not_not] at hi
    rw [← pow_mul, ← scale_apply w s i, hi, pow_zero]

lemma scaleSub_eq_sum (w : σ → ℕ) (f : MvPolynomial σ R) :
    scaleSub w f = ∑ s ∈ f.support, monomial (scale w s) (f.coeff s) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  simp_rw [scaleSub_monomial]

lemma coeff_scaleSub_scale {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (f : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (scaleSub w f).coeff (scale w s) = f.coeff s := by
  rw [scaleSub_eq_sum, coeff_sum, Finset.sum_eq_single s]
  · simp [coeff_monomial]
  · intro t _ hts
    rw [coeff_monomial, ite_eq_right_iff]
    intro h
    exact absurd (scale_injective hw h) hts
  · intro hs
    simp only [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]

lemma support_scaleSub_subset (w : σ → ℕ) (f : MvPolynomial σ R) :
    (scaleSub w f).support ⊆ f.support.image (scale w) := by
  rw [scaleSub_eq_sum]
  refine MvPolynomial.support_sum.trans ?_
  intro t ht
  rw [Finset.mem_biUnion] at ht
  obtain ⟨s, hs, hts⟩ := ht
  rw [Finset.mem_image]
  refine ⟨s, hs, ?_⟩
  have h := support_monomial_subset hts
  rw [Finset.mem_singleton] at h
  exact h.symm

lemma degreeOf_scaleSub_le (w : σ → ℕ) (f : MvPolynomial σ R) (i : σ) :
    degreeOf i (scaleSub w f) ≤ w i * degreeOf i f := by
  rw [degreeOf_le_iff]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (support_scaleSub_subset w f ht)
  rw [scale_apply]
  exact Nat.mul_le_mul_left _ (monomial_le_degreeOf i hs)

lemma le_degreeOf_scaleSub {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (f : MvPolynomial σ R) (i : σ) :
    w i * degreeOf i f ≤ degreeOf i (scaleSub w f) := by
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨s, hs, hsi⟩ : ∃ s ∈ f.support, degreeOf i f = s i := by
      rw [degreeOf_eq_sup]
      exact Finset.exists_mem_eq_sup _ (support_nonempty.mpr hf) _
    have hmem : scale w s ∈ (scaleSub w f).support := by
      rw [MvPolynomial.mem_support_iff, coeff_scaleSub_scale hw]
      exact MvPolynomial.mem_support_iff.mp hs
    have h := monomial_le_degreeOf i hmem
    rw [scale_apply, ← hsi] at h
    exact h

lemma degreeOf_scaleSub {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (f : MvPolynomial σ R) (i : σ) :
    degreeOf i (scaleSub w f) = w i * degreeOf i f :=
  le_antisymm (degreeOf_scaleSub_le w f i) (le_degreeOf_scaleSub hw f i)

lemma scaleSub_eq_zero_iff {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (f : MvPolynomial σ R) :
    scaleSub w f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext s
    rw [← coeff_scaleSub_scale hw f s, h]
    simp
  · rintro rfl
    simp

lemma eval_scaleSub (w : σ → ℕ) (x : σ → R) (p : MvPolynomial σ R) :
    eval x (scaleSub w p) = eval (fun i => x i ^ w i) p := by
  unfold scaleSub
  simp only [MvPolynomial.eval, eval₂Hom_bind₁, map_pow, eval₂Hom_X']

/-- Evaluation of a twisted polynomial: if `x i ^ w i = τ (x i ^ u i)` for every coordinate, then
`(scaleSub w (map τ G))(x) = τ ((scaleSub u G)(x))`. This is the computation behind Lemma 4.1(a). -/
lemma eval_scaleSub_map (τ : R →+* R) (w u : σ → ℕ) (G : MvPolynomial σ R) (x : σ → R)
    (hx : ∀ i, x i ^ w i = τ (x i ^ u i)) :
    eval x (scaleSub w (map τ G)) = τ (eval x (scaleSub u G)) := by
  rw [eval_scaleSub, eval_scaleSub, eval_map]
  have h : τ (eval (fun i => x i ^ u i) G)
      = eval₂ (τ.comp (RingHom.id R)) (τ ∘ fun i => x i ^ u i) G :=
    eval₂_comp_left τ (RingHom.id R) _ G
  rw [h, RingHom.comp_id]
  congr 1
  funext i
  exact hx i

end Scale

/-! ## Part B: derivatives of twisted polynomials in characteristic two -/
section Deriv

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

lemma pderiv_X_pow_two_pow (v : σ → ℕ) (j k : σ) (hj : v j = 0) :
    pderiv j (X k ^ 2 ^ v k : MvPolynomial σ R) = scaleSub (fun k => 2 ^ v k) (pderiv j (X k)) := by
  by_cases hk : k = j
  · rw [hk]
    simp [hj, pderiv_X]
  · rw [pderiv_X, Pi.single_eq_of_ne hk, map_zero, Derivation.leibniz_pow, pderiv_X,
      Pi.single_eq_of_ne hk]
    simp

/-- Lemma 4.1(c): in the direction `j` where no power is taken, `pderiv j` commutes with the twist. -/
lemma pderiv_scaleSub_of_eq_zero (v : σ → ℕ) (j : σ) (hj : v j = 0) (H : MvPolynomial σ R) :
    pderiv j (scaleSub (fun k => 2 ^ v k) H) = scaleSub (fun k => 2 ^ v k) (pderiv j H) := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [scaleSub]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p k hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, scaleSub_X, hp,
      pderiv_X_pow_two_pow v j k hj]
    simp only [smul_eq_mul, map_mul, scaleSub_X]

/-- Lemma 4.1(b): in a direction `i` with `v i ≠ 0`, all exponents of `X i` in the twisted
polynomial are even, so `pderiv i` kills it in characteristic two. -/
lemma pderiv_scaleSub_of_ne_zero [CharP R 2] (v : σ → ℕ) (i : σ) (hi : v i ≠ 0)
    (H : MvPolynomial σ R) :
    pderiv i (scaleSub (fun k => 2 ^ v k) H) = 0 := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [scaleSub]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p k hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_zero, add_zero, scaleSub_X, Derivation.leibniz_pow]
    by_cases hk : k = i
    · have h2 : ((2 ^ v k : ℕ) : MvPolynomial σ R) = 0 := by
        rw [CharP.cast_eq_zero_iff (MvPolynomial σ R) 2]
        exact dvd_pow_self 2 (hk ▸ hi)
      rw [nsmul_eq_mul, h2, zero_mul, smul_zero]
    · rw [pderiv_X, Pi.single_eq_of_ne hk]
      simp

end Deriv

/-! ## Part C: Frobenius selectors and grid exponent identities -/
section Grid

/-- If `x ^ q ^ m = x` then `x ^ q ^ s` depends only on `s mod m`. -/
lemma pow_pow_mod {M : Type*} [Monoid M] {x : M} {q m : ℕ} (hx : x ^ q ^ m = x)
    (s : ℕ) : x ^ q ^ s = x ^ q ^ (s % m) := by
  have key : ∀ k, x ^ (q ^ m) ^ k = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hx]
  conv_lhs => rw [← Nat.div_add_mod s m, pow_add, pow_mul q m, pow_mul x, key]

lemma pow_pow_congr {M : Type*} [Monoid M] {x : M} {q m : ℕ} (hx : x ^ q ^ m = x)
    {a b : ℕ} (hab : a ≡ b [MOD m]) : x ^ q ^ a = x ^ q ^ b := by
  have h : a % m = b % m := hab
  rw [pow_pow_mod hx a, pow_pow_mod hx b, h]

/-- Lemma 1.1 (Frobenius selectors), arithmetic part: for pairwise coprime moduli, any family of
residues is realised by one exponent `s`. -/
lemma exists_selector {ι : Type*} [Fintype ι] (m : ι → ℕ) (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (fun i k => Nat.Coprime (m i) (m k))) (w : ι → ℕ) :
    ∃ s : ℕ, ∀ i, s ≡ w i [MOD m i] := by
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset w m Finset.univ (fun i _ => hm i)
    (by
      intro i _ k _ hik
      exact hcop hik)
  exact ⟨k, fun i => hk i (Finset.mem_univ i)⟩

/-- Generalised CRT with a common factor `f` in all moduli: residues that agree modulo `f` are
simultaneously realised modulo `f * m i`. -/
lemma exists_selector_mul {ι : Type*} [Fintype ι] [Nonempty ι] (f : ℕ) (m : ι → ℕ)
    (hm : ∀ i, m i ≠ 0) (hcop : Pairwise (fun i k => Nat.Coprime (m i) (m k)))
    (r : ι → ℕ) (hr : ∀ i k, r i ≡ r k [MOD f]) :
    ∃ e : ℕ, ∀ i, e ≡ r i [MOD f * m i] := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨e', he'⟩ := exists_selector m hm hcop (fun i => r i / f)
  refine ⟨r i₀ % f + f * e', fun i => ?_⟩
  have h1 : r i = r i₀ % f + f * (r i / f) := by
    have h2 : r i % f = r i₀ % f := hr i i₀
    calc r i = r i % f + f * (r i / f) := (Nat.mod_add_div (r i) f).symm
      _ = r i₀ % f + f * (r i / f) := by rw [h2]
  rw [h1]
  exact Nat.ModEq.add_left _ ((he' i).mul_left' f)

end Grid

/-! ## Part D: the twist lemma, core form (Lemma 4.1 (a)–(d)) -/
section Twist

variable {ι F : Type*} [DecidableEq ι] [Field F] [CharP F 2] [PerfectRing F 2]

/-- The inverse `e`-fold Frobenius `c ↦ c ^ (2⁻ᵉ)`, as a ring homomorphism. -/
noncomputable def invFrob (e : ℕ) : F →+* F := ((iterateFrobeniusEquiv F 2 e).symm : F ≃+* F)

lemma invFrob_apply (e : ℕ) (c : F) : invFrob e c = (iterateFrobeniusEquiv F 2 e).symm c := rfl

lemma invFrob_injective (e : ℕ) : Function.Injective (invFrob e : F → F) :=
  (iterateFrobeniusEquiv F 2 e).symm.injective

lemma invFrob_apply_pow (e : ℕ) (c : F) : invFrob e c ^ 2 ^ e = c := by
  rw [invFrob_apply, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply]
  exact (iterateFrobeniusEquiv F 2 e).apply_symm_apply c

/-- The twist `R_j := (scaleSub (2 ^ v)) (map (invFrob e) G)`. -/
noncomputable def twist (v : ι → ℕ) (e : ℕ) (G : MvPolynomial ι F) : MvPolynomial ι F :=
  scaleSub (fun i => 2 ^ v i) (map (invFrob e) G)

/-- Coordinate identity: on a grid point `x` fixed by `x ↦ x ^ (2 ^ fm)`, and with
`v + e ≡ u (mod fm)`, we have `x ^ 2 ^ v = invFrob e (x ^ 2 ^ u)`. -/
lemma coord_identity {x : F} {fm : ℕ} (hx : x ^ 2 ^ fm = x) {v u e : ℕ}
    (hcong : v + e ≡ u [MOD fm]) : x ^ 2 ^ v = invFrob e (x ^ 2 ^ u) := by
  apply (iterateFrobeniusEquiv F 2 e).injective
  rw [iterateFrobeniusEquiv_apply, iterateFrobeniusEquiv_apply, iterateFrobenius_def,
    iterateFrobenius_def, invFrob_apply_pow, ← pow_mul, ← pow_add]
  exact pow_pow_congr hx hcong

/-- **Lemma 4.1 (a)**: on the grid, the twist evaluates to `invFrob e` of `F := scaleSub (2 ^ u) G`. -/
theorem twist_eval (fm : ι → ℕ) (v u : ι → ℕ) (e : ℕ)
    (hcong : ∀ i, v i + e ≡ u i [MOD fm i]) (G : MvPolynomial ι F) (x : ι → F)
    (hx : ∀ i, x i ^ 2 ^ fm i = x i) :
    eval x (twist v e G) = invFrob e (eval x (scaleSub (fun i => 2 ^ u i) G)) := by
  unfold twist
  apply eval_scaleSub_map
  intro i
  exact coord_identity (hx i) (hcong i)

/-- **Lemma 4.1 (b)** -/
theorem pderiv_twist_of_ne_zero (v : ι → ℕ) (e : ℕ) (i : ι) (hi : v i ≠ 0)
    (G : MvPolynomial ι F) : pderiv i (twist v e G) = 0 :=
  pderiv_scaleSub_of_ne_zero v i hi _

/-- **Lemma 4.1 (c)** -/
theorem pderiv_twist_of_eq_zero (v : ι → ℕ) (e : ℕ) (j : ι) (hj : v j = 0)
    (G : MvPolynomial ι F) : pderiv j (twist v e G) = twist v e (pderiv j G) := by
  unfold twist
  rw [pderiv_scaleSub_of_eq_zero v j hj, pderiv_map]

/-- **Lemma 4.1 (d)**: degree bookkeeping. -/
theorem degreeOf_twist (v : ι → ℕ) (e : ℕ) (G : MvPolynomial ι F) (i : ι) :
    degreeOf i (twist v e G) = 2 ^ v i * degreeOf i G := by
  unfold twist
  rw [degreeOf_scaleSub (fun i => pow_ne_zero _ two_ne_zero)]
  congr 1
  -- `map` by an injective ring hom preserves the support, hence the degree
  rw [degreeOf_eq_sup, degreeOf_eq_sup, support_map_of_injective G (invFrob_injective e)]

end Twist

/-! ## Part E: choice of the exponents `v`, `e` (the arithmetic of Lemma 4.1) -/
section Exponents

/-- Choice of `v`: `v j = 0`, and for `i ≠ j`, `v i ∈ [1, f]` with `v i + u j ≡ u i [MOD f]`. -/
lemma exists_v {ι : Type*} [DecidableEq ι] (f : ℕ) (hf : 0 < f) (u : ι → ℕ) (j : ι) :
    ∃ v : ι → ℕ, v j = 0 ∧ (∀ i, i ≠ j → 1 ≤ v i ∧ v i ≤ f) ∧ ∀ i, v i + u j ≡ u i [MOD f] := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  let d : ι → ℕ := fun i => u i + f' * u j
  let vOf : ℕ → ℕ := fun a => if a % (f' + 1) = 0 then f' + 1 else a % (f' + 1)
  have hvOf1 : ∀ a, 1 ≤ vOf a ∧ vOf a ≤ f' + 1 := by
    intro a
    simp only [vOf]
    split_ifs with h0
    · exact ⟨by omega, le_refl _⟩
    · exact ⟨Nat.pos_of_ne_zero h0, (Nat.mod_lt _ (by omega)).le⟩
  have hvOf2 : ∀ a, vOf a ≡ a [MOD f' + 1] := by
    intro a
    simp only [vOf]
    split_ifs with h0
    · show (f' + 1) % (f' + 1) = a % (f' + 1)
      rw [Nat.mod_self, h0]
    · show a % (f' + 1) % (f' + 1) = a % (f' + 1)
      exact Nat.mod_mod _ _
  refine ⟨fun i => if i = j then 0 else vOf (d i), by simp, ?_, ?_⟩
  · intro i hij
    simp only [if_neg hij]
    exact hvOf1 _
  · intro i
    by_cases hij : i = j
    · rw [hij]
      show (if j = j then 0 else vOf (d j)) + u j ≡ u j [MOD f' + 1]
      rw [if_pos rfl, zero_add]
    · simp only [if_neg hij]
      calc vOf (d i) + u j ≡ d i + u j [MOD f' + 1] := (hvOf2 (d i)).add_right _
        _ = u i + (f' + 1) * u j := by simp only [d]; ring
        _ ≡ u i + 0 [MOD f' + 1] :=
            Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
        _ = u i := add_zero _

/-- The exponents needed in Lemma 4.1: `v j = 0`, `1 ≤ v i ≤ f` for `i ≠ j`, and
`v i + e ≡ u i (mod f * m i)` for all `i`. Uses pairwise coprimality of the `m i`. -/
theorem exists_twist_exponents {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℕ) (hf : 0 < f)
    (m : ι → ℕ) (hm : ∀ i, m i ≠ 0) (hcop : Pairwise (fun i k => Nat.Coprime (m i) (m k)))
    (u : ι → ℕ) (j : ι) :
    ∃ v : ι → ℕ, ∃ e : ℕ, v j = 0 ∧ (∀ i, i ≠ j → 1 ≤ v i ∧ v i ≤ f) ∧
      ∀ i, v i + e ≡ u i [MOD f * m i] := by
  obtain ⟨v, hvj, hvb, hvu⟩ := exists_v f hf u j
  have hle : ∀ i, v i ≤ u i + f * m i * v i := fun i =>
    le_add_left (Nat.le_mul_of_pos_left _ (Nat.mul_pos hf (Nat.pos_of_ne_zero (hm i))))
  let r : ι → ℕ := fun i => u i + f * m i * v i - v i
  have hrv : ∀ i, r i + v i = u i + f * m i * v i := fun i => Nat.sub_add_cancel (hle i)
  have hrmod : ∀ i, r i ≡ u j [MOD f] := by
    intro i
    have h2 : u i + f * m i * v i ≡ u i + 0 [MOD f] :=
      Nat.ModEq.add_left (u i)
        (Nat.modEq_zero_iff_dvd.mpr (by rw [mul_assoc]; exact dvd_mul_right f _))
    rw [add_zero] at h2
    have h1 : r i + v i ≡ u j + v i [MOD f] := by
      rw [hrv i]
      exact h2.trans ((hvu i).symm.trans (by rw [add_comm]))
    exact Nat.ModEq.add_right_cancel' (v i) h1
  have : Nonempty ι := ⟨j⟩
  obtain ⟨e, he⟩ := exists_selector_mul f m hm hcop r (fun i k => (hrmod i).trans (hrmod k).symm)
  refine ⟨v, e, hvj, hvb, fun i => ?_⟩
  calc v i + e ≡ v i + r i [MOD f * m i] := Nat.ModEq.add_left _ (he i)
    _ = u i + f * m i * v i := by rw [add_comm, hrv i]
    _ ≡ u i + 0 [MOD f * m i] :=
        Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
    _ = u i := add_zero _

end Exponents

/-! ## Part F: the polynomial `b_j = scaleSub (2 ^ u) (pderiv j G)` -/
section BDeriv

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

lemma mem_support_pderiv (H : MvPolynomial σ R) (j : σ) {t : σ →₀ ℕ}
    (ht : t ∈ (pderiv j H).support) :
    ∃ s ∈ H.support, (s j : R) ≠ 0 ∧ t = s - Finsupp.single j 1 := by
  have h1 : pderiv j H
      = ∑ s ∈ H.support, monomial (s - Finsupp.single j 1) (H.coeff s * (s j : R)) := by
    conv_lhs => rw [H.as_sum]
    rw [map_sum]
    simp_rw [pderiv_monomial]
  rw [h1] at ht
  obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
  refine ⟨s, hs, ?_, ?_⟩
  · intro h0
    rw [h0, mul_zero, monomial_zero] at hts
    simp at hts
  · have h2 := support_monomial_subset hts
    rwa [Finset.mem_singleton] at h2

lemma degreeOf_pderiv_le (H : MvPolynomial σ R) (i j : σ) :
    degreeOf i (pderiv j H) ≤ degreeOf i H := by
  rw [degreeOf_le_iff]
  intro t ht
  obtain ⟨s, hs, -, rfl⟩ := mem_support_pderiv H j ht
  calc (s - Finsupp.single j 1 : σ →₀ ℕ) i ≤ s i := by
        rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _
    _ ≤ degreeOf i H := monomial_le_degreeOf i hs

/-- `b_j := scaleSub w (pderiv j G)` has strictly smaller total degree than `scaleSub w G`
(when `pderiv j G ≠ 0` and all `w i ≠ 0`). -/
lemma totalDegree_scaleSub_pderiv_lt {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (G : MvPolynomial σ R)
    (j : σ) (hG : pderiv j G ≠ 0) :
    (scaleSub w (pderiv j G)).totalDegree < (scaleSub w G).totalDegree := by
  set D := (scaleSub w G).totalDegree with hD
  have hlt : ∀ t ∈ (scaleSub w (pderiv j G)).support, (t.sum fun _ e => e) < D := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp (support_scaleSub_subset w _ ht)
    obtain ⟨s, hs, hsj, rfl⟩ := mem_support_pderiv G j ht'
    have hsj' : s j ≠ 0 := by
      intro h0
      apply hsj
      rw [h0]
      simp
    have hjs : j ∈ s.support := Finsupp.mem_support_iff.mpr hsj'
    have hsub1 : (scale w (s - Finsupp.single j 1)).support ⊆ s.support := by
      refine (scale_support_subset _ _).trans ?_
      intro x hx
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      rw [Finsupp.tsub_apply, h0]
      simp
    have hsub2 : (scale w s).support ⊆ s.support := scale_support_subset _ _
    rw [Finsupp.sum_of_support_subset _ hsub1 _ (fun _ _ => rfl)]
    have hmem : scale w s ∈ (scaleSub w G).support := by
      rw [MvPolynomial.mem_support_iff, coeff_scaleSub_scale hw]
      exact MvPolynomial.mem_support_iff.mp hs
    have hle := le_totalDegree hmem
    rw [Finsupp.sum_of_support_subset _ hsub2 _ (fun _ _ => rfl)] at hle
    refine lt_of_lt_of_le ?_ hle
    apply Finset.sum_lt_sum
    · intro x _
      simp only [scale_apply, Finsupp.tsub_apply]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    · refine ⟨j, hjs, ?_⟩
      simp only [scale_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (Nat.pos_of_ne_zero hsj') one_pos)
        (Nat.pos_of_ne_zero (hw j))
  have hne : scaleSub w (pderiv j G) ≠ 0 := (scaleSub_eq_zero_iff hw _).not.mpr hG
  obtain ⟨t0, ht0⟩ := support_nonempty.mpr hne
  have hDpos : 0 < D := lt_of_le_of_lt (Nat.zero_le _) (hlt t0 ht0)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hDpos]
  exact hlt

end BDeriv

/-! ## Part G: Lemma 4.1 of the note, assembled -/
section Main

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2] [PerfectRing F 2]

/-- **Lemma 4.1 of the note** (core form). Setting: `P = 2 ^ f`, pairwise coprime `m i`, grid
points `x` with `x i ^ 2 ^ (f * m i) = x i` (i.e. `x i ∈ 𝔽_{P^{m i}}`); `F = scaleSub (2 ^ u) G`
with `pderiv j G ≠ 0` (the 2-power extraction in direction `j` is maximal). Then there are `v`, `e`
with `v j = 0`, `1 ≤ v i ≤ f` for `i ≠ j`, such that `R := twist v e G` satisfies

* (a) `R(x) = σ(F(x))` on the grid, with `σ = invFrob e` injective (same zero set);
* (b) `∂ᵢ R = 0` identically for `i ≠ j`;
* (c) `(∂ⱼ R)(x) = σ(b(x))` on the grid, where `b := scaleSub (2 ^ u) (pderiv j G)`;
* (d) `degᵢ R ≤ 2 ^ f · degᵢ F` for `i ≠ j` and `degⱼ R ≤ degⱼ F`;

and `b ≠ 0`, `totalDegree b < totalDegree F`, `degᵢ b ≤ degᵢ F` for all `i`. -/
theorem lemma_4_1 (f : ℕ) (hf : 0 < f) (m : ι → ℕ) (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (fun i k => Nat.Coprime (m i) (m k))) (u : ι → ℕ) (G : MvPolynomial ι F)
    (j : ι) (hG : pderiv j G ≠ 0) :
    ∃ v : ι → ℕ, ∃ e : ℕ, v j = 0 ∧ (∀ i, i ≠ j → 1 ≤ v i ∧ v i ≤ f) ∧
      (∀ x : ι → F, (∀ i, x i ^ 2 ^ (f * m i) = x i) →
        eval x (twist v e G) = invFrob e (eval x (scaleSub (fun i => 2 ^ u i) G))) ∧
      (∀ i, i ≠ j → pderiv i (twist v e G) = 0) ∧
      (∀ x : ι → F, (∀ i, x i ^ 2 ^ (f * m i) = x i) →
        eval x (pderiv j (twist v e G))
          = invFrob e (eval x (scaleSub (fun i => 2 ^ u i) (pderiv j G)))) ∧
      (∀ i, i ≠ j →
        degreeOf i (twist v e G) ≤ 2 ^ f * degreeOf i (scaleSub (fun i => 2 ^ u i) G)) ∧
      degreeOf j (twist v e G) ≤ degreeOf j (scaleSub (fun i => 2 ^ u i) G) ∧
      scaleSub (fun i => 2 ^ u i) (pderiv j G) ≠ 0 ∧
      (scaleSub (fun i => 2 ^ u i) (pderiv j G)).totalDegree
        < (scaleSub (fun i => 2 ^ u i) G).totalDegree ∧
      ∀ i, degreeOf i (scaleSub (fun i => 2 ^ u i) (pderiv j G))
        ≤ degreeOf i (scaleSub (fun i => 2 ^ u i) G) := by
  obtain ⟨v, e, hvj, hvb, hcong⟩ := exists_twist_exponents f hf m hm hcop u j
  have hw : ∀ i, (2 : ℕ) ^ u i ≠ 0 := fun i => pow_ne_zero _ two_ne_zero
  refine ⟨v, e, hvj, hvb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact twist_eval (fun i => f * m i) v u e hcong G x hx
  · intro i hi
    exact pderiv_twist_of_ne_zero v e i (by have := (hvb i hi).1; omega) G
  · intro x hx
    rw [pderiv_twist_of_eq_zero v e j hvj]
    exact twist_eval (fun i => f * m i) v u e hcong (pderiv j G) x hx
  · intro i hi
    rw [degreeOf_twist, degreeOf_scaleSub hw]
    calc 2 ^ v i * degreeOf i G ≤ 2 ^ f * degreeOf i G :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hvb i hi).2)
      _ ≤ 2 ^ f * (2 ^ u i * degreeOf i G) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hw i)))
  · rw [degreeOf_twist, degreeOf_scaleSub hw, hvj, pow_zero, one_mul]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hw j))
  · exact (scaleSub_eq_zero_iff hw _).not.mpr hG
  · exact totalDegree_scaleSub_pderiv_lt hw G j hG
  · intro i
    rw [degreeOf_scaleSub hw, degreeOf_scaleSub hw]
    exact Nat.mul_le_mul_left _ (degreeOf_pderiv_le G i j)

end Main

/-! ## Part H: `Q ∤ 𝒯Q` (Lemma 2.1 of the note) -/
section NoDivide

variable {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The `p ^ f`-th power of a multivariate polynomial in characteristic `p` is the expansion of
its coefficientwise Frobenius image. -/
lemma pow_char_pow_eq_expand {σ : Type*} (f : ℕ) (g : MvPolynomial σ K) :
    g ^ (p ^ f) = expand (p ^ f) (map (iterateFrobenius K p f) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [map_C, expand_C, iterateFrobenius_def, C_pow]
  | add q r hq hr => rw [add_pow_char_pow, hq, hr, map_add, map_add]
  | mul_X q i hq => rw [mul_pow, hq, map_mul, map_mul, map_X, expand_X]

/-- `𝒯Q := Q^σ(X₀, X₁^P)`: twist the coefficients by `σ`, then substitute `X₁ ↦ X₁ ^ P`. -/
noncomputable def tw (σ : K →+* K) (P : ℕ) (Q : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  scaleSub ![1, P] (map σ Q)

/-- **Lemma 2.1 of the note**: an irreducible `Q` of bidegree `(a, b)` with `a, b ≥ 1` does not
divide `𝒯Q = Q^σ(X₀, X₁^P)`, for any field automorphism `σ` and `P = p ^ f` with `f ≥ 1`. -/
theorem not_dvd_tw (σ : K ≃+* K) (f : ℕ) (hf : 0 < f) (Q : MvPolynomial (Fin 2) K)
    (hQ : Irreducible Q) (h0 : 0 < degreeOf 0 Q) (h1 : 0 < degreeOf 1 Q) :
    ¬ Q ∣ tw (σ : K →+* K) (p ^ f) Q := by
  intro hdvd
  have hP1 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  have hw0 : ∀ i : Fin 2, (![p ^ f, 1] : Fin 2 → ℕ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hp.out.ne_zero]
  have hw1 : ∀ i : Fin 2, (![1, p ^ f] : Fin 2 → ℕ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hp.out.ne_zero]
  -- the composite substitution `X₀ ↦ X₀^P` after `X₁ ↦ X₁^P` is `expand P`
  have hcomp : (scaleSub ![p ^ f, 1] : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K).comp
      (scaleSub ![1, p ^ f]) = expand (p ^ f) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [scaleSub_X, expand_X]
  -- `θσ := Frob⁻ᶠ ∘ σ` and `H := map θσ Q`, so that `H ^ P = expand P (map σ Q)`
  set θσe : K ≃+* K := σ.trans (iterateFrobeniusEquiv K p f).symm with hθσe
  set H : MvPolynomial (Fin 2) K := map (θσe : K →+* K) Q with hH
  have hfrob : (iterateFrobenius K p f).comp (θσe : K →+* K) = (σ : K →+* K) := by
    ext c
    show iterateFrobenius K p f ((iterateFrobeniusEquiv K p f).symm (σ c)) = σ c
    rw [← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hHirr : Irreducible H := by
    have h := (MulEquiv.irreducible_iff (MvPolynomial.mapEquiv (Fin 2) θσe)).mpr hQ
    simpa [hH] using h
  have hHprime : Prime H := UniqueFactorizationMonoid.irreducible_iff_prime.mp hHirr
  have hkey : scaleSub ![p ^ f, 1] (tw (σ : K →+* K) (p ^ f) Q) = H ^ (p ^ f) := by
    unfold tw
    rw [← AlgHom.comp_apply, hcomp, pow_char_pow_eq_expand p f H, hH, map_map, hfrob]
  have hQne : Q ≠ 0 := hQ.ne_zero
  have hψQne : scaleSub ![p ^ f, 1] Q ≠ 0 := (scaleSub_eq_zero_iff hw0 Q).not.mpr hQne
  have hmapdeg : ∀ i, degreeOf i (map (σ : K →+* K) Q) = degreeOf i Q := by
    intro i
    rw [degreeOf_eq_sup, degreeOf_eq_sup, support_map_of_injective _ σ.injective]
  have hdeg0 : degreeOf 0 (scaleSub ![p ^ f, 1] Q) = p ^ f * degreeOf 0 Q := by
    rw [degreeOf_scaleSub hw0]
    simp
  have hdeg1 : degreeOf 1 (scaleSub ![p ^ f, 1] Q) = degreeOf 1 Q := by
    rw [degreeOf_scaleSub hw0]
    simp
  have hdegH : degreeOf 0 H = degreeOf 0 Q := by
    rw [degreeOf_eq_sup, degreeOf_eq_sup, hH, support_map_of_injective _ θσe.injective]
  have hdegtw : degreeOf 1 (scaleSub ![p ^ f, 1] (tw (σ : K →+* K) (p ^ f) Q))
      = p ^ f * degreeOf 1 Q := by
    rw [degreeOf_scaleSub hw0]
    unfold tw
    rw [degreeOf_scaleSub hw1, hmapdeg]
    simp
  -- `ψ Q ∣ H ^ P`, hence `ψ Q ~ H ^ e` for some `e ≤ P`
  have hdvd' : scaleSub ![p ^ f, 1] Q ∣ H ^ (p ^ f) := by
    rw [← hkey]
    exact map_dvd _ hdvd
  obtain ⟨e, he, hassoc⟩ := (dvd_prime_pow hHprime _).mp hdvd'
  -- `e = P`, by comparing degrees in `X₀`
  have heP : e = p ^ f := by
    obtain ⟨W, hW⟩ := hassoc.dvd
    have hWne : W ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hW
      exact pow_ne_zero _ hHprime.ne_zero hW
    have h2 : degreeOf 0 (H ^ e) = degreeOf 0 (scaleSub ![p ^ f, 1] Q) + degreeOf 0 W := by
      rw [hW, degreeOf_mul_eq hψQne hWne]
    have h5 : p ^ f * degreeOf 0 Q ≤ e * degreeOf 0 Q :=
      calc p ^ f * degreeOf 0 Q = degreeOf 0 (scaleSub ![p ^ f, 1] Q) := hdeg0.symm
        _ ≤ degreeOf 0 (H ^ e) := by rw [h2]; exact Nat.le_add_right _ _
        _ ≤ e * degreeOf 0 H := degreeOf_pow_le _ _ _
        _ = e * degreeOf 0 Q := by rw [hdegH]
    have hPe : p ^ f ≤ e := Nat.le_of_mul_le_mul_right h5 h0
    omega
  subst heP
  -- now `H ^ P = ψ(𝒯Q)` divides `ψ Q`: compare degrees in `X₁`
  obtain ⟨W, hW⟩ := hassoc.symm.dvd
  have hWne : W ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hW
    exact hψQne hW
  have h4 : degreeOf 1 (scaleSub ![p ^ f, 1] Q) = degreeOf 1 (H ^ (p ^ f)) + degreeOf 1 W := by
    rw [hW, degreeOf_mul_eq (pow_ne_zero _ hHprime.ne_zero) hWne]
  rw [← hkey, hdegtw, hdeg1] at h4
  have h6 : 2 * degreeOf 1 Q ≤ p ^ f * degreeOf 1 Q := Nat.mul_le_mul_right _ hP1
  omega

end NoDivide

end CoprimeFrobenius

/-! ## Verification hooks

`#print axioms` lists every axiom a theorem ultimately depends on. For a genuine proof the list
must contain only the three standard axioms `propext`, `Classical.choice`, `Quot.sound`; the
presence of `sorryAx` would mean an incomplete proof. -/
#print axioms CoprimeFrobenius.lemma_4_1
#print axioms CoprimeFrobenius.not_dvd_tw
#print axioms CoprimeFrobenius.exists_selector_mul
#eval Lean.versionString
#eval "CoprimeFrobenius: all declarations checked"
