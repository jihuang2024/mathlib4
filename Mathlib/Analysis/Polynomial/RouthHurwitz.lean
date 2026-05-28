/-
Copyright (c) 2026 Ji Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Huang
-/
module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Hurwitz Stability of Real Polynomials

A real polynomial is called *Hurwitz stable* if all of its complex roots have strictly negative
real part. This is a fundamental concept in control theory and the analysis of linear ODE systems,
where it characterises asymptotic stability.

## Main Definitions

* `Polynomial.IsHurwitzStable`: all complex roots of a real polynomial have negative real part.

## Main Results

* `Polynomial.isHurwitzStable_X_add_C`: `X + C a` is Hurwitz stable iff `0 < a`.
* `Polynomial.isHurwitzStable_quadratic`: `X ^ 2 + C b * X + C c` is Hurwitz stable
  iff `0 < b ∧ 0 < c`.
* `Polynomial.isHurwitzStable_cubic`: `X ^ 3 + C b * X ^ 2 + C c * X + C d` is Hurwitz stable
  iff `0 < b ∧ 0 < d ∧ d < b * c`.

## Scope

This file treats monic polynomials of degree 1, 2, and 3. The general Routh–Hurwitz criterion
for degree `n` — stated in terms of the `n × n` Hurwitz matrix and its leading principal minors —
requires infrastructure (Cauchy index or Bezoutian theory) not yet present in Mathlib and is left
for future work.

## References

* <https://en.wikipedia.org/wiki/Routh%E2%80%93Hurwitz_stability_criterion>
-/

@[expose] public section

open Complex Polynomial

namespace Polynomial

variable {a b c d : ℝ}

/-- A real polynomial is *Hurwitz stable* if all its complex roots have strictly negative
real part. -/
def IsHurwitzStable (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0

/-- The zero polynomial is not Hurwitz stable since every complex number is a root. -/
theorem not_isHurwitzStable_zero : ¬IsHurwitzStable (0 : Polynomial ℝ) := by
  intro h
  have := h 0 (by simp [IsRoot.def])
  simp at this

/-- A Hurwitz stable polynomial is nonzero. -/
theorem IsHurwitzStable.ne_zero {p : Polynomial ℝ} (hp : IsHurwitzStable p) : p ≠ 0 :=
  fun h => not_isHurwitzStable_zero (h ▸ hp)

/-- The monic linear polynomial `X + C a` is Hurwitz stable if and only if `0 < a`. -/
theorem isHurwitzStable_X_add_C : IsHurwitzStable (X + C a) ↔ 0 < a := by
  constructor
  · intro h
    have hroot : ((X + C a : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot (-(a : ℂ)) := by
      rw [IsRoot.def]
      simp [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
            RCLike.algebraMap_eq_ofReal]
    have key := h _ hroot
    simp only [neg_re, ofReal_re] at key
    linarith
  · intro ha z hz
    rw [IsRoot.def] at hz
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
               RCLike.algebraMap_eq_ofReal, Polynomial.eval_add, Polynomial.eval_X,
               Polynomial.eval_C] at hz
    have heq : z = -(a : ℂ) := eq_neg_of_add_eq_zero_left hz
    simp only [heq, neg_re, ofReal_re]
    linarith

-- Helper: the degree of the complexified quadratic is positive
private lemma quad_map_degree_pos (b c : ℝ) :
    0 < ((X ^ 2 + C b * X + C c : ℝ[X]).map (algebraMap ℝ ℂ)).degree := by
  have hnd : (X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := by
    rw [show (X ^ 2 + C b * X + C c : ℝ[X]) = C 1 * X ^ 2 + C b * X + C c by simp]
    exact natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)
  have hne : X ^ 2 + C b * X + C c ≠ (0 : ℝ[X]) := by
    intro h
    have := congr_arg (Polynomial.coeff · 2) h
    simp at this
  rw [Polynomial.degree_map_eq_of_injective (algebraMap ℝ ℂ).injective,
      degree_eq_natDegree hne, hnd]
  norm_num

-- Helper: IsRoot of the quadratic corresponds to the complex equation
private lemma quad_isRoot_iff (b c : ℝ) (z : ℂ) :
    ((X ^ 2 + C b * X + C c : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot z ↔
    z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
  rw [IsRoot.def]
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.map_C, RCLike.algebraMap_eq_ofReal, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

-- Helper: real and imaginary parts of a quadratic root equation
private lemma quad_re_im (b c : ℝ) (z : ℂ) (hz : z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) :
    z.re ^ 2 - z.im ^ 2 + b * z.re + c = 0 ∧ z.im * (2 * z.re + b) = 0 := by
  exact ⟨by have := congr_arg re hz; simp [add_re, sq, mul_re] at this; linarith,
         by have := congr_arg im hz; simp [add_im, sq, mul_im] at this; linarith⟩

/-- The monic quadratic `X ^ 2 + C b * X + C c` is Hurwitz stable iff `0 < b ∧ 0 < c`. -/
theorem isHurwitzStable_quadratic :
    IsHurwitzStable (X ^ 2 + C b * X + C c) ↔ 0 < b ∧ 0 < c := by
  simp_rw [IsHurwitzStable, quad_isRoot_iff]
  constructor
  · intro h
    -- Obtain a root using the Fundamental Theorem of Algebra
    obtain ⟨z, hz⟩ := Complex.exists_root (quad_map_degree_pos b c)
    rw [quad_isRoot_iff] at hz
    have hzre : z.re < 0 := h z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · -- Real root: both the root z.re and the complementary root -b - z.re are in left half-plane
      have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      -- The complementary root -b - z.re is also a root (by Vieta)
      have hroot2 : ((-b - z.re : ℝ) : ℂ) ^ 2 + (b : ℂ) * ((-b - z.re : ℝ) : ℂ) + (c : ℂ) = 0 := by
        norm_cast
        have : (-b - z.re) ^ 2 + b * (-b - z.re) + c = z.re ^ 2 + b * z.re + c := by ring
        linarith [hc_eq]
      have h2re := h (-b - z.re : ℝ) hroot2
      simp only [ofReal_re] at h2re
      exact ⟨by linarith, by nlinarith [hc_eq]⟩
    · -- Complex root: z.re = -b/2
      have hb_val : b = -2 * z.re := by linarith
      constructor
      · linarith
      · rw [hb_val] at hre
        nlinarith [sq_nonneg z.im, sq_nonneg z.re]
  · -- Sufficient: 0 < b, 0 < c implies all roots have Re < 0
    intro ⟨hb, hc⟩ z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · -- Real root: z.re^2 + b*z.re + c = 0 with b, c > 0 forces z.re < 0
      have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      by_contra h
      simp only [not_lt] at h
      nlinarith [sq_nonneg z.re]
    · -- Complex root: 2*z.re + b = 0, so z.re = -b/2 < 0
      linarith

-- Helper: natDegree of our monic cubic is 3
private lemma cubic_natDegree (b c d : ℝ) :
    (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).natDegree = 3 := by
  rw [show (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]) =
      C 1 * X ^ 3 + C b * X ^ 2 + C c * X + C d by simp]
  exact natDegree_cubic (by norm_num : (1 : ℝ) ≠ 0)

-- Helper: IsRoot of the cubic corresponds to the complex equation
private lemma cubic_isRoot_iff (b c d : ℝ) (z : ℂ) :
    ((X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot z ↔
    z ^ 3 + (b : ℂ) * z ^ 2 + (c : ℂ) * z + (d : ℂ) = 0 := by
  rw [IsRoot.def]
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.map_C, RCLike.algebraMap_eq_ofReal, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

-- Helper: real and imaginary parts of a cubic root equation
private lemma cubic_re_im (b c d : ℝ) (z : ℂ)
    (hz : z ^ 3 + (b : ℂ) * z ^ 2 + (c : ℂ) * z + (d : ℂ) = 0) :
    z.re ^ 3 - 3 * z.re * z.im ^ 2 + b * (z.re ^ 2 - z.im ^ 2) + c * z.re + d = 0 ∧
    z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * b * z.re + c) = 0 := by
  constructor
  · have h := congr_arg re hz
    simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero,
               zero_re, show z ^ 3 = z ^ 2 * z from by ring, sq] at h
    nlinarith [sq_nonneg z.re, sq_nonneg z.im, mul_comm z.im z.re]
  · have h := congr_arg im hz
    simp only [add_im, mul_im, mul_re, ofReal_re, ofReal_im, zero_mul, add_zero,
               zero_im, show z ^ 3 = z ^ 2 * z from by ring, sq] at h
    nlinarith [sq_nonneg z.re, sq_nonneg z.im, mul_comm z.im z.re]

-- Helper: every monic real cubic has a real root (via IVT with explicit bounds)
private lemma cubic_has_real_root (b c d : ℝ) :
    ∃ r : ℝ, (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).eval r = 0 := by
  set p := X ^ 3 + C b * X ^ 2 + C c * X + C d with hp_def
  set K := |b| + |c| + |d| + 2 with hK_def
  have hK2 : (2 : ℝ) ≤ K := by linarith [abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have hKb : |b| ≤ K - 2 := by linarith [hK_def, abs_nonneg c, abs_nonneg d]
  have hKc : |c| ≤ K - 2 := by linarith [hK_def, abs_nonneg b, abs_nonneg d]
  have hKd : |d| ≤ K - 2 := by linarith [hK_def, abs_nonneg b, abs_nonneg c]
  have hpos : 0 < p.eval K := by
    simp only [hp_def, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    nlinarith [le_abs_self b, neg_abs_le b, le_abs_self c, neg_abs_le c,
               le_abs_self d, neg_abs_le d, sq_nonneg K, sq_nonneg (K - 2)]
  have hneg : p.eval (-K) < 0 := by
    simp only [hp_def, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    nlinarith [le_abs_self b, neg_abs_le b, le_abs_self c, neg_abs_le c,
               le_abs_self d, neg_abs_le d, sq_nonneg K, sq_nonneg (K - 2)]
  have hle : -K ≤ K := by linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc (p.eval (-K)) (p.eval K) :=
    ⟨le_of_lt hneg, le_of_lt hpos⟩
  obtain ⟨r, _, hr⟩ := (intermediate_value_Icc hle p.continuous.continuousOn) h0mem
  exact ⟨r, hr⟩

/-- The monic cubic `X ^ 3 + C b * X ^ 2 + C c * X + C d` is Hurwitz stable iff
    `0 < b ∧ 0 < d ∧ d < b * c`. -/
theorem isHurwitzStable_cubic :
    IsHurwitzStable (X ^ 3 + C b * X ^ 2 + C c * X + C d) ↔ 0 < b ∧ 0 < d ∧ d < b * c := by
  constructor
  · intro h
    -- Convert real roots to complex for Hurwitz stability
    have h_real_neg : ∀ y : ℝ, (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).IsRoot y → y < 0 := by
      intro y hy
      have hcy : ((X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot ↑y := by
        rw [cubic_isRoot_iff]
        have h := IsRoot.def.mp hy
        simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at h
        exact_mod_cast h
      have := h ↑y hcy
      simpa [Complex.ofReal_re] using this
    -- d > 0: use that all real roots < 0 and leadingCoeff = 1 ≥ 0
    have hlc : 0 ≤ (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]).leadingCoeff := by
      have hnd := cubic_natDegree b c d
      simp only [leadingCoeff, hnd, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
      norm_num
    have hd : 0 < d := by
      have hgt := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg h_real_neg hlc
      simpa [eval_add, eval_mul, eval_pow, eval_C, eval_X] using hgt
    -- Get a real root r < 0
    obtain ⟨r, hr_eval⟩ := cubic_has_real_root b c d
    have hr_neg : r < 0 := h_real_neg r (by rw [IsRoot.def]; exact hr_eval)
    -- Factor p = (X - C r) * q where q = X² + C(b+r)*X + C(c+r*(b+r))
    have hr0 : r ^ 3 + b * r ^ 2 + c * r + d = 0 := by
      have := hr_eval; simp [eval_add, eval_mul, eval_pow, eval_C, eval_X] at this; linarith
    let e := b + r
    let f := c + r * (b + r)
    let q : ℝ[X] := X ^ 2 + C e * X + C f
    have hfactor : (X ^ 3 + C b * X ^ 2 + C c * X + C d : ℝ[X]) = (X - C r) * q := by
      have hdeq : d = -(r ^ 3 + b * r ^ 2 + c * r) := by linarith
      simp only [q, e, f, hdeq, C_neg, C_add, C_mul, C_pow]
      ring
    -- q is Hurwitz stable (its roots are also roots of p)
    have hq_stable : IsHurwitzStable q := by
      intro w hw
      apply h
      rw [hfactor, Polynomial.map_mul, IsRoot.def, Polynomial.eval_mul]
      exact mul_eq_zero.mpr (Or.inr hw)
    -- Apply quadratic theorem to q
    have hq_iff := isHurwitzStable_quadratic (b := e) (c := f)
    rw [show X ^ 2 + C e * X + C f = q from rfl] at hq_iff
    obtain ⟨he, hf⟩ := hq_iff.mp hq_stable
    -- Derive b > 0
    have hb : 0 < b := by linarith [hr_neg, he]
    -- Derive d < b*c via factored form: d = -r*f, b*c - d = e*(f - r*b) > 0
    have hd_eq : d = -r * f := by
      have := congr_arg (Polynomial.eval 0) hfactor
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow, zero_sub, zero_add,
                 zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero] at this
      linarith
    refine ⟨hb, hd, ?_⟩
    nlinarith [mul_pos he hf, mul_neg_of_neg_of_pos hr_neg he,
               mul_neg_of_neg_of_pos hr_neg hf, mul_pos hb hf]
  · -- Sufficient direction: b > 0, d > 0, d < b*c → all roots have Re < 0
    intro ⟨hb, hd, hbc⟩ z hz
    rw [cubic_isRoot_iff] at hz
    -- c > 0 follows from b*c > d > 0 and b > 0
    have hc : 0 < c := by
      rcases mul_pos_iff.mp (lt_trans hd hbc) with ⟨_, hc⟩ | ⟨hb', _⟩
      · exact hc
      · linarith
    obtain ⟨hre, him⟩ := cubic_re_im b c d z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · -- Real root: z.re^3 + b*z.re^2 + c*z.re + d = 0
      have hreal : z.re ^ 3 + b * z.re ^ 2 + c * z.re + d = 0 := by
        simp only [him0] at hre; linarith
      by_contra h
      push Not at h
      nlinarith [sq_nonneg z.re, mul_nonneg (mul_nonneg hb.le (sq_nonneg z.re)) (le_of_lt hc)]
    · -- Complex root: z.im^2 = 3*z.re^2 + 2*b*z.re + c
      have hysq : z.im ^ 2 = 3 * z.re ^ 2 + 2 * b * z.re + c := by linarith [him1]
      -- Substitute to get 8*z.re^3 + 8*b*z.re^2 + 2*(b^2+c)*z.re + (b*c-d) = 0
      have hcomb : 8 * z.re ^ 3 + 8 * b * z.re ^ 2 + 2 * (b ^ 2 + c) * z.re + (b * c - d) = 0 := by
        nlinarith [sq_nonneg z.re, hre, hysq, mul_self_nonneg z.re]
      by_contra h
      push Not at h
      nlinarith [sq_nonneg z.re, mul_nonneg hb.le (sq_nonneg z.re),
                 mul_nonneg (add_nonneg (sq_nonneg b) hc.le) h, sub_pos.mpr hbc]

end Polynomial
