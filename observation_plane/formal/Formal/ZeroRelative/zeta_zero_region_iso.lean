import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith

/-!
# 非平凡零点的临界带钉死 (素数角度快路径)

素数角度 (Euler 乘积/级数收敛域) 给出的零点区域约束:
  Re s ≥ 1:  ζ(s) ≠ 0        (mathlib riemannZeta_ne_zero_of_one_le_re, L 级数收敛半平面)
  Re s < 0:  ζ(s) ≠ 0        (函数方程镜像: ζ(1-s) = F(s)·ζ(s), 1-s.re > 1)
  Re s = 0:  ζ(s) ≠ 0        (函数方程镜像, s ≠ 0; ζ(0) = -1/2 ≠ 0)
  ⟹ 非平凡零点全在临界带 0 < Re s < 1 内 (与共轭三片/共轭计数衔接)。

负整数处: 偶数为平凡零点 (riemannZeta_neg_two_mul_nat_add_one = 0),
  奇数 = 伯努利值 (riemannZeta_neg_nat_eq_bernoulli), 非零是经典结果但
  mathlib 缺偶伯努利数非零定理 ⟹ 显式排除 (hs_int : ∀ n : ℕ, s ≠ -n)。

诚实边界: "零点只在临界带" 已钉死; "零点只在临界线" (RH) 仍缺
  N₀(T) = N(T) 计数工具。

English: zero region: on/off-zero observations for ζ -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- Re s < 0 无零点 (s 非负整数): 函数方程镜像 riemannZeta_ne_zero_of_one_le_re.
    ζ(s) = 0 ⟹ ζ(1-s) = F(s)·0 = 0, 但 1-s.re > 1 处 ζ ≠ 0. 
English: No zeros for Re s < 0 (s not a nonpositive integer): functional equation mirrored via riemannZeta_ne_zero_of_one_le_re. ζ(s) = 0 ⟹ ζ(1−s) = F(s)·0 = 0, but ζ ≠ 0 where 1−s.re > 1. -/
theorem riemannZeta_ne_zero_of_re_lt_zero (s : ℂ) (hs : s.re < 0)
    (hs_int : ∀ n : ℕ, s ≠ -n) : riemannZeta s ≠ 0 := by
  intro hz
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hfe := riemannZeta_one_sub (s := s) hs_int hs_ne_one
  have hzsub : riemannZeta (1 - s) = 0 := by
    rw [hfe, hz]
    simp
  -- 1-s.re = 1 - s.re > 1 ⟹ ζ(1-s) ≠ 0
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs]
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- Re s = 0 无零点 (s ≠ 0): 函数方程在 1-s 处镜像. 
English: No zeros for Re s = 0 (s ≠ 0): functional equation mirrored at 1−s. -/
theorem riemannZeta_ne_zero_of_re_eq_zero (s : ℂ) (hs : s.re = 0) (hs0 : s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  -- 函数方程在 1-s 处: ζ(s) = F(1-s)·ζ(1-s); F 因子全非零 ⟹ ζ(1-s) = 0
  have hs_int : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h
    have hre : (1 - s).re = (-(n : ℂ)).re := by rw [h]
    rw [Complex.sub_re, Complex.one_re, hs] at hre
    have : ((-(n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hsub_ne_one : 1 - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by norm_num
  have hfe := riemannZeta_one_sub (s := 1 - s) hs_int hsub_ne_one
  -- hfe : ζ(s) = 2·(2π)^(-(1-s))·Γ(1-s)·cos(π(1-s)/2)·ζ(1-s)
  -- 因子分解: 2 ≠ 0, (2π)^(-(1-s)) ≠ 0, Γ(1-s) ≠ 0, cos(π(1-s)/2) ≠ 0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have htwo_pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero htwo (by exact_mod_cast Real.pi_ne_zero)
  have hcpow : (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl htwo_pi)
  have hgamma : Complex.Gamma (1 - s) ≠ 0 := by
    exact Complex.Gamma_ne_zero hs_int
  -- cos(π(1-s)/2) ≠ 0: s.re = 0 且 s ≠ 0 ⟹ s ∉ 2ℤ ⟹ 1-s ∉ 2ℤ+1 ⟹ cos ≠ 0
  have hs_not_int : ∀ k : ℤ, s ≠ 2 * (k : ℂ) := by
    intro k h
    have hre : s.re = (2 * (k : ℝ) : ℝ) := by
      rw [h]
      simp
    have hk0 : (k : ℝ) = 0 := by
      rw [hs] at hre
      nlinarith
    have hk0' : k = 0 := by exact_mod_cast hk0
    apply hs0
    rw [h, hk0']
    norm_num
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    -- π(1-s)/2 = (2k+1)π/2 ⟹ 1-s = 2k+1 ⟹ s = -2k ∈ 2ℤ, 矛盾
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : ↑Real.pi * (1 - s) = (2 * (k : ℂ) + 1) * ↑Real.pi := by
      calc
        ↑Real.pi * (1 - s) = (↑Real.pi * (1 - s) / 2) * 2 := by field_simp [h2]
        _ = ((2 * (k : ℂ) + 1) * ↑Real.pi / 2) * 2 := by rw [hk]
        _ = (2 * (k : ℂ) + 1) * ↑Real.pi := by field_simp [h2]
    have hk' : 1 - s = ↑(2 * k + 1) := by
      have hc : 1 - s = 2 * (k : ℂ) + 1 := by
        exact mul_right_cancel₀ hpi (by simpa [mul_comm] using hmul)
      simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hc
    have hs2 : s = 2 * ((-k : ℤ) : ℂ) := by
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - ↑(2 * k + 1) := by rw [hk']
        _ = (2 : ℂ) * ↑(-k) := by
          rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_neg]
          ring
    exact (hs_not_int (-k)) hs2
  have hF : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
      * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hcpow) hgamma) hcos
  -- ζ(s) = F·ζ(1-s) = 0 且 F ≠ 0 ⟹ ζ(1-s) = 0 ⟹ 矛盾 (1 ≤ Re(1-s), 1-s ≠ 1)
  have hzsub : riemannZeta (1 - s) = 0 := by
    have hFz : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
        * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [← hfe]
      simpa using hz
    exact (mul_eq_zero.mp hFz).resolve_left hF
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re, hs]
    norm_num
  have hsub_ne_one' : 1 - s ≠ 1 := hsub_ne_one
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- 非平凡零点全在临界带: ζ(s) = 0 (排除平凡零点与极点, 排除负整数) ⟹ 0 < Re s < 1. 
English: All nontrivial zeros lie in the critical strip: ζ(s) = 0 (excluding trivial zeros and the pole, excluding nonpositive integers) ⟹ 0 < Re s < 1. -/
theorem nontrivial_zero_in_critical_strip {s : ℂ} (hz : riemannZeta s = 0)
    (h_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1)
    (hs_int : ∀ n : ℕ, s ≠ -n) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · -- 0 < s.re: 反证, s.re ≤ 0
    by_contra h
    have hle : s.re ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hs_neg | hs_zero
    · exact (riemannZeta_ne_zero_of_re_lt_zero s hs_neg hs_int) hz
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, riemannZeta_zero] at hz
        norm_num at hz
      exact (riemannZeta_ne_zero_of_re_eq_zero s hs_zero hs0) hz
  · -- s.re < 1: 反证, 1 ≤ s.re ⟹ ζ ≠ 0
    by_contra h
    have hge : 1 ≤ s.re := le_of_not_gt h
    exact (riemannZeta_ne_zero_of_one_le_re (s := s) hge) hz

end RiemannUnifiedObservation
