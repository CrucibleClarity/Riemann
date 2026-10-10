import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

noncomputable section

namespace EtaFactorPhase

/-! ## 层 5: 因子幅角显式化 (临界线截面 1 − 2^{1−s})

η = (1 − 2^{1−s})·ζ 带内表示 (eta 级数 Re s > 0 收敛) ⟹ 奇侧 = 周期圆 (周期 P = 2π/ln 2)。
本文件把因子在临界线 s = 1/2 + ti 的截面显式化为:
  ① 2^{1−s} = √2·exp(−i·t·ln2) (cpow → exp, log 实桥);
  ② 因子 = 1 − √2·e^{−iφ} (φ = t·ln2) 的实部/虚部显式;
  ③ 圆分解: 大圆 (半径 √2, 绕原点) × 小圆 (中心 1, 半径 1/√2, 右半平面)。
层 5d (圈数 Δθ_因子 = −2π/周期) 将基于 ③: 小圆 Re > 0 ⟹ 无绕 ⟹ 圈数 = 大圆圈数。
-/

/-- **2^{1−s} 在临界线展开** (s = 1/2 + ti):
    2^{1−s} = √2 · exp(−i·t·ln2) — cpow_def_of_ne_zero + log 实桥 + exp_add. -/
lemma two_pow_one_sub_half_ts (t : ℝ) :
    (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      (Real.sqrt 2 : ℂ) * Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  -- log2 · (1 − s) = ↑(ln2/2) + (−t·ln2)·I (实部虚部分离, 点级)
  have harg : (Real.log 2 : ℂ) * (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      (((Real.log 2 / 2 : ℝ)) : ℂ) + ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.add_re, Complex.I_re, Complex.I_im]
      ring
    · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.add_im, Complex.I_re, Complex.I_im]
      ring
  rw [harg]
  rw [Complex.exp_add]
  have he : Complex.exp (((Real.log 2 / 2 : ℝ)) : ℂ) = (Real.sqrt 2 : ℂ) := by
    -- Complex.exp ↑(ln2/2) = ↑(Real.exp (ln2/2)) — ofReal_exp 反向:
    rw [← Complex.ofReal_exp]
    -- Real.exp(ln2/2) = 2^(1/2): ln2/2 = log(2^(1/2)) → exp_log 消
    have hlog2 : Real.log 2 / 2 = Real.log (Real.rpow 2 ((1 / 2 : ℝ))) := by
      rw [show Real.log (Real.rpow 2 ((1 / 2 : ℝ))) = (1 / 2) * Real.log 2 by
        exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) ((1 / 2 : ℝ))]
      ring
    rw [hlog2]
    have hrpow : (Real.rpow 2 (((1 / 2 : ℝ)))) = Real.sqrt 2 :=
      (Real.sqrt_eq_rpow (2 : ℝ)).symm
    have hexp : Real.exp (Real.log (Real.rpow 2 (1 / 2))) = Real.sqrt 2 := by
      rw [show Real.log (Real.rpow 2 (1 / 2)) = Real.log (Real.sqrt 2) by rw [hrpow]]
      rw [Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    exact congrArg (fun x : ℝ => (x : ℂ)) hexp
  rw [he]

/-- **因子沿临界线展开**: 1 − 2^{1−s} = 1 − √2·e^{−iφ} (φ = t·ln2).
    直接用 two_pow_one_sub_half_ts 的负侧. -/
lemma factor_line_form (t : ℝ) :
    (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) =
      1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I) := by
  rw [two_pow_one_sub_half_ts]

/-- **因子实数表示**: 1 − √2·e^{−iφ} = (1 − √2 cos φ) + i·(√2 sin φ)
    (φ = t·ln2 — exp_mul_I 展开). -/
theorem factor_line_re_im (t : ℝ) :
    (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) =
      ((1 - Real.sqrt 2 * Real.cos (t * Real.log 2) : ℝ) : ℂ) +
        (Real.sqrt 2 * Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [factor_line_form]
  rw [Complex.exp_mul_I]
  -- 目标: 1 − ↑√2·(cos(−x) + sin(−x)·i) = ↑(1 − √2 cos x) + ↑√2·↑(sin x)·i
  have hc : Complex.cos (-((t * Real.log 2 : ℝ) : ℂ)) = Complex.cos (((t * Real.log 2 : ℝ) : ℂ)) := by
    exact Complex.cos_neg _
  have hs : Complex.sin (-((t * Real.log 2 : ℝ) : ℂ)) = -Complex.sin (((t * Real.log 2 : ℝ) : ℂ)) := by
    exact Complex.sin_neg _
  rw [hc, hs]
  -- 归一: 复三角函数 → 实三角函数 (ofReal 版本) — 所有出现处
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_sin]
  rw [← Complex.ofReal_neg]
  -- 目标: 1 − ↑√2·(↑cos + ↑(−sin)·i) = ↑(1 − √2 cos x) + ↑√2·↑(sin)·i (纯 ↑ 型)
  -- 直接 ext: 左 (mul_re/im 链) 右 (ofReal_sub/ofReal_mul) 展开 → 实部/虚部对接:
  apply Complex.ext
  · simp [Complex.ofReal_sub, Complex.ofReal_mul, Complex.mul_re, Complex.add_re,
      Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_neg,
      Complex.zero_re, Complex.zero_im, sub_zero, zero_sub, add_zero, zero_add,
      mul_zero, mul_one, neg_zero, neg_neg, neg_mul, mul_neg, sub_eq_add_neg]
    ring
  · simp [Complex.ofReal_sub, Complex.ofReal_mul, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_neg,
      Complex.zero_re, Complex.zero_im, sub_zero, zero_sub, add_zero, zero_add,
      mul_zero, mul_one, neg_zero, neg_neg, neg_mul, mul_neg, sub_eq_add_neg]
    ring

/-- **√2 ≠ 0** (0 < √2, ne_of_gt + sqrt_pos — 数值前提 norm_num, 无自动化无理数). -/
lemma sqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))

/-- **因子圆分解**: 1 − √2·e^{−iφ} = (−√2·e^{−iφ})·(1 − e^{iφ}/√2)
    (φ = t·ln2) — 大圆 (半径 √2, 中心 0, 含原点) × 小圆 (半径 1/√2, 中心 1, 远离原点).
    代数: mul_sub + exp 合差 (exp_add) + div_self (√2≠0) + 多项式整理 (ring, 原子形). -/
lemma factor_line_g_split (t : ℝ) :
    (1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I)) =
      (-(Real.sqrt 2 : ℂ) * Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I)) *
        (1 - Complex.exp (((t * Real.log 2 : ℝ) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)) := by
  rw [mul_sub]
  rw [mul_one]
  rw [← mul_div_assoc]
  have hexp : Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((t * Real.log 2 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hzero : (-(t * Real.log 2 : ℝ) : ℂ) * Complex.I +
        ((t * Real.log 2 : ℝ) : ℂ) * Complex.I = 0 := by
      ring
    rw [hzero, Complex.exp_zero]
  rw [mul_assoc, hexp, mul_one]
  rw [neg_div]
  rw [div_self (Complex.ofReal_ne_zero.mpr sqrt2_ne)]
  -- 目标: 1 − √2·e^A = (−√2·e^A) − (−1): 多项式整理 (ring, ↑√2/e^A 为原子):
  ring

/-- **小圆右半平面**: Re(1 − e^{iφ}/√2) > 0 — 半径 1/√2 的盘中心在 1,
    cos φ ≤ 1 ⟹ Re ≥ 1 − 1/√2 > 0 (右半平面 ⟹ 小圆绕原点圈数 = 0). -/
lemma g_re_pos (t : ℝ) :
    0 < (((1 - Complex.exp (((t * Real.log 2 : ℝ) : ℂ) * Complex.I) /
        (Real.sqrt 2 : ℂ)) : ℂ).re) := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_sin]
  rw [div_eq_mul_inv]
  rw [← Complex.ofReal_inv]
  -- 全部 ↑ 系数, simp only 展开 re (full simp 会经 ofReal_cos 默认引理反向展开):
  simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im,
    sub_zero, zero_sub, add_zero, zero_add, mul_zero, mul_one, neg_zero, sub_eq_add_neg]
  -- 目标 (ℝ): 0 < 1 − c·√2⁻¹ — c ≤ 1 链:
  have hcos : Real.cos (t * Real.log 2) ≤ 1 := Real.cos_le_one (t * Real.log 2)
  have hdiv : Real.cos (t * Real.log 2) * (Real.sqrt 2)⁻¹ ≤ (Real.sqrt 2)⁻¹ := by
    have h0k : (Real.sqrt 2)⁻¹ * Real.cos (t * Real.log 2) ≤ (Real.sqrt 2)⁻¹ :=
      mul_le_of_le_one_right (inv_nonneg_of_nonneg (Real.sqrt_nonneg 2)) hcos
    rw [mul_comm] at h0k
    exact h0k
  have hlt : Real.cos (t * Real.log 2) * (Real.sqrt 2)⁻¹ < 1 := by
    have hsq : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    have hlt1 : (Real.sqrt 2)⁻¹ < 1 := by
      rw [← one_div]
      exact div_lt_self (by norm_num : (0 : ℝ) < 1) hsq
    exact lt_of_le_of_lt hdiv hlt1
  exact sub_pos.mpr hlt

/-- **因子周期律**: 1 − 2^{1−s} 在虚方向周期 P = 2π/ln 2 (因子沿临界线 t ↦ t + P 闭合).
    证明: (t+P)·ln2 = t·ln2 + 2π ⟹ e^{−i((t+P)ln2)} = e^{−itln2}·e^{−2πi} = e^{−itln2}. -/
lemma factor_line_period (t : ℝ) :
    (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((t + 2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I))) =
      (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) := by
  rw [factor_line_form, factor_line_form]
  have hln : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  have hstep : (t + 2 * Real.pi / Real.log 2) * Real.log 2 = t * Real.log 2 + 2 * Real.pi := by
    rw [add_mul, div_mul_cancel₀ (2 * Real.pi) hln]
  rw [hstep]
  -- 目标: exp(−↑(t·ln2 + 2π)·I) = exp(−↑(t·ln2)·I) — 幅角差 −2π:
  have hargs : (-(t * Real.log 2 + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      ((-(t * Real.log 2 : ℝ) : ℂ)) * Complex.I +
        ((-(2 * Real.pi : ℝ) : ℂ)) * Complex.I := by
    rw [Complex.ofReal_add]
    ring
  rw [hargs, Complex.exp_add]
  -- 第二因子 = 1: e^{−2πi} = cos(−2π) + i·sin(−2π) = 1:
  have hon : Complex.exp ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_neg]
    rw [← Complex.ofReal_cos]
    rw [← Complex.ofReal_sin]
    rw [Real.cos_neg, Real.sin_neg, Real.cos_two_pi, Real.sin_two_pi,
      neg_zero, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one]
  rw [hon, mul_one]

end EtaFactorPhase
