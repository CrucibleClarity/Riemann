import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# 零点四元组 cosh 分解 (iso 43)

黎曼显式公式的项 x^ρ = x^{Re ρ}·e^{it·log x} (ρ = β + it) 在
临界线反射 ρ ↦ 1−ρ 与共轭 ρ ↦ conj ρ 生成的轨道 {ρ, 1−ρ, conj ρ, 1−conj ρ}
下的实部贡献:

    Re(x^ρ + x^{1−ρ} + x^conj ρ + x^{1−conj ρ})
        = 4 · x^{1/2} · cosh((β − 1/2)·log x) · cos(t·log x)

β = 1/2 ⟺ cosh 因子 = 1 (纯 x^{1/2} 尺度, 振荡项 cos(t·log x) 不乘尺度因子);
β ≠ 1/2 ⟹ cosh((β − 1/2)·log x) 随 log x 对数尺度增长 (尺度叠加)。

本文件: 隔离 (Mathlib only), 零洞。核心恒等式的机器验证。

English: exp(I·θ) = cos θ + I·sin θ (real-parameter version). -/

open scoped ComplexConjugate

noncomputable section

namespace RH_PrimeAxis

/-- exp(I·θ) = cos θ + I·sin θ (实数参数版). 
English: exp(I·θ) = cos θ + I·sin θ (real-parameter version). -/
lemma exp_I_mul_ofReal (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
  rw [mul_comm Complex.I (θ : ℂ)]
  rw [Complex.exp_mul_I (θ : ℂ)]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- Re(x^ρ) = x^{Re ρ} · cos(Im ρ · log x), 对 x > 0.
    (x:ℂ)^ρ = exp(ρ·log x) = x^β·(cos(t·log x) + i·sin(t·log x)) 
English: Re(x^ρ) = x^{Re ρ}·cos(Im ρ · log x), for x > 0. (x:ℂ)^ρ = exp(ρ·log x) = x^β·(cos(t·log x) + i·sin(t·log x)). -/
lemma cpow_re_ofReal_pos (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ ρ)).re = x ^ ρ.re * Real.cos (ρ.im * Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hcpow : (x : ℂ) ^ ρ = Complex.exp (ρ * Complex.log (x : ℂ)) := by
    simpa [mul_comm] using Complex.cpow_def_of_ne_zero hx0 ρ
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  have hmul : ρ * (Real.log x : ℂ) = (ρ.re * Real.log x : ℂ)
      + Complex.I * (ρ.im * Real.log x : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
  calc
    (((x : ℂ) ^ ρ)).re = (Complex.exp (ρ * Complex.log (x : ℂ))).re := by rw [hcpow]
    _ = (Complex.exp (ρ * (Real.log x : ℂ))).re := by rw [hlog]
    _ = (Complex.exp ((ρ.re * Real.log x : ℂ)
          + Complex.I * (ρ.im * Real.log x : ℂ))).re := by rw [hmul]
    _ = (Complex.exp (ρ.re * Real.log x : ℂ)
          * Complex.exp (Complex.I * (ρ.im * Real.log x : ℂ))).re := by rw [Complex.exp_add]
    _ = x ^ ρ.re * Real.cos (ρ.im * Real.log x) := by
      have h1 : Complex.exp ((ρ.re * Real.log x : ℝ) : ℂ) =
          (Real.exp (ρ.re * Real.log x) : ℂ) := by
        rw [← Complex.ofReal_exp]
      have h1' : (Real.exp (ρ.re * Real.log x) : ℂ) = ((x ^ ρ.re : ℝ) : ℂ) := by
        congr 1
        rw [mul_comm (ρ.re) (Real.log x)]
        rw [← Real.rpow_def_of_pos hx ρ.re]
      have h2 : Complex.exp (Complex.I * (ρ.im * Real.log x : ℂ)) =
          (Real.cos (ρ.im * Real.log x) : ℂ)
            + Complex.I * (Real.sin (ρ.im * Real.log x) : ℂ) := by
        rw [← Complex.ofReal_mul]
        exact exp_I_mul_ofReal (ρ.im * Real.log x)
      have hxr : x ^ ρ.re ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx ρ.re)
      rw [← Complex.ofReal_mul]
      rw [h1, h1', h2]
      rw [Complex.mul_re]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring_nf

/-- x^b + x^{1−b} = 2·x^{1/2}·cosh((b − 1/2)·log x), 对 x > 0.
    (尺度恒等式: 幂和 = 几何平均 × 双曲余弦) 
English: x^b + x^{1−b} = 2·x^{1/2}·cosh((b − 1/2)·log x), for x > 0. (Scale identity: power sum = geometric mean × hyperbolic cosine). -/
lemma rpow_add_reflect (x : ℝ) (hx : 0 < x) (b : ℝ) :
    x ^ b + x ^ (1 - b) = 2 * x ^ (1 / 2 : ℝ) * Real.cosh ((b - 1 / 2) * Real.log x) := by
  have h1 : x ^ b = x ^ (1 / 2 : ℝ) * x ^ (b - 1 / 2) := by
    rw [← Real.rpow_add hx (1 / 2) (b - 1 / 2)]
    congr 1
    ring
  have h2 : x ^ (1 - b) = x ^ (1 / 2 : ℝ) * x ^ (-(b - 1 / 2)) := by
    rw [← Real.rpow_add hx (1 / 2) (-(b - 1 / 2))]
    congr 1
    ring
  calc
    x ^ b + x ^ (1 - b)
        = x ^ (1 / 2 : ℝ) * x ^ (b - 1 / 2) + x ^ (1 / 2 : ℝ) * x ^ (-(b - 1 / 2)) := by
      rw [h1, h2]
    _ = x ^ (1 / 2 : ℝ) * (x ^ (b - 1 / 2) + x ^ (-(b - 1 / 2))) := by ring
    _ = x ^ (1 / 2 : ℝ) * (2 * Real.cosh ((b - 1 / 2) * Real.log x)) := by
      have h1 : x ^ (b - 1 / 2) = Real.exp ((b - 1 / 2) * Real.log x) := by
        rw [Real.rpow_def_of_pos hx (b - 1 / 2)]
        congr 1
        ring
      have h2 : x ^ (-(b - 1 / 2)) = Real.exp (-((b - 1 / 2) * Real.log x)) := by
        rw [Real.rpow_def_of_pos hx (-(b - 1 / 2))]
        congr 1
        ring
      rw [h1, h2]
      rw [Real.cosh_eq ((b - 1 / 2) * Real.log x)]
      ring
    _ = 2 * x ^ (1 / 2 : ℝ) * Real.cosh ((b - 1 / 2) * Real.log x) := by ring

/-- 零点四元组贡献 (实部): 反射 + 共轭 的四项和
    Re(x^ρ + x^{1−ρ} + x^conj ρ + x^{1−conj ρ})
        = 4·x^{1/2}·cosh((β − 1/2)·log x)·cos(t·log x)
    β = 1/2 ⟺ cosh 因子 = 1 (纯 x^{1/2} 尺度, 相位清晰);
    β ≠ 1/2 ⟹ cosh((β−1/2)·log x) 对数尺度增长 (尺度叠加, 相位模糊). 
English: Zero-quadruple contribution (real part): sum of the four reflection + conjugation terms Re(x^ρ + x^{1−ρ} + x^conj ρ + x^{1−conj ρ}) = 4·x^{1/2}·cosh((β − 1/2)·log x)·cos(t·log x). β = 1/2 ⟺ cosh factor = 1 (pure x^{1/2} scale, clear phase); β ≠ 1/2 ⟹ cosh((β−1/2)·log x) grows logarithmically (scale accumulation, phase blurred). -/
theorem zero_quadruple_re_contribution (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ ρ + (x : ℂ) ^ (1 - ρ) + (x : ℂ) ^ (conj ρ)
        + (x : ℂ) ^ (1 - conj ρ))).re
      = 4 * x ^ (1 / 2 : ℝ) * Real.cosh ((ρ.re - 1 / 2) * Real.log x)
          * Real.cos (ρ.im * Real.log x) := by
  -- 各项实部
  have h1 := cpow_re_ofReal_pos x hx ρ
  have h2 := cpow_re_ofReal_pos x hx (1 - ρ)
  have h3 := cpow_re_ofReal_pos x hx (conj ρ)
  have h4 := cpow_re_ofReal_pos x hx (1 - conj ρ)
  -- conj ρ 与 1−conj ρ 的实部公式 (用 ρ 的实部/虚部)
  have hconj_re : (conj ρ).re = ρ.re := by simp
  have hconj_im : (conj ρ).im = -ρ.im := by simp
  have h1c_im : (1 - conj ρ).im = ρ.im := by
    rw [Complex.sub_im]
    simp
  have h3' : (((x : ℂ) ^ (conj ρ))).re = x ^ ρ.re * Real.cos (ρ.im * Real.log x) := by
    rw [h3, hconj_re, hconj_im]
    rw [show (-ρ.im) * Real.log x = -(ρ.im * Real.log x) by ring]
    rw [Real.cos_neg]
  have h2' : (((x : ℂ) ^ (1 - ρ))).re = x ^ (1 - ρ.re) * Real.cos (ρ.im * Real.log x) := by
    rw [h2]
    rw [show (1 - ρ).re = 1 - ρ.re by simp]
    rw [Complex.sub_im]
    rw [show (Complex.im 1 - ρ.im) * Real.log x = -(ρ.im * Real.log x) by
      norm_num]
    rw [Real.cos_neg]
  have h4' : (((x : ℂ) ^ (1 - conj ρ))).re = x ^ (1 - ρ.re) * Real.cos (ρ.im * Real.log x) := by
    rw [h4]
    rw [show (1 - conj ρ).re = 1 - ρ.re by simp]
    rw [h1c_im]
  -- 四项实部求和
  have hsum : (((x : ℂ) ^ ρ + (x : ℂ) ^ (1 - ρ) + (x : ℂ) ^ (conj ρ)
        + (x : ℂ) ^ (1 - conj ρ))).re
      = 2 * (x ^ ρ.re + x ^ (1 - ρ.re)) * Real.cos (ρ.im * Real.log x) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re]
    rw [h1, h2', h3', h4']
    ring_nf
  rw [hsum]
  -- x^β + x^{1−β} = 2·x^{1/2}·cosh
  rw [rpow_add_reflect x hx ρ.re]
  ring

end RH_PrimeAxis

end
