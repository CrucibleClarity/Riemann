import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# T4: χ 的平移递推 — 单方向延拓的差分 (模 2π)

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) (函数方程乘子)。沿实轴平移 2:

  χ(s+2) = -4π²/(s(s+1))·χ(s)

构件: sin(π(s+2)/2) = -sin(πs/2) (sin 周期 π),
        Γ(-1-s) = Γ(1-s)/(s(s+1)) (Γ 递推两次, mathlib Gamma_add_one),
        (2π)^{s+1} = (2π)^{s-1}·(2π)² (cpow_add)。
取相位 (Real.Angle):

  arg χ(s+2) - arg χ(s) = π - arg(s(s+1))   (模 2π; arg(-4π²) = π)

这就是"单方向延拓" (用户例子: 交替中心反射 → 两步复合 = 平移) 在
χ 相位上的落地: 沿实轴每步平移 2 的相位差分全显式。连续幅角的步进:
T3 (2·arg ζ = arg χ) + 本定理 ⟹ arg ζ(1/2+i(t+2)) - arg ζ(1/2+it)
= -(1/2)arg((1/2+it)(3/2+it)) + π·(t,t+2] 零点数。

隔离文件 (mathlib-only, 不依赖 37 项目), 编译通过后再合并。

English: chi translation recursion: the 2π and 4π phase translations (T4) -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- χ 的平移递推 (数字层): χ(s+2) = -4π²/(s(s+1))·χ(s)。
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。s ≠ 0, -1 (Γ 递推与分母)。 
English: Translation recursion of χ (numeric layer): χ(s+2) = -4π²/(s(s+1))·χ(s), χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2); s ≠ 0, -1 (Γ recursion and denominator). -/
theorem chi_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
      = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)) := by
  -- (2π)^{s+1} = (2π)^{s-1}·(2π)²
  have hpow : (2 * ↑Real.pi : ℂ) ^ (s + 1) = (2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) 2 (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne')]
    congr 1
    ring
  have hpow2 : (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) = 4 * (↑Real.pi) ^ 2 := by
    have hc2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
    rw [hc2, Complex.cpow_natCast]
    ring
  -- sin(π(s+2)/2) = -sin(πs/2)
  have hsin : Complex.sin (↑Real.pi * (s + 2) / 2) = -Complex.sin (↑Real.pi * s / 2) := by
    have harg : ↑Real.pi * (s + 2) / 2 = ↑Real.pi * s / 2 + ↑Real.pi := by ring
    rw [harg, Complex.sin_add_pi]
  -- Γ(-1-s) = Γ(1-s)/(s(s+1)): Gamma_add_one 两次 (需 -s ≠ 0, -1-s ≠ 0)
  have hG1 : Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := by
    have hne : -s ≠ 0 := by
      intro h
      apply hs0
      exact neg_eq_zero.mp h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Complex.Gamma_add_one (-s) hne)
  have hG2 : Complex.Gamma (-s) = (-1 - s) * Complex.Gamma (-1 - s) := by
    have hne : -1 - s ≠ 0 := by
      intro h
      apply hs1
      -- -1 - s = 0 ⟹ s = -1
      have h' : (s + 1 : ℂ) = 0 := by
        have : s + 1 = -(-1 - s) := by ring
        rw [this, h]
        norm_num
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h']
        _ = -1 := by norm_num
    have hg := Complex.Gamma_add_one (-1 - s) hne
    have harg : (-1 - s) + 1 = -s := by ring
    rw [harg] at hg
    exact hg
  have hrel : Complex.Gamma (1 - s) = s * (s + 1) * Complex.Gamma (-1 - s) := by
    calc
      Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := hG1
      _ = (-s) * ((-1 - s) * Complex.Gamma (-1 - s)) := by rw [hG2]
      _ = s * (s + 1) * Complex.Gamma (-1 - s) := by ring
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hG : Complex.Gamma (-1 - s) = Complex.Gamma (1 - s) / (s * (s + 1)) := by
    calc
      Complex.Gamma (-1 - s) = (s * (s + 1) * Complex.Gamma (-1 - s)) / (s * (s + 1)) := by
        rw [mul_comm (s * (s + 1)) (Complex.Gamma (-1 - s))]
        rw [mul_div_cancel_right₀ _ hs']
      _ = Complex.Gamma (1 - s) / (s * (s + 1)) := by
        rw [← hrel]
  -- 组装
  calc
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
        = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ)) * Complex.Gamma (-1 - s) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow, hsin]
      _ = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (4 * (↑Real.pi) ^ 2)) * (Complex.Gamma (1 - s) / (s * (s + 1))) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow2, hG]
      _ = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)) := by
            ring

/-- χ 的平移递推 (相位层, 模 2π):
    arg χ(s+2) - arg χ(s) = π - arg(s(s+1))。arg(-4π²) = π (模 2π)。 
English: Translation recursion of χ (phase layer, mod 2π): arg χ(s+2) - arg χ(s) = π - arg(s(s+1)); arg(-4π²) = π (mod 2π). -/
theorem chi_arg_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hχ : 2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) *
      Complex.sin (↑Real.pi * (s + 2) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + (↑Real.pi : Real.Angle)
        - ((s * (s + 1)).arg : Real.Angle) := by
  have h := chi_translation_two s hs0 hs1
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: -4π²/(s(s+1)) · χ(s)
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hπ2 : (-4 * (↑Real.pi) ^ 2 : ℂ) ≠ 0 := by
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    exact mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ)
  have hfac : (-4 * (↑Real.pi) ^ 2 / (s * (s + 1)) : ℂ) ≠ 0 :=
    div_ne_zero hπ2 hs'
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle hπ2 hs'] at harg
  -- arg(-4π²) = π (模 2π)
  have harg_neg : ((-4 * (↑Real.pi) ^ 2 : ℂ).arg : Real.Angle) = (↑Real.pi : Real.Angle) := by
    have h1 : (-4 * (↑Real.pi) ^ 2 : ℂ) = (-1 : ℂ) * (4 * (↑Real.pi) ^ 2 : ℂ) := by ring
    rw [h1]
    have hπ' : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    have hm := Complex.arg_mul_coe_angle (by norm_num : (-1 : ℂ) ≠ 0)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ'))
    rw [hm]
    rw [Complex.arg_neg_one]
    have harg4 : (4 * (↑Real.pi) ^ 2 : ℂ).arg = 0 := by
      have hc : (4 * (↑Real.pi) ^ 2 : ℂ) = (↑(4 * Real.pi ^ 2 : ℝ) : ℂ) := by norm_num
      rw [hc]
      exact Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (4 * Real.pi ^ 2 : ℝ))
    rw [harg4]
    simp
  rw [harg_neg] at harg
  -- harg: ↑arg χ(s+2) = (π - ↑arg(s(s+1))) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+2) = ↑arg χ(s) + π - ↑arg(s(s+1))
  have h1 : (↑Real.pi - ((s * (s + 1)).arg : Real.Angle))
        + ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + ↑Real.pi - ((s * (s + 1)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg



/-- 辅助: s + k = 0 ⟹ s = -k (ℂ 上, k : ℕ)。 
English: Auxiliary: s + k = 0 ⟹ s = -k (over ℂ, k : ℕ). -/
private lemma eq_neg_of_add_eq_zero (s : ℂ) (k : ℕ) (h : s + (k : ℂ) = 0) :
    s = -(k : ℂ) := by
  calc
    s = (s + (k : ℂ)) - (k : ℂ) := by ring
    _ = 0 - (k : ℂ) := by rw [h]
    _ = -(k : ℂ) := by norm_num

/-- χ 的两步平移递推 (数字层): χ(s+4) = 16π⁴/(s(s+1)(s+2)(s+3))·χ(s)。
    对称点与延拓点交换: 每一步以上一步的结果为对称点, 无固定中心。
    由 chi_translation_two 迭代两次 (χ(s+4) = χ((s+2)+2))。 
English: Two-step translation recursion of χ (numeric layer): χ(s+4) = 16π⁴/(s(s+1)(s+2)(s+3))·χ(s); symmetry point and continuation point swap — each step takes the previous result as symmetry point, no fixed center; obtained by iterating chi_translation_two twice (χ(s+4) = χ((s+2)+2)). -/
theorem chi_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3) :
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
      = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
          Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
  have h1 := chi_translation_two s hs0 hs1
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 2 ≠ -1 := by
    intro h
    apply hs3
    -- s + 2 = -1 ⟹ s = -3
    have : s = -3 := by
      have h' : s + 3 = 0 := by
        have : s + 3 = (s + 2) + 1 := by ring
        rw [this, h]
        norm_num
      simpa using (eq_neg_of_add_eq_zero s 3 h')
    exact this
  have h2 := chi_translation_two (s + 2) hs2' hs3'
  -- 归一 h2 的参数
  have hg1 : (s + 2) + 1 = s + 3 := by ring
  have hg2 : -1 - (s + 2) = -3 - s := by ring
  have hg3 : (s + 2) + 2 = s + 4 := by ring
  have hg4 : 1 - (s + 2) = -1 - s := by ring
  have hg5 : (s + 2) - 1 = s + 1 := by ring
  rw [hg1, hg2, hg3, hg4, hg5] at h2
  -- 组装
  calc
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
        = -4 * (↑Real.pi) ^ 2 / ((s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s + 1) * Complex.Gamma (-1 - s) *
            Complex.sin (↑Real.pi * (s + 2) / 2)) := by
            exact h2
      _ = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
            Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
            rw [h1]
            field_simp [hs0, hs1', hs2', hs3']
            ring

/-- χ 的两步平移递推 (相位层, 模 2π): "交换延拓"的迭代 —
    arg χ(s+4) = arg χ(s) - arg(s(s+1)) - arg((s+2)(s+3))。
    arg(16π⁴) = 0 (正实数), 两步的 π 常数抵消 (π + π = 2π)。 
English: Two-step translation recursion of χ (phase layer, mod 2π): iteration of 'swapped continuation' — arg χ(s+4) = arg χ(s) - arg(s(s+1)) - arg((s+2)(s+3)); arg(16π⁴) = 0 (positive real), the two π constants cancel (π + π = 2π). -/
theorem chi_arg_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3)
    (hχ : 2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) *
      Complex.sin (↑Real.pi * (s + 4) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
  have h := chi_translation_four s hs0 hs1 hs2 hs3
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: 16π⁴/(s(s+1)(s+2)(s+3)) · χ(s)
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 3 ≠ 0 := by
    intro h
    apply hs3
    have h' : s + ((3 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 3 h')
  have hsden : (s * (s + 1) * (s + 2) * (s + 3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1') hs2') hs3'
  have hπ : (↑Real.pi : ℂ) ≠ 0 := by
    intro h
    apply Real.pi_ne_zero
    have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
    simpa using this
  have h16 : (16 * (↑Real.pi) ^ 4 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) (pow_ne_zero 4 hπ)
  have hfac : (16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) : ℂ) ≠ 0 :=
    div_ne_zero h16 hsden
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle h16 hsden] at harg
  -- arg(16π⁴) = 0 (正实数)
  have harg16 : ((16 * (↑Real.pi) ^ 4 : ℂ).arg : Real.Angle) = 0 := by
    have hc : (16 * (↑Real.pi) ^ 4 : ℂ) = (↑(16 * Real.pi ^ 4 : ℝ) : ℂ) := by norm_num
    rw [hc]
    exact congrArg (fun x : ℝ => (x : Real.Angle))
      (Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (16 * Real.pi ^ 4 : ℝ)))
  rw [harg16] at harg
  -- harg: ↑arg χ(s+4) = 0 - ↑arg(s(s+1)) - ↑arg((s+2)(s+3)) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+4) = ↑arg χ(s) - ↑arg(s(s+1)) - ↑arg((s+2)(s+3))
  have h1 : (0 : Real.Angle) - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle)
        + ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg
end RiemannUnifiedObservation
