import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Γ 相位对称约化 — 组合定理 (N(T) - N₀(T) 的快速路径, 模 2π)

G(t) = (1/2)·arg Γ(1/2-it) + arg Γ(1/4+it/2) 的约化链 (无 Stirling):

  共轭 (A):  arg Γ(1/4-it/2) = -arg Γ(1/4+it/2)      (模 2π)
  倍增 (B):  arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im
  反射 (C):  arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im
  组合 (D):  2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im
                                  + (log sin(π(3/4+it/2))).im

D 代入 G: 2G = -t·ln2 + (log sin(...)).im — Γ 完全消去, 全显式。
全部在 Real.Angle (ℝ/2πℤ) 中: 整数组合合法, 模 2π。

对称操作来源 (pat0): 倍增 = Legendre 乘法公式, 反射 = Euler 反射公式,
共轭 = Γ(conj s) = conj Γ(s)。三者全是"对称操作", 非差分链。

English: A: conjugation phase (mod 2π): arg Γ(conj s) = -arg Γ(s). Unconditional: arg_conj_coe_angle is an Angle-level identity; the branch disappears mod 2π. -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- A: 共轭相位 (模 2π): arg Γ(conj s) = -arg Γ(s)。
    无条件: arg_conj_coe_angle 是 Angle 层恒等式, 分支在模 2π 下消失。 
English: A: conjugation phase (mod 2π): arg Γ(conj s) = -arg Γ(s). Unconditional: arg_conj_coe_angle is an Angle-level identity; the branch disappears mod 2π. -/
theorem gamma_conj_arg_angle (s : ℂ) :
    ((Complex.Gamma ((starRingEnd ℂ) s)).arg : Real.Angle)
      = -((Complex.Gamma s).arg : Real.Angle) := by
  rw [Complex.Gamma_conj]
  exact Complex.arg_conj_coe_angle (Complex.Gamma s)

/-- B: 倍增相位 (模 2π, s = 1/4+it/2): Legendre 倍增公式的 arg 版本。
    arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im。 
English: B: doubling phase (mod 2π, s = 1/4+it/2): arg version of the Legendre duplication formula. arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im. -/
theorem gamma_doubling_arg_angle (t : ℝ) :
    ((Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hs_pos : 0 < s.re := by dsimp [s]; simp
  have hs2_pos : 0 < (s + 1 / 2).re := by dsimp [s]; simp; norm_num
  have h2s_pos : 0 < (2 * s).re := by dsimp [s]; simp
  have hs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_pos
  have hs2_ne : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2_pos
  have h2s_ne : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h2s_pos
  have hpow_ne : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hsqrt_ne : (↑(Real.sqrt Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- Legendre 倍增公式 (无条件)
  have h := Complex.Gamma_mul_Gamma_add_half s
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 左侧: Γ(s)·Γ(s+1/2)
  rw [Complex.arg_mul_coe_angle hs_ne hs2_ne] at harg
  -- 右侧: (Γ(2s)·2^{1-2s})·√π
  rw [Complex.arg_mul_coe_angle (mul_ne_zero h2s_ne hpow_ne) hsqrt_ne] at harg
  rw [Complex.arg_mul_coe_angle h2s_ne hpow_ne] at harg
  -- arg √π = 0
  have harg_sqrt : (↑(Real.sqrt Real.pi) : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)
  simp [harg_sqrt] at harg
  -- arg(2^{1-2s}) = (log 2^{1-2s}).im (log_im 反向)
  have hlog : (Complex.log ((2 : ℂ) ^ (1 - 2 * s))).im = ((2 : ℂ) ^ (1 - 2 * s)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 s 的具体值: s+1/2 = 3/4+it/2, 2s = 1/2+it, 1-2s = 1/2-it
  have hs12 : s + (2 : ℂ)⁻¹ = (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2 := by
    dsimp [s]; ring
  have h2s : 2 * s = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
    dsimp [s]; ring
  have h12s : 1 - 2 * s = ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ) := by
    dsimp [s]; ring
  -- h12s 需在 h2s 前: h2s 会先替换掉 harg 中的 2*s
  rw [hs12, h12s, h2s] at harg
  dsimp [s] at harg
  exact harg

/-- C: 反射相位 (模 2π, z = 3/4+it/2):
    arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im。
    Euler 反射公式 Γ(z)Γ(1-z) = π/sin(πz) 的 arg 版本; sin 非零由左侧
    Γ 非零 (re > 0) 自动推出, 无整数/无理数论证。 
English: C: reflection phase (mod 2π, z = 3/4+it/2): arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im. Arg version of Euler's reflection formula Γ(z)Γ(1-z) = π/sin(πz); sin ≠ 0 follows automatically from Γ ≠ 0 (re > 0) on the left, no integer/irrationality argument. -/
theorem gamma_reflection_arg_angle (t : ℝ) :
    ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = -((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let z : ℂ := (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hz_pos : 0 < z.re := by dsimp [z]; simp
  have h1z_pos : 0 < (1 - z).re := by dsimp [z]; simp; norm_num
  have hz_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_pos
  have h1z_ne : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1z_pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  -- sin(πz) ≠ 0: 由 Γ(z)Γ(1-z) = π/sin(πz) ≠ 0 推出
  have hleft_ne : Complex.Gamma z * Complex.Gamma (1 - z) ≠ 0 := mul_ne_zero hz_ne h1z_ne
  have hsin_ne : Complex.sin (↑Real.pi * z) ≠ 0 := by
    intro hs
    have hzero : Complex.Gamma z * Complex.Gamma (1 - z) = 0 := by
      rw [hrefl, hs]
      simp
    exact hleft_ne hzero
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) hrefl
  -- 左侧: Γ(z)·Γ(1-z)
  rw [Complex.arg_mul_coe_angle hz_ne h1z_ne] at harg
  -- 右侧: arg(π/sin(πz)) = arg π - arg sin(πz)
  rw [Complex.arg_div_coe_angle (by exact_mod_cast Real.pi_ne_zero) hsin_ne] at harg
  -- arg π = 0
  have harg_pi : (↑Real.pi : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
  rw [harg_pi] at harg
  simp at harg
  -- arg(sin(πz)) = (log sin(πz)).im (log_im 反向)
  have hlog : (Complex.log (Complex.sin (↑Real.pi * z))).im =
      (Complex.sin (↑Real.pi * z)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 z 的具体值: 1-z = 1/4-it/2
  have h1z : 1 - z = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    dsimp [z]; ring
  rw [h1z] at harg
  dsimp [z] at harg
  exact harg

/-- D: 组合 (模 2π): 2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im
    + (log sin(π(3/4+it/2))).im。
    代数: B + C + A ⟹ 2a = d + e + f (Γ 完全消去)。 
English: D: combination (mod 2π): 2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im + (log sin(π(3/4+it/2))).im. Algebra: B + C + A ⟹ 2a = d + e + f (Γ fully cancels). -/
theorem gamma_quarter_phase_combine (t : ℝ) :
    (((2 : ℝ) * (Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg) : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle)
        + ((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  let a : ℝ := (Complex.Gamma s).arg
  let b : ℝ := (Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg
  let d : ℝ := (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg
  let e : ℝ := (Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im
  let f : ℝ := (Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im
  have hA := gamma_conj_arg_angle s
  have hB := gamma_doubling_arg_angle t
  have hC := gamma_reflection_arg_angle t
  -- hA 里 conj s = 1/4-it/2, 用于消 hC 中的 Γ(1/4-)
  have hconj : (starRingEnd ℂ) s = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    apply Complex.ext <;> dsimp [s] <;> simp
  rw [hconj] at hA
  -- hA: ↑arg Γ(1/4-) = -↑arg Γ(s) = -↑a
  rw [hA] at hC
  -- hC: ↑b + (-↑a) = -↑f ⟹ ↑b = ↑a - ↑f
  have hb : (↑b : Real.Angle) = (↑a : Real.Angle) - (↑f : Real.Angle) := by
    calc
      (↑b : Real.Angle) = (↑b + (-↑a)) + ↑a := by abel
      _ = (-↑f) + (↑a : Real.Angle) := by rw [hC]
      _ = (↑a : Real.Angle) - (↑f : Real.Angle) := by abel
  -- hB: ↑a + ↑b = ↑d + ↑e
  rw [hb] at hB
  -- ↑a + (↑a - ↑f) = ↑d + ↑e ⟹ ↑a + ↑a = ↑d + ↑e + ↑f
  have hsum : (↑a : Real.Angle) + (↑a : Real.Angle)
      = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by
    calc
      (↑a : Real.Angle) + (↑a : Real.Angle) = (↑a + (↑a - ↑f)) + (↑f : Real.Angle) := by abel
      _ = (↑d + ↑e) + (↑f : Real.Angle) := by rw [hB]
      _ = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by abel
  -- 目标左侧: ↑(2·a) = ↑a + ↑a
  have htwo : (↑(2 * a) : Real.Angle) = (↑a : Real.Angle) + (↑a : Real.Angle) := by
    rw [two_mul]; simp
  rw [htwo]
  dsimp [a, d, e, f]
  exact hsum

end RiemannUnifiedObservation
