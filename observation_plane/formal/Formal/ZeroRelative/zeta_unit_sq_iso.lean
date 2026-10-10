import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

/-!
# T5: u² = χ — 无分支的相位恒等式 (三角函数累积延拓)

u(t) = ζ(1/2+it)/|ζ(1/2+it)| = e^{i·arg ζ}: 良定义连续 (ζ ≠ 0 处), 无分支。
由函数方程 (s = 1/2+it 时 1-s = conj s) + mathlib 全域共轭 riemannZeta_conj:

  ζ(s) = χ(s)·conj ζ(s)  ⟹  u(t)² = χ(1/2+it)

u 是 χ 的连续平方根: 沿 t 累积延拓, 每跨一个零点 u → -u (符号翻转 =
arg 跳 π = 一个零点), 翻转次数 = N₀(T)。整数计数由累积自动给出
(傅里叶相位校准) — 不需要解析地维护 arg 的分支。

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) (临界线全显式)。

隔离文件 (mathlib-only: riemannZeta_conj 来自 ZetaAsymp, olean 可用)。

English: u² = χ: the unit-phase square equals the multiplier (isolated version of T5) -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

-- arg(2π) ≠ π (conj_cpow 的条件: 底数不在负实轴)
private lemma arg_two_pi_ne_pi : ((2 * ↑Real.pi : ℂ).arg) ≠ Real.pi := by
  have h0 : (2 * ↑Real.pi : ℂ).arg = 0 := by
    have h0' : ((2 * Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by positivity)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

-- conj 穿透 cpow (2π 底数, 正实数)
private lemma conj_two_pi_cpow (z : ℂ) :
    (starRingEnd ℂ) ((2 * ↑Real.pi : ℂ) ^ z) = (2 * ↑Real.pi : ℂ) ^ ((starRingEnd ℂ) z : ℂ) := by
  have h := Complex.conj_cpow (2 * ↑Real.pi : ℂ) z arg_two_pi_ne_pi
  have hc : (starRingEnd ℂ) (2 * ↑Real.pi : ℂ) = 2 * ↑Real.pi := by
    have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hcast]
    exact Complex.conj_ofReal (2 * Real.pi)
  rw [hc] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

/-- 临界线闭合: ζ(s) = χ(s)·conj ζ(s), s = 1/2+it。
    函数方程 (1-s = conj s) + riemannZeta_conj (mathlib 全域共轭)。
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。 
English: Critical-line closure: ζ(s) = χ(s)·conj ζ(s), s = 1/2+it. Functional equation (1−s = conj s) plus riemannZeta_conj (mathlib global conjugation). χ(s) = 2·(2π)^{s−1}·Γ(1−s)·sin(πs/2). -/
theorem zeta_eq_chi_mul_conj_on_line (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) *
          (starRingEnd ℂ) (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  have hs_int : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = (-(n : ℂ)).re := by rw [hn]
    rw [hre] at this
    have hnre : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [hnre] at this
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = 1 := by rw [h]; simp
    rw [hre] at this
    norm_num at this
  have hfe := riemannZeta_one_sub (s := s) hs_int hs1
  -- hfe : ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  rw [h1s] at hfe
  -- hfe : ζ(conj s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  rw [riemannZeta_conj s] at hfe
  -- hfe : conj ζ(s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  have hfe' := congrArg (starRingEnd ℂ) hfe
  -- hfe' : ζ(s) = conj(2(2π)^{-s}Γ(s)cos(πs/2)ζ(s))
  have hfe'' : riemannZeta s = 2 * (2 * ↑Real.pi) ^ (-(starRingEnd ℂ) s) *
      Complex.Gamma ((starRingEnd ℂ) s) * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) *
      riemannZeta ((starRingEnd ℂ) s) := by
    -- conj 穿透: star 保环运算 + 各 conj 定理 (← 方向: conj(cos x) → cos(conj x))
    have h2c : (starRingEnd ℂ) 2 = 2 := by exact Complex.conj_ofReal 2
    simpa [h2c, ← Complex.Gamma_conj, ← Complex.cos_conj, ← riemannZeta_conj, conj_two_pi_cpow]
      using hfe'
  -- 替换 conj s = 1-s
  rw [← h1s] at hfe''
  -- -(1-s) = s-1
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe''
  -- cos(π(1-s)/2) = sin(πs/2)
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [← Complex.cos_sub_pi_div_two]
    have harg : ↑Real.pi * (1 - s) / 2 = -((↑Real.pi * s / 2) - ↑Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  rw [hcos] at hfe''
  -- ζ(1-s) → conj ζ(s): 只替换 ζ 的参数 (Γ(1-s) 保持)
  have hzeta_arg : riemannZeta (1 - s) = riemannZeta ((starRingEnd ℂ) s) := by rw [h1s]
  rw [hzeta_arg] at hfe''
  rw [riemannZeta_conj s] at hfe''
  -- hfe'' : ζ(s) = 2(2π)^{s-1}·Γ(1-s)·sin(πs/2)·conj ζ(s)
  dsimp [s] at hfe''
  exact hfe''

/-- u² = χ: u(t) = ζ(s)/|ζ(s)| 满足 u² = χ(s) (s = 1/2+it)。
    ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1)。
    u 是 χ 的连续平方根 — 累积延拓的基元。 
English: u² = χ: u(t) = ζ(s)/|ζ(s)| satisfies u² = χ(s) (s = 1/2+it). ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1). u is a continuous square root of χ — the primitive of cumulative continuation. -/
theorem zeta_unit_sq_eq_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) ^ 2
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := riemannZeta s / ‖riemannZeta s‖
  have hmain := zeta_eq_chi_mul_conj_on_line t
  -- |ζ|² = χ·(conj ζ)² (hmain 乘 conj ζ)
  have h2 : (‖riemannZeta s‖ : ℂ) ^ 2 =
      2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
        (starRingEnd ℂ) (riemannZeta s) := by
    calc
      (‖riemannZeta s‖ : ℂ) ^ 2 = (↑(‖riemannZeta s‖ ^ 2) : ℂ) := by
        exact (map_pow Complex.ofRealHom (‖riemannZeta s‖) 2).symm
      _ = (Complex.normSq (riemannZeta s) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ = riemannZeta s * (starRingEnd ℂ) (riemannZeta s) := by
        rw [← Complex.mul_conj]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s)) *
          (starRingEnd ℂ) (riemannZeta s) := by
        -- hmain 两边乘 star ζ (s = (1/2:ℂ)+... 是 let, defeq)
        exact congrArg (fun x : ℂ => x * (starRingEnd ℂ) (riemannZeta s)) hmain
  have hz_norm : (‖riemannZeta s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  -- 1 = χ·(conj u)² (h2 除以 ‖ζ‖²)
  have h1 : (1 : ℂ) = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
    calc
      1 = (‖riemannZeta s‖ : ℂ) ^ 2 / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        field_simp [hz_norm]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
            (starRingEnd ℂ) (riemannZeta s)) / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        rw [h2]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ)) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
        -- star(ζ/‖ζ‖) = star ζ/‖ζ‖ (‖ζ‖ 实)
        congr 1
        have hu : (starRingEnd ℂ) (riemannZeta s / (‖riemannZeta s‖ : ℂ)) =
            (starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ) := by
          rw [map_div₀]
          simp
        simpa [u] using hu
  -- u·conj u = 1
  have hu1 : u * (starRingEnd ℂ) u = 1 := by
    have hnorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div]
      have hn : ‖(‖riemannZeta s‖ : ℂ)‖ = ‖riemannZeta s‖ := by
        calc
          ‖(‖riemannZeta s‖ : ℂ)‖ = |‖riemannZeta s‖| :=
            RCLike.norm_ofReal (‖riemannZeta s‖)
          _ = ‖riemannZeta s‖ := abs_of_nonneg (norm_nonneg _)
      rw [hn]
      have hz_norm_r : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp [hz_norm_r]
    rw [Complex.mul_conj]
    -- (normSq u : ℂ) = 1: normSq u = ‖u‖², ‖u‖ = 1
    have hnsq : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
    rw [hnsq, hnorm]
    norm_num
  -- u² = χ (1 = χ·(conj u)² 两边乘 u²)
  have hu2 : u ^ 2 = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) := by
    calc
      u ^ 2 = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2) * u ^ 2 := by
            rw [← h1]
            simp
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (((starRingEnd ℂ) u) * u) ^ 2 := by
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (u * (starRingEnd ℂ) u) ^ 2 := by
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * 1 := by
          rw [hu1]
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) := by
          ring
  -- 替换 s, u
  dsimp [u, s] at hu2
  exact hu2

end RiemannUnifiedObservation
