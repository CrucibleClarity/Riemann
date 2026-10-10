import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# 临界带 ζ 共轭 (pat0 启发快速 0pat 延拓)

路径: 不证解析延拓 (反全纯基础设施缺口), 从定义层把共轭逐项穿透:
  ζ(s) = (s·Λ₀(s) − 1 − s/(1−s)) / (2·π^(−s/2)·Γ(s/2+1))     [mathlib riemannZeta_eq_mul_completedRiemannZeta₀]
  Λ₀(s) = mellin f_modif(s) = ∫ t∈(0,∞), t^(s−1) • f_modif t   [mathlib 定义]
  conj(∫ g) = ∫ conj∘g                                        [integral_conj, Bochner 无条件]
  f_modif 实值 (evenKernel : ℝ→ℝ, ofReal 嵌入) ⟹ conj 穿透到 t^(conj s −1)
  ⟹ conj(ζ(s)) = ζ(conj s) 对 0 < Re s < 1 (临界带)

English: strip: zero/pole observations in the critical strip -/

noncomputable section

open scoped BigOperators
open Complex
open HurwitzZeta
open Set

namespace RiemannUnifiedObservation

/-- 正实数的 cpow 共轭: conj(t^w) = t^(conj w) 对 t > 0 (arg = 0). 
English: Conjugation of cpow for positive reals: conj(t^w) = t^(conj w) for t > 0 (arg = 0). -/
lemma conj_cpow_of_pos {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ (w : ℂ)) = (t : ℂ) ^ ((starRingEnd ℂ) w : ℂ) := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    have h0 : ((t : ℂ)).arg = 0 := by
      have h0' : ((t : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt ht)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (t : ℂ) w harg
  have htc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
    exact Complex.conj_ofReal t
  rw [htc] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

/-- f_modif (hurwitzEvenFEPair 0) 实值: evenKernel 实值 (ofReal 嵌入) + 系数全实. 
English: f_modif (hurwitzEvenFEPair 0) is real-valued: evenKernel real-valued (ofReal embedding) plus all coefficients real. -/
lemma conj_f_modif_zero (t : ℝ) :
    (starRingEnd ℂ) ((hurwitzEvenFEPair 0).f_modif t) = (hurwitzEvenFEPair 0).f_modif t := by
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, map_add]
  -- 项 1: indicator (Ioi 1) (fun x => f x - f₀)
  have h1 : (starRingEnd ℂ)
      ((Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t)
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  -- 项 2: indicator (Ioo 0 1) (fun x => f x - (ε * ↑(x ^ (-k))) • g₀)
  have h2 : (starRingEnd ℂ)
      ((Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t)
      = (Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  rw [h1, h2]

/-- Mellin 共轭 (f_modif 实值, 积分共轭无条件): conj(mellin f w) = mellin f (conj w). 
English: Mellin conjugation (f_modif real-valued, integral conjugation unconditional): conj(mellin f w) = mellin f (conj w). -/
lemma conj_mellin_f_modif (w : ℂ) :
    (starRingEnd ℂ) (mellin (hurwitzEvenFEPair 0).f_modif w)
      = mellin (hurwitzEvenFEPair 0).f_modif ((starRingEnd ℂ) w) := by
  unfold mellin
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
  rw [smul_eq_mul, smul_eq_mul]
  rw [map_mul]
  rw [conj_cpow_of_pos ht (w - 1)]
  rw [conj_f_modif_zero t]
  simp [map_sub]

/-- Λ₀ 共轭 (整函数定义层穿透): conj(completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s). 
English: Λ₀ conjugation (definition-layer penetration for the entire function): conj(completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s). -/
lemma conj_completedRiemannZeta₀ (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ s) = completedRiemannZeta₀ (starRingEnd ℂ s) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  rw [map_div₀]
  rw [map_ofNat]
  have hme : (starRingEnd ℂ) ((hurwitzEvenFEPair 0).Λ₀ (s / 2))
      = (hurwitzEvenFEPair 0).Λ₀ ((starRingEnd ℂ) s / 2) := by
    unfold WeakFEPair.Λ₀
    simpa [map_div₀, map_ofNat] using conj_mellin_f_modif (s / 2)
  rw [hme]

/-- 临界带 ζ 共轭: conj(ζ(s)) = ζ(conj s) 对 0 < Re s < 1.
    pat0 启发: 对称性接力 (Λ₀ 结构/函数方程) 替代解析延拓差分论证. 
English: Critical-strip conjugation of ζ: conj(ζ(s)) = ζ(conj s) for 0 < Re s < 1. pat0 heuristic: symmetry relay (Λ₀ structure/functional equation) replaces the analytic-continuation difference argument. -/
theorem zeta_conj_of_critical_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, s / 2 + 1 ≠ -↑n := by
    intro n h
    have hre : (s / 2 + 1).re = (-(↑n : ℂ)).re := by rw [h]
    have hre' : (s / 2 + 1).re = s.re / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re]
      simp
    have hpos : 0 < s.re / 2 + 1 := by linarith [hs0]
    have hneg : ((-(↑n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcne : (↑Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hpi)
  have hgam2 : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact Complex.Gamma_ne_zero hsneg
  have hden : 2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hcne) hgam2
  -- 分母共轭: conj(2·π^(-s/2)·Γ(s/2+1)) = 2·π^(-conj s/2)·Γ(conj s/2+1)
  have harg_pi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    have h0 : (↑Real.pi : ℂ).arg = 0 := by
      have h0' : ((Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have hpi_conj : (starRingEnd ℂ) ((↑Real.pi : ℂ) ^ ((-s / 2) : ℂ))
      = (↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s / 2) : ℂ) := by
    have h := Complex.conj_cpow (↑Real.pi : ℂ) (-s / 2 : ℂ) harg_pi
    have hpic : (starRingEnd ℂ) (↑Real.pi : ℂ) = ↑Real.pi := by
      exact Complex.conj_ofReal Real.pi
    rw [hpic] at h
    have h' := congrArg (starRingEnd ℂ) h
    simpa [map_div₀, map_neg, map_ofNat] using h'
  have hgamma_conj : (starRingEnd ℂ) (Complex.Gamma (s / 2 + 1))
      = Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    have h := Complex.Gamma_conj (s / 2 + 1)
    rw [← h]
    congr 1
    simp [map_div₀, map_add, map_one, map_ofNat]
  -- 主证明: 对 riemannZeta_eq_mul_completedRiemannZeta₀ s 两边 conj
  have hfe := riemannZeta_eq_mul_completedRiemannZeta₀ s
  have hc := congrArg (starRingEnd ℂ) hfe
  rw [map_div₀] at hc
  -- 分子 conj: conj(s·Λ₀(s) − 1 − s/(1−s))
  have hnum : (starRingEnd ℂ) (s * completedRiemannZeta₀ s - 1 - s / (1 - s))
      = (starRingEnd ℂ) s * completedRiemannZeta₀ (starRingEnd ℂ s) - 1
        - (starRingEnd ℂ) s / (1 - (starRingEnd ℂ) s) := by
    rw [map_sub, map_sub, map_mul]
    rw [conj_completedRiemannZeta₀ s]
    rw [map_div₀]
    rw [map_sub]
    simp
  rw [hnum] at hc
  -- 分母 conj
  have hden_conj : (starRingEnd ℂ) (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))
      = 2 * (↑Real.pi : ℂ) ^ (-(starRingEnd ℂ) s / 2) * Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    rw [map_mul, map_mul]
    rw [map_ofNat]
    rw [hpi_conj]
    rw [hgamma_conj]
  rw [hden_conj] at hc
  -- 目标: conj(ζ(s)) = ζ(conj s); 展开 ζ(conj s) 用同一公式
  rw [riemannZeta_eq_mul_completedRiemannZeta₀ (starRingEnd ℂ s)]
  exact hc

end RiemannUnifiedObservation
