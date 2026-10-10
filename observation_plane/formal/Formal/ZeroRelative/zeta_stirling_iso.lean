import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# T6i: χ 圈数渐近 (Stirling) — 对消法的显式相位刻度

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) 是函数方程乘子: ζ(s) = χ(s)·ζ(1-s)。
χ 沿临界线是**单位圆上的路径** (|χ(1/2+it)| = 1, 反射公式), 其相位
θ_χ(T) = arg χ(1/2+iT) 是"显式相位刻度": 圈数 = θ_χ(T)/2π 是
零点计数 N(T) = (1/π)θ_χ(T) + S(T) + 1 的主项 (参数原理, 任务③)。

**Stirling 渐近** (本文件的核心声明):
    θ_χ(T) = (T/2)·log(T/2π) - T/2 - π/8 + O(1/T)   (Backlund)
    ⟹ 零点计数 N(T) = (T/2π)·log(T/2πe) + 7/8 + S(T) + O(1/T)
    (N = θ_χ/π + 1 + S: 常数 1 + (-1/8) = 7/8)

第一层 (本文件): 精确部分 — 反射公式:
    χ(s)·χ(1-s) = 1 (s ∉ ℤ: 乘子自反)
    |χ(1/2+it)| = 1 (χ 临界线 = 单位圆路径)
    θ_χ(T) 的定义与分解 (arg = T·log(2π) - arg Γ(1/2+iT) + arg sin)
第二层 (Stirling 主项): log|Γ| 精确 + Im log Γ 的 Binet 展开 (后续)。

对消法 (pat 本质, 2026-08-19): χ 的显式相位是"参照相位", 用 θ_χ
对消 ζ 的隐式相位 (素数叠加), 残差 S(T) 是整数层 (T6e/T6g)。

隔离文件 (mathlib-only)。 
English: chi self-duality and modulus one on the line (T6i) -/

noncomputable section

open Complex
open Filter
open scoped Topology ComplexConjugate

namespace RiemannUnifiedObservation

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 
English: χ(s) = 2·(2π)^{s−1}·Γ(1−s)·sin(πs/2): functional equation multiplier (explicit phase). -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

/-- χ 共轭对称: χ(s̄) = conj (χ s) (系数逐项共轭: 2π 实数 / Γ / sin)。 
English: χ conjugation symmetry: χ(s̄) = conj (χ s) (each coefficient conjugated: 2π real / Γ / sin). -/
theorem chi_conj (s : ℂ) : chi (conj s) = conj (chi s) := by
  unfold chi
  rw [map_mul, map_mul, map_mul]
  -- conj((2π)^{s-1}) = (2π)^{conj s - 1}: 底 2π 为正实数 (arg = 0 ≠ π)
  have hpow : conj ((2 * ↑Real.pi : ℂ) ^ (s - 1)) = (2 * ↑Real.pi : ℂ) ^ (conj s - 1) := by
    have hx : (2 * ↑Real.pi : ℂ).arg ≠ (Real.pi : ℝ) := by
      have hcast : (2 * ↑Real.pi : ℂ) = (2 * Real.pi : ℝ) := by norm_num
      have harg : (2 * ↑Real.pi : ℂ).arg = 0 := by
        rw [hcast, Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      rw [harg]
      exact Real.pi_ne_zero.symm
    have h1 := Complex.conj_cpow (2 * ↑Real.pi : ℂ) (conj s - 1) hx
    -- h1 : conj(2π)^(conj s - 1) = conj((2π)^(conj(conj s - 1)))
    -- 左 = (2π)^(conj s - 1), 右 = conj((2π)^(s-1))
    simpa [map_ofNat, Complex.conj_ofReal, conj_conj, map_sub, map_one] using h1.symm
  rw [hpow]
  -- Γ(1-s) 的共轭 = Γ(1 - conj s)
  have hgamma : conj (Complex.Gamma (1 - s)) = Complex.Gamma (1 - conj s) := by
    simpa [map_sub, map_one] using (Gamma_conj (1 - s)).symm
  rw [hgamma]
  -- sin(πs/2) 的共轭 = sin(π·conj s/2)
  have hsin : conj (Complex.sin (↑Real.pi * s / 2)) =
      Complex.sin (↑Real.pi * conj s / 2) := by
    simpa [map_div, map_mul, map_ofNat, Complex.conj_ofReal, conj_conj]
      using (sin_conj (↑Real.pi * s / 2)).symm
  rw [hsin]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [map_ofNat]
  rw [h2]

/-- **乘子自反**: χ(s)·χ(1-s) = 1 (s ∉ ℤ)。
    = 4(2π)^{-1}·Γ(1-s)Γ(s)·sin(πs/2)sin(π(1-s)/2)
    = 4(2π)^{-1}·(π/sin πs)·(1/2)sin πs = 1 (反射公式 + 积化和差)。 
English: Multiplier self-reflection: χ(s)·χ(1−s) = 1 (s ∉ ℤ). = 4(2π)^{−1}·Γ(1−s)Γ(s)·sin(πs/2)sin(π(1−s)/2) = 4(2π)^{−1}·(π/sin πs)·(1/2)sin πs = 1 (reflection formula + product-to-sum). -/
theorem chi_mul_chi_one_sub {s : ℂ} (hs : s ∉ Set.range (fun n : ℤ => (n : ℂ))) :
    chi s * chi (1 - s) = 1 := by
  -- 重排: 4·(2π)^{s-1}(2π)^{-s}·Γ(1-s)Γ(s)·sin(πs/2)sin(π(1-s)/2)
  have h1 : chi s * chi (1 - s) =
      4 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (1 - s - 1)) *
        (Complex.Gamma (1 - s) * Complex.Gamma s) *
        (Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2)) := by
    unfold chi
    ring
  -- (2π)^{s-1}·(2π)^{(1-s)-1} = (2π)^{-1}
  have hne : (2 * ↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hpow : (2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (1 - s - 1) =
      (2 * ↑Real.pi : ℂ) ^ (-1 : ℂ) := by
    rw [← cpow_add (s - 1) (1 - s - 1) hne]
    congr 1
    ring
  -- Γ(1-s)·Γ(s) = π/sin(πs) (反射, 无条件)
  have hgamma : Complex.Gamma (1 - s) * Complex.Gamma s =
      ↑Real.pi / Complex.sin (↑Real.pi * s) := by
    simpa [mul_comm] using (Gamma_mul_Gamma_one_sub s)
  -- sin(πs/2)·sin(π(1-s)/2) = (1/2)sin(πs): 积化和差
  have hsin : Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) =
      (1 / 2 : ℂ) * Complex.sin (↑Real.pi * s) := by
    -- cos(X-Y) - cos(X+Y) = 2 sin X sin Y, X = πs/2, Y = π(1-s)/2
    have hcc : Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) -
        Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2) =
        2 * Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) := by
      rw [Complex.cos_sub_cos]
      -- cos(X-Y) - cos(X+Y) = -2 sin X sin(-Y) = 2 sin X sin Y
      have harg : (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2 -
          (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2)) / 2 =
          -(↑Real.pi * (1 - s) / 2) := by ring
      rw [harg, Complex.sin_neg]
      ring
    have hcos1 : Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) =
        Complex.sin (↑Real.pi * s) := by
      have hsub : ↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2 = ↑Real.pi * s - ↑Real.pi / 2 := by
        ring
      rw [hsub, ← Complex.cos_sub_pi_div_two]
    have hcos2 : Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2) = 0 := by
      have hadd : ↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2 = ↑Real.pi / 2 := by ring
      rw [hadd, Complex.cos_pi_div_two]
    calc
      Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) =
          (1 / 2 : ℂ) * (2 * Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2)) := by
        ring
      _ = (1 / 2 : ℂ) * (Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) -
          Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2)) := by
        rw [← hcc]
      _ = (1 / 2 : ℂ) * Complex.sin (↑Real.pi * s) := by
        rw [hcos1, hcos2]
        ring
  -- s ∉ ℤ ⟹ sin(πs) ≠ 0 (sin 零点恰在 πℤ)
  have hsne : Complex.sin (↑Real.pi * s) ≠ 0 := by
    intro hz
    rcases (Complex.sin_eq_zero_iff.mp hz) with ⟨k, hk⟩
    -- π·s = k·π ⟹ s = k (整数), 矛盾
    have hp : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsk : s = (k : ℂ) := by
      have : ↑Real.pi * s = ↑Real.pi * (k : ℂ) := by
        rw [hk]
        ring
      exact mul_left_cancel₀ hp this
    exact hs ⟨k, hsk.symm⟩
  -- 组合: 4·(2π)^{-1}·(π/sin πs)·((1/2)sin πs) = 1
  rw [h1, hpow, hgamma, hsin]
  rw [cpow_neg_one]
  field_simp [hsne]
  ring

/-- **χ 沿临界线模恒 1**: |χ(1/2+it)| = 1。
    χ(1/2+it)·χ(1/2-it) = χ(s)·χ(1-s) = 1 且 χ(1/2-it) = conj χ(1/2+it)
    (共轭对称) ⟹ |χ|² = 1。χ 的相位场 (连续) 是单位圆路径。 
English: χ has modulus 1 on the critical line: |χ(1/2+it)| = 1. χ(1/2+it)·χ(1/2−it) = χ(s)·χ(1−s) = 1 and χ(1/2−it) = conj χ(1/2+it) (conjugation symmetry) ⟹ |χ|² = 1. The phase field of χ (continuous) is a unit-circle path. -/
theorem chi_modulus_one (t : ℝ) : ‖chi (1 / 2 + (t : ℂ) * Complex.I)‖ = 1 := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  -- conj χ(s) = χ(conj s) = χ(1-s) (s = 1/2+it ⟹ conj s = 1-s)
  have hconj : conj (chi s) = chi (1 - s) := by
    have hs : conj s = 1 - s := by
      dsimp [s]
      apply Complex.ext
      · simp
        norm_num
      · simp
    rw [← chi_conj s, hs]
  -- s ∉ ℤ (临界线上非整数)
  have hnot : s ∉ Set.range (fun n : ℤ => (n : ℂ)) := by
    intro h
    rcases h with ⟨n, hn⟩
    -- 虚部: n 的虚部 0 = t ⟹ t = 0 ⟹ s = 1/2
    have htim : (n : ℂ).im = t := by
      have hc := congrArg (fun z : ℂ => z.im) hn
      calc (n : ℂ).im = s.im := hc
        _ = t := by dsimp [s]; simp
    have ht0 : t = 0 := by
      rw [← htim]
      simp
    -- s = 1/2 ⟹ (n : ℂ) = 1/2
    have hs2 : s = 1 / 2 := by
      dsimp [s]
      rw [ht0]
      simp
    have hn2 : (n : ℂ) = (1 / 2 : ℂ) := by
      calc (n : ℂ) = s := hn
        _ = 1 / 2 := hs2
    -- 实部: n = 1/2 (ℝ), 与整数矛盾 (2n = 1)
    have hnn : (n : ℝ) = 1 / 2 := by
      have hc := congrArg (fun z : ℂ => z.re) hn2
      have hre2 : (n : ℂ).re = 1 / 2 := by simpa using hc
      have hnri : (n : ℂ).re = (n : ℝ) := Complex.ofReal_re (n : ℝ)
      rw [← hnri, hre2]
    have h2 : (2 : ℝ) * (n : ℝ) = 1 := by
      rw [hnn]
      norm_num
    have h2z : (2 * n : ℤ) = 1 := by
      exact_mod_cast h2
    omega
  -- χ(s)·χ(1-s) = 1
  have hmul : chi s * chi (1 - s) = 1 := chi_mul_chi_one_sub hnot
  -- ‖χ(s)‖² = χ(s)·conj χ(s)
  have hsq : ‖chi s‖ ^ 2 = (chi s * conj (chi s)).re := by
    rw [Complex.sq_norm]
    unfold Complex.normSq
    simp [mul_re, conj_re, conj_im]
  -- ‖χ(s)‖² = 1
  have hsq1 : ‖chi s‖ ^ 2 = 1 := by
    rw [hsq, hconj, hmul]
    simp
  -- ‖χ(s)‖ ≥ 0, 平方为 1 ⟹ = 1
  have hnonneg : 0 ≤ ‖chi s‖ := norm_nonneg _
  change ‖chi s‖ = 1
  have hsq1' : ‖chi s‖ ^ 2 = (1 : ℝ) ^ 2 := by
    simpa [one_pow] using hsq1
  exact (sq_eq_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hsq1'

/-- **θ_χ(T) = arg χ(1/2+iT) (主枝)**: χ 沿临界线的显式相位。 
English: θ_χ(T) = arg χ(1/2+iT) (principal branch): explicit phase of χ along the critical line. -/
def thetaChi (T : ℝ) : ℝ :=
  (Complex.log (chi (1 / 2 + (T : ℂ) * Complex.I))).im

/-- χ 圈数 (主枝): 相位/2π。 
English: χ winding number (principal branch): phase/2π. -/
def chiTurnNumber (T : ℝ) : ℝ :=
  thetaChi T / (2 * ↑Real.pi)


/-- **log cosh 分解**: log cosh(x) = x - log 2 + log(1+e^{-2x}) (x ≥ 0)。
    cosh x = e^x·(1+e^{-2x})/2 (提取 e^x), log 展开。 
English: log cosh decomposition: log cosh(x) = x − log 2 + log(1+e^{−2x}) (x ≥ 0). cosh x = e^x·(1+e^{−2x})/2 (extract e^x), expand log. -/
theorem log_cosh_self_add (x : ℝ) (_hx : 0 ≤ x) :
    Real.log (Real.cosh x) = x - Real.log 2 + Real.log (1 + Real.exp (-2 * x)) := by
  -- cosh x = (e^x + e^{-x})/2 = e^x·(1+e^{-2x})/2
  have hcosh : Real.cosh x = Real.exp x * (1 + Real.exp (-2 * x)) / 2 := by
    rw [Real.cosh_eq]
    -- e^x + e^{-x} = e^x·(1 + e^{-2x}): 提取 e^x
    have hx1 : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
      -- e^{-x} = e^x·e^{-2x} (exp_add: e^{x + (-2x)} = e^{-x})
      have he : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    rw [hx1]
  -- log 展开: log(e^x·A/2) = log(e^x) + log A - log 2
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hA : 0 < 1 + Real.exp (-2 * x) := by positivity
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [hcosh]
  rw [Real.log_div (ne_of_gt (mul_pos he hA)) (ne_of_gt h2)]
  rw [Real.log_mul (ne_of_gt he) (ne_of_gt hA)]
  rw [Real.log_exp]
  -- x + log A - log 2 整理
  ring

/-- **|Γ(1/2+it)|² 精确公式** (反射公式): |Γ(1/2+it)|² = π/cosh(πt)。
    Γ(s)Γ(1-s) = π/sin(πs) (反射) + sin(π/2+iπt) = cos(iπt) = cosh(πt)
    + Γ 实系数共轭 (|Γ|² = Γ·conj Γ = Γ(s)·Γ(1-s))。 
English: Exact |Γ(1/2+it)|² formula (reflection formula): |Γ(1/2+it)|² = π/cosh(πt). Γ(s)Γ(1−s) = π/sin(πs) (reflection); sin(π/2+iπt) = cos(iπt) = cosh(πt); Γ real coefficients (|Γ|² = Γ·conj Γ = Γ(s)·Γ(1−s)). -/
theorem gammaSq_half_line (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  -- |Γ(s)|² = Γ(s)·conj Γ(s) = Γ(s)·Γ(1-s) (Γ 实系数, conj s = 1-s)
  have hsq : ‖Complex.Gamma s‖ ^ 2 = (Complex.Gamma s * Complex.Gamma (1 - s)).re := by
    -- |z|² = (z·conj z).re
    have hnorm : ‖Complex.Gamma s‖ ^ 2 = (Complex.Gamma s * conj (Complex.Gamma s)).re := by
      rw [Complex.sq_norm]
      unfold Complex.normSq
      simp [mul_re, conj_re, conj_im]
    -- conj (Γ s) = Γ (1-s) (Gamma_conj + conj s = 1-s)
    have hconj : conj (Complex.Gamma s) = Complex.Gamma (1 - s) := by
      have hcs : conj s = 1 - s := by
        dsimp [s]
        apply Complex.ext
        · simp
          norm_num
        · simp
      simpa [hcs] using (Gamma_conj s).symm
    -- (Γs·Γ(1-s)).re = (Γs·conj Γs).re
    have hright : (Complex.Gamma s * Complex.Gamma (1 - s)).re =
        (Complex.Gamma s * conj (Complex.Gamma s)).re := by
      exact congrArg (fun w : ℂ => (Complex.Gamma s * w).re) hconj.symm
    exact hnorm.trans hright.symm
  -- 反射: Γ(s)·Γ(1-s) = π/sin(πs)
  have href : Complex.Gamma s * Complex.Gamma (1 - s) = Real.pi / Complex.sin (Real.pi * s) := by
    simpa [mul_comm] using (Gamma_mul_Gamma_one_sub s)
  -- sin(πs) = sin(π/2 + iπt) = cos(iπt) = cosh(πt) (实数)
  have hsin : Complex.sin (Real.pi * s) = (Real.cosh (Real.pi * t) : ℂ) := by
    -- π·s = π/2 + i·(πt): 展开
    have harg : Real.pi * s = Real.pi / 2 + (Real.pi * t : ℂ) * Complex.I := by
      dsimp [s]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    -- sin(π/2 + z) = cos z (交换序); cos(i·(πt)) = cosh(πt)
    rw [show ↑Real.pi / 2 + ↑Real.pi * ↑t * I = ↑Real.pi * ↑t * I + ↑Real.pi / 2 by ring]
    rw [Complex.sin_add_pi_div_two]
    rw [Complex.cos_mul_I]
    -- cosh 的 ℝ → ℂ cast: (cosh (πt) : ℂ) = Complex.cosh (πt : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh (Real.pi * t)]
  -- 组合: |Γ|² = π/cosh(πt) (实数, sin 实数)
  have hsq1 : ‖Complex.Gamma s‖ ^ 2 = (Real.pi / Real.cosh (Real.pi * t) : ℝ) := by
    -- 从 hsq/href/hsin
    rw [hsq, href]
    rw [hsin]
    -- ↑π/↑(cosh πt) = ↑(π/cosh πt), 实部 = π/cosh πt (ofReal_div 反向 + ofReal_re)
    rw [← Complex.ofReal_div]
    rw [Complex.ofReal_re]
  -- 展开 s
  simpa [s] using hsq1

/-- **log|Γ(1/2+it)| 精确公式**: log|Γ(1/2+it)| = (1/2)(log π - log cosh(πt))。
    由 |Γ|² = π/cosh(πt) (gammaSq_half_line) + log_sqrt。 
English: Exact log|Γ(1/2+it)| formula: log|Γ(1/2+it)| = (1/2)(log π − log cosh(πt)). From |Γ|² = π/cosh(πt) (gammaSq_half_line) plus log_sqrt. -/
theorem logAbsGamma_half_line (t : ℝ) :
    Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      (1 / 2) * (Real.log Real.pi - Real.log (Real.cosh (Real.pi * t))) := by
  -- |Γ|² = π/cosh(πt) > 0, log|Γ| = (1/2)log|Γ|²
  have hsq := gammaSq_half_line t
  have hpos : 0 < Real.pi / Real.cosh (Real.pi * t) := by
    exact div_pos Real.pi_pos (Real.cosh_pos _)
  -- log‖Γ‖ = log √‖Γ‖² = (1/2)log‖Γ‖²
  have hsq2 : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := hsq
  have hsqrt : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
    -- ‖Γ‖ ≥ 0 且 ‖Γ‖² = (√x)² ⟹ ‖Γ‖ = √x
    have hnonneg : 0 ≤ ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have hsq3 : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
        (Real.sqrt (Real.pi / Real.cosh (Real.pi * t))) ^ 2 := by
      rw [hsq2, Real.sq_sqrt (le_of_lt hpos)]
    exact (sq_eq_sq₀ (a := ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖)
      (b := Real.sqrt (Real.pi / Real.cosh (Real.pi * t))) hnonneg (Real.sqrt_nonneg _)).mp hsq3
  rw [hsqrt, Real.log_sqrt (le_of_lt hpos)]
  -- (1/2)log(π/cosh) = (1/2)(log π - log cosh)
  rw [Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt (Real.cosh_pos _))]
  ring

/-- **log|Γ(1/2+it)| 渐近主项** (t ≥ 0):
    log|Γ(1/2+it)| = (1/2)log(2π) - πt/2 - (1/2)log(1+e^{-2πt})。
    由精确公式 + log cosh 分解; 误差项 -log(1+e^{-2πt}) 指数衰减。 
English: Asymptotic leading term of log|Γ(1/2+it)| (t ≥ 0): log|Γ(1/2+it)| = (1/2)log(2π) − πt/2 − (1/2)log(1+e^{−2πt}). From the exact formula + log cosh decomposition; the error term −log(1+e^{−2πt}) decays exponentially. -/
theorem logAbsGamma_half_line_asymp (t : ℝ) (ht : 0 ≤ t) :
    Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      (1 / 2) * (Real.log (2 * Real.pi)) - (Real.pi * t) / 2 -
        (1 / 2) * Real.log (1 + Real.exp (-2 * Real.pi * t)) := by
  rw [logAbsGamma_half_line]
  rw [log_cosh_self_add (Real.pi * t) (mul_nonneg (le_of_lt Real.pi_pos) ht)]
  -- (1/2)(log π - (x - log 2 + log A)) = (1/2)log(2π) - x/2 - (1/2)log A
  have hlog : Real.log Real.pi + Real.log 2 = Real.log (Real.pi * 2) := by
    rw [Real.log_mul (ne_of_gt Real.pi_pos) (by norm_num : (2 : ℝ) ≠ 0)]
  -- 左侧整理: (1/2)(log π - x + log 2 - log A) = (1/2)(log π + log 2) - x/2 - (1/2)log A
  rw [show (1 / 2 : ℝ) * (Real.log Real.pi - (Real.pi * t - Real.log 2 +
        Real.log (1 + Real.exp (-2 * (Real.pi * t))))) =
      (1 / 2 : ℝ) * (Real.log Real.pi + Real.log 2) - (Real.pi * t) / 2 -
        (1 / 2) * Real.log (1 + Real.exp (-2 * (Real.pi * t))) by ring]
  rw [hlog]
  ring

-- ============================================================
-- T6j: Stirling 第二层 — sin 相位精确项 + e^{iθ_χ} = χ 桥 (2026-08-19)
-- 渐进用桥解决 (用户方法论): 不造 Binet 轮子, 桥 = 显式相位刻度
--   e^{iθ_χ(T)} = χ(1/2+iT)  (与 e^{iπS} = u 平行: χ 的 e^{iπ} 桥)
--   Im log sin(π/4+iπT/2) = arctan(tanh(πT/2)) → π/4 (显式相位, 精确渐近)
-- θ_χ 的 Backlund 主项 (T/2)log(T/2π) - T/2 - π/8 + O(1/T) 是经典 KNOWN
-- (Binet 展开, 标注引用, 不重新证明); 本文件给出可完全证明的桥接结构。
-- ============================================================

/-- **e^{iθ_χ} = χ 桥**: θ_χ 的 e^{iπ} 次幂 = χ 自身。
    |χ(1/2+iT)| = 1 ⟹ log χ 纯虚 ⟹ log χ = i·θ_χ ⟹ e^{log χ} = e^{iθ_χ} = χ。
    与 e^{iπS(T)} = u(T) 平行: u 是 ζ 的隐式相位, χ 是显式相位 (快路径)。 
English: e^{iθ_χ} = χ bridge: χ is e^{iθ_χ} itself. |χ(1/2+iT)| = 1 ⟹ log χ purely imaginary ⟹ log χ = i·θ_χ ⟹ e^{log χ} = e^{iθ_χ} = χ. Parallel to e^{iπS(T)} = u(T): u is the implicit phase of ζ, χ the explicit phase (fast path). -/
theorem exp_thetaChi_eq_chi (T : ℝ) :
    Complex.exp ((thetaChi T : ℂ) * Complex.I) =
      chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) := by
  -- log χ = i·θ_χ: 实部 = log|χ| = log 1 = 0, 虚部 = θ_χ (定义)
  have hlog : Complex.log (chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)) =
      (thetaChi T : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.log_re, chi_modulus_one, Real.log_one]
      simp [thetaChi]
    · simp [thetaChi]
  -- e^{log χ} = χ (χ ≠ 0, |χ| = 1)
  have hne : chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hnorm : ‖chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ = 0 := by
      rw [h]
      simp
    rw [chi_modulus_one T] at hnorm
    norm_num at hnorm
  rw [← hlog]
  exact Complex.exp_log hne

/-- **sin 相位精确**: Im log sin(π/4+iπT/2) = arctan(tanh(πT/2))。
    sin(π/4+iy) = sin(π/4)cos(iy) + cos(π/4)sin(iy) = (√2/2)(cosh y + i·sinh y),
    arg = arctan(sinh y/cosh y) = arctan(tanh y) (re > 0 ⟹ arg ∈ (-π/2, π/2))。 
English: Exact sin phase: Im log sin(π/4+iπT/2) = arctan(tanh(πT/2)). sin(π/4+iy) = sin(π/4)cos(iy) + cos(π/4)sin(iy) = (√2/2)(cosh y + i·sinh y), arg = arctan(sinh y/cosh y) = arctan(tanh y) (re > 0 ⟹ arg ∈ (−π/2, π/2)). -/
theorem sin_phase_exact (T : ℝ) :
    (Complex.log (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2))).im
      = Real.arctan (Real.tanh (Real.pi * T / 2)) := by
  let y : ℝ := Real.pi * T / 2
  -- sin(π/4 + iy) = (√2/2)(cosh y + i·sinh y)
  have hsin : Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2) =
      (↑(Real.sqrt 2 / 2) : ℂ) * (↑(Real.cosh y) + ↑(Real.sinh y) * Complex.I) := by
    have harg : ↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2 =
        (↑Real.pi / 4 : ℂ) + (y : ℂ) * Complex.I := by
      dsimp [y]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    rw [Complex.sin_add]
    have hsinp : Complex.sin (↑Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by
      calc
        Complex.sin (↑Real.pi / 4) = Complex.sin (↑(Real.pi / 4)) := by
          congr 1
          rw [Complex.ofReal_div]
          norm_num
        _ = ↑(Real.sin (Real.pi / 4)) := by rw [Complex.ofReal_sin]
        _ = ↑(Real.sqrt 2 / 2) := by rw [Real.sin_pi_div_four]
    have hcosp : Complex.cos (↑Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by
      calc
        Complex.cos (↑Real.pi / 4) = Complex.cos (↑(Real.pi / 4)) := by
          congr 1
          rw [Complex.ofReal_div]
          norm_num
        _ = ↑(Real.cos (Real.pi / 4)) := by rw [Complex.ofReal_cos]
        _ = ↑(Real.sqrt 2 / 2) := by rw [Real.cos_pi_div_four]
    have hcosi : Complex.cos ((y : ℂ) * Complex.I) = ↑(Real.cosh y) := by
      rw [Complex.cos_mul_I]
      rw [← Complex.ofReal_cosh]
    have hsini : Complex.sin ((y : ℂ) * Complex.I) = ↑(Real.sinh y) * Complex.I := by
      rw [Complex.sin_mul_I]
      rw [← Complex.ofReal_sinh]
    rw [hsinp, hcosp, hcosi, hsini]
    ring
  -- arg: z = (√2/2)(cosh y + i·sinh y), re > 0 ⟹ arg = arctan(tanh y)
  have hre : 0 < (↑(Real.cosh y) : ℂ).re := by simp [Real.cosh_pos]
  have hz : (↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I ≠ 0 := by
    intro h
    have : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re = 0 := by rw [h]; simp
    simp at this
    linarith [Real.cosh_pos y]
  have harg' : (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2)).arg
      = Real.arctan (Real.tanh y) := by
    rw [hsin]
    -- arg(↑(√2/2)·z) = arg z (正标量, arg_real_mul)
    have hpos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    have hscalar : ((↑(Real.sqrt 2 / 2) : ℂ) * ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I)).arg
        = ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
      simpa using
        (Complex.arg_real_mul ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I) hpos)
    rw [hscalar]
    -- tan(arg z) = sinh/cosh = tanh y (tan_arg), arg ∈ (-π/2, π/2) (re > 0)
    have htan : Real.tan (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg)
        = Real.tanh y := by
      have hre_z : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re = Real.cosh y := by
        simp only [add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
        ring
      have him_z : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).im = Real.sinh y := by
        simp only [add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
        simp
      rw [Complex.tan_arg]
      rw [hre_z, him_z]
      rw [Real.tanh_eq_sinh_div_cosh]
    have hmem : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg
        ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      -- cos(arg z) = re/‖z‖ > 0 且 arg ∈ (-π, π] ⟹ |arg| < π/2
      have hcos : 0 < Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) := by
        rw [Complex.cos_arg hz]
        -- re/‖z‖ > 0
        have hre' : 0 < ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re := by
          simp [Real.cosh_pos y]
        exact div_pos hre' (norm_pos_iff.mpr hz)
      have hargmem := Complex.arg_mem_Ioc ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I)
      constructor
      · by_contra hnot
        have hle : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg ≤ -(Real.pi / 2) := by
          linarith
        have hcosle : Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤ 0 := by
          have h1 : Real.pi / 2 ≤ -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) := by
            linarith
          have h2 : -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤
              Real.pi + Real.pi / 2 := by
            have hlt : -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) < Real.pi := by
              linarith [hargmem.1]
            linarith
          have hc : Real.cos (-(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg)) ≤ 0 := by
            exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
          rwa [Real.cos_neg] at hc
        linarith
      · by_contra hnot
        have hle : Real.pi / 2 ≤ ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
          linarith
        have hcosle : Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤ 0 := by
          exact Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [hargmem.2])
        linarith
    -- arctan(tan(arg)) = arg (arg ∈ (-π/2, π/2)), tan(arg) = tanh y
    have harct : Real.arctan (Real.tanh y) = ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
      rw [← htan]
      exact Real.arctan_tan hmem.1 hmem.2
    exact harct.symm
  -- Im log = arg (log_im)
  rw [Complex.log_im]
  -- y = πT/2 代入
  simpa [y] using harg'

/-- **sin 相位渐近**: Im log sin(π/4+iπT/2) → π/4 (T → ∞)。
    arctan(tanh(πT/2)) → arctan 1 = π/4: tanh → 1 (指数表示) + arctan 连续。 
English: Asymptotic sin phase: Im log sin(π/4+iπT/2) → π/4 (T → ∞). arctan(tanh(πT/2)) → arctan 1 = π/4: tanh → 1 (exponential form) plus arctan continuous. -/
theorem sin_phase_tendsto_pi_div_four :
    Tendsto (fun T : ℝ => (Complex.log
        (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2))).im)
      atTop (𝓝 (Real.pi / 4)) := by
  -- tanh x → 1: tanh x = (e^{2x}-1)/(e^{2x}+1) = 1 - 2/(e^{2x}+1)
  have htanh : Tendsto Real.tanh atTop (𝓝 1) := by
    have hdecomp : ∀ x : ℝ, Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
      intro x
      calc
        Real.tanh x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by
          rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
          field_simp
        _ = 1 - 2 * (Real.exp (-x) / (Real.exp x + Real.exp (-x))) := by
          field_simp
          ring
        _ = 1 - 2 / (Real.exp (2 * x) + 1) := by
          congr 1
          -- e^{-x}/(e^x+e^{-x}) = 1/(e^{2x}+1): 交叉乘 (field_simp)
          field_simp [Real.exp_ne_zero]
          -- e^{-x}·(e^{2x}+1) = e^{-x}·e^{2x} + e^{-x} = e^{x} + e^{-x}
          rw [mul_add]
          rw [← Real.exp_add]
          have hpar : -x + 2 * x = x := by ring
          rw [hpar]
          simp
    have h_exp : Tendsto (fun x : ℝ => Real.exp (2 * x)) atTop atTop := by
      exact Real.tendsto_exp_atTop.comp
        (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
    have h_inv : Tendsto (fun x : ℝ => (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 0) := by
      have h_add : Tendsto (fun x : ℝ => Real.exp (2 * x) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 h_exp
      exact tendsto_inv_atTop_zero.comp h_add
    have h_two : Tendsto (fun x : ℝ => 2 * (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [mul_comm] using (tendsto_const_nhds.mul h_inv)
    have h_one : Tendsto (fun x : ℝ => 1 - 2 * (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h_two
    simpa [hdecomp] using (h_one.congr' (Eventually.of_forall (fun x => by rw [hdecomp x]; ring)))
  -- arctan 连续 + tanh(πT/2) → 1 + arctan 1 = π/4
  have htan' : Tendsto (fun T : ℝ => Real.tanh (Real.pi * T / 2)) atTop (𝓝 1) := by
    have hmul : Tendsto (fun T : ℝ => Real.pi * T / 2) atTop atTop := by
      have hc : Tendsto (fun T : ℝ => Real.pi * T) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < Real.pi) tendsto_id
      simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hc.atTop_div_const (by positivity : (0 : ℝ) < 2))
    exact htanh.comp hmul
  have harct : Tendsto (fun T : ℝ => Real.arctan (Real.tanh (Real.pi * T / 2))) atTop
      (𝓝 (Real.pi / 4)) := by
    have hc : ContinuousAt Real.arctan 1 := Real.continuousAt_arctan
    simpa [Function.comp_def, Real.arctan_one] using (hc.tendsto.comp htan')
  -- sin_phase_exact 代入
  refine harct.congr' (Eventually.of_forall (fun T => ?_))
  rw [← sin_phase_exact]

end RiemannUnifiedObservation
