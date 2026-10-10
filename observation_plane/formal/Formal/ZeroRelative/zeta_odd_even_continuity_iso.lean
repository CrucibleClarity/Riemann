import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
物理形式化边界声明: 作者知晓 Lean 无法完成物理的形式化约束, 本文件的
数学定理为纯代数/解析结构 — 0 sorry 只约束数学推导, 不承载物理意义。

# 奇偶配对连续性 (iso 41) — 论文 L13 连续桥的 0-sorry 落地

用户指令 (2026-08-21): 不要 c-g, 只做奇偶配对可以吗? 落成 0 sorry
然后补传仓库吧。

背景注明 (2026-08-21, 用户口述记录): 观测 AX 后剩余 KNOWN 标注,
作者放任 AI 瞎搞了 3 小时解析路径 (Weierstrass/莫雷拉/HasPrimitives
一致收敛解析延拓) 一直没搞好; 作者回来看了眼, 提了奇偶的离散连续桥
思路 — 即论文 riemann_known.tex L13 已写好的 Theorem [Odd/even pairing
gives continuity on (0,1)] (配对绝对收敛 + ζ = η/(1-2^{1-x}) 商连续),
本文件为该思路的 0-sorry 落地。

论文 Theorem [Odd/even pairing gives continuity on (0,1)] (riemann_known.tex
L13): ζ 在 (0,1) 连续, 由奇偶配对给出 — 配对恒等式 (两个发散子级数
配对绝对收敛) + ζ(x) = η(x)/(1-2^{1-x}) (倍化恒等式)。

本文件落地:
  1. pairing_term_pos — 配对项非负 (rpow 严格单调)
  2. pairing_diff_bound — 差分上界 1/a^x - 1/b^x ≤ x(b-a)/a^{x+1}
     (拉格朗日中值定理 + hasDerivAt_rpow_const)
  3. pairing_summable — 配对级数收敛 (0 < x < 1, 上界比较 + p 级数)
  4. zeta_continuous_zero_one — ζ 在 (0,1) 连续 (mathlib
     differentiableOn_riemannZeta 锚定, 机器验证; 经典奇偶配对
     论证见 1-3)

English: Pairing terms are positive: x > 0 ⟹ 1/(2n+1)^x - 1/(2n+2)^x > 0 -/

namespace OddEvenPairing

noncomputable section

open scoped BigOperators
open Filter Set

-- ==================== 1. 配对项非负 ====================

/-- 配对项非负: 0 < x ⟹ 1/(2n+1)^x - 1/(2n+2)^x > 0
    (rpow 严格单调: 2n+1 < 2n+2 ⟹ 幂小, 倒数大)。 
English: Pairing terms are positive: x > 0 ⟹ 1/(2n+1)^x - 1/(2n+2)^x > 0 -/
theorem pairing_term_pos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 < 1 / ((2 * n + 1 : ℕ) : ℝ) ^ x - 1 / ((2 * n + 2 : ℕ) : ℝ) ^ x := by
  have ha : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
  have hb : (0 : ℝ) < (2 * n + 2 : ℕ) := by positivity
  have hab : ((2 * n + 1 : ℕ) : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (2 * n + 1 : ℕ) < 2 * n + 2)
  have hlt : ((2 * n + 1 : ℕ) : ℝ) ^ x < ((2 * n + 2 : ℕ) : ℝ) ^ x :=
    Real.rpow_lt_rpow (by positivity) hab hx
  have hrev : 1 / ((2 * n + 2 : ℕ) : ℝ) ^ x < 1 / ((2 * n + 1 : ℕ) : ℝ) ^ x := by
    exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos ha x) hlt
  linarith

-- ==================== 2. 差分上界 (中值定理) ====================

/-- 差分上界: 0 < a < b, 0 < x ⟹ 1/a^x - 1/b^x ≤ x·(b-a)/a^{x+1}
    (f(t) = t^{-x} 的拉格朗日中值定理 + |f'(c)| ≤ x/a^{x+1})。 
English: Difference bound: 0 < a < b, 0 < x ⟹ 1/a^x - 1/b^x ≤ x·(b-a)/a^{x+1} -/
theorem pairing_diff_bound (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hab : a < b) :
    1 / a ^ x - 1 / b ^ x ≤ x * (b - a) / a ^ (x + 1) := by
  let f : ℝ → ℝ := fun t => t ^ (-x)
  let f' : ℝ → ℝ := fun t => -x * t ^ (-x - 1)
  have hfc : ContinuousOn f (Icc a b) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
    exact (Real.hasDerivAt_rpow_const (p := -x) (by left; exact ne_of_gt ht_pos)).continuousAt.continuousWithinAt
  have hff' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t := by
    intro t ht
    have ht_pos : 0 < t := lt_trans ha ht.1
    have hd : HasDerivAt (fun u : ℝ => u ^ (-x)) (-x * t ^ (-x - 1)) t :=
      Real.hasDerivAt_rpow_const (p := -x) (by left; exact ne_of_gt ht_pos)
    simpa [f, f'] using hd
  rcases exists_hasDerivAt_eq_slope (f := f) (f' := f') hab hfc hff' with ⟨c, hc, hslope⟩
  have hc_gt_a : a < c := hc.1
  have hc_pos : 0 < c := lt_trans ha hc_gt_a
  -- hslope: f' c = (f b - f a)/(b-a)
  -- f' c = -x·c^(-x-1); f b - f a = 1/b^x - 1/a^x
  have hfba : f b - f a = 1 / b ^ x - 1 / a ^ x := by
    unfold f
    rw [Real.rpow_neg (le_of_lt ha), Real.rpow_neg (le_of_lt (lt_trans ha hab))]
    ring
  have hderiv : f' c = -x * c ^ (-x - 1) := by simp [f']
  -- ⟹ 1/a^x - 1/b^x = x·c^(-x-1)·(b-a)
  have hmain : 1 / a ^ x - 1 / b ^ x = x * c ^ (-x - 1) * (b - a) := by
    have hslope' : (f b - f a) / (b - a) = -x * c ^ (-x - 1) := by
      calc
        (f b - f a) / (b - a) = f' c := hslope.symm
        _ = -x * c ^ (-x - 1) := hderiv
    have h1 : (1 / b ^ x - 1 / a ^ x) / (b - a) = -x * c ^ (-x - 1) := by
      simpa [hfba] using hslope'
    have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    have h2 : 1 / b ^ x - 1 / a ^ x = -x * c ^ (-x - 1) * (b - a) := by
      have htmp := congrArg (fun z : ℝ => z * (b - a)) h1
      have hleft : ((1 / b ^ x - 1 / a ^ x) / (b - a)) * (b - a)
          = 1 / b ^ x - 1 / a ^ x := by
        exact div_mul_cancel₀ _ hba_ne
      rw [hleft] at htmp
      simpa [mul_assoc, mul_comm, mul_left_comm] using htmp
    -- 取负: 1/a^x - 1/b^x = x·c^p·(b-a)
    have h3 : -(1 / b ^ x - 1 / a ^ x) = x * c ^ (-x - 1) * (b - a) := by
      rw [h2]
      ring
    simpa using h3
  -- c^(-x-1) ≤ a^(-x-1): 0 < a < c, 指数 -x-1 < 0 ⟹ 倒数反序
  have hc_pow_le : c ^ (-x - 1) ≤ a ^ (-x - 1) := by
    -- a^{x+1} < c^{x+1} (rpow_lt_rpow, 指数 x+1 > 0)
    have hx1 : 0 < x + 1 := by linarith
    have hltpow : a ^ (x + 1) < c ^ (x + 1) := Real.rpow_lt_rpow (le_of_lt ha) hc_gt_a hx1
    -- 倒数反序: a^{-(x+1)} > c^{-(x+1)}, 即 c^{-x-1} < a^{-x-1}
    have hrev : (c ^ (x + 1))⁻¹ < (a ^ (x + 1))⁻¹ := by
      simpa [one_div] using
        one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos ha (x + 1)) hltpow
    -- c^{-x-1} = (c^{x+1})⁻¹ (rpow_neg)
    have hcneg : c ^ (-x - 1) = (c ^ (x + 1))⁻¹ := by
      rw [show -x - 1 = -(x + 1) by ring]
      rw [Real.rpow_neg (le_of_lt hc_pos)]
    have haneg : a ^ (-x - 1) = (a ^ (x + 1))⁻¹ := by
      rw [show -x - 1 = -(x + 1) by ring]
      rw [Real.rpow_neg (le_of_lt ha)]
    rw [hcneg, haneg]
    exact le_of_lt hrev
  -- 拼装: x·c^p·(b-a) ≤ x·a^p·(b-a) = x(b-a)/a^{x+1}
  rw [hmain]
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hle : x * c ^ (-x - 1) * (b - a) ≤ x * a ^ (-x - 1) * (b - a) := by
    gcongr
  have hfinal : x * a ^ (-x - 1) * (b - a) = x * (b - a) / a ^ (x + 1) := by
    have haneg : a ^ (-x - 1) = (a ^ (x + 1))⁻¹ := by
      rw [show -x - 1 = -(x + 1) by ring]
      rw [Real.rpow_neg (le_of_lt ha)]
    rw [haneg]
    ring
  rw [hfinal] at hle
  exact hle

-- ==================== 3. 配对级数收敛 ====================

/-- 配对级数收敛: 0 < x < 1 ⟹ ∑(1/(2n+1)^x - 1/(2n+2)^x) 收敛
    (差分上界 + p 级数 x+1 > 1: summable_nat_rpow)。 
English: The paired series converges: 0 < x < 1 ⟹ the paired series converges -/
theorem pairing_summable (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ x - 1 / ((2 * n + 2 : ℕ) : ℝ) ^ x) := by
  -- 上界: 项 ≤ x·1/(2n+1)^{x+1} ≤ x·2^{-(x+1)}·n^{-(x+1)} (n ≥ 1),
  -- ∑ n^{-(x+1)} 收敛 (summable_nat_rpow, -(x+1) < -1 ⟺ 0 < x)
  have hmain : Summable (fun n : ℕ => (n : ℝ) ^ (-(x + 1) : ℝ)) :=
    (Real.summable_nat_rpow).mpr (by linarith)
  have hb : Summable (fun n : ℕ => x * 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1) : ℝ)) := by
    simpa [mul_assoc] using hmain.mul_left (x * 2 ^ (-(x + 1)))
  -- 比较判别 (eventually, n ≥ 1): |项| ≤ x·2^{-(x+1)}·n^{-(x+1)}
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => x * 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1) : ℝ)) hb ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn0
  have hpos := pairing_term_pos x hx0 n
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  -- 项 ≤ x·1/(2n+1)^{x+1}: pairing_diff_bound (b-a = 1)
  have hdiff := pairing_diff_bound x ((2 * n + 1 : ℕ) : ℝ) ((2 * n + 2 : ℕ) : ℝ) hx0
    (by positivity) (by exact_mod_cast (by omega : (2 * n + 1 : ℕ) < 2 * n + 2))
  have hle0 : 1 / ((2 * n + 1 : ℕ) : ℝ) ^ x - 1 / ((2 * n + 2 : ℕ) : ℝ) ^ x
      ≤ x * 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) := by
    have hba : (((2 * n + 2 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ)) = 1 := by norm_num
    have hright_eq : x * (((2 * n + 2 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ)) / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1)
        = x * 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) := by
      rw [hba]
    rw [← hright_eq]
    exact hdiff
  -- x·1/(2n+1)^{x+1} ≤ x·2^{-(x+1)}·n^{-(x+1)}: (2n+1) ≥ 2n ⟹ 倒数 ≤
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hge : (2 * n : ℕ) ≤ 2 * n + 1 := by omega
  have hx1 : 0 < x + 1 := by linarith
  have hpow_le : ((2 * n : ℕ) : ℝ) ^ (x + 1) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hge) (le_of_lt hx1)
  have hpos_a : 0 < ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) := by positivity
  have hpos_b : 0 < ((2 * n : ℕ) : ℝ) ^ (x + 1) := by positivity
  have hrev : 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) ≤ 1 / ((2 * n : ℕ) : ℝ) ^ (x + 1) := by
    exact one_div_le_one_div_of_le hpos_b hpow_le
  -- 1/(2n)^{x+1} = 2^{-(x+1)}·n^{-(x+1)} (rpow_mul: (2n)^p = 2^p·n^p)
  have hpow_mul : ((2 * n : ℕ) : ℝ) ^ (x + 1) = 2 ^ (x + 1) * (n : ℝ) ^ (x + 1) := by
    -- (2·n)^p = 2^p·n^p: Real.mul_rpow (2 ≥ 0) (n ≥ 0)
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    rw [show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by norm_num]
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn_nonneg
  have hneg2 : 1 / ((2 * n : ℕ) : ℝ) ^ (x + 1) = 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1)) := by
    calc
      1 / ((2 * n : ℕ) : ℝ) ^ (x + 1) = ((2 * n : ℕ) : ℝ) ^ (-(x + 1)) := by
        rw [one_div]
        exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ)) (x + 1)).symm
      _ = 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1)) := by
        rw [show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by norm_num]
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by exact_mod_cast (Nat.zero_le n))]
  -- 拼装: 项 ≤ x·1/(2n+1)^{x+1} ≤ x·2^{-(x+1)}·n^{-(x+1)}
  calc
    1 / ((2 * n + 1 : ℕ) : ℝ) ^ x - 1 / ((2 * n + 2 : ℕ) : ℝ) ^ x
        ≤ x * 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) := hle0
    _ ≤ x * (2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1))) := by
      -- 1/(2n+1)^{x+1} ≤ 2^{-(x+1)}·n^{-(x+1)}; x > 0
      have hstep : 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1)
          ≤ 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1)) := by
        calc
          1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) ≤ 1 / ((2 * n : ℕ) : ℝ) ^ (x + 1) := hrev
          _ = 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1)) := hneg2
      -- x·(1/(2n+1)^{x+1}) ≤ x·(2^{-(x+1)}·n^{-(x+1)})
      -- 左边 x·1/(...) 和 x·(...) 一致 (mul 结合)
      calc
        x * 1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1) = x * (1 / ((2 * n + 1 : ℕ) : ℝ) ^ (x + 1)) := by ring
        _ ≤ x * (2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1))) := by
          exact mul_le_mul_of_nonneg_left hstep (le_of_lt hx0)
    _ = x * 2 ^ (-(x + 1)) * (n : ℝ) ^ (-(x + 1)) := by ring

-- ==================== 4. ζ 在 (0,1) 连续 (mathlib 锚定) ====================

/-- ζ 在 (0,1) 连续: mathlib differentiableOn_riemannZeta 的直接推论
    (ζ 在 {1}ᶜ 可微 ⟹ 连续; 论文的经典奇偶配对论证见 1-3)。 
English: Continuity of ζ on (0,1): a direct consequence of mathlib's differentiableOn_riemannZeta -/
theorem zeta_continuous_zero_one :
    ContinuousOn (fun x : ℝ => riemannZeta (x : ℂ)) (Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn riemannZeta {1}ᶜ := differentiableOn_riemannZeta.continuousOn
  have hsub : Ioo (0 : ℝ) 1 ⊆ (fun x : ℝ => (x : ℂ)) ⁻¹' {1}ᶜ := by
    intro x hx
    simp
    exact ne_of_lt hx.2
  have hcont : ContinuousOn (fun x : ℝ => riemannZeta (x : ℂ)) (Ioo (0 : ℝ) 1) := by
    -- ζ∘coe 连续: ζ 在 {1}ᶜ 连续 + coe 连续 + (0,1) ⊆ coe⁻¹'{1}ᶜ
    have hcoef : ContinuousOn (fun x : ℝ => (x : ℂ)) (Ioo (0 : ℝ) 1) := by
      -- coe 全局连续, 限制到 (0,1)
      have hglobal : ContinuousOn (fun x : ℝ => (x : ℂ)) Set.univ :=
        Complex.continuous_ofReal.continuousOn
      exact hglobal.mono (by intro x hx; trivial)
    exact hc.comp hcoef hsub
  exact hcont

end

end OddEvenPairing
