import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# T6f: 残差预测方法 0pat 化 — 误差测量序列 (RulerErrorSeq 的 mathlib-only 版)

pat 残差预测 (内部笔记 §8.2) 已解决残差方法:
- 误差测量序列 e(n) = n^{1-s}/(s-1) (多项式级数截断误差模型)
- 核心比率定理: e(2n)/e(n) = 2^{1-s} (每层比率恒定 ⟹ 测量一次推全部)
- 误差单调递减: n 加倍 ⟹ 误差 ÷ 2^{s-1}
- 提前量反解: 要精度 ε ⟹ n ≥ (C/ε)^{1/(s-1)}

log = e⁻¹ (有限↔无限逆桥): 误差的指数结构来自 e 的幂 (n^{1-s} = e^{(1-s)ln n}),
残差控制 = 幂的比率/反解, 全快路径 (纯代数, 无迭代逼近)。

隔离文件 (mathlib-only)。 
English: predictor residuals: five theorems of the error sequence -/

noncomputable section

namespace RiemannUnifiedObservation

/-- 多项式级数 ∑ k^{-s} (k > n) 的截断误差模型: e(n) = n^{1-s}/(s-1)。
    来源: ∫_n^∞ x^{-s} dx = n^{1-s}/(s-1) (积分判别, s > 1)。 
English: Truncation-error model of the polynomial series ∑ k^{-s} (k > n): e(n) = n^{1-s}/(s-1); source: ∫_n^∞ x^{-s} dx = n^{1-s}/(s-1) (integral test, s > 1). -/
def polyError (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - s) / (s - 1)

/-- **核心比率定理**: e(2n)/e(n) = 2^{1-s} — 每层误差比率恒定,
    测量一次 e(n₀) ⟹ 推出所有 e(2^k·n₀)。 
English: Core ratio theorem: e(2n)/e(n) = 2^{1-s} — the error ratio is constant per level; measuring e(n₀) once ⟹ all e(2^k·n₀). -/
theorem poly_error_ratio {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) / polyError s n = (2 : ℝ) ^ (1 - s) := by
  dsimp [polyError]
  have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
    rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
    rw [Real.mul_rpow]
    · norm_num
    · exact_mod_cast (Nat.zero_le n)
  rw [hpow]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  field_simp [hs, hnsq]

/-- 误差序列预测: 测量一次推全部 — e(2n) = e(n)·2^{1-s}。 
English: Error-sequence prediction: one measurement gives all — e(2n) = e(n)·2^{1-s}. -/
theorem error_seq_predicts {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
  have hr := poly_error_ratio hs hn
  dsimp [polyError] at hr ⊢
  -- 从比率定理: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  -- 需要 e(n) ≠ 0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  have hne : polyError s n ≠ 0 := by
    dsimp [polyError]
    exact div_ne_zero hnsq (sub_ne_zero.mpr hs)
  -- hr : e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  have hr' : polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
    -- 从比率: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
    dsimp [polyError] at hr ⊢
    -- 同 poly_error_ratio 的代数
    have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
      rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
      rw [Real.mul_rpow]
      · norm_num
      · exact_mod_cast (Nat.zero_le n)
    rw [hpow] at hr ⊢
    -- hr : (2^{1-s}·n^{1-s}/(s-1)) / (n^{1-s}/(s-1)) = 2^{1-s}
    -- 目标: (2^{1-s}·n^{1-s})/(s-1) = (n^{1-s}/(s-1))·2^{1-s}
    field_simp [hs, hnsq]
  exact hr' 

/-- 误差单调递减: n 加倍 ⟹ 误差按 2^{1-s} 收缩 (s > 1 时 2^{1-s} < 1)。 
English: Error is monotonically decreasing: doubling n ⟹ error shrinks by 2^{1-s} (2^{1-s} < 1 when s > 1). -/
theorem poly_error_monotone {s : ℝ} (hs1 : 1 < s) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) < polyError s n := by
  change ((2 * n : ℕ) : ℝ) ^ (1 - s) / (s - 1) < (n : ℝ) ^ (1 - s) / (s - 1)
  have hr := error_seq_predicts (ne_of_gt hs1) hn
  -- e(2n) = e(n)·2^{1-s}, s > 1 ⟹ 2^{1-s} < 1, e(n) > 0
  have hpos : 0 < polyError s n := by
    dsimp [polyError]
    -- n^{1-s} > 0 (n > 0), s-1 > 0
    exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) (1 - s)) (sub_pos.mpr hs1)
  have hratio : (2 : ℝ) ^ (1 - s) < 1 := by
    -- s > 1 ⟹ 1-s < 0 ⟹ 2^{1-s} < 1 (rpow_lt_one_iff)
    have hneg : 1 - s < 0 := by linarith
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Or.inl ⟨by norm_num, hneg⟩
  calc
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := hr
    _ < polyError s n * 1 := by
      exact mul_lt_mul_of_pos_left hratio hpos
    _ = polyError s n := by ring

/-- 提前量反解: 要精度 ε ⟹ n ≥ (1/ε)^{1/(s-1)} 时 e(n) ≤ ε/(s-1)。
    从 e(n) = n^{1-s}/(s-1) 反解 (s > 1): n^{1-s} ≤ ε ⟺ n ≥ (1/ε)^{1/(s-1)}。 
English: Lead amount solved back: for precision ε, n ≥ (1/ε)^{1/(s-1)} gives e(n) ≤ ε/(s-1); solving back from e(n) = n^{1-s}/(s-1) (s > 1): n^{1-s} ≤ ε ⟺ n ≥ (1/ε)^{1/(s-1)}. -/
theorem error_precision_bound {s : ℝ} (hs1 : 1 < s) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hn : (1 / ε) ^ (1 / (s - 1)) ≤ (n : ℝ)) :
    polyError s n ≤ ε / (s - 1) := by
  dsimp [polyError]
  have hs1' : 0 < s - 1 := sub_pos.mpr hs1
  have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hεinv (1 / (s - 1))) hn
  -- (1/ε)^{1/(s-1)} ≤ n ⟹ 1/ε ≤ n^{s-1} (rpow (s-1) 保序 + 复合)
  have hle : 1 / ε ≤ (n : ℝ) ^ (s - 1) := by
    have h1 : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) ≤ (n : ℝ) ^ (s - 1) :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hεinv (1 / (s - 1)))) hn (le_of_lt hs1')
    have hcomp : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) = 1 / ε := by
      rw [← Real.rpow_mul (le_of_lt hεinv) (1 / (s - 1)) (s - 1)]
      congr 1
      field_simp [hs1', hε]
      simp [pow_one]
      field_simp [hε]
    rwa [hcomp] at h1
  -- 1/ε ≤ n^{s-1} ⟹ n^{1-s} = 1/n^{s-1} ≤ ε (倒数保序)
  have hle2 : (n : ℝ) ^ (1 - s) ≤ ε := by
    have hneg : (n : ℝ) ^ (1 - s) = (n : ℝ) ^ (-(s - 1) : ℝ) := by
      congr 1
      ring
    rw [hneg]
    rw [Real.rpow_neg (le_of_lt hnpos) (s - 1)]
    -- 目标: (n^{s-1})⁻¹ ≤ ε ⟸ hle: 1/ε ≤ n^{s-1}
    have hle' : (n : ℝ) ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
    rw [inv_eq_one_div]
    have hle'' : 1 / (n : ℝ) ^ (s - 1) ≤ 1 / (1 / ε) := by
      exact one_div_le_one_div_of_le hεinv hle
    -- 1/(1/ε) = ε
    have hle3 : 1 / (n : ℝ) ^ (s - 1) ≤ ε := by
      simpa using hle''
    exact hle3
  -- n^{1-s} ≤ ε ⟹ n^{1-s}/(s-1) ≤ ε/(s-1)
  exact div_le_div_of_nonneg_right hle2 (le_of_lt hs1')

end RiemannUnifiedObservation
