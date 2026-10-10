import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# FlipZeroPair — 翻转-零点配对 (断点 B 组装: 符号变化 ⟹ 奇阶, 2026-08-26)

**落点**: 组装链断点 B (翻转数 = 线上奇阶零点数) 的核心新件 —
实值函数在零点两侧异号 ⟹ 该零点奇重 (符号变化穿过 ⟹ 奇数重根)。
数学: f 局部 = (t-t₀)^m·h (h 连续非零 ⟹ 局部恒号); 左侧
(t-t₀)^m = (-1)^m·(t₀-t)^m (符号 = (-1)^m); 异号 ⟹ (-1)^m = -1 ⟹ m 奇。

**与已有件的关系**: flip_iff_odd (zeta_zero_order_iso: u 翻转 ⟺ m 奇,
i^m 方向) 是复相位侧; 本文件是实值符号侧 (Z 实值 ⟹ 翻转 = 符号变化
⟹ 奇阶)。两者合起来: 翻转 ⟺ 奇阶线上零点 (Hardy Z 双向)。

隔离文件 (mathlib-only)。 
English: Flip-zero pairing: sign change of a real-valued function at a zero forces odd order (the real-side counterpart of flip_iff_odd; together: flip ⟺ odd-order on-line zero) -/

noncomputable section

open Filter
open scoped Topology

namespace RiemannUnifiedObservation

/-- **符号变化 ⟹ 奇重根**: 实值 f 在 t₀ 展开 (t-t₀)^m·h (h 连续非零),
    f 在 t₀ 左侧负、右侧正 (异号) ⟹ m 奇。
    证明: h 局部恒号 (连续非零) ⟹ 右侧 (t-t₀)^m 取 h 符号;
    左侧 (t-t₀)^m = (-1)^m·(t₀-t)^m 取 (-1)^m·h 符号; 异号 ⟹
    (-1)^m = -1 ⟹ m 奇 (与 flip_ratio_iff_odd 同代数)。 
English: Sign change forces odd order: real f = (t−t₀)^m·h locally (h continuous nonzero), f negative left / positive right of t₀ ⟹ m odd -/
theorem sign_change_odd_order {f h : ℝ → ℝ} {t₀ : ℝ} (m : ℕ)
    (h_exp : ∀ᶠ t in 𝓝 t₀, f t = (t - t₀) ^ m * h t)
    (h_cont : ContinuousAt h t₀) (h0 : h t₀ ≠ 0)
    (h_left : ∀ᶠ t in 𝓝[<] t₀, f t < 0) (h_right : ∀ᶠ t in 𝓝[>] t₀, 0 < f t) :
    Odd m := by
  -- h 局部恒号: 分 h t₀ > 0 / h t₀ < 0
  by_cases hpos : 0 < h t₀
  · -- h > 0 于邻域 (连续 + 正 ⟹ 局部正)
    have hsig : ∀ᶠ t in 𝓝 t₀, 0 < h t := h_cont.eventually (isOpen_Ioi.mem_nhds hpos)
    -- 右侧取点 t₁: t₀ < t₁, 展开成立, f > 0, h > 0
    have hpick : ∃ t₁, t₀ < t₁ ∧ (f t₁ = (t₁ - t₀) ^ m * h t₁) ∧ 0 < f t₁ ∧ 0 < h t₁ := by
      have hE : ∀ᶠ t in 𝓝[>] t₀,
          t₀ < t ∧ (f t = (t - t₀) ^ m * h t) ∧ 0 < f t ∧ 0 < h t := by
        filter_upwards [self_mem_nhdsWithin, h_exp.filter_mono nhdsWithin_le_nhds, h_right,
          hsig.filter_mono nhdsWithin_le_nhds] with t ht0 ht1 ht2 ht3
        exact ⟨ht0, ht1, ht2, ht3⟩
      exact hE.exists
    rcases hpick with ⟨t₁, ht₁, hf₁, hfpos₁, hhpos₁⟩
    -- 右侧: f = (t₁-t₀)^m·h > 0 且 h > 0 ⟹ (t₁-t₀)^m > 0 (平凡, 自动)
    -- 左侧取点 t₂: t₂ < t₀, 展开成立, f < 0, h > 0
    have hpick2 : ∃ t₂, t₂ < t₀ ∧ (f t₂ = (t₂ - t₀) ^ m * h t₂) ∧ f t₂ < 0 ∧ 0 < h t₂ := by
      have hE : ∀ᶠ t in 𝓝[<] t₀,
          t < t₀ ∧ (f t = (t - t₀) ^ m * h t) ∧ f t < 0 ∧ 0 < h t := by
        filter_upwards [self_mem_nhdsWithin, h_exp.filter_mono nhdsWithin_le_nhds, h_left,
          hsig.filter_mono nhdsWithin_le_nhds] with t ht0 ht1 ht2 ht3
        exact ⟨ht0, ht1, ht2, ht3⟩
      exact hE.exists
    rcases hpick2 with ⟨t₂, ht₂, hf₂, hfneg₂, hhpos₂⟩
    -- 左侧: f = (-1)^m·(t₀-t₂)^m·h < 0; (t₀-t₂)^m > 0, h > 0 ⟹ (-1)^m < 0
    have hnegpow : (-1 : ℝ) ^ m < 0 := by
      have hsub : (t₂ - t₀) ^ m = (-1 : ℝ) ^ m * (t₀ - t₂) ^ m := by
        have hrel : (t₂ - t₀) = -((t₀ - t₂) : ℝ) := by ring
        rw [hrel, neg_pow]
      have hf₂' : (-1 : ℝ) ^ m * (t₀ - t₂) ^ m * h t₂ < 0 := by
        rw [hsub] at hf₂
        rwa [hf₂] at hfneg₂
      -- (t₀-t₂)^m > 0 (t₀ > t₂) 且 h > 0 ⟹ (-1)^m < 0
      have hpospow : 0 < (t₀ - t₂) ^ m := pow_pos (sub_pos.mpr ht₂) m
      have hprod : 0 < (t₀ - t₂) ^ m * h t₂ := mul_pos hpospow hhpos₂
      -- ((-1)^m · X) < 0, X > 0 ⟹ (-1)^m < 0
      have hmulneg : (-1 : ℝ) ^ m * ((t₀ - t₂) ^ m * h t₂) < 0 := by
        rw [← mul_assoc]
        exact hf₂'
      -- (-1)^m·Y < 0 且 Y > 0 ⟹ (-1)^m < 0
      have hY : 0 < (t₀ - t₂) ^ m * h t₂ := hprod
      nlinarith
    have hne_one : (-1 : ℝ) ^ m = -1 := by
      -- (-1)^m < 0 ⟹ (-1)^m = -1 (实值: (-1)^m ∈ {±1})
      have hsq : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
        rw [← pow_mul]
        rw [mul_comm]
        -- (-1)^(2·m) = ((-1)^2)^m = 1
        have hpow2 : (-1 : ℝ) ^ (2 * m) = 1 := by
          calc
            (-1 : ℝ) ^ (2 * m) = ((-1 : ℝ) ^ 2) ^ m := pow_mul (-1 : ℝ) 2 m
            _ = 1 := by norm_num
        exact hpow2
      have hcases : (-1 : ℝ) ^ m = 1 ∨ (-1 : ℝ) ^ m = -1 := by
        exact sq_eq_one_iff.mp hsq
      rcases hcases with h1 | hneg
      · -- = 1 与 < 0 矛盾
        exfalso
        rw [h1] at hnegpow
        exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1)) hnegpow
      · exact hneg
    -- (-1)^m = -1 ⟹ m 奇 (与 flip_ratio_iff_odd 同代数)
    have hodd : (-1 : ℝ) ^ m = -1 → Odd m := by
      intro h
      by_contra hm
      have heven : Even m := Nat.not_odd_iff_even.mp hm
      rcases heven with ⟨k, hk⟩
      subst m
      have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by
        rw [pow_mul]
        norm_num
      have : (1 : ℝ) = -1 := by simpa [hpow] using h
      norm_num at this
    exact hodd hne_one
  · -- h t₀ < 0 (非正 ⟹ 负): 对称论证 (h 局部负, 两侧 f 符号反转)
    have hneg0 : h t₀ < 0 := lt_of_not_ge (by
      intro hge
      exact hpos (lt_of_le_of_ne hge (Ne.symm h0)))
    have hsig : ∀ᶠ t in 𝓝 t₀, h t < 0 := h_cont.eventually (isOpen_Iio.mem_nhds hneg0)
    -- 右侧: f > 0, h < 0 ⟹ (t₁-t₀)^m < 0 (矛盾! (t₁-t₀)^m > 0)
    -- ⟹ 右侧情形不可能 ⟹ 反证: 若 h t₀ < 0 且右侧 f > 0 ⟹ (t₁-t₀)^m·h > 0, h < 0 ⟹ (t₁-t₀)^m < 0 — 与 pow_pos 矛盾
    exfalso
    have hpick : ∃ t₁, t₀ < t₁ ∧ (f t₁ = (t₁ - t₀) ^ m * h t₁) ∧ 0 < f t₁ ∧ h t₁ < 0 := by
      have hE : ∀ᶠ t in 𝓝[>] t₀,
          t₀ < t ∧ (f t = (t - t₀) ^ m * h t) ∧ 0 < f t ∧ h t < 0 := by
        filter_upwards [self_mem_nhdsWithin, h_exp.filter_mono nhdsWithin_le_nhds, h_right,
          hsig.filter_mono nhdsWithin_le_nhds] with t ht0 ht1 ht2 ht3
        exact ⟨ht0, ht1, ht2, ht3⟩
      exact hE.exists
    rcases hpick with ⟨t₁, ht₁, hf₁, hfpos₁, hhneg₁⟩
    -- f = (t₁-t₀)^m·h > 0, h < 0 ⟹ (t₁-t₀)^m < 0 — 但 pow_pos 给 > 0
    have hpp : 0 < (t₁ - t₀) ^ m := pow_pos (sub_pos.mpr ht₁) m
    have hpm : (t₁ - t₀) ^ m < 0 := by
      -- f > 0, f = (t₁-t₀)^m·h ⟹ 乘积 > 0; h < 0 ⟹ (t₁-t₀)^m < 0
      have hprodpos : 0 < (t₁ - t₀) ^ m * h t₁ := by
        rwa [← hf₁]
      -- 反证: X ≥ 0 且 Y < 0 ⟹ X·Y ≤ 0 — 与 > 0 矛盾
      by_contra hge
      have hX : 0 ≤ (t₁ - t₀) ^ m := le_of_not_gt hge
      have hprod : (t₁ - t₀) ^ m * h t₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hX (le_of_lt hhneg₁)
      exact (not_lt_of_ge hprod) hprodpos
    exact (not_lt_of_ge (le_of_lt hpp)) hpm

end RiemannUnifiedObservation
