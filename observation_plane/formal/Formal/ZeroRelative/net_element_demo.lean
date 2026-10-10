import Mathlib

/-! # Net-element one-step practice (净元一步达点演示, 自包含)

0pat: 演示净元组装 "一步达点" — 局部输入 (每条相邻差 = 2πi 整数倍) 经
净元 layer_sum_formula 一步得到全局输出 (总差 = 2πi 整数倍), 无中间搜索。
净元表条目 (layer_sum_formula) 内嵌于此 (生产区同源定理见
flip_sum_chain_iso.lean)。模拟四段: 0 → 2πi (奇零点跳) → 2πi (对齐)
→ 2πi (对齐) ⟹ 总差 = 2πi·1。

English: net-element one-step practice (self-contained) -- the local inputs
(every adjacent difference is an integer multiple of 2πi) pass through the
net element layer_sum_formula and return, in one step, the global output
(the total difference is an integer multiple of 2πi), with no intermediate
search. The net-element table entry is embedded here (the production
theorem is in flip_sum_chain_iso.lean). Simulated segments: 0 → 2πi (odd
zero jump) → 2πi (aligned) → 2πi (aligned) ⟹ total = 2πi. -/

open scoped BigOperators

namespace NetElementDemo

/-! ## 净元表条目 (net-element table entry): layer_sum_formula -/

/-- 拼接恒等式 (telescoping): 全局端点差 = Σ 相邻差。
    English: telescoping identity: global endpoint difference = sum of adjacent differences. -/
theorem telescoping_sum {N : ℕ} (a : ℕ → ℂ) :
    a N - a 0 = ∑ i ∈ Finset.range N, (a (i + 1) - a i) := by
  symm
  exact Finset.sum_range_sub a N

/-- 层差守恒 (净元): 若每条相邻差 = 2πi 整数倍 ⟹ 全局端点差 = 2πi 整数倍。
    English: layer-sum conservation (net element): every adjacent difference
    an integer multiple of 2πi ⟹ the global endpoint difference is an integer
    multiple of 2πi. -/
theorem layer_sum_formula {N : ℕ} (f : ℕ → ℂ)
    (hjump : ∀ i : ℕ, i < N → ∃ nᵢ : ℤ,
      f (i + 1) - f i = (nᵢ : ℂ) * (2 * ↑Real.pi * Complex.I)) :
    ∃ n : ℤ,
      f N - f 0 = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  classical
  let k : ℕ → ℤ := fun i => if hi : i < N then Classical.choose (hjump i hi) else 0
  refine ⟨∑ i ∈ Finset.range N, k i, ?_⟩
  rw [telescoping_sum f]
  calc
    ∑ i ∈ Finset.range N, (f (i + 1) - f i)
        = ∑ i ∈ Finset.range N, ((k i : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiN : i < N := Finset.mem_range.mp hi
          have hji := Classical.choose_spec (hjump i hiN)
          simpa [k, hiN] using hji
    _ = (∑ i ∈ Finset.range N, (k i : ℂ)) * (2 * ↑Real.pi * Complex.I) := by
          rw [Finset.sum_mul]
    _ = ((∑ i ∈ Finset.range N, k i : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
          rw [Int.cast_sum]

/-! ## 一步达点: 局部输入 → 净元 → 全局输出 -/

/-- 一步达点: layer_sum_formula 把局部输入 (每段差 = 1·2πi)
    一步降为全局输出: 总差 = 2πi·3。
    English: one-step arrival: the net element reduces the local inputs
    (every segment difference = 1·2πi) to the global output in one step:
    total difference = 2πi·3. -/
theorem one_step_global :
    ∃ n : ℤ,
      (3 : ℂ) * (2 * ↑Real.pi * Complex.I) - (0 : ℂ)
        = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  let f : ℕ → ℂ := fun i => (i : ℂ) * (2 * ↑Real.pi * Complex.I)
  have hjump : ∀ i : ℕ, i < 3 → ∃ nᵢ : ℤ,
      f (i + 1) - f i = (nᵢ : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    intro i hi
    refine ⟨1, ?_⟩
    simp [f]
    ring
  -- 净元一步: layer_sum_formula (N = 3)
  rcases layer_sum_formula (N := 3) f hjump with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [f] using hn

end NetElementDemo
