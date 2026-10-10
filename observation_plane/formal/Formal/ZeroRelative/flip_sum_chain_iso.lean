import Mathlib

/-! # Flip-sum chain (L12 counting chain, restored from proof_v3)

0pat: 层求和链 — 拼接恒等式 / 层差守恒 / 提升-对数桥 / π 跳 — 每奇重零点一层的计数骨架。

English: flip-sum chain -- telescoping identity, layer-sum conservation, lift-log bridge, and the pi-jump per odd-order zero

-/

open scoped BigOperators

namespace FlipSumChain


/-- **覆盖提升的层跳**: exp θ₁ = u₁, exp θ₂ = u₂, u₁/u₂ = −1 ⟹
    θ₂ − θ₁ = iπ + 2πi·n (跳一 π 层, 模整数圈)。

English: Covering-lift layer jump: exp θ₁ = u₁, exp θ₂ = u₂, u₁/u₂ = −1 ⟹ θ₂ − θ₁ = iπ + 2πi·n (a π-layer jump, modulo integer turns). -/

theorem lift_diff_pi_layer {θ₁ θ₂ u₁ u₂ : ℂ}
    (h1 : Complex.exp θ₁ = u₁) (h2 : Complex.exp θ₂ = u₂)
    (h : u₁ / u₂ = -1) :
    ∃ n : ℤ, θ₂ - θ₁ = (n : ℂ) * (2 * ↑Real.pi * Complex.I) + Complex.I * Real.pi := by
  have hu1 : u₁ ≠ 0 := by
    intro hz
    have : u₁ / u₂ = 0 := by rw [hz]; exact zero_div u₂
    rw [h] at this
    norm_num at this
  have hu2 : u₂ ≠ 0 := by
    intro hz
    have : u₁ / u₂ = 0 := by rw [hz]; exact div_zero u₁
    rw [h] at this
    norm_num at this
  -- 用 h ⟹ u₁ = −u₂, 然后 exp 值相等
  have hneg : u₁ = -u₂ := by
    simpa using (div_eq_iff hu2).1 h
  have hexp : Complex.exp (θ₂ - θ₁) = -1 := by
    rw [Complex.exp_sub]
    rw [h2, h1]
    rw [hneg]
    rw [div_neg]
    rw [div_self hu2]
  have hexp' : Complex.exp (θ₂ - θ₁) = Complex.exp (↑Real.pi * Complex.I) := by
    rw [Complex.exp_pi_mul_I]
    exact hexp
  rcases (Complex.exp_eq_exp_iff_exists_int).1 hexp' with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn]
  ring


/-- **拼接恒等式 (telescoping)**: 全局端点差 = Σ 相邻差 —
    零点的有限分割拼接的代数骨架 (每个"相邻差" = 段差 + 跨零点跳)。

English: Telescoping identity: global endpoint difference = sum of adjacent differences -- the algebraic skeleton of the finite partition of zeros. -/
theorem telescoping_sum {N : ℕ} (a : ℕ → ℂ) :
    a N - a 0 = ∑ i ∈ Finset.range N, (a (i + 1) - a i) := by
  symm
  exact Finset.sum_range_sub a N


/-- **层差求和 (主定理保险丝)**: 若每条相邻差 = 2πi 的整数倍 —
    (① 段差 = 0 对齐 + ② 跨 m 奇零点层跳 2πi·n),
    则全局端点差 = 2πi·(整数) — 求和定理, 层差守恒。

English: Layer-sum conservation: if every adjacent difference is an integer multiple of 2πi, then the global difference is 2πi times an integer -- the fuse of the counting theorem. -/
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


/-- **提升-对数桥**: exp θ₁ = u₁, exp θ₂ = u₂ ⟹
    θ₂ − θ₁ = (log u₂ − log u₁) + 2πi·n — 任何连续提升差 =
    log 主支差 + 整数圈 (层值 ↔ 主支值的桥, 组装①常数性与②跳层的连接件)。

English: Lift-log bridge: exp θ₁ = u₁, exp θ₂ = u₂ ⟹ θ₂ − θ₁ = (log u₂ − log u₁) + 2πi·n -- connects layer values with principal-branch values. -/
theorem lift_diff_log_bridge {θ₁ θ₂ u₁ u₂ : ℂ}
    (h1 : Complex.exp θ₁ = u₁) (h2 : Complex.exp θ₂ = u₂) :
    ∃ n : ℤ, θ₂ - θ₁ = (Complex.log u₂ - Complex.log u₁) +
      (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  have hu1 : u₁ ≠ 0 := by rw [← h1]; exact Complex.exp_ne_zero θ₁
  have hu2 : u₂ ≠ 0 := by rw [← h2]; exact Complex.exp_ne_zero θ₂
  have hexp1 : Complex.exp (θ₂ - θ₁) = u₂ / u₁ := by
    rw [Complex.exp_sub, h2, h1]
  have hexp2 : Complex.exp (Complex.log u₂ - Complex.log u₁) = u₂ / u₁ := by
    rw [Complex.exp_sub, Complex.exp_log hu2, Complex.exp_log hu1]
  have hnz : u₂ / u₁ ≠ 0 := div_ne_zero hu2 hu1
  have hexp : Complex.exp (θ₂ - θ₁ - (Complex.log u₂ - Complex.log u₁)) = 1 := by
    rw [Complex.exp_sub, hexp1, hexp2]
    exact div_self hnz
  have hexp' : Complex.exp (θ₂ - θ₁ - (Complex.log u₂ - Complex.log u₁)) =
      Complex.exp 0 := by
    rw [Complex.exp_zero]
    exact hexp
  rcases (Complex.exp_eq_exp_iff_exists_int).1 hexp' with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hmain : θ₂ - θ₁ - (Complex.log u₂ - Complex.log u₁) =
      (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [hn]
    simp
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp hmain)


/-- **2θ-层跳 (m 奇, 对称相位操作)**: u₁/u₂ = −1 (e^{iπ} 对称) ⟹
    2θ₂ − 2θ₁ = 2πi + 4πi·n — 每跨一个 m 奇零点, 2θ_ζ 跳 2πi 的
    奇数层 (log 主支跳跃被整数圈吸收 — "不连续就跳过去")。
    主定理的逐零点点项: 每奇重零点贡献一个 2πi 层。

English: 2θ-layer jump (m odd, symmetric phase op): u₁/u₂ = −1 (e^{iπ} symmetry) ⟹ 2θ₂ − 2θ₁ = 2πi + 4πi·n -- each crossing of an odd-multiplicity zero jumps the 2θ_ζ phase by an odd 2πi layer (the principal-branch jump is absorbed by integer turns). -/

theorem two_theta_zero_jump {θ₁ θ₂ u₁ u₂ : ℂ}
    (h1 : Complex.exp θ₁ = u₁) (h2 : Complex.exp θ₂ = u₂)
    (hdiv : u₁ / u₂ = -1) :
    ∃ n : ℤ,
      2 * θ₂ - 2 * θ₁ =
        (n : ℂ) * (4 * ↑Real.pi * Complex.I) + 2 * (Complex.I * Real.pi) := by
  rcases lift_diff_pi_layer h1 h2 hdiv with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [show 2 * θ₂ - 2 * θ₁ = 2 * (θ₂ - θ₁) by ring]
  rw [hn]
  ring


  -- ============================================================
  -- T6q 零点升序枚举 (2026-08-25, 目标 N₀ 显式化块③):
  -- 带内有限 (T6a) ⟹ 临界线 [0,T] 上零点 t 集有限 ⟹ 升序列表
  -- (Finset.sort): 包含全部零点且只含零点。Pairwise ≤ + Nodup
  -- ⟹ 相邻严格递增 (下游 lt_of_le_of_ne), 分割骨架。
  -- ============================================================


end FlipSumChain
