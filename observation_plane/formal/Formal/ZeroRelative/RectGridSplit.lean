import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# 矩形网格分割可加性 (断点 A 分析侧最后一块基础设施, 2026-08-26)

多孔 hΓ: 大矩形 [z.re,w.re]×[z.im,w.im] 内挖掉 K 个零点周围小洞。
矩形网格分割: 网格 {x_i}_{i≤M}×{y_j}_{j≤N} 分大矩形为 M·N 个小矩形,
每个小矩形边界积分 = rectBoundary (mathlib `integral_boundary_rect` 的
左侧形式, 逆时针 4 段: 底 − 顶 + I·右 − I·左)。

**主定理** `rect_boundary_grid_split`: Σ 小矩形边界积分 = 大矩形边界积分
(连续 f) — 公共边正反对消 (代数侧已机证: segment_pair_cancel /
segment_sum_cancel / contour_decomposition_cancel, ExclusionNetElements.lean)
的分析侧对应: 水平公共边对消 (对固定 j 合并 Σ_i 后, Σ_j 望远镜 → 只剩
y₀ 与 y_N 两段) + 垂直公共边对消 (对固定 i 合并 Σ_j 后, Σ_i 望远镜 →
只剩 x₀ 与 x_M 两段) ⟹ 只剩大矩形外边界 4 段 (逆时针)。

1D 相邻区间合并用 `intervalIntegral.sum_integral_adjacent_intervals`
(连续 ⟹ IntervalIntegrable 自动); 望远镜用 sum_range_sub_telescope /
sum_range_shift。

English: Rectangle grid split additivity — the analytic-side infrastructure
for the multi-hole contour: summing boundary integrals over a rectangular
grid collapses to the outer boundary integral (shared edges cancel in pairs).
-/

noncomputable section

open Complex Filter
open scoped Topology Interval BigOperators

namespace ZeroRelative

/-- 矩形边界积分 (逆时针 4 段): 底 − 顶 + I·右 − I·左 —
    mathlib `integral_boundary_rect` 的左侧形式 (z = 左下角, w = 右上角).
    Rectangle boundary integral: bottom − top + I·right − I·left. -/
noncomputable def rectBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
    Complex.I • (∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I • (∫ y in z.im..w.im, f (z.re + y * Complex.I))

/-! ## 1. 求和代数引理 (望远镜 / 重标) -/

/-- **望远镜**: Σ_{i<n} (a_{i+1} − a_i) = a_n − a_0.
    Telescoping: the sum of successive differences collapses to the endpoints. -/
theorem sum_range_sub_telescope (a : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a (i + 1) - a i)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- **重标平移**: Σ_{j<n} a_{j+1} = (Σ_{j≤n} a_j) − a_0 —
    把下标 j+1 的求和换成 j = 1..n 再补首项. -/
theorem sum_range_shift (a : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, a (j + 1)) = (∑ j ∈ Finset.range (n + 1), a j) - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ j ∈ Finset.range (n + 1), a (j + 1))
            = (∑ j ∈ Finset.range n, a (j + 1)) + a (n + 1) := by
              exact Finset.sum_range_succ (f := fun j => a (j + 1)) n
        _ = ((∑ j ∈ Finset.range (n + 1), a j) - a 0) + a (n + 1) := by
              rw [ih]
        _ = (∑ j ∈ Finset.range (n + 2), a j) - a 0 := by
              have hsucc : (∑ j ∈ Finset.range (n + 2), a j)
                  = (∑ j ∈ Finset.range (n + 1), a j) + a (n + 1) := by
                exact Finset.sum_range_succ (f := a) (n + 1)
              rw [hsucc]
              abel

/-! ## 2. 1D 相邻区间合并 (连续 ⟹ 可积自动) -/

/-- **相邻区间合并**: Σ_{k<n} ∫_{a_k}^{a_{k+1}} g = ∫_{a_0}^{a_n} g (连续 g).
    Adjacent-interval merge: the sum over a partition equals the whole. -/
theorem sum_integral_adjacent (g : ℝ → ℂ) (hg : Continuous g) (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), g x) = ∫ x in a 0..a n, g x := by
  exact intervalIntegral.sum_integral_adjacent_intervals (f := g) (a := a) (n := n) (by
    intro k hk
    exact hg.intervalIntegrable (a k) (a (k + 1)))

/-- t ↦ f (t + c·I) 连续 (平移复合). -/
theorem continuous_translate_complex {f : ℂ → ℂ} (hf : Continuous f) (c : ℝ) :
    Continuous (fun t : ℝ => f (t + c * Complex.I)) :=
  hf.comp (continuous_ofReal.add continuous_const)

/-- t ↦ f (c + t·I) 连续 (垂直复合). -/
theorem continuous_vertical_complex {f : ℂ → ℂ} (hf : Continuous f) (c : ℝ) :
    Continuous (fun t : ℝ => f (c + t * Complex.I)) :=
  hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const))

/-! ## 3. 水平/垂直边合并 (对固定 y / 固定 x) -/

/-- **水平边合并**: 对固定虚部 y, Σ_i 底边 (∫_{x_i}^{x_{i+1}} f(t+y·I)) =
    整段 ∫_{x_0}^{x_M} f(t+y·I). -/
theorem sum_bottom_edges (f : ℂ → ℂ) (hf : Continuous f) (x : ℕ → ℝ) (y : ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range M, ∫ t in x i..x (i + 1), f (t + y * Complex.I)) =
      ∫ t in x 0..x M, f (t + y * Complex.I) := by
  exact sum_integral_adjacent (fun t : ℝ => f (t + y * Complex.I))
    (continuous_translate_complex hf y) x M

/-- **垂直边合并**: 对固定实部 x, Σ_j 左边 (∫_{y_j}^{y_{j+1}} f(x+t·I)) =
    整段 ∫_{y_0}^{y_N} f(x+t·I). -/
theorem sum_left_edges (f : ℂ → ℂ) (hf : Continuous f) (x : ℝ) (y : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∫ t in y j..y (j + 1), f (x + t * Complex.I)) =
      ∫ t in y 0..y N, f (x + t * Complex.I) := by
  exact sum_integral_adjacent (fun t : ℝ => f (x + t * Complex.I))
    (continuous_vertical_complex hf x) y N

/-! ## 4. 主定理: 网格分割可加性 -/

/-- **★矩形网格分割可加性**: 网格 {x_i}_{i≤M}×{y_j}_{j≤N} 分割大矩形
    [x₀,x_M]×[y₀,y_N], 小矩形边界积分之和 = 大矩形边界积分 (连续 f)。
    水平公共边对消 (Σ_j 望远镜 → y₀,y_N 两段) + 垂直公共边对消
    (Σ_i 望远镜 → x₀,x_M 两段) ⟹ 只剩外边界 4 段。
    多孔 hΓ 的分割件: 挖洞时每个小矩形内部最多一个零点, 无零小矩形
    Goursat = 0, 有零小矩形贡献 m·2π (逐孔), 总 = Σ m_k·2π。
    ★Rectangle grid split: sum of small boundary integrals = big boundary
    integral — shared edges cancel in pairs (telescoping in both axes). -/
theorem rect_boundary_grid_split (f : ℂ → ℂ) (hf : Continuous f)
    (x y : ℕ → ℝ) (M N : ℕ) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        rectBoundary f (x i + y j * Complex.I) (x (i + 1) + y (j + 1) * Complex.I)) =
      rectBoundary f (x 0 + y 0 * Complex.I) (x M + y N * Complex.I) := by
  let A : ℕ → ℂ := fun j => ∫ t in x 0..x M, f (t + y j * Complex.I)
  let C : ℕ → ℂ := fun i => ∫ t in y 0..y N, f (x i + t * Complex.I)
  -- 底边组 (固定 j, 对 i 合并)
  have hbottom : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        ∫ t in x i..x (i + 1), f (t + y j * Complex.I)) = ∑ j ∈ Finset.range N, A j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact sum_bottom_edges f hf x (y j) M
  -- 顶边组 (y_{j+1})
  have htop : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        ∫ t in x i..x (i + 1), f (t + y (j + 1) * Complex.I)) =
        ∑ j ∈ Finset.range N, A (j + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact sum_bottom_edges f hf x (y (j + 1)) M
  -- 右边组 (x_{i+1})
  have hright : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        ∫ t in y j..y (j + 1), f (x (i + 1) + t * Complex.I)) =
        ∑ i ∈ Finset.range M, C (i + 1) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact sum_left_edges f hf (x (i + 1)) y N
  -- 左边组 (x_i)
  have hleft : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        ∫ t in y j..y (j + 1), f (x i + t * Complex.I)) = ∑ i ∈ Finset.range M, C i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact sum_left_edges f hf (x i) y N
  -- 水平望远镜: Σ_j A_j − Σ_j A_{j+1} = A_0 − A_N
  have hhoriz : (∑ j ∈ Finset.range N, A j) - (∑ j ∈ Finset.range N, A (j + 1)) = A 0 - A N := by
    rw [sum_range_shift A N, Finset.sum_range_succ]
    abel
  -- 垂直望远镜: Σ_i C_{i+1} − Σ_i C_i = C_M − C_0
  have hvert : (∑ i ∈ Finset.range M, C (i + 1)) - (∑ i ∈ Finset.range M, C i) = C M - C 0 := by
    rw [sum_range_shift C M, Finset.sum_range_succ]
    abel
  calc
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        rectBoundary f (x i + y j * Complex.I) (x (i + 1) + y (j + 1) * Complex.I))
        = (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
            ((∫ t in x i..x (i + 1), f (t + y j * Complex.I)) -
            (∫ t in x i..x (i + 1), f (t + y (j + 1) * Complex.I)) +
            Complex.I • (∫ t in y j..y (j + 1), f (x (i + 1) + t * Complex.I)) -
            Complex.I • (∫ t in y j..y (j + 1), f (x i + t * Complex.I)))) := by
      simp [rectBoundary]
    _ = (∑ j ∈ Finset.range N, A j) - (∑ j ∈ Finset.range N, A (j + 1)) +
        Complex.I • (∑ i ∈ Finset.range M, C (i + 1)) -
        Complex.I • (∑ i ∈ Finset.range M, C i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_eq_mul, ← Finset.mul_sum]
      rw [hbottom, htop, hright, hleft]
    _ = (A 0 - A N) + Complex.I • (C M - C 0) := by
      rw [hhoriz]
      rw [add_sub_assoc]
      rw [← smul_sub]
      rw [hvert]
    _ = rectBoundary f (x 0 + y 0 * Complex.I) (x M + y N * Complex.I) := by
      rw [smul_sub]
      unfold rectBoundary
      simp [A, C]
      abel

end ZeroRelative
