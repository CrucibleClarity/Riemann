import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# T6h: 零点阶 — 翻转方向 (跨零点 ±1 的局部论证)

ζ 在零点 s₀ 的局部展开 (mathlib IsolatedZeros):
    ζ(s) = (s - s₀)^m · g(s),  g(s₀) ≠ 0,  m = 零点阶 (p.order)
沿临界线 s = 1/2 + it 跨 t₀ (s₀ = 1/2 + it₀):
    ζ(1/2+it) = (i(t-t₀))^m · g(1/2+it) = i^m·(t-t₀)^m·g
    u = ζ/|ζ| → i^m·g(s₀)/|g(s₀)|  (t → t₀⁺)
              → (-i)^m·g(s₀)/|g(s₀)|  (t → t₀⁻)
**翻转 (u(t₀⁺) = -u(t₀⁻)) ⟺ m 奇** (m 偶则 u 连续通过, 可延拓)。

这是"符号改变但位置不变"的局部机制: 翻转方向 ±1 由 i^m 决定
(i 的迭代), 整数层 (T6e/T6g) 的跨零点跳变 = ±1 由此给出。
m = 1 (单零点, RH 预期) 时翻转 = 乘以 -1, 即 pat ±1 过程的最小步。

## pat 本质: 对消法 (2026-08-19 用户指明的方法论)

pat = 单相位数; 数字 = 多相位叠加的模糊数; 方法 = 对消消相位。
- ζ(s) = Π_p (1-p^{-s})^{-1}: 相位 = 全素数相位叠加 (模糊数)。
- χ 是显式单相位参照: 对消 θ_ζ - θ_χ/2, 残差落在 πiℤ (整数层
  T6e/T6g) — 连续相位对消干净后剩离散 ±1 序列 (pat 单相位)。
- 零点 = 完全对消点 (各素数相位对消使模归零, 相位无定义, u 翻转)。
- 本文件: m 阶零点 = m 重对消; 翻转方向 = i^m (m 次 90° 旋转);
  单零点 (1 重对消) 翻转 = -1 (pat ±1 最小步), 偶阶对消后相位仍连续。
- 参数原理 (任务③) = 对消的积分形式: 绕闭合路径一圈, 连续相位全消,
  剩整数 2π·N(T) (完全对消 ⟹ 计数)。

隔离文件 (mathlib-only)。 
English: zero-order flip: local expansion, left/right limits, flip ratio (T6h) -/

noncomputable section

open Complex
open Filter Function Set
open scoped Topology

namespace RiemannUnifiedObservation

/-- 临界线参数化: z(t) = 1/2 + t·i。 
English: Critical-line parametrization: z(t) = 1/2 + t·i. -/
def zetaLine (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- u(t) = ζ(1/2+it)/|ζ(1/2+it)|: ζ 沿临界线的单位化 (相位)。 
English: u(t) = ζ(1/2+it)/|ζ(1/2+it)|: unit-normalization of ζ along the critical line (phase). -/
def zetaUnit (t : ℝ) : ℂ :=
  riemannZeta (zetaLine t) / ‖riemannZeta (zetaLine t)‖

/-- **零点局部展开**: ζ 在零点 s₀ 的 m 阶展开 ζ(s) = (s-s₀)^m·g(s),
    g(s₀) ≠ 0 且 g 在 s₀ 连续 (m = p.order, g = dslope 迭代)。 
English: Local expansion at a zero: m-th order expansion of ζ at zero s₀, ζ(s) = (s−s₀)^m·g(s), g(s₀) ≠ 0 and g continuous at s₀ (m = p.order, g = dslope iterate). -/
theorem zeta_local_expansion (s₀ : ℂ) (hs₀ : s₀ ≠ 1) (_hz₀ : riemannZeta s₀ = 0) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ,
      (∀ᶠ s in 𝓝 s₀, riemannZeta s = (s - s₀) ^ m * g s) ∧
        g s₀ ≠ 0 ∧ ContinuousAt g s₀ := by
  -- ζ 在 s₀ 解析 (s₀ ≠ 1): analyticOn_riemannZeta 已是 AnalyticOnNhd
  have hana : AnalyticAt ℂ riemannZeta s₀ :=
    (analyticOn_riemannZeta.analyticOn).analyticAt
      (isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_singleton_iff] using hs₀))
  rcases hana with ⟨p, hp⟩
  -- p ≠ 0: ζ 在 s₀ 不恒零 (若恒零, 由解析延拓 ζ 在 {1}ᶜ 全零, 与 ζ(2) ≠ 0 矛盾)
  have hp_ne : p ≠ 0 := by
    intro hp0
    have hzero : ∀ᶠ z in 𝓝 s₀, riemannZeta z = 0 := hp.locally_zero_iff.mpr hp0
    have hfreq : ∃ᶠ z in 𝓝[≠] s₀, riemannZeta z = 0 :=
      (hzero.filter_mono nhdsWithin_le_nhds).frequently
    have heq : EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
      analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by simpa [Set.mem_compl_singleton_iff] using hs₀) hfreq
    have hz2 : riemannZeta 2 = 0 := heq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    exact (riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat) hz2
  -- m = p.order, g = dslope 迭代: 展开 + 非零 + 连续
  refine ⟨p.order, (swap dslope s₀)^[p.order] riemannZeta, ?_, ?_, ?_⟩
  · -- ζ(s) = (s-s₀)^m · g(s) 逐点 (邻域内恒成立)
    exact Eventually.of_forall (fun s => by
      simpa [smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope s)
  · exact hp.iterate_dslope_fslope_ne_zero hp_ne
  · -- g 在 s₀ 连续: dslope 迭代保持解析
    exact (hp.has_fpower_series_iterate_dslope_fslope p.order).continuousAt

/-- 展开在临界线上的形式: ζ(z(t)) = (t-t₀)^m·(i^m·g(z(t)))
    (沿 t > t₀ 侧; 由 s₀ = z(t₀) 与 z(t)-s₀ = (t-t₀)·i 代入展开)。 
English: Expansion on the critical line: ζ(z(t)) = (t−t₀)^m·(i^m·g(z(t))) (on the t > t₀ side; from s₀ = z(t₀) and z(t)−s₀ = (t−t₀)·i substituted in the expansion). -/
lemma zetaLine_expansion_right {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s) :
    ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) := by
  -- 从 𝓝 s₀ 限制到 t 侧: z 连续 ⟹ preimage ∈ 𝓝 t₀; 再与 {t > t₀} 相交
  have hcont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hpre : ∀ᶠ t in 𝓝 t₀,
      riemannZeta (zetaLine t) = (zetaLine t - zetaLine t₀) ^ m * g (zetaLine t) :=
    ContinuousAt.preimage_mem_nhds hcont h_exp
  filter_upwards [hpre.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
  -- 代数: z(t) - z(t₀) = (t - t₀)·i ⟹ (z(t)-z(t₀))^m = (t-t₀)^m · i^m
  have hdiff : zetaLine t - zetaLine t₀ = (t - t₀ : ℂ) * I := by
    unfold zetaLine
    ring_nf
  rw [ht, hdiff, mul_pow]
  ring

/-- **u 在零点右侧的极限**: u(t) → i^m·g(s₀)/|g(s₀)| (t → t₀⁺)。
    方向由 i^m 决定 (i 的迭代): 翻转向量 = m 次旋转 90°。 
English: Right-hand limit of u at a zero: u(t) → i^m·g(s₀)/|g(s₀)| (t → t₀⁺). The direction is determined by i^m (iteration of i): flip vector = m rotations of 90°. -/
theorem zetaUnit_tendsto_right {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto zetaUnit (𝓝[>] t₀)
      (𝓝 (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) := by
  -- g(z(t)) → g(s₀) 且附近非零
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[>] t₀) (𝓝 (g (zetaLine t₀))) :=
    (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
  have hgz_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  -- ζ(z(t)) 的展开与模分解 (t > t₀: |t-t₀| = t-t₀, |i^m| = 1)
  have hzeta : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) :=
    zetaLine_expansion_right h_exp
  have hnorm : ∀ᶠ t in 𝓝[>] t₀,
      ‖riemannZeta (zetaLine t)‖ = (t - t₀) ^ m * ‖g (zetaLine t)‖ := by
    filter_upwards [hzeta, self_mem_nhdsWithin] with t ht hgt
    rw [ht, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
    -- ‖(t-t₀ : ℂ)‖ = |t-t₀| = t-t₀ (t > t₀)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hgt))]
    ring
  -- u(t) = i^m·g(z(t))/|g(z(t))| (消去 (t-t₀)^m)
  have hu : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnit t = I ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hnorm, hgz_ne, self_mem_nhdsWithin] with t ht hnm hgne hgt
    unfold zetaUnit
    rw [hnm, ht]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- 极限: i^m · (g/|g| 的极限)
  have hg_ratio : Tendsto (fun t : ℝ => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  exact (tendsto_const_nhds.mul hg_ratio).congr' (EventuallyEq.symm hu)

/-- **u 在零点左侧的极限**: u(t) → (-i)^m·g(s₀)/|g(s₀)| (t → t₀⁻)。
    左侧多出 (-1)^m: m 奇时反向 (翻转), m 偶时同向 (通过)。 
English: Left-hand limit of u at a zero: u(t) → (−i)^m·g(s₀)/|g(s₀)| (t → t₀⁻). The left side gains (−1)^m: reversed when m odd (flip), same direction when m even (pass). -/
theorem zetaUnit_tendsto_left {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto zetaUnit (𝓝[<] t₀)
      (𝓝 ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) := by
  -- g(z(t)) → g(s₀) 且附近非零
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[<] t₀) (𝓝 (g (zetaLine t₀))) :=
    (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
  have hgz_ne : ∀ᶠ t in 𝓝[<] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  -- 展开 (左侧同样成立) 与模分解 (t < t₀: |t-t₀| = t₀-t)
  have hzeta : ∀ᶠ t in 𝓝[<] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) := by
    have htmp : ∀ᶠ t in 𝓝 t₀,
        riemannZeta (zetaLine t) = (zetaLine t - zetaLine t₀) ^ m * g (zetaLine t) :=
      ContinuousAt.preimage_mem_nhds hz_cont h_exp
    filter_upwards [htmp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
    have hdiff : zetaLine t - zetaLine t₀ = (t - t₀ : ℂ) * I := by
      unfold zetaLine
      ring_nf
    rw [ht, hdiff, mul_pow]
    ring
  have hnorm : ∀ᶠ t in 𝓝[<] t₀,
      ‖riemannZeta (zetaLine t)‖ = (t₀ - t) ^ m * ‖g (zetaLine t)‖ := by
    filter_upwards [hzeta, self_mem_nhdsWithin] with t ht hgt
    rw [ht, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hgt))]
    ring
  -- u(t) = (t₀-t)^m·i^m·g / ((t₀-t)^m·|g|) = i^m·g/|g|: (t-t₀)^m = (-1)^m·(t₀-t)^m
  have hu : ∀ᶠ t in 𝓝[<] t₀,
      zetaUnit t = (-I) ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hnorm, hgz_ne, self_mem_nhdsWithin] with t ht hnm hgne hgt
    unfold zetaUnit
    rw [hnm, ht]
    have hlt : t < t₀ := by simpa using hgt
    have htne : (t₀ - t : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (sub_pos.mpr hlt))
    have htnz : (t₀ - t : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    -- (t-t₀)^m = (-1)^m·(t₀-t)^m: 从 t-t₀ = -(t₀-t)
    have hneg : (t - t₀ : ℂ) ^ m = (-1 : ℂ) ^ m * (t₀ - t) ^ m := by
      have hsub : (t - t₀ : ℂ) = -(t₀ - t : ℂ) := by ring
      calc (t - t₀ : ℂ) ^ m = (-(t₀ - t : ℂ)) ^ m := by rw [hsub]
        _ = (-1 : ℂ) ^ m * (t₀ - t) ^ m := by
          have hnegmul : -(t₀ - t : ℂ) = (-1 : ℂ) * (t₀ - t : ℂ) := by ring
          rw [hnegmul, mul_pow]
    -- i^m · (-1)^m = (-i)^m (及交换序版本)
    have hIm : I ^ m * (-1 : ℂ) ^ m = (-I) ^ m := by
      rw [← mul_pow]
      ring_nf
    have hIm' : (-1 : ℂ) ^ m * I ^ m = (-I) ^ m := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hIm
    rw [hneg]
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
    -- 左侧重排使 (-1)^m·I^m 相邻, 用 hIm' 合并为 (-I)^m
    rw [show (-1 : ℂ) ^ m * ↑((t₀ - t) ^ m) * I ^ m * ↑‖g (zetaLine t)‖ =
        ↑((t₀ - t) ^ m) * ↑‖g (zetaLine t)‖ * ((-1 : ℂ) ^ m * I ^ m) by ring]
    rw [hIm']
    rw [← Complex.ofReal_mul]
  -- 极限
  have hg_ratio : Tendsto (fun t : ℝ => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[<] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[<] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  exact (tendsto_const_nhds.mul hg_ratio).congr' (EventuallyEq.symm hu)


/-- **翻转比值 (乘除法对消)**: σ(t) = 2t₀-t 是 t₀ 的反射 (右侧 ↔ 左侧),
    u(σ(t))/u(t) → (-1)^m (t → t₀⁺)。
    ζ 的展开因子 (t-t₀)^m·i^m 与模 |(t-t₀)^m| 在比值中全部对消,
    g/|g| 因子在极限中自消 (g 连续) — 只剩符号 (-1)^m。
    乘除法对消: 两个对称方向的相位贡献相消, 留 (−1)^m (共轭反射对称)。 
English: Flip ratio (multiplicative cancellation): σ(t) = 2t₀−t is the reflection of t₀ (right ↔ left), u(σ(t))/u(t) → (−1)^m (t → t₀⁺). Expansion factors (t−t₀)^m·i^m and modulus |(t−t₀)^m| cancel in the ratio; g/|g| self-cancels in the limit (g continuous); only (−1)^m remains. Symmetric directions' phase contributions cancel, leaving (−1)^m (conjugate reflection symmetry). -/
theorem flip_ratio_reflection {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto (fun t : ℝ => zetaUnit (2 * t₀ - t) / zetaUnit t) (𝓝[>] t₀)
      (𝓝 ((-1 : ℂ) ^ m)) := by
  -- 反射的连续性: σ 与 z∘σ; z(σ t₀) = z(t₀) (2t₀-t₀ = t₀)
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hcont : ContinuousAt (fun t : ℝ => zetaLine (2 * t₀ - t)) t₀ := by
    unfold zetaLine
    fun_prop
  have hz : zetaLine (2 * t₀ - t₀) = zetaLine t₀ := by
    unfold zetaLine
    congr 1
    ring
  -- ζ(z(σ t)) 的展开: z(σ t) - s₀ = (t₀-t)·i
  have hzeta_sigma : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine (2 * t₀ - t)) = (t₀ - t) ^ m * (I ^ m * g (zetaLine (2 * t₀ - t))) := by
    have h_exp' : ∀ᶠ s in 𝓝 (zetaLine (2 * t₀ - t₀)),
        riemannZeta s = (s - zetaLine t₀) ^ m * g s := by
      simpa [hz] using h_exp
    have hpre : ∀ᶠ t in 𝓝 t₀,
        riemannZeta (zetaLine (2 * t₀ - t)) =
          (zetaLine (2 * t₀ - t) - zetaLine t₀) ^ m * g (zetaLine (2 * t₀ - t)) :=
      ContinuousAt.preimage_mem_nhds hcont h_exp'
    filter_upwards [hpre.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
    have hdiff : zetaLine (2 * t₀ - t) - zetaLine t₀ = (t₀ - t : ℂ) * I := by
      unfold zetaLine
      apply Complex.ext
      · simp
      · simp
        ring
    rw [ht, hdiff, mul_pow]
    ring
  -- g(z(σ t)) → g(s₀) 且附近非零
  have hgσ_tendsto : Tendsto (fun t : ℝ => g (zetaLine (2 * t₀ - t))) (𝓝[>] t₀)
      (𝓝 (g (zetaLine t₀))) := by
    have hcont' : Tendsto (fun t : ℝ => zetaLine (2 * t₀ - t)) (𝓝 t₀) (𝓝 (zetaLine t₀)) := by
      simpa [hz] using hcont.tendsto
    have ht := hg_cont.tendsto.comp hcont'
    have hg_cod : g (zetaLine (2 * t₀ - t₀)) = g (zetaLine t₀) := congrArg g hz
    simpa [Function.comp_def, hg_cod] using ht.mono_left nhdsWithin_le_nhds
  have hgσ_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine (2 * t₀ - t)) ≠ 0 := by
    have hne' : ∀ᶠ s in 𝓝 (zetaLine (2 * t₀ - t₀)), g s ≠ 0 := by
      simpa [hz] using hg_cont.eventually_ne hg
    have hgσ_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine (2 * t₀ - t)) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hcont hne'
    exact hgσ_ne0.filter_mono nhdsWithin_le_nhds
  -- u(σ t) = (-1)^m·(i^m·(g(z(σ t))/|g(z(σ t))|)): (t₀-t)^m = (-1)^m·(t-t₀)^m, |t₀-t| = t-t₀
  have hu_sigma : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnit (2 * t₀ - t) =
        (-1 : ℂ) ^ m * (I ^ m * (g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖)) := by
    filter_upwards [hzeta_sigma, hgσ_ne, self_mem_nhdsWithin] with t ht hgne hgt
    unfold zetaUnit
    have hnm : ‖(t₀ - t : ℂ) ^ m * (I ^ m * g (zetaLine (2 * t₀ - t)))‖ =
        (t - t₀) ^ m * ‖g (zetaLine (2 * t₀ - t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hgt))]
      ring
    rw [ht, hnm]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine (2 * t₀ - t))‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    -- (t₀-t)^m = (-1)^m·(t-t₀)^m
    have hneg : (t₀ - t : ℂ) ^ m = (-1 : ℂ) ^ m * (t - t₀) ^ m := by
      have hsub : (t₀ - t : ℂ) = -(t - t₀ : ℂ) := by ring
      calc (t₀ - t : ℂ) ^ m = (-(t - t₀ : ℂ)) ^ m := by rw [hsub]
        _ = (-1 : ℂ) ^ m * (t - t₀) ^ m := by
          have hnegmul : -(t - t₀ : ℂ) = (-1 : ℂ) * (t - t₀ : ℂ) := by ring
          rw [hnegmul, mul_pow]
    rw [hneg]
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    -- (-1)^m·(i^m·g)·‖g‖⁻¹ = (-1)^m·(i^m·(g/‖g‖)): 乘除重排 (field_simp 已化简)
  -- u(t) = i^m·(g(z t)/|g(z t)|) (右侧, 与 zetaUnit_tendsto_right 内相同)
  have hzeta : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) :=
    zetaLine_expansion_right h_exp
  have hgz_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  have hu : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnit t = I ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hgz_ne, self_mem_nhdsWithin] with t ht hgne hgt
    unfold zetaUnit
    have hnm : ‖(t - t₀ : ℂ) ^ m * (I ^ m * g (zetaLine t))‖ =
        (t - t₀) ^ m * ‖g (zetaLine t)‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hgt))]
      ring
    rw [ht, hnm]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- 比值: i^m 因子对消 ⟹ (-1)^m·(gσ/|gσ|)/(g/|g|)
  have hratio : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnit (2 * t₀ - t) / zetaUnit t =
        (-1 : ℂ) ^ m * ((g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
          (g (zetaLine t) / ‖g (zetaLine t)‖)) := by
    filter_upwards [hu_sigma, hu] with t hs h
    rw [hs, h]
    field_simp [pow_ne_zero m (by norm_num : (I : ℂ) ≠ 0)]
  -- 两个 g 比值因子 → g(s₀)/|g(s₀)|, 商 → 1
  have hratio1 : Tendsto (fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine (2 * t₀ - t))‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgσ_tendsto.norm
    exact hgσ_tendsto.div hden hnz
  have hratio2 : Tendsto (fun t => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[>] t₀) (𝓝 (g (zetaLine t₀))) :=
      (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  have ha : g (zetaLine t₀) / ‖g (zetaLine t₀)‖ ≠ 0 := by
    exact div_ne_zero hg (by exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg))
  have hquot : Tendsto (fun t => (g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
      (g (zetaLine t) / ‖g (zetaLine t)‖)) (𝓝[>] t₀) (𝓝 1) := by
    have hq := hratio1.div hratio2 ha
    -- hq : Tendsto (f1/f2) (𝓝 (a/a)); 函数商 = 逐点商, a/a = 1
    have hfun : ((fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
        (fun t => g (zetaLine t) / ‖g (zetaLine t)‖)) =
        (fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖ /
          (g (zetaLine t) / ‖g (zetaLine t)‖)) := by
      funext t
      rfl
    simpa [hfun, div_self ha] using hq
  -- 组合: (-1)^m·1 = (-1)^m
  have hmul : Tendsto (fun t : ℝ => (-1 : ℂ) ^ m *
      ((g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
        (g (zetaLine t) / ‖g (zetaLine t)‖))) (𝓝[>] t₀) (𝓝 ((-1 : ℂ) ^ m)) := by
    have hc : Tendsto (fun _ : ℝ => (-1 : ℂ) ^ m) (𝓝[>] t₀) (𝓝 ((-1 : ℂ) ^ m)) :=
      tendsto_const_nhds
    simpa using hc.mul hquot
  exact hmul.congr' (EventuallyEq.symm hratio)

/-- **翻转 ⟺ 比值 = -1 (乘除法对消版)**: 由 flip_ratio_reflection,
    u(σ(t))/u(t) → (-1)^m, 翻转 (u(t₀⁻) = -u(t₀⁺)) ⟺ (-1)^m = -1 ⟺ m 奇。
    对称方向的相位 (i^m 与 (-i)^m) 在比值中对消, 留下符号 (-1)^m。 
English: Flip ⟺ ratio = −1 (multiplicative-cancellation form): by flip_ratio_reflection, u(σ(t))/u(t) → (−1)^m; flip (u(t₀⁻) = −u(t₀⁺)) ⟺ (−1)^m = −1 ⟺ m odd. The phases of the symmetric directions (i^m and (−i)^m) cancel in the ratio, leaving the sign (−1)^m. -/
theorem flip_ratio_iff_odd {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    ((-1 : ℂ) ^ m = -1) ↔ Odd m := by
  constructor
  · -- (-1)^m = -1 ⟹ m 奇: 反证 m 偶 ⟹ (-1)^m = 1
    intro h
    by_contra hm
    have heven : Even m := Nat.not_odd_iff_even.mp hm
    rcases heven with ⟨k, hk⟩
    subst m
    have hpow : (-1 : ℂ) ^ (2 * k) = 1 := by
      calc (-1 : ℂ) ^ (2 * k) = ((-1 : ℂ) ^ 2) ^ k := by simp [pow_mul]
        _ = 1 := by norm_num
    -- 1 = -1 矛盾
    have : (1 : ℂ) = -1 := by simpa [hpow] using h
    norm_num at this
  · -- m 奇 ⟹ (-1)^m = -1
    intro hm
    rcases hm with ⟨k, hk⟩
    subst m
    calc (-1 : ℂ) ^ (2 * k + 1) = (-1 : ℂ) ^ (2 * k) * (-1 : ℂ) := by simp [pow_succ]
      _ = ((-1 : ℂ) ^ 2) ^ k * (-1 : ℂ) := by simp [pow_mul]
      _ = -1 := by norm_num

/-- **奇阶翻转**: m 奇 ⟹ u 跨零点翻转 — 左右极限互为相反数。 
English: Odd-order flip: m odd ⟹ u flips across the zero — left and right limits are negatives of each other. -/
theorem flip_of_odd_order {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
      -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
  -- (-i)^m = -i^m ⟺ m 奇
  have hIm : (-I) ^ m = -(I ^ m) := by
    rcases hm with ⟨k, hk⟩
    subst m
    rw [show (-I : ℂ) = (-1 : ℂ) * I by ring]
    rw [mul_pow]
    have hneg1 : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
      calc
        (-1 : ℂ) ^ (2 * k + 1) = (-1 : ℂ) ^ (2 * k) * (-1 : ℂ) := by simp [pow_succ]
        _ = ((-1 : ℂ) ^ 2) ^ k * (-1 : ℂ) := by simp [pow_mul]
        _ = -1 := by norm_num
    rw [hneg1]
    ring
  rw [hIm]
  ring

/-- **偶阶通过**: m 偶 ⟹ u 跨零点连续通过 (左右极限相等, 可延拓)。 
English: Even-order pass: m even ⟹ u passes continuously across the zero (left and right limits equal, extendable). -/
theorem pass_of_even_order {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Even m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
  -- (-i)^m = i^m ⟺ m 偶
  have hIm : (-I) ^ m = I ^ m := by
    rcases hm with ⟨k, hk⟩
    subst m
    -- Even m = ∃ r, m = r + r ⟹ m = 2k (two_mul)
    have htwo : k + k = 2 * k := by omega
    rw [htwo]
    rw [show (-I : ℂ) = (-1 : ℂ) * I by ring]
    rw [mul_pow]
    have hneg1 : (-1 : ℂ) ^ (2 * k) = 1 := by
      calc
        (-1 : ℂ) ^ (2 * k) = ((-1 : ℂ) ^ 2) ^ k := by simp [pow_mul]
        _ = 1 := by norm_num
    rw [hneg1]
    ring
  rw [hIm]

/-- **翻转 ⟺ m 奇 (主定理)**: 由左右极限公式,
    u(t₀⁻) = -u(t₀⁺) ⟺ (-i)^m = -i^m ⟺ (-1)^m = -1 ⟺ m 奇。 
English: Flip ⟺ m odd (main theorem): from the left/right limit formulas, u(t₀⁻) = −u(t₀⁺) ⟺ (−i)^m = −i^m ⟺ (−1)^m = −1 ⟺ m odd. -/
theorem flip_iff_odd {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    ((I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
        -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) ↔ Odd m := by
  constructor
  · -- 翻转 ⟹ m 奇: 反证 m 偶 ⟹ 相等, 与相反矛盾
    intro hflip
    by_contra hodd
    have heven : Even m := Nat.not_odd_iff_even.mp hodd
    have hpass := pass_of_even_order heven h_exp hg hg_cont
    -- 相等且相反 ⟹ u⁺ = 0
    have hzero : I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) = 0 := by
      -- hflip (u⁺ = -u⁻) 与 hpass (u⁺ = u⁻) ⟹ u⁺ = -u⁺
      have hneg_self : I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) =
          -(I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
        calc
          I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) =
              -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := hflip
          _ = -(I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by rw [← hpass]
      have hsum : 2 * (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = 0 := by
        rw [two_mul]
        nth_rw 1 [hneg_self]
        ring
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hsum).resolve_left h2
    -- g(s₀)/|g(s₀)| ≠ 0 ⟹ i^m 非零 ⟹ 矛盾
    have hg_ratio_ne : g (zetaLine t₀) / ‖g (zetaLine t₀)‖ ≠ 0 := by
      exact div_ne_zero hg (by exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg))
    exact (mul_ne_zero (pow_ne_zero m (by norm_num : (I : ℂ) ≠ 0)) hg_ratio_ne) hzero
  · -- m 奇 ⟹ 翻转
    intro hm
    exact flip_of_odd_order hm h_exp hg hg_cont


  -- ============================================================
  -- T6n: 翻转 = π 相位跳桥 (2026-08-19)
  -- 用户方法论继续: 未证部分 (翻转计数 = 零点数) 用桥接推进。
  -- 翻转 (u⁻ = -u⁺, ① flip_of_odd_order) ⟹ u⁻/u⁺ = -1 = e^{iπ}:
  -- 左右对称方向的相位 (I^m 与 (-I)^m) 在对消后只剩 e^{iπ},
  -- 翻转 = π 相位跳 = e^{iπ} 桥的离散版 (与 e^{iπS} = u 平行)。
  -- 翻转计数 = 零点数的最后拼装: 每跨零点 θ_ζ 跳 π (此桥) +
  -- T6e 整数层 (2θ_ζ - θ_χ = 2πim) + θ_χ 连续 ⟹ 层跳 1。
  -- ============================================================

/-- **翻转 = π 相位跳**: u(t₀⁻)/u(t₀⁺) = -1 — 左右对称方向的相位
    (I^m 与 (-I)^m) 在比值中对消, 剩下符号 -1 = e^{iπ}。
    翻转 (m 奇, ①) 的比值形式: 相位跳 π 而非任意相位。 
English: Flip = π phase jump: u(t₀⁻)/u(t₀⁺) = −1 — phases of the symmetric directions (I^m and (−I)^m) cancel in the ratio, leaving −1 = e^{iπ}. Ratio form of flip (m odd): phase jumps by π, not by an arbitrary phase. -/
theorem flip_phase_jump_pi {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = -1 := by
  -- u⁻ ≠ 0 (G = g/|g| ≠ 0)
  have hden : (-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by simp : (-I : ℂ) ≠ 0)) (div_ne_zero hg (by simpa using hg))
  -- 翻转: u⁺ = -u⁻ (flip_of_odd_order) ⟹ u⁺/u⁻ = -1
  have hflip := flip_of_odd_order hm h_exp hg hg_cont
  calc
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
        ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))
        = (-((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) /
            ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
          rw [hflip]
    _ = -1 := by
      field_simp [hden, (norm_ne_zero_iff.mpr hg : ‖g (zetaLine t₀)‖ ≠ 0)]

/-- **翻转 = e^{iπ} (指数形式)**: u(t₀⁻)/u(t₀⁺) = e^{iπ} —
    e^{iπ} 桥的离散版: 翻转 = π 相位跳 = 单位元 -1 的指数表示。
    与 e^{iπS(T)} = u(T) 平行: 连续相位用 e^{iπS}, 翻转用 e^{iπ}。 
English: Flip = e^{iπ} (exponential form): u(t₀⁻)/u(t₀⁺) = e^{iπ} — discrete version of the e^{iπ} bridge: flip = π phase jump = exponential form of the unit −1. Parallel to e^{iπS(T)} = u(T): continuous phase uses e^{iπS}, flip uses e^{iπ}. -/
theorem flip_phase_jump_exp {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = Complex.exp (↑Real.pi * Complex.I) := by
  -- -1 = e^{iπ} (exp_pi_mul_I)
  rw [flip_phase_jump_pi hm h_exp hg hg_cont]
  rw [Complex.exp_pi_mul_I]

end RiemannUnifiedObservation
