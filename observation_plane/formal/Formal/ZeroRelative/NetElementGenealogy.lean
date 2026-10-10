import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NetElementGenealogy — 净元谱系 0-6 阶 + 卦限族 (独立自包含文件)

0pat 独立文件 (仅 Mathlib): 格点阶谱系 (0 生成锁定 / 1 跳变 π→±1 /
2 配对 / 3 圈合成 2K / 4 圈加法 / 5 负圈 / 6 平移群闭合), 1 阶升维-回0
二分 (ReorientNetElement 族), 对合应用族 (InvolutionNetElement),
配对几何 (PairingNetElement), 维度阶卦限族 (DirectionTensor:
n 维 → 2^n 卦限, 6 阶 = 64 六十四卦) — 全机证 0 sorry。
D116 (2026-08-27): 用户指令 "整理下, 作为一个独立的 lean, 加入到论文中"。
-/

namespace ZeroRelative

noncomputable section

-- ===== from ExchangeNetElement.lean =====

/-!
# ExchangeNetElement — 可交换净元: theta = num (通用版)

相位互锁点 (cos θ = 0, sin θ = ±1 — 方向由 sin 承载) 与数字 k 的
双向交换: θ_k = π/2 + kπ ⟷ k。零信息损失 (往返恒等), 通用 —
不依赖任何具体解析函数 (黎曼无关)。方向一致性是 pat 体系内蕴
(相位互锁方向承载); 换方向/不单调 = 回 pat0 重定基点/轴, 非本
净元职责。

English: exchange net element -- theta = num: the phase-interlock
lattice θ_k = π/2 + kπ (where cos θ = 0 and the direction is carried
by sin θ) exchanges with the integer k, in both directions, with
identity round-trips. General-purpose; no specific analytic function
is involved. Direction is intrinsic to the pat system (interlock
direction); reversing direction / non-monotonicity returns to pat0
(basepoint/axis re-fixing), outside this net element's scope.
-/



/-- **互锁格点**: θ_k = π/2 + kπ — cos θ = 0 的相位互锁点
    (方向由 sin θ = (−1)^k 承载; 每 π 相位行走恰一个格点). -/
def interlockPhase (k : ℤ) : ℝ := Real.pi / 2 + (k : ℝ) * Real.pi

/-- **数字读出**: 相位 → 数字 — 从互锁相位 θ 提取格点序数
    k = ⌊(θ − π/2)/π⌋ (在格点上精确). -/
def numOfInterlock (θ : ℝ) : ℤ :=
  Int.floor ((θ - Real.pi / 2) / Real.pi)

/-- **互锁相位余** (cos θ = 0): 互锁格点的联合判定 — cos θ = 0. -/
theorem interlock_cos_zero (k : ℤ) :
    Real.cos (interlockPhase k) = 0 := by
  rw [interlockPhase]
  rw [Real.cos_add]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [Real.cos_int_mul_pi, Real.sin_int_mul_pi]
  simp

/-- **互锁相位方向** (sin θ = (−1)^k): 方向由 sin 承载 — 每格点
    交替方向 (相位互锁: 单用 cos 丢方向). -/
theorem interlock_sin_dir (k : ℤ) :
    Real.sin (interlockPhase k) = (-1 : ℝ) ^ k := by
  rw [interlockPhase]
  rw [Real.sin_add]
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [Real.sin_int_mul_pi, Real.cos_int_mul_pi]
  simp

/-- **数字读出精确** (num∘theta = id): 在互锁格点上, 数字读出
    回到格点序数 — theta → num 无损失. -/
theorem numOfInterlock_spec (k : ℤ) :
    numOfInterlock (interlockPhase k) = k := by
  unfold numOfInterlock interlockPhase
  have h : ((Real.pi / 2 + (k : ℝ) * Real.pi) - Real.pi / 2) / Real.pi = (k : ℝ) := by
    field_simp
    ring
  rw [h]
  rw [Int.floor_intCast]

/-- **相位重建精确** (theta∘num = id on lattice): 数字 → 相位
    → 数字读出 → 原相位 — 往返恒等 (可交换). -/
theorem interlock_roundtrip (k : ℤ) :
    interlockPhase (numOfInterlock (interlockPhase k)) = interlockPhase k := by
  rw [numOfInterlock_spec]

/-- **格点间距** (每 π 一个格点): 相邻互锁格点相距 π —
    相位行走每 π 恰一个数字. -/
theorem interlock_step (k : ℤ) :
    interlockPhase (k + 1) - interlockPhase k = Real.pi := by
  unfold interlockPhase
  rw [Int.cast_add]
  ring

/-- **方向交替** (互锁方向): 相邻格点的 sin 方向相反 —
    相位互锁的方向信息 (cos 零点 + sin 方向联合判定). -/
theorem interlock_dir_opposite (k : ℤ) :
    Real.sin (interlockPhase (k + 1)) = -Real.sin (interlockPhase k) := by
  rw [interlock_sin_dir]
  rw [interlock_sin_dir]
  rw [show (-1 : ℝ) ^ (k + 1) = (-1 : ℝ) ^ k * (-1 : ℝ) ^ (1 : ℤ) by
    exact zpow_add₀ (a := (-1 : ℝ)) (by norm_num : (-1 : ℝ) ≠ 0) k 1]
  norm_num

/-- **半周期翻号** (零点翻转原型): sin(θ + π) = −sin θ — 过互锁
    格点翻号 (FlipCount 原型的互锁形: 每个格点一次方向翻转). -/
theorem interlock_flip_neg (k : ℤ) :
    Real.sin (interlockPhase k + Real.pi) = -Real.sin (interlockPhase k) := by
  rw [interlockPhase]
  rw [Real.sin_add]
  simp

/-- **行走 = 数字×π** (theta = num 的行走形态): k 个格点间距 =
    k·π — 数字 k 读出的相位行走 (每 π 一个数字; 方向一致是 pat
    内蕴, 换方向回 pat0). -/
theorem walk_of_nums (k : ℤ) :
    interlockPhase k - interlockPhase 0 = (k : ℝ) * Real.pi := by
  unfold interlockPhase
  ring

/-! ## 0 阶定理: 相位数值同时生成锁定 -/

/-- **相位数值同时生成锁定 (0 阶定理)**: 互锁条件 (cos θ = 0)
    同时生成相位与数字并双向锁定 — cos θ = 0 时, 数字条件
    (numOfInterlock θ = k) 与相位条件 (θ = interlockPhase k)
    互推: 一个条件同时确定相位格点与数字, 生成互逆
    (theta = num 的单一公设形). -/
theorem gen_lock_iff (θ : ℝ) (k : ℤ) :
    Real.cos θ = 0 → (numOfInterlock θ = k ↔ θ = interlockPhase k) := by
  intro hcos
  constructor
  · intro hk
    -- cos θ = 0 ⟹ θ = interlockPhase j (cos_eq_zero_iff: θ = (2j+1)π/2)
    rcases Real.cos_eq_zero_iff.mp hcos with ⟨j, hj⟩
    have hθj : θ = interlockPhase j := by
      rw [hj]
      unfold interlockPhase
      ring
    -- numOfInterlock θ = k 且 θ = interlockPhase j ⟹ k = j (锁定)
    have hkj : k = j := by
      rw [← hk]
      rw [hθj]
      exact numOfInterlock_spec j
    rw [hkj, hθj]
  · intro hθ
    rw [hθ]
    exact numOfInterlock_spec k

/-- **一阶派生 (从 0 阶)**: 跳变 π 保持格点 (interlock_flip_step:
    θ_k + π = θ_{k+1}) 且数字锁定 +1 — jump_cross_one 的格点形
    (一阶 = 0 阶锁定 + 格点平移). -/
theorem jump_derived (k : ℤ) :
    numOfInterlock (interlockPhase k + Real.pi) = k + 1 := by
  -- interlockPhase k + π = interlockPhase (k+1) (格点平移, 代数)
  have h : interlockPhase k + Real.pi = interlockPhase (k + 1) := by
    unfold interlockPhase
    rw [Int.cast_add]
    ring
  rw [h]
  exact numOfInterlock_spec (k + 1)

/-! ## 有向交叉 = 行走/π (净元推广, 无条件) -/

/-- **数字平移 (2π 周期)**: numOfInterlock(θ + 2πK) = numOfInterlock θ + 2K —
    整圈行走的净交叉 = 2K (每圈 2 个有向交叉: 上穿 π/2 与下穿 3π/2). -/
theorem num_shift_period (θ : ℝ) (K : ℤ) :
    numOfInterlock (θ + 2 * (K : ℝ) * Real.pi) = numOfInterlock θ + 2 * K := by
  unfold numOfInterlock
  have h : ((θ + 2 * (K : ℝ) * Real.pi - Real.pi / 2) / Real.pi) =
      ((θ - Real.pi / 2) / Real.pi) + 2 * (K : ℝ) := by
    field_simp
    ring
  rw [h]
  rw [show 2 * (K : ℝ) = ((2 * K : ℤ) : ℝ) by norm_num]
  rw [Int.floor_add_intCast]

/-- **净交叉 = 数字差**: 有向交叉净数 (θ 从 a 走到 b 穿过互锁格点
    π/2+kπ 的净次数) = numOfInterlock b − numOfInterlock a —
    相位行走的净数字读出 (无条件, 方向性内蕴). -/
theorem net_cross_num_diff (a b : ℝ) :
    numOfInterlock b - numOfInterlock a =
      Int.floor (((b - Real.pi / 2) / Real.pi)) - Int.floor (((a - Real.pi / 2) / Real.pi)) := by
  unfold numOfInterlock
  ring

/-- **跳变 = 交叉等价 (一阶配对形态)**: 相位跳 π (奇阶零点的
    翻转) 跨过恰 1 个互锁格点 — numOfInterlock(θ+π) = numOfInterlock θ
    + 1 — 跳变与交叉统一计数 (每 π 一个格点, 无条件 floor 代数). -/
theorem jump_cross_one (θ : ℝ) :
    numOfInterlock (θ + Real.pi) = numOfInterlock θ + 1 := by
  unfold numOfInterlock
  have h : (θ + Real.pi - Real.pi / 2) / Real.pi = (θ - Real.pi / 2) / Real.pi + 1 := by
    field_simp
    ring
  rw [h]
  rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num]
  rw [Int.floor_add_intCast]

/-- **跳变 = −π (反向一阶)**: 反向跳 −π 跨过 −1 个互锁格点 —
    方向性内蕴 (回 pat0 的有向计数). -/
theorem jump_cross_neg_one (θ : ℝ) :
    numOfInterlock (θ - Real.pi) = numOfInterlock θ - 1 := by
  unfold numOfInterlock
  have h : (θ - Real.pi - Real.pi / 2) / Real.pi = (θ - Real.pi / 2) / Real.pi - 1 := by
    field_simp
    ring
  rw [h]
  have hx : (θ - Real.pi / 2) / Real.pi - 1 = (θ - Real.pi / 2) / Real.pi + (-1 : ℝ) := by ring
  rw [hx]
  rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num]
  rw [Int.floor_add_intCast]
  ring

/-- **闭合路径净交叉 = 2×圈数**: 行走 2πK (K 圈) 的有向交叉净数
    = 2K — theta = num 的围道形: 每圈恰 2 个净交叉 (幅角原理的
    互锁读法, 无条件). -/
theorem net_cross_winding (θ : ℝ) (K : ℤ) :
    numOfInterlock (θ + 2 * (K : ℝ) * Real.pi) - numOfInterlock θ = 2 * K := by
  rw [num_shift_period]
  ring

/- ## 四阶: 圈数加法 (双圈合成) -/

/-- **圈数加法 (四阶)**: J 圈 + K 圈的净交叉 = 2J + 2K — 双圈
    参数分解 (num_shift_period 两次): 圈数相加的数字形. -/
theorem net_cross_add (θ : ℝ) (J K : ℤ) :
    numOfInterlock (θ + 2 * (J : ℝ) * Real.pi + 2 * (K : ℝ) * Real.pi)
        - numOfInterlock θ = 2 * J + 2 * K := by
  have h1 := num_shift_period (θ + 2 * (J : ℝ) * Real.pi) K
  have h2 := num_shift_period θ J
  rw [h1, h2]
  ring

/- ## 五阶: 有向圈 (负圈/反向) -/

/-- **有向圈 (五阶)**: 反向行走 −2πK (负圈) 的净交叉 = −2K —
    方向性内蕴 (回 pat0 的有向计数, ℤ 圈完整). -/
theorem net_cross_neg (θ : ℝ) (K : ℤ) :
    numOfInterlock (θ - 2 * (K : ℝ) * Real.pi) - numOfInterlock θ = -2 * K := by
  unfold numOfInterlock
  have h : (θ - 2 * (K : ℝ) * Real.pi - Real.pi / 2) / Real.pi =
      (θ - Real.pi / 2) / Real.pi - 2 * (K : ℝ) := by
    field_simp
    ring
  rw [h]
  have hx : (θ - Real.pi / 2) / Real.pi - 2 * (K : ℝ) =
      (θ - Real.pi / 2) / Real.pi + (-2 * (K : ℝ)) := by ring
  rw [hx]
  rw [show -2 * (K : ℝ) = ((-2 * K : ℤ) : ℝ) by norm_num]
  rw [Int.floor_add_intCast]
  ring

/- ## 六阶: 完整平移群 (π·m 任意平移) -/

/-- **完整平移 (六阶)**: 任意 π·m 平移 (m 个互锁格点) 的数字读出
    = +m — 一阶跳变 (m=±1) + 三阶圈 (m=2K) + 五阶反圈 (m<0)
    的统一: 格点平移群的完整结构, 无条件. -/
theorem num_translate (θ : ℝ) (m : ℤ) :
    numOfInterlock (θ + (m : ℝ) * Real.pi) = numOfInterlock θ + m := by
  unfold numOfInterlock
  have h : (θ + (m : ℝ) * Real.pi - Real.pi / 2) / Real.pi =
      (θ - Real.pi / 2) / Real.pi + (m : ℝ) := by
    field_simp
    ring
  rw [h]
  rw [Int.floor_add_intCast]

-- ===== from ReorientNetElement.lean =====

/-!
# ReorientNetElement — 方向改变的两种途径 (升维 / 回 0 点)

方向宣称的改变, 完备二分 (pat 体系):
- **升维 (向量/矩阵/张量化)**: 方向放进高维结构 — 单位向量
  v(θ) = (cos θ, sin θ) 承载方向 (相位互锁 = 分量联合, 单用 cos
  丢方向); 换向 = 旋转矩阵 R(φ) 作用, 可逆 (信息不丢); 张量化
  = 多方向分量并存。
- **回 0 点 (pat0 重定)**: 方向反转 = 在 0 点重定基点 — 翻号
  v(θ+π) = −v(θ), 格点从基点 0 重新读出 (interlockPhase k =
  interlockPhase 0 + k·π)。

English: reorient net element -- the two ways to change a direction
claim: lift (vector/matrix/tensor: the direction is carried by the
unit vector v(θ) = (cos θ, sin θ), reorientation is an invertible
rotation) or return to zero (pat0 re-fixing: sign flip v(θ+π) = −v(θ),
lattice re-read from the basepoint 0).
-/



/-- **方向向量** (升维承载): v(θ) = (cos θ, sin θ) — 方向在 2D 向量,
    换向连续 (信息不丢); 相位互锁 = 分量联合. -/
def dirVec (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)

/-- **旋转矩阵作用** (升维的换向算子): R(φ) 旋转方向, 可逆. -/
def rot (φ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos φ * p.1 - Real.sin φ * p.2, Real.sin φ * p.1 + Real.cos φ * p.2)

/-- **旋转 = 方向加法** (升维): v(θ+φ) = R(φ)·v(θ) — 方向改变
    由旋转矩阵承载, 相位加法 = 矩阵作用. -/
theorem dirVec_add_rot (θ φ : ℝ) :
    dirVec (θ + φ) = rot φ (dirVec θ) := by
  unfold dirVec rot
  rw [Real.cos_add, Real.sin_add]
  ext <;> ring

/-- **旋转可逆 (无损失)**: R(−φ)·R(φ)·v = v — 升维承载方向改变
    可逆还原, 信息零损失 (往返恒等). -/
theorem rot_inverse (φ : ℝ) (p : ℝ × ℝ) :
    rot (-φ) (rot φ p) = p := by
  unfold rot
  rw [Real.sin_neg, Real.cos_neg]
  ext <;> ring_nf
  · calc
      Real.cos φ ^ 2 * p.1 + p.1 * Real.sin φ ^ 2
          = p.1 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
      _ = p.1 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  · calc
      Real.sin φ ^ 2 * p.2 + Real.cos φ ^ 2 * p.2
          = p.2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
      _ = p.2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring

/-- **半周期 = 翻号 (回 0 点重定)**: v(θ+π) = −v(θ) — 方向反转
    π = 在 0 点重定基点 (方向宣称换向的最小操作). -/
theorem dirVec_flip (θ : ℝ) :
    dirVec (θ + Real.pi) = (-dirVec θ) := by
  unfold dirVec
  rw [Real.cos_add, Real.sin_add]
  rw [Real.cos_pi, Real.sin_pi]
  ext <;> simp

/-- **回 0 点读出** (pat0 重定): 互锁格点从基点 0 重定 —
    θ_k = θ_0 + k·π — 任何格点经基点 0 与数字 k 读出 (回 0
    后方向宣称在新基点下重建). -/
theorem interlock_from_zero (k : ℤ) :
    interlockPhase k = interlockPhase 0 + (k : ℝ) * Real.pi := by
  unfold interlockPhase
  ring

/-- **格点平移 = 方向反转** (回 0 的格点形): θ_k + π = θ_{k+1} —
    翻号把格点移到相邻格点 — 换向 = 在 0 点重定后沿新方向
    数下一个数字. -/
theorem interlock_flip_step (k : ℤ) :
    interlockPhase k + Real.pi = interlockPhase (k + 1) := by
  unfold interlockPhase
  rw [Int.cast_add]
  ring

/-- **翻号保持互锁** (回 0 不破坏结构): 方向反转后仍是互锁格点 —
    cos(θ_k + π) = 0 (翻号 = 0 点重定, 格点结构平移不变). -/
theorem flip_stays_interlock (k : ℤ) :
    Real.cos (interlockPhase k + Real.pi) = 0 := by
  rw [interlock_flip_step]
  exact interlock_cos_zero (k + 1)

/-- **方向改变二分完备性** (升维 vs 回 0): 方向反转 φ = π 时两种
    途径一致 — 升维形 v(θ+π) = −v(θ) (旋转 π 无损失) ⟺ 回 0 形
    θ ↦ θ+π 是 0 点重定 (格点平移). -/
theorem reorient_equivalence (k : ℤ) :
    dirVec (interlockPhase k + Real.pi) = -dirVec (interlockPhase k) ∧
    interlockPhase k + Real.pi = interlockPhase (k + 1) := by
  constructor
  · exact dirVec_flip (interlockPhase k)
  · exact interlock_flip_step k

-- ===== from InvolutionNetElement.lean =====

/-!
# InvolutionNetElement — 净元调用: 反射/镜像/对合元族

回 0 元 (ReorientNetElement) 的应用场景: 方向改变算子族 —
- **反射 (镜像)**: θ ↦ −θ — 实轴镜像, 矩阵 M = [[1,0],[0,−1]],
  对合 (M·M = id)
- **翻号**: θ ↦ θ+π (dirVec_flip) — 对合 (向量形: 2π 周期)
- **旋转 π**: 对合 (rot π · rot π = id)
- **对合族交换**: 翻号 ∘ 反射 = 反射 ∘ 翻号

English: involution net element -- the reorient application family:
reflection (mirror θ ↦ −θ, involutive matrix), sign flip (θ ↦ θ+π,
involutive as a vector: 2π periodic), rotation by π (involutive), and
the commuting of the family.
-/



/-- **反射 (镜像)**: 实轴反射 (θ ↦ −θ 的向量形) — 方向反转的
    镜像途径 (升维承载: 矩阵 [[1,0],[0,−1]]). -/
def reflect (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

/-- **镜像 = 反射作用**: v(−θ) = M·v(θ) — 负角 = 实轴镜像
    (方向改变二分的升维形, 用旋转族同款矩阵语言). -/
theorem reflect_dirVec (θ : ℝ) :
    dirVec (-θ) = reflect (dirVec θ) := by
  unfold dirVec reflect
  rw [Real.cos_neg, Real.sin_neg]

/-- **反射对合**: M·M·v = v — 镜像两次还原 (反射是严格对合,
    与翻号不同: 翻号需 2π 才还原). -/
theorem reflect_involution (p : ℝ × ℝ) :
    reflect (reflect p) = p := by
  unfold reflect
  ext <;> simp

/-- **翻号对合 (向量形)**: v(θ+2π) = v(θ) — 两次翻号 = 恒等
    (2π 周期: 方向向量的周期 = 互锁格点间距的 2 倍). -/
theorem flip_involution_vec (θ : ℝ) :
    dirVec (θ + 2 * Real.pi) = dirVec θ := by
  unfold dirVec
  rw [Real.cos_add, Real.sin_add]
  rw [Real.cos_two_pi, Real.sin_two_pi]
  ext <;> simp

/-- **旋转 π 对合**: R(π)·R(π)·v = v — 半圈两次 = 整圈 = 恒等
    (旋转族可逆 rot_inverse 的 π 特例). -/
theorem rot_pi_involution (p : ℝ × ℝ) :
    rot Real.pi (rot Real.pi p) = p := by
  unfold rot
  rw [Real.cos_pi, Real.sin_pi]
  ext <;> ring

/-- **对合族交换**: 翻号 ∘ 反射 = 反射 ∘ 翻号 — 两个方向改变
    算子可交换 (族的结构: 交换的对合群, 阶 2 × 阶 2). -/
theorem flip_reflect_commute (p : ℝ × ℝ) :
    (-reflect p) = reflect (-p) := by
  unfold reflect
  ext <;> simp <;> ring

/-- **格点镜像 (回 0 的镜像形)**: −θ_k = θ_{−k−1} — 镜像把互锁
    格点送到互锁格点 (格点结构在镜像下平移, 方向宣称在镜像后
    由新格点序数承接). -/
theorem interlock_mirror (k : ℤ) :
    interlockPhase (-k - 1) = -interlockPhase k := by
  unfold interlockPhase
  rw [show ((-k - 1 : ℤ) : ℝ) = -(k : ℝ) - 1 by
    norm_num]
  ring

/-- **镜像保持互锁**: cos(−θ_k) = 0 — 镜像后仍是互锁格点
    (回 0 元 flip_stays_interlock 的镜像对应). -/
theorem mirror_stays_interlock (k : ℤ) :
    Real.cos (-interlockPhase k) = 0 := by
  rw [← interlock_mirror]
  exact interlock_cos_zero (-k - 1)

-- ===== from PairingNetElement.lean =====

/-!
# PairingNetElement — 配对结构 (升维: 方向向量绕圈的互锁几何)

用户映射 (2026-08-26): 圈数和配对 = 相位数值可交换的两个定理 —
圈数 = 单调破坏回 pat0 (有向交叉计数, 已机证 net_cross_winding);
配对 = 升维/向量、矩阵、张量化 (方向向量绕圈的互锁几何)。

配对结构的内容: 方向向量 v(θ) = (cos θ, sin θ) 绕一圈 (升维承载),
cos 分量过零恰 2 次 — 互锁方向 π/2 与 3π/2 (每圈恰 2 个互锁点)。
每零点一圈 (幅角原理) ⟹ 每零点恰 2 个交叉 (配对): 翻转 = 净交叉/2
(value_bridge_net_form 的几何支撑)。

English: pairing net element -- the pairing structure (lift:
interlock geometry of the direction vector circling once). The
direction vector v(θ) = (cos θ, sin θ) crosses the cos = 0 direction
exactly twice per circle (π/2 and 3π/2); one circle per zero
(argument principle) gives two crossings per zero.
-/



/-- **周期内互锁格点**: [0, 2π) 内的互锁格点恰是 k = 0 与 k = 1
    (θ₀ = π/2, θ₁ = 3π/2) — 每圈恰 2 个互锁点 (配对代数核). -/
theorem interlock_in_period_iff (k : ℤ) :
    interlockPhase k ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ↔ k = 0 ∨ k = 1 := by
  unfold interlockPhase
  constructor
  · intro h
    -- 0 ≤ π/2 + kπ ⟹ k ≥ 0; π/2 + kπ < 2π ⟹ k ≤ 1
    have h0 : (0 : ℝ) ≤ Real.pi / 2 + (k : ℝ) * Real.pi := h.1
    have h1 : Real.pi / 2 + (k : ℝ) * Real.pi < 2 * Real.pi := h.2
    have hk0 : 0 ≤ k := by
      by_contra hk
      have hk' : k < 0 := lt_of_not_ge hk
      have hneg : Real.pi / 2 + (k : ℝ) * Real.pi < 0 := by
        have : (k : ℝ) * Real.pi < -Real.pi / 2 := by
          -- k ≤ −1 ⟹ kπ ≤ −π < −π/2
          have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_iff.mpr hk')
          nlinarith [Real.pi_pos]
        linarith
      exact (not_le_of_gt hneg) h0
    have hk1 : k ≤ 1 := by
      by_contra hk
      have hk' : 1 < k := lt_of_not_ge hk
      have hpos : 2 * Real.pi ≤ Real.pi / 2 + (k : ℝ) * Real.pi := by
        -- k ≥ 2 ⟹ kπ ≥ 2π
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk'
        nlinarith [Real.pi_pos]
      linarith
    omega
  · intro h
    rcases h with rfl | rfl
    · constructor <;> nlinarith [Real.pi_pos]
    · constructor <;> nlinarith [Real.pi_pos]

/-- **cos 零点在周期内恰 2 个**: θ ∈ [0, 2π) ∧ cos θ = 0
    ⟹ θ = π/2 ∨ θ = 3π/2 — 互锁方向 (配对: 方向向量绕圈,
    cos 分量过零恰 2 次). -/
theorem cos_zero_period (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ < 2 * Real.pi)
    (hc : Real.cos θ = 0) : θ = Real.pi / 2 ∨ θ = 3 * Real.pi / 2 := by
  have hc' : ∃ k : ℤ, θ = (2 * k + 1) * Real.pi / 2 := Real.cos_eq_zero_iff.mp hc
  rcases hc' with ⟨k, hk⟩
  -- θ = (2k+1)π/2 = π/2 + kπ = interlockPhase k
  have hθ : θ = interlockPhase k := by
    rw [hk]
    unfold interlockPhase
    ring
  have hk2 : k = 0 ∨ k = 1 := by
    apply (interlock_in_period_iff k).mp
    rw [← hθ]
    exact ⟨h0, h1⟩
  rcases hk2 with rfl | rfl
  · left
    rw [hθ]
    unfold interlockPhase
    ring
  · right
    rw [hθ]
    unfold interlockPhase
    norm_num
    ring

/-- **每圈 2 配对 (升维几何)**: 单位圆上 cos 分量为零的方向恰 2 个
    (π/2 与 3π/2) — 配对的方向向量几何: 方向向量绕一圈, 互锁
    方向出现 2 次 (π/2 上穿 + 3π/2 下穿). -/
theorem pairing_per_circle (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ < 2 * Real.pi) :
    Real.cos θ = 0 → θ = Real.pi / 2 ∨ θ = 3 * Real.pi / 2 :=
  cos_zero_period θ h0 h1

/-- **配对分解 (二阶形态)**: 每圈净交叉 2 = 跳变 1 (一阶: 零点
    翻转, jump_cross_one) + 连续行走 1 (邻点交叉) — 配对内部结构:
    每零点 2 交叉的分工 (零点关联交叉 + 邻点交叉, 各 1). -/
theorem pairing_decomp (θ : ℝ) :
    numOfInterlock (θ + Real.pi) - numOfInterlock θ = 1 ∧
      numOfInterlock (θ + 2 * Real.pi) - numOfInterlock (θ + Real.pi) = 1 := by
  constructor
  · rw [jump_cross_one]
    ring
  · have h := jump_cross_one (θ + Real.pi)
    rw [show (θ + Real.pi) + Real.pi = θ + 2 * Real.pi by ring] at h
    omega

/-- **配对分解 × 圈数 (二阶合成)**: K 圈的净交叉 2K = 每圈 2 配对
    (跳变 K + 连续 K) × K 圈 — 圈数定理与配对结构的完整合成
    (theta = num: 圈数 (回 pat0 计数) + 配对 (升维几何) + 一阶
    跳变 (翻转) 三面一体). -/
theorem pairing_decomp_circle (θ : ℝ) (K : ℕ) :
    numOfInterlock (θ + 2 * (K : ℝ) * Real.pi) - numOfInterlock θ = 2 * (K : ℤ) :=
  net_cross_winding θ (K : ℤ)

/-- **配对 × 圈数**: K 圈的净交叉 = 2K = 每圈 2 配对 × K 圈 —
    配对结构与圈数定理的合成 (theta = num 的完整计数:
    圈数 (回 pat0 计数) + 配对 (升维几何) 同源). -/
theorem pairing_net_cross (θ : ℝ) (K : ℤ) :
    numOfInterlock (θ + 2 * (K : ℝ) * Real.pi) - numOfInterlock θ = 2 * K :=
  net_cross_winding θ K

-- ===== from DirectionTensor.lean =====

/-!
# DirectionTensor — 张量化: 多方向分量并存 (正演投影)

方向分量的张量形态: 向量 (u, v) 的正演投影分解
(u⁺, u⁻, v⁺, v⁻) = (max u 0, max (−u) 0, max v 0, max (−v) 0)
— 四个方向分量并存 (u⁺ ⊥ u⁻ 互斥), 无逆运算 (正演投影,
重构 = 正演定理 u = u⁺ − u⁻)。

通用版 (不依赖任何具体函数 — FoldObservation 四方向分量的抽象):
- pos_neg_decomp: 任意实数分解为正负部分 (往返可重构)
- pos_neg_excl: 正负部分互斥 (分量并存 = 张量, 无信息混合)
- quad_zero_iff: 4 分量全零 ⟺ 向量全零 (零点判定的张量形)

English: direction tensor -- the multi-direction component form:
forward projection (u⁺,u⁻,v⁺,v⁻) = (max u 0, max (−u) 0, max v 0,
max (−v) 0), four components coexisting (u⁺ ⊥ u⁻ mutually exclusive),
no inverse operation (reconstruction is a forward theorem).
-/



/-- **正分量**: u⁺ = max u 0 — 正演投影 (方向分量的张量元). -/
def posPart (u : ℝ) : ℝ := max u 0

/-- **负分量**: u⁻ = max (−u) 0 — 正演投影 (负方向的独立分量). -/
def negPart (u : ℝ) : ℝ := max (-u) 0

/-- **正演分解** (重构定理): u = u⁺ − u⁻ — 投影无损失
    (任意实数的正负部分精确重构). -/
theorem pos_neg_decomp (u : ℝ) :
    posPart u - negPart u = u := by
  unfold posPart negPart
  by_cases h : u ≤ 0
  · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -u)]
    simp
  · have hpos : (0 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left hpos, max_eq_right (by linarith : -u ≤ (0 : ℝ))]
    simp

/-- **分量互斥** (张量性): u⁺·u⁻ = 0 — 正负分量并存但不混合
    (方向分量互相独立, 支撑不相交). -/
theorem pos_neg_excl (u : ℝ) :
    posPart u * negPart u = 0 := by
  unfold posPart negPart
  by_cases h : u ≤ 0
  · have h1 : max u 0 = 0 := max_eq_right h
    have h2 : max (-u) 0 = -u := max_eq_left (by linarith : (0 : ℝ) ≤ -u)
    rw [h1, h2]
    simp
  · have h1 : max u 0 = u := max_eq_left (by linarith : (0 : ℝ) ≤ u)
    have h2 : max (-u) 0 = 0 := max_eq_right (by linarith : -u ≤ (0 : ℝ))
    rw [h1, h2]
    simp

/-- **4 方向分量** (张量): (u⁺, u⁻, v⁺, v⁻) — 四个方向分量并存,
    无逆运算 (正演投影). -/
def quadDirection (u v : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (posPart u, negPart u, posPart v, negPart v)

/-- **张量重构** (正演定理): 分量差还原向量 — (u⁺−u⁻, v⁺−v⁻) = (u, v)
    (4 分量 → 向量, 无逆运算: 重构即正演). -/
theorem quad_reconstruct (u v : ℝ) :
    (posPart u - negPart u, posPart v - negPart v) = (u, v) := by
  rw [pos_neg_decomp, pos_neg_decomp]

/-- **全零判定 (张量形)**: 4 分量全零 ⟺ 向量全零 — 零点判定的
    张量读法 (方向分量并存的塌缩判定: 张量全零 ⟺ 源向量零). -/
theorem quad_zero_iff (u v : ℝ) :
    posPart u = 0 ∧ negPart u = 0 ∧ posPart v = 0 ∧ negPart v = 0
      ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hu : u = 0 := by
      calc
        u = posPart u - negPart u := by rw [pos_neg_decomp]
        _ = 0 - 0 := by rw [h.1, h.2.1]
        _ = 0 := by simp
    have hv : v = 0 := by
      calc
        v = posPart v - negPart v := by rw [pos_neg_decomp]
        _ = 0 - 0 := by rw [h.2.2.1, h.2.2.2]
        _ = 0 := by simp
    exact ⟨hu, hv⟩
  · intro h
    constructor
    · rw [h.1]
      simp [posPart]
    · constructor
      · rw [h.1]
        simp [negPart]
      · constructor
        · rw [h.2]
          simp [posPart]
        · rw [h.2]
          simp [negPart]

/-- **投影幂等** (正演): 投影两次 = 投影一次 — 分量是稳定点
    (张量分量经重构后不变, 正演无积累). -/
theorem pos_part_idem (u : ℝ) :
    posPart (posPart u) = posPart u := by
  unfold posPart
  rw [max_eq_left (le_max_right u 0)]

/- ## 卦限族 (n 维方向空间, 2^n 卦限 — 阶数 = 维度) -/

/-- **卦限**: n 维方向空间 x 的符号模式 σ (每维 2 态: 正/负) —
    2^n 个卦限 (一阶 2 阴阳 / 三阶 8 八卦 / 六阶 64 六十四卦). -/
def orthant (n : ℕ) (σ : Fin n → Bool) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, (0 < x i ↔ σ i = true)

/-- **卦限计数**: 卦限数 = 2^n — n 维方向空间的符号模式总数
    (每维 2 态独立). -/
theorem orthant_count (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun]
  rw [Fintype.card_bool]
  rw [Fintype.card_fin]

/-- **卦限互斥**: 非零向量属于唯一卦限 — 不同符号模式不相交
    (σ ≠ τ ⟹ x 不能同时在两者; 符号由值决定). -/
theorem orthant_exclusive {n : ℕ} {σ τ : Fin n → Bool} (x : Fin n → ℝ)
    (hσ : orthant n σ x) (hτ : orthant n τ x) : σ = τ := by
  funext i
  have hiff : (σ i = true ↔ τ i = true) := (hσ i).symm.trans (hτ i)
  cases hσi : σ i <;> cases hτi : τ i <;> simp [hσi, hτi] at hiff ⊢

/-- **n 维全零判定** (张量形): 所有正负分量零 ⟺ 向量零 —
    零点判定的 n 维张量读法 (quad_zero_iff 的通用化). -/
theorem tensor_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    (∀ i : Fin n, posPart (x i) = 0 ∧ negPart (x i) = 0) ↔ (∀ i : Fin n, x i = 0) := by
  constructor
  · intro h i
    calc
      x i = posPart (x i) - negPart (x i) := by rw [pos_neg_decomp]
      _ = 0 - 0 := by rw [(h i).1, (h i).2]
      _ = 0 := by simp
  · intro h i
    constructor
    · rw [h i]
      simp [posPart]
    · rw [h i]
      simp [negPart]

/-- **六阶实例 (64 卦)**: 6 维方向空间恰 64 个卦限 — 六十四卦
    (2⁶): 阶数 = 维度, 卦限 = 2^阶. -/
theorem orthant_count_six :
    Fintype.card (Fin 6 → Bool) = 64 := by
  rw [orthant_count]
  norm_num

/-- **三阶实例 (八卦)**: 3 维方向空间恰 8 个卦限 — 八卦 (2³). -/
theorem orthant_count_three :
    Fintype.card (Fin 3 → Bool) = 8 := by
  rw [orthant_count]
  norm_num

/- ## 对称元: 对偶卦限 (反射/镜像, n 维) -/

/-- **对偶卦限** (对称): σ 的逐维取反 (反射通过原点 — 方向反转
    的 n 维形: 每维 ± 对调). -/
def orthant_dual (n : ℕ) (σ : Fin n → Bool) : Fin n → Bool :=
  fun i => !σ i

/-- **对偶对合** (对称): 两次对偶 = 恒等 — 反射是严格对合
    (镜像两次还原, InvolutionNetElement 的 n 维推广). -/
theorem dual_involution (n : ℕ) (σ : Fin n → Bool) :
    orthant_dual n (orthant_dual n σ) = σ := by
  funext i
  simp [orthant_dual]

/-- **对偶 = 反射** (对称-相位桥): 对偶卦限的 −x = 原卦限的 x
    — 反射通过原点 (方向反转) 交换对偶卦限: 每分量非零时
    orthant(dual σ)(−x) ⟺ orthant σ x. -/
theorem dual_neg {n : ℕ} (σ : Fin n → Bool) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, x i ≠ 0) : orthant n (orthant_dual n σ) (-x) ↔ orthant n σ x := by
  constructor
  · -- 方向 1: orthant (dual σ) (−x) ⟹ orthant σ x
    intro h i
    have hi := h i
    unfold orthant_dual at hi
    by_cases hs : σ i = true
    · -- σ true: 0 < −x i ⟺ false (hi) ⟹ ¬(0 < −x i) ⟹ 0 < x i
      have hnot : ¬(0 < -x i) := by
        intro hpos
        have hiff : (!σ i) = true := hi.mp hpos
        rw [hs] at hiff
        simp at hiff
      have hxlt : ¬(x i < 0) := by
        intro hlt
        exact hnot (by linarith)
      have hposx : 0 < x i := lt_of_le_of_ne (le_of_not_gt hxlt) (by intro hz; exact hx i hz.symm)
      rw [hs]
      simp [hposx]
    · have hs' : σ i = false := Bool.eq_false_of_not_eq_true hs
      -- σ false: 0 < −x i (hi.mpr) ⟹ x i < 0
      have hpos : 0 < -x i := by
        have hiff : (!σ i) = true := by
          rw [hs']
          rfl
        exact hi.mpr hiff
      have hxlt : x i < 0 := by linarith
      rw [hs']
      constructor
      · intro hposx
        linarith
      · intro hf
        exfalso
        simpa using hf
  · -- 方向 2: orthant σ x ⟹ orthant (dual σ) (−x)
    intro h i
    have hi := h i
    unfold orthant_dual
    by_cases hs : σ i = true
    · -- σ true: 0 < x i (hi) ⟹ ¬(0 < −x i) ⟺ !true = false
      have hposx : 0 < x i := hi.mpr hs
      have hnot : ¬(0 < -x i) := by
        intro hneg
        linarith
      rw [hs]
      simp [hnot]
    · have hs' : σ i = false := Bool.eq_false_of_not_eq_true hs
      -- σ false: ¬(0 < x i) (hi) ⟹ x i < 0 (hx) ⟹ 0 < −x i ⟺ !false = true
      have hnotx : ¬(0 < x i) := by
        intro hposx
        rw [hs'] at hi
        have hff : false = true := hi.mp hposx
        simp at hff
      have hxlt : x i < 0 := lt_of_le_of_ne (le_of_not_gt hnotx) (by intro hz; exact hx i hz)
      have hpos : 0 < -x i := by linarith
      rw [hs']
      simp [hpos]

/-- **对偶互斥** (对称): 非零向量不在对偶卦限 — 反射通过原点
    把卦限送到对偶卦限 (不重叠). -/
theorem dual_exclusive {n : ℕ} (hn : 0 < n) (σ : Fin n → Bool) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, x i ≠ 0) : ¬(orthant n σ x ∧ orthant n (orthant_dual n σ) x) := by
  intro h
  have hσ := h.1
  have hσd := h.2
  -- 取一维 x i ≠ 0 (n > 0)
  have hx0 : ∃ i : Fin n, x i ≠ 0 := ⟨⟨0, hn⟩, hx ⟨0, hn⟩⟩
  rcases hx0 with ⟨i, hxi⟩
  have hσi := hσ i
  have hσdi := hσd i
  unfold orthant_dual at hσdi
  by_cases hs : σ i = true
  · -- σ true: hσi 给 0 < x i; hσdi 给 ¬(0 < x i) — 矛盾
    have hpos : 0 < x i := hσi.mpr hs
    have hnot : ¬(0 < x i) := by
      intro hpx
      have hiff : (!σ i) = true := hσdi.mp hpx
      rw [hs] at hiff
      simp at hiff
    exact hnot hpos
  · -- σ false: hσi 给 x i < 0; hσdi 给 0 < x i — 矛盾
    have hs' : σ i = false := Bool.eq_false_of_not_eq_true hs
    have hnotx : ¬(0 < x i) := by
      intro hpx
      rw [hs'] at hσi
      have hff : false = true := hσi.mp hpx
      simp at hff
    have hneg : x i < 0 := lt_of_le_of_ne (le_of_not_gt hnotx) (by intro hz; exact hx i hz)
    have hpos : 0 < x i := by
      rw [hs'] at hσdi
      exact hσdi.mpr rfl
    linarith

/- ## 相位元: 方向向量卦限 (2 维: 4 象限) -/

/-- **象限对偶 = 旋转 π** (相位-对称桥): dirVec(θ+π) = −dirVec θ
    — 旋转 π 把象限送到对偶象限 (对称语言: 对偶卦限; 相位语言:
    半圈). -/
theorem dirVec_dual_rot (θ : ℝ) :
    dirVec (θ + Real.pi) = -dirVec θ := by
  unfold dirVec
  rw [Real.cos_add, Real.sin_add]
  rw [Real.cos_pi, Real.sin_pi]
  ext <;> simp

/- ## 三语言等价组装 -/

/-- **三语言等价 (代数 ⟷ 相位 ⟷ 对称)**: 64 卦限 (六阶) 的每个
    卦限同时有: 代数形 (分量符号模式), 相位形 (方向向量符号),
    对称形 (对偶卦限配对) — 三者互译无损失. -/
theorem trilingual_orthant {n : ℕ} (hn : 0 < n) (σ : Fin n → Bool) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, x i ≠ 0) :
    orthant n σ x → orthant n (orthant_dual n σ) (-x) ∧
      ¬ orthant n (orthant_dual n σ) x := by
  intro h
  constructor
  · exact (dual_neg σ x hx).mpr h
  · intro hd
    exact dual_exclusive hn σ x hx ⟨h, hd⟩

-- ===== 配对几何核 (ZetaNetElement.pairing_geom) =====

/-- **配对几何核**: 互锁方向 π/2 与 3π/2 是 cos 零点且相距 π —
    每圈 2 配对的方向向量几何. -/
theorem pairing_geom :
    Real.cos (Real.pi / 2) = 0 ∧ Real.cos (3 * Real.pi / 2) = 0 ∧
      (3 * Real.pi / 2 - Real.pi / 2 = Real.pi) := by
  constructor
  · rw [Real.cos_pi_div_two]
  · constructor
    · rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
      rw [Real.cos_add]
      rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    · ring

end

end ZeroRelative
