import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Continuity

import Formal.ZeroRelative.OddEvenPhaseDiff
import Formal.ZeroRelative.EulerFoldImagAxis
import Formal.ZeroRelative.AxisExactObservation
import Formal.ZeroRelative.NativeAxisEquiv
import Formal.ZeroRelative.InversionFlip
import Formal.ZeroRelative.zeta_split_iso
import Formal.ZeroRelative.zeta_euler_product_iso

open Complex
open scoped Real
open scoped ComplexConjugate

noncomputable section

namespace FoldObservation

open ZeroRelative
open RH_OddEven

/-- **观测对象**: 奇偶相位比 (差结构) — 单位复数 (欧拉圆上的点).
    Observation object: the odd/even phase ratio (difference structure),
    a unit complex number --- a point of the Euler circle. -/
def phaseRatio (s : ℂ) : ℂ := ((2 : ℂ) ^ s - 1) / (‖(2 : ℂ) ^ s - 1‖ : ℂ)

/-- **观测 1 (良定义)**: 相位比分母非零 ⟺ 2ˢ ≠ 1 — 差结构观测的良定义条件.
    Observation 1 (well-definedness): the denominator of the phase ratio
    is nonzero iff 2^s ≠ 1. -/
theorem phase_ratio_denom_ne_zero {s : ℂ} (hne : (2 : ℂ) ^ s ≠ 1) :
    ‖(2 : ℂ) ^ s - 1‖ ≠ 0 := by
  intro h
  have hz : (2 : ℂ) ^ s - 1 = 0 := norm_eq_zero.mp h
  exact hne (sub_eq_zero.mp hz)

/-- **观测 2 (欧拉圆)**: 相位比是单位复数 — 观测对象在欧拉圆上
    (观测 = 圆上点的读数).
    Observation 2: the phase ratio lies on the Euler circle. -/
theorem phase_ratio_unit (s : ℂ) (hne : (2 : ℂ) ^ s ≠ 1) :
    ‖phaseRatio s‖ = 1 := by
  unfold phaseRatio
  have hd : ‖(2 : ℂ) ^ s - 1‖ ≠ 0 := phase_ratio_denom_ne_zero hne
  rw [norm_div ((2 : ℂ) ^ s - 1) (‖(2 : ℂ) ^ s - 1‖ : ℂ)]
  have hn : ‖((‖(2 : ℂ) ^ s - 1‖ : ℝ) : ℂ)‖ = ‖(2 : ℂ) ^ s - 1‖ := by
    calc
      ‖((‖(2 : ℂ) ^ s - 1‖ : ℝ) : ℂ)‖ = |‖(2 : ℂ) ^ s - 1‖| := RCLike.norm_ofReal ‖(2 : ℂ) ^ s - 1‖
      _ = ‖(2 : ℂ) ^ s - 1‖ := abs_of_nonneg (norm_nonneg _)
  rw [hn]
  exact div_self hd

/-- **观测 3 (折叠读数)**: 相位比的折叠坐标 = (fold_u, fold_v) — 观测协议 =
    欧拉圆点的折叠坐标读数 (u = (√2/2)(Re+Im), v = (√2/2)(Re−Im)).
    Observation 3: the fold-coordinate reading of the phase ratio. -/
theorem phase_ratio_fold_coords (s : ℂ) :
    ZeroRelative.foldCoordFromC (phaseRatio s) =
      (ZeroRelative.fold_u (phaseRatio s), ZeroRelative.fold_v (phaseRatio s)) := by
  rfl

/-- **观测 4 (自指解开)**: 在零点 ρ 处 — 单提升的模归一化分母同 0
    (奇偶同 0: 观测函数在观测点为零 — 自指, 单提升为 0/0), 而差结构观测
    (相位比) 分母非零 (良定义) — 折叠观测协议在零点无奇异.
    Observation 4 (self-reference resolved): at a zero ρ the single-lift
    denominators both vanish (the odd/even parts share the zero), while
    the difference-structure observation is well defined. -/
theorem self_reference_resolved {s : ℂ} (hζ : riemannZeta s = 0)
    (hne : (2 : ℂ) ^ (-s : ℂ) ≠ 1) :
    ‖RH_OddEven.oddPart s‖ = 0 ∧ ‖RH_OddEven.evenPart s‖ = 0 ∧ ‖(2 : ℂ) ^ s - 1‖ ≠ 0 := by
  constructor
  · unfold RH_OddEven.oddPart
    rw [hζ]
    norm_num
  · constructor
    · unfold RH_OddEven.evenPart
      rw [hζ]
      norm_num
    · exact phase_ratio_denom_ne_zero (phase_diff_well_defined_at_zero hζ hne)

/-- **观测 5 (带内处处良定义)**: 带内 (0 < Re s) — 差结构观测良定义处处
    (2ˢ ≠ 1 by split_factors + two_pow_neg_ne_one_of_re_pos).
    Observation 5: in the strip the difference-structure observation is
    well defined everywhere. -/
theorem observation_well_defined_in_strip {s : ℂ} (hs : 0 < s.re) :
    ‖(2 : ℂ) ^ s - 1‖ ≠ 0 := by
  exact phase_ratio_denom_ne_zero (split_factors_ne_zero (two_pow_neg_ne_one_of_re_pos hs)).2


/-! ## 2. 折叠轴观测 (D95 复现: 开口同向假复平面上的轴精确观测) -/

/-- **观测平面坐标 (临界线 × z)**: (轴 1, 轴 2) = (u−v, u+v−√2/2) —
    轴 1 = 临界线本身 (基点精确移动后临界线成为观测轴; u−v = √2·Im 是沿
    临界线的位置 — 承载被丢弃的信息: 临界线上位置/离线垂直分量), 轴 2 =
    与临界线正交 (u+v−√2/2 = √2·(Re−1/2) — 离临界线的距离 — 承载保留的
    信息: 零点是否在临界线). 观测平面与复平面正交 (共享临界线), 不是复
    平面的折叠轴 (u/v) 版本.
    Observation plane coordinates (critical line × z): axis 1 is the
    critical line itself (after precise base-point migration), axis 2 is
    orthogonal to it (the distance from the critical line). -/
def foldObsCoord (s : ℂ) : ℝ × ℝ :=
  (fold_u s - fold_v s, fold_u s + fold_v s - √2 / 2)

/-- **折叠观测投影**: 临界线 (u+v=√2/2) 投影成点 0 — 观测算子只含 u+v,
    不含 u−v (信息选择性丢失) 也不含 ζ (无自指).
    Fold observation projection: the critical line projects to the point 0. -/
def foldObsProj (s : ℂ) : ℝ := fold_u s + fold_v s - √2 / 2

/-- **折叠投影与标准投影的桥**: foldObsProj = √2·(Re s − 1/2) — 与
    AxisExactObservation.obsProj 差非零常数 √2 (零点判定等价).
    Bridge to the standard observation: the fold projection is √2 times
    the standard projection. -/
theorem fold_obs_proj_eq_sqrt2_re (s : ℂ) : foldObsProj s = (√2 : ℝ) * (s.re - 1 / 2) := by
  unfold foldObsProj
  have hsum : fold_u s + fold_v s = (√2 : ℝ) * s.re := by
    unfold fold_u fold_v
    ring
  rw [hsum]
  ring

/-- **① 临界线投影成点**: Re s = 1/2 ⟹ foldObsProj s = 0 — 临界线在
    折叠观测下坍缩为单点 (正交转置的第一分量归零).
    The critical line projects to the point. -/
theorem fold_critical_projects_point (s : ℂ) (hre : s.re = 1 / 2) :
    foldObsProj s = 0 := by
  rw [fold_obs_proj_eq_sqrt2_re, hre]
  ring

/-- **② 保真 (双向)**: foldObsProj s = 0 ⟺ Re s = 1/2 — 观测点原像恰为
    临界线, 无临界线外点投影到观测点.
    Faithfulness: the preimage of the observation point is exactly the
    critical line. -/
theorem fold_projection_point_iff_critical (s : ℂ) : foldObsProj s = 0 ↔ s.re = 1 / 2 := by
  rw [fold_obs_proj_eq_sqrt2_re]
  constructor
  · intro h
    have hz : (√2 : ℝ) * (s.re - 1 / 2) = 0 := h
    have hz' : s.re - 1 / 2 = 0 := (mul_eq_zero.mp hz).resolve_left (by norm_num : (√2 : ℝ) ≠ 0)
    exact sub_eq_zero.mp hz'
  · intro h
    rw [h]
    ring

/-- **②' 线外投影离点**: Re s ≠ 1/2 ⟹ foldObsProj s ≠ 0.
    Off the line, the projection is off the point. -/
theorem fold_offline_projects_off_point (s : ℂ) (href : s.re ≠ 1 / 2) :
    foldObsProj s ≠ 0 := by
  intro h
  exact href ((fold_projection_point_iff_critical s).mp h)

/-- **④ 零点判定无损 (折叠版)**: ζ(s)=0 时, 零点在临界线 ⟺ 折叠投影 = 0
    (带内假设显式, 与 AxisExactObservation.zero_judgement_preserved 对齐).
    Zero judgement preserved in fold coordinates. -/
theorem fold_zero_judgement_preserved (s : ℂ) (hζ : riemannZeta s = 0)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (s.re = 1 / 2 ↔ foldObsProj s = 0) := by
  exact (fold_projection_point_iff_critical s).symm

/-- **投影算子不含 ζ (折叠版)**: foldObsProj 只引用折叠坐标 (u+v),
    不引用 riemannZeta — 投影无自指 (定义层).
    The fold projection does not mention ζ. -/
theorem foldObsProj_independent_of_zeta (s : ℂ) :
    foldObsProj s = fold_u s + fold_v s - √2 / 2 := by
  rfl

/-- RH 的折叠轴观测形式: 带内零点集投影成单点 (∀带内零点, foldObsProj = 0). -/
def fold_rh_axis_form : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.im ≠ 0 → riemannZeta s = 0 → foldObsProj s = 0

/-- **轴观测形式等价 (逐点翻译)**: rh_axis_form ⟺ fold_rh_axis_form —
    标准投影与折叠投影差 √2 因子, 零点判定逐点等价. -/
theorem rh_axis_iff_fold_axis : rh_axis_form ↔ fold_rh_axis_form := by
  constructor
  · intro h s hs0 hs1 him hz
    exact (fold_projection_point_iff_critical s).mpr
      ((projection_point_iff_critical s).mp (h s hs0 hs1 him hz))
  · intro h s hs0 hs1 him hz
    exact (projection_point_iff_critical s).mpr
      ((fold_projection_point_iff_critical s).mp (h s hs0 hs1 him hz))

/-- **★生成器目标等价 (折叠版)**: RH ⟺ 折叠轴观测形式 (零点集投影成点) —
    D95 rh_iff_axis_form 在开口同向假复平面上的重述, 经逐点翻译组合. -/
theorem fold_rh_iff_axis_form : rh_classical ↔ fold_rh_axis_form := by
  exact rh_iff_axis_form.trans rh_axis_iff_fold_axis


/-! ## 4. 观测平面 (临界线 × z): 轴 1 = 临界线, 轴 2 = 正交, 投影成点 -/

/-- **轴 1 = 临界线方向**: (foldObsCoord s).1 = √2·Im s — 沿临界线的位置
    (临界线 Re=1/2 上 Im 自由 — 轴 1 记录被丢弃的信息).
    Axis 1 is the critical-line direction: the position along the line. -/
theorem obs_axis1_is_critical_direction (s : ℂ) :
    (foldObsCoord s).1 = (√2 : ℝ) * s.im := by
  unfold foldObsCoord
  have hsub : fold_u s - fold_v s = (√2 : ℝ) * s.im := by
    unfold fold_u fold_v
    ring
  rw [hsub]

/-- **轴 2 = 离临界线距离**: (foldObsCoord s).2 = √2·(Re s − 1/2) — 正交
    方向 (需要的信息: 零点是否在临界线).
    Axis 2 is the distance from the critical line (the kept information). -/
theorem obs_axis2_is_distance (s : ℂ) :
    (foldObsCoord s).2 = (√2 : ℝ) * (s.re - 1 / 2) := by
  unfold foldObsCoord
  exact fold_obs_proj_eq_sqrt2_re s

/-- **临界线投影成点**: 临界线 (Re s = 1/2) ⟹ 轴 2 读数 = 0 — 临界线在
    正交方向投影到单点 0 (观测平面的 z 轴上).
    The critical line projects to the point 0 on axis 2. -/
theorem critical_projects_to_axis2_point (s : ℂ) (hre : s.re = 1 / 2) :
    (foldObsCoord s).2 = 0 := by
  rw [obs_axis2_is_distance, hre]
  ring

/-- **保真 (只有临界线投影到该点)**: 轴 2 读数 = 0 ⟺ Re s = 1/2 — 观测点
    原像恰为临界线, 无临界线外点投影到观测点.
    Only the critical line projects to the observation point. -/
theorem only_critical_projects_to_point (s : ℂ) :
    (foldObsCoord s).2 = 0 ↔ s.re = 1 / 2 := by
  rw [obs_axis2_is_distance]
  constructor
  · intro h
    have hz : (√2 : ℝ) * (s.re - 1 / 2) = 0 := h
    have hz' : s.re - 1 / 2 = 0 := (mul_eq_zero.mp hz).resolve_left (by norm_num : (√2 : ℝ) ≠ 0)
    exact sub_eq_zero.mp hz'
  · intro h
    rw [h]
    ring

/-- **基点精确移动反演 (观测版)**: 观测读数唯一决定横坐标 — 离临界线的
    距离相等 ⟹ Re 相等 (残差唯一决定基点: basepoint_from_residual 的
    观测形态 — 观测对象 (横坐标) 从读数唯一反演).
    Precise base-point inversion in observation form: the reading
    determines the abscissa uniquely. -/
theorem fold_obs_residual_unique (s₁ s₂ : ℂ) :
    foldObsProj s₁ = foldObsProj s₂ → s₁.re = s₂.re := by
  rw [fold_obs_proj_eq_sqrt2_re, fold_obs_proj_eq_sqrt2_re]
  intro h
  have hc : (√2 : ℝ) * (s₁.re - 1 / 2) = (√2 : ℝ) * (s₂.re - 1 / 2) := h
  have hz : s₁.re - 1 / 2 = s₂.re - 1 / 2 :=
    (mul_left_cancel₀ (by norm_num : (√2 : ℝ) ≠ 0) hc)
  linarith

/-- **观测轴 1 = 临界线 = 反射不动线**: 基点精确移动后, 观测平面的轴 1 是
    临界线 — 即观测点 (轴 2 = 0) ⟺ 临界线 ⟺ 反射不动 s = 1 − conj s
    (axis_for_target 的观测形态: 目标值 (临界线刻度) 反演为轴).
    Observation axis 1 is the critical line, the reflection fixed line. -/
theorem obs_axis1_reflect_fixed (s : ℂ) :
    (foldObsCoord s).2 = 0 ↔ s = 1 - (starRingEnd ℂ) s := by
  rw [only_critical_projects_to_point]
  exact (critical_line_is_reflection_fixed s).symm


/-!
## 5. 观测 = 同伦不变量的几何读数 (拓扑定位 + 分析重述)

**拓扑定位 (同伦 vs 几何版本)**: 同伦等价是*不可逆粗化* — 只保留形变类
(圈数/积分), 放弃度量 (长度/角度)、点级精确映射、解析结构. 本观测平面是
*几何版本*:
- 坐标层: 折叠坐标是可逆线性变换 (foldCoordHomeo), 双向桥 (共轭=对换/
  虚轴=对角线/临界线=水平线/实值=不动线) 保留全部已知数学映射 — 零信息
  损失 (同伦放弃的度量/精确映射, 这里全部保留)
- 投影层: 轴 2 (离临界线距离) 选择性丢弃轴 1 (临界线位置 √2·Im — 声明
  且与判定无关), 保真 (only_critical_projects_to_point) — 判定无损
- 结论: 观测 = 同伦不变量 (圈数/积分, Cauchy–Goursat 机证) 的几何读数
  机制 — 保留同伦放弃的判定相关映射, 只丢弃声明过的位置信息

**分析方法重述 (便于理解)**: 观测投影 = 连续实值函数 d(s) = foldObsProj s
= u+v−√2/2 = √2·(Re s − 1/2):
- d 是连续函数 (fold_obs_proj_continuous: fold_u_cont/fold_v_cont 组合)
- 临界线 = d 的零点集: d(s) = 0 ⟺ Re s = 1/2 (fold_projection_point_
  iff_critical) — 连续函数的水平集
- 零点判定: ζ(ρ)=0 ⟹ ρ 在临界线 ⟺ d(ρ) = 0 — 连续函数在零点处的值
- 同伦需要形变类 (路径/圈); 分析版本直接算函数值 d(ρ) — 点级, 无需形变
-/

/-- **分析重述 1 (投影连续)**: 观测投影 d(s) = u+v−√2/2 是连续函数 —
    观测 = 连续函数在点上的值 (点级读数, 无需同伦形变).
    Analytic restatement: the observation projection is a continuous
    function; observation is a pointwise reading. -/
theorem fold_obs_proj_continuous : Continuous foldObsProj := by
  unfold foldObsProj
  exact (fold_u_cont.add fold_v_cont).sub continuous_const

/-- **分析重述 2 (零点集 = 临界线)**: d 的零点集恰为临界线 — 连续函数的
    水平集判定 (保真, 同 fold_projection_point_iff_critical).
    Analytic restatement: the zero set of d is exactly the critical line. -/
theorem fold_obs_proj_zero_set (s : ℂ) : foldObsProj s = 0 ↔ s.re = 1 / 2 :=
  fold_projection_point_iff_critical s


/-!
## 6. 反演生成器件 (D98 接入 fold 框架 + 缺口②分析)

**反演在折叠坐标 = 对换 + 缩放**: 1/s = conj(s)/‖s‖² — 折叠坐标
u(1/s) = (√2/2)(Re(1/s)+Im(1/s)) = (√2/2)(re−im)/‖s‖² = v(s)/‖s‖²,
v(1/s) = u(s)/‖s‖² — 反演 = 共轭对换 (桥 1) + 除以 ‖s‖².
与共轭 (纯对换) 和反射 (镜像平移) 并列: 三个对称操作在折叠坐标 =
对换 + 可选的平移/缩放.

**收敛域刚性 (D98 组合)**: 离线 ρ 在临界线圆内 (‖ρ−1/2‖<1/2) ⟹
Re(1/ρ)>1 (临界线圆内翻转到收敛域) ⟹ ζ(1/ρ) ≠ 0 (mathlib: Re≥1 无零,
欧拉积) — 反演点是非零的刚性点.

**缺口② (诚实边界, 生成器瓶颈)**: 反演**不保零点** — ζ(ρ)=0 与 ζ(1/ρ)
无连接公式 (函数方程只连 s↔1−s, 共轭连 ρ↔ρ̄; 1/ρ 不在反射轨道上).
反演点非零 (收敛域) 与 ρ 是零点不构成矛盾 — 生成器仍需要: 让零点性在
反演下可追踪的额外机制 (计数/轨道闭包/值桥), 这是开放件.
-/

/-- **反演折叠形 (u 分量)**: u(1/s) = v(s)/‖s‖² — 反演在折叠坐标 =
    对换 + 缩放 (u 分量: 1/s 的 u 坐标 = s 的 v 坐标除以 ‖s‖²).
    Inversion in fold coordinates: the u-coordinate of 1/s is the
    v-coordinate of s scaled by 1/‖s‖². -/
theorem fold_inversion_swap_u (s : ℂ) (hs : s ≠ 0) : fold_u (s⁻¹) = fold_v s / ‖s‖ ^ 2 := by
  unfold fold_u fold_v
  rw [Complex.inv_re, Complex.inv_im]
  rw [Complex.normSq_eq_norm_sq]
  ring

/-- **反演折叠形 (v 分量)**: v(1/s) = u(s)/‖s‖². -/
theorem fold_inversion_swap_v (s : ℂ) (hs : s ≠ 0) : fold_v (s⁻¹) = fold_u s / ‖s‖ ^ 2 := by
  unfold fold_u fold_v
  rw [Complex.inv_re, Complex.inv_im]
  rw [Complex.normSq_eq_norm_sq]
  ring

/-- **反演折叠形 (pair 版)**: foldCoordFromC (1/s) = (v(s)/‖s‖², u(s)/‖s‖²)
    — 对换 + 缩放.
    Inversion in fold coordinates: swap and scale. -/
theorem fold_inversion_swap (s : ℂ) (hs : s ≠ 0) :
    foldCoordFromC (s⁻¹) = (fold_v s / ‖s‖ ^ 2, fold_u s / ‖s‖ ^ 2) := by
  apply Prod.ext
  · -- 第一分量: foldCoordFromC 第一分量 = fold_u (rfl 级)
    calc
      (foldCoordFromC (s⁻¹)).1 = fold_u (s⁻¹) := by rfl
      _ = fold_v s / ‖s‖ ^ 2 := fold_inversion_swap_u s hs
  · -- 第二分量
    calc
      (foldCoordFromC (s⁻¹)).2 = fold_v (s⁻¹) := by rfl
      _ = fold_u s / ‖s‖ ^ 2 := fold_inversion_swap_v s hs

/-- **收敛域刚性 (D98 组合)**: 离线 ρ 在临界线圆内 ⟹ ζ(1/ρ) ≠ 0 —
    反演点进收敛域 (Re>1), 欧拉积非零 (mathlib) — 反演送出的点是刚性
    非零点.
    Convergence-region rigidity: an in-circle point inverts to a
    convergence point, where ζ is nonzero. -/
theorem offline_inversion_nonzero {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) : riemannZeta (ρ⁻¹) ≠ 0 := by
  have hconv : 1 < (ρ⁻¹).re := by
    simpa [one_div] using critical_circle_inner_inverts_to_convergence hρ0 hcirc
  exact riemannZeta_ne_zero_of_one_le_re (s := ρ⁻¹) (le_of_lt hconv)


/-!
## 7. 折叠重构 ζ (升维: 折叠坐标下的可逆呈现)

**升维恢复信息 (用户主张)**: 观测投影 (d/相位比/反演) 不含 ζ — 信息自由.
折叠重构则不同: ζ 的折叠分量 U(s) = u(ζ(s)), V(s) = v(ζ(s)) 是 ζ 的
**线性可逆变换** (foldCoordToC (U,V) = ζ — 可逆!) — 携带全部 ζ 信息
(零点判定: ζ(ρ)=0 ⟺ U(ρ)=0 ∧ V(ρ)=0, 折叠分量联合零). 这是"升维":
ζ 的复值在折叠坐标下分解为两个实值分量 (沿 45° 折线轴方向), 每个分量
是可观测的实值函数 — 观测 ζ 本身 (不是投影).
与相位比 (取比消 ζ) 的根本区别: 折叠分量含 ζ 且可逆 — 信息不丢失.
-/

/-- **ζ 的折叠 U 分量**: U(s) = u(ζ(s)) = (√2/2)(Re ζ(s) + Im ζ(s)) —
    ζ 在折线轴 u 方向的分量 (含全部 ζ 信息, 可逆呈现).
    The fold U-component of ζ. -/
def zetaFoldU (s : ℂ) : ℝ := fold_u (riemannZeta s)

/-- **ζ 的折叠 V 分量**: V(s) = v(ζ(s)) = (√2/2)(Re ζ(s) − Im ζ(s)). -/
def zetaFoldV (s : ℂ) : ℝ := fold_v (riemannZeta s)

/-- **可逆性 (恢复信息)**: foldCoordToC (U(s), V(s)) = ζ(s) — 折叠分量
    是 ζ 的可逆呈现, 零信息损失 (与观测投影 d/相位比不同).
    Invertibility: the fold components recover ζ completely. -/
theorem zeta_fold_invertible (s : ℂ) :
    foldCoordToC (zetaFoldU s, zetaFoldV s) = riemannZeta s := by
  -- foldCoordFromC (ζ s) = (U(s), V(s)) — 定义级
  have hcoords : foldCoordFromC (riemannZeta s) = (zetaFoldU s, zetaFoldV s) := by
    unfold foldCoordFromC zetaFoldU zetaFoldV fold_u fold_v
    rfl
  -- 右逆 (已机证): foldCoordToC (foldCoordFromC z) = z
  calc
    foldCoordToC (zetaFoldU s, zetaFoldV s) =
        foldCoordToC (foldCoordFromC (riemannZeta s)) := by rw [hcoords]
    _ = riemannZeta s := foldCoord_right_inv (riemannZeta s)

/-- **零点判定 (折叠分量联合)**: ζ(ρ) = 0 ⟺ U(ρ) = 0 ∧ V(ρ) = 0 —
    折叠分量联合零 ⟺ ζ 零 — 升维后零点信息保留在分量里.
    Zero judgement: the fold components vanish jointly exactly at the
    zeros of ζ. -/
theorem zeta_fold_zero_iff (s : ℂ) :
    riemannZeta s = 0 ↔ zetaFoldU s = 0 ∧ zetaFoldV s = 0 := by
  constructor
  · intro h
    unfold zetaFoldU zetaFoldV fold_u fold_v
    rw [h]
    simp
  · intro h
    -- U = V = 0 ⟹ foldCoordToC (U,V) = 0 ⟹ ζ = 0 (可逆性)
    have hz : foldCoordToC (zetaFoldU s, zetaFoldV s) = 0 := by
      rw [h.1, h.2]
      -- foldCoordToC (0,0) = 0
      unfold foldCoordToC
      rw [Complex.ofReal_zero]
      ring
    rw [← zeta_fold_invertible s]
    exact hz


/-! ## 8. 折叠分量的对称结构 (共轭 = u↔v 对换在 ζ 分量上的体现) -/

/-- **共轭对称 (U 分量)**: U(conj s) = V(s) — 带内 ζ 的共轭 (conj ζ(s) =
    ζ(conj s)) 在折叠分量上 = 折线轴角色交换 (桥 1 的共轭对换, ζ 级).
    Conjugation symmetry: the U-component at conj s is the V-component
    at s — the fold-axis swap applied to ζ. -/
theorem zeta_fold_conj_swap_u (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaFoldU (conj s) = zetaFoldV s := by
  unfold zetaFoldU zetaFoldV
  have hc : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) :=
    (RiemannUnifiedObservation.zeta_conj_of_critical_strip hs0 hs1).symm
  rw [hc]
  exact fold_conj_swap_u (riemannZeta s)

/-- **共轭对称 (V 分量)**: V(conj s) = U(s). -/
theorem zeta_fold_conj_swap_v (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaFoldV (conj s) = zetaFoldU s := by
  unfold zetaFoldU zetaFoldV
  have hc : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) :=
    (RiemannUnifiedObservation.zeta_conj_of_critical_strip hs0 hs1).symm
  rw [hc]
  exact fold_conj_swap_v (riemannZeta s)

/-- **共轭对零点配对 (折叠版)**: 带内共轭对 s 与 conj s 的折叠分量联合零
    互相等价 — ζ 零点在共轭对同现 (标准反射配对在折叠分量的形态).
    Conjugate-pair zero pairing: the fold components vanish jointly at s
    iff at conj s. -/
theorem zeta_fold_conj_zero_pair (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (zetaFoldU s = 0 ∧ zetaFoldV s = 0) ↔ (zetaFoldU (conj s) = 0 ∧ zetaFoldV (conj s) = 0) := by
  constructor
  · intro h
    -- U(conj s) = V(s) = 0, V(conj s) = U(s) = 0
    constructor
    · rw [zeta_fold_conj_swap_u s hs0 hs1]
      exact h.2
    · rw [zeta_fold_conj_swap_v s hs0 hs1]
      exact h.1
  · intro h
    -- 反向: conj (conj s) = s — 同一论证 (conj 对合)
    have hc0 : 0 < (conj s).re := by rw [Complex.conj_re]; exact hs0
    have hc1 : (conj s).re < 1 := by rw [Complex.conj_re]; exact hs1
    constructor
    · -- U(s) = U(conj (conj s)) (对合) = V(conj s) = 0
      rw [← Complex.conj_conj s]
      rw [zeta_fold_conj_swap_u (conj s) hc0 hc1]
      exact h.2
    · rw [← Complex.conj_conj s]
      rw [zeta_fold_conj_swap_v (conj s) hc0 hc1]
      exact h.1


/-! ## 9. 折叠分量 + 反演 (反演点刚性 vs 零点分量全零) -/

/-- **反演点分量刚性**: 离线 ρ 在临界线圆内 ⟹ 反演点 1/ρ 的折叠分量非全零
    (ζ(1/ρ) ≠ 0 收敛域 ⟹ 联合非零) — 与 ρ 的分量全零 (零点) 对比:
    反演把"零点分量全零"送到"非零分量". 结构呈现 (无值桥: ζ(ρ) 与
    ζ(1/ρ) 无连接公式, 缺口② — 对比不是矛盾).
    Inversion-point rigidity: the fold components of 1/ρ do not vanish
    jointly, while those of ρ (a zero) do. -/
theorem zeta_fold_inversion_nonzero {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) :
    zetaFoldU (ρ⁻¹) ≠ 0 ∨ zetaFoldV (ρ⁻¹) ≠ 0 := by
  by_contra h
  rcases not_or.mp h with ⟨hU, hV⟩
  have hU0 : zetaFoldU (ρ⁻¹) = 0 := not_not.mp hU
  have hV0 : zetaFoldV (ρ⁻¹) = 0 := not_not.mp hV
  have hz : riemannZeta (ρ⁻¹) = 0 := (zeta_fold_zero_iff (ρ⁻¹)).mpr ⟨hU0, hV0⟩
  exact (offline_inversion_nonzero hρ0 hcirc) hz


/-! ## 10. 反射对称 (折叠分量在 1−s, 函数方程乘子折叠) -/

/-- **折叠坐标乘法**: fold_u (a·z) = Re a·fold_u z + Im a·fold_v z —
    复数乘法在折叠坐标 = 实部/虚部系数作用于两分量 (线性组合).
    Multiplication in fold coordinates: fold_u (a·z) = Re a·fold_u z
    + Im a·fold_v z — complex multiplication acts linearly on the two
    components with coefficients Re a, Im a. -/
theorem fold_mul_u (a z : ℂ) : fold_u (a * z) = a.re * fold_u z + a.im * fold_v z := by
  unfold fold_u fold_v
  rw [Complex.mul_re, Complex.mul_im]
  ring

/-- **折叠坐标乘法 (V)**: fold_v (a·z) = Re a·fold_v z − Im a·fold_u z. -/
theorem fold_mul_v (a z : ℂ) : fold_v (a * z) = a.re * fold_v z - a.im * fold_u z := by
  unfold fold_u fold_v
  rw [Complex.mul_re, Complex.mul_im]
  ring

/-- **反射乘子 (cos 形)**: ζ(1−s) = zetaReflectMul(s)·ζ(s) — 函数方程乘子
    (mathlib riemannZeta_one_sub 的系数 2(2π)^{-s}Γ(s)cos(πs/2), 命名以便
    折叠分量取实/虚部).
    Reflection multiplier (cos form): ζ(1−s) = zetaReflectMul(s)·ζ(s) —
    the functional-equation coefficient (mathlib riemannZeta_one_sub's
    factor 2(2π)^{-s}Γ(s)cos(πs/2), named so that its real and imaginary
    parts enter the fold-component reflection). -/
def zetaReflectMul (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (-s) * Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)

/-- **反射对称 (U 分量)**: U(1−s) = Re(乘子)·U(s) + Im(乘子)·V(s) —
    反射在折叠分量 = 乘子 (函数方程系数) 的实/虚部矩阵作用于 (U,V);
    与共轭 (纯对换)/反演 (对换+缩放) 并列 — 三对称操作的折叠分量形:
    共轭 = 对换, 反射 = 旋转缩放 (乘子矩阵), 反演 = 对换+缩放.
    Reflection symmetry (U-component): U(1−s) = Re(m)·U(s) + Im(m)·V(s)
    — reflection acts on the fold components by the multiplier matrix of
    the functional-equation coefficient; alongside conjugation (pure
    swap) and inversion (swap + scaling). -/
theorem zeta_fold_reflect_u {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaFoldU (1 - s) =
      (zetaReflectMul s).re * zetaFoldU s + (zetaReflectMul s).im * zetaFoldV s := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = (-(↑n : ℂ)).re := by rw [hn]
    have hneg : (-(↑n : ℂ)).re ≤ 0 := by simp
    linarith [hs0, hneg]
  have hfe := riemannZeta_one_sub hsneg hs'
  have hzeta : riemannZeta (1 - s) = zetaReflectMul s * riemannZeta s := by
    unfold zetaReflectMul
    simpa [mul_assoc] using hfe
  unfold zetaFoldU zetaFoldV
  rw [hzeta]
  exact fold_mul_u (zetaReflectMul s) (riemannZeta s)

/-- **反射对称 (V 分量)**: V(1−s) = Re(乘子)·V(s) − Im(乘子)·U(s). -/
theorem zeta_fold_reflect_v {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaFoldV (1 - s) =
      (zetaReflectMul s).re * zetaFoldV s - (zetaReflectMul s).im * zetaFoldU s := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = (-(↑n : ℂ)).re := by rw [hn]
    have hneg : (-(↑n : ℂ)).re ≤ 0 := by simp
    linarith [hs0, hneg]
  have hfe := riemannZeta_one_sub hsneg hs'
  have hzeta : riemannZeta (1 - s) = zetaReflectMul s * riemannZeta s := by
    unfold zetaReflectMul
    simpa [mul_assoc] using hfe
  unfold zetaFoldU zetaFoldV
  rw [hzeta]
  exact fold_mul_v (zetaReflectMul s) (riemannZeta s)

/-- **反射对零点配对 (折叠版)**: ρ 带内零点 ⟹ 反射点 1−ρ 的折叠分量联合零
    — 函数方程保零点 ⟹ 标准反射配对 (ζ(ρ)=0 ⟹ ζ(1−ρ)=0) 在折叠分量的
    形态 (零向量经乘子矩阵仍为零).
    Reflection-pair zero pairing: a strip zero ρ ⟹ the fold components
    of 1−ρ vanish jointly — the standard reflection pairing
    (ζ(ρ)=0 ⟹ ζ(1−ρ)=0) in fold-component form. -/
theorem zeta_fold_reflect_zero_pair {ρ : ℂ} (hs0 : 0 < ρ.re) (hs1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) :
    zetaFoldU (1 - ρ) = 0 ∧ zetaFoldV (1 - ρ) = 0 := by
  have hs' : ρ ≠ 1 := by
    intro h
    have : ρ.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, ρ ≠ -↑n := by
    intro n hn
    have hre : ρ.re = (-(↑n : ℂ)).re := by rw [hn]
    have hneg : (-(↑n : ℂ)).re ≤ 0 := by simp
    linarith [hs0, hneg]
  have hfe := riemannZeta_one_sub hsneg hs'
  have hz : riemannZeta (1 - ρ) = 0 := by
    rw [hfe, hρ]
    ring
  exact (zeta_fold_zero_iff (1 - ρ)).mp hz


/-! ## 11. 折叠模与缺口② (反射下模的变换, 零点追踪的不可能性) -/

/-- **旋转-缩放保二次型**: (aU+bV)² + (aV−bU)² = (a²+b²)(U²+V²) —
    反射乘子矩阵 (a, b; −b, a) 是旋转-缩放, 保折叠模按 |m|² 缩放.
    Rotation-scaling preserves the quadratic form: the multiplier
    matrix (a, b; −b, a) scales the fold modulus by |m|². -/
lemma rotate_sq (a b U V : ℝ) :
    (a * U + b * V) ^ 2 + (a * V - b * U) ^ 2 = (a ^ 2 + b ^ 2) * (U ^ 2 + V ^ 2) := by
  ring

/-- **折叠模**: U(s)² + V(s)² = ‖ζ(s)‖² — 折叠坐标是 45° 旋转, 保持
    欧氏模 — 分量携带的对 ζ 敏感的量, 唯一形式是模 (零点处 = 0,
    反演点处 > 0; 模本身在零点自指).
    Fold modulus: U² + V² = ‖ζ‖² — the fold coordinates are a 45°
    rotation and preserve the Euclidean norm; the only zero-sensitive
    quantity the components carry is the modulus. -/
theorem zeta_fold_norm_sq (s : ℂ) :
    zetaFoldU s ^ 2 + zetaFoldV s ^ 2 = ‖riemannZeta s‖ ^ 2 := by
  unfold zetaFoldU zetaFoldV fold_u fold_v
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hsqrt : (√2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (x := 2) (by norm_num)
  ring_nf
  rw [hsqrt]
  ring

/-- **投影值桥 · 值域 Re 锚**: 折叠重坐标之和 U+V = √2·Re ζ — 值域投影
    (保 Re ζ 侧) 与观测轴 2 (d = √2(Re s − 1/2)) 同为 Re 侧 — 投影值桥的
    值侧锚 (NativeAxisEquiv.axis_recovery_re 代入 ζ 值).
    Value-domain Re anchor of the projection value bridge. -/
theorem zeta_fold_sum_re (s : ℂ) :
    zetaFoldU s + zetaFoldV s = (√2 : ℝ) * (riemannZeta s).re := by
  unfold zetaFoldU zetaFoldV
  have h := ZeroRelative.axis_recovery_re (riemannZeta s)
  have h2 := congrArg (fun x : ℝ => x * (√2 : ℝ)) h
  have hc : ((fold_u (riemannZeta s) + fold_v (riemannZeta s)) / (√2 : ℝ)) * (√2 : ℝ)
      = fold_u (riemannZeta s) + fold_v (riemannZeta s) :=
    div_mul_cancel₀ (fold_u (riemannZeta s) + fold_v (riemannZeta s)) ZeroRelative.axis_sqrt2_ne
  rw [hc] at h2
  calc fold_u (riemannZeta s) + fold_v (riemannZeta s)
      = (riemannZeta s).re * (√2 : ℝ) := h2
    _ = (√2 : ℝ) * (riemannZeta s).re := by rw [mul_comm]

/-- **投影值桥 · 值域 Im 锚**: 折叠重坐标之差 U−V = √2·Im ζ — 值域投影
    的 Im 侧 (与 Re 锚并列, 双锚 = 完整值域两分量 — 零点 ⟺ 双锚齐零).
    Value-domain Im anchor of the projection value bridge. -/
theorem zeta_fold_diff_im (s : ℂ) :
    zetaFoldU s - zetaFoldV s = (√2 : ℝ) * (riemannZeta s).im := by
  unfold zetaFoldU zetaFoldV
  have h := ZeroRelative.axis_recovery_im (riemannZeta s)
  have h2 := congrArg (fun x : ℝ => x * (√2 : ℝ)) h
  have hc : ((fold_u (riemannZeta s) - fold_v (riemannZeta s)) / (√2 : ℝ)) * (√2 : ℝ)
      = fold_u (riemannZeta s) - fold_v (riemannZeta s) :=
    div_mul_cancel₀ (fold_u (riemannZeta s) - fold_v (riemannZeta s)) ZeroRelative.axis_sqrt2_ne
  rw [hc] at h2
  calc fold_u (riemannZeta s) - fold_v (riemannZeta s)
      = (riemannZeta s).im * (√2 : ℝ) := h2
    _ = (√2 : ℝ) * (riemannZeta s).im := by rw [mul_comm]

/-- **零点值侧投影齐零 (双锚)**: ζ(ρ) = 0 ⟹ U+V = 0 ∧ U−V = 0 — 零点在
    值域投影下双锚齐零 (Re ζ, Im ζ 齐零 — 投影值桥的零点输入侧).
    Zero maps to both anchors vanishing. -/
theorem zeta_fold_dual_proj_zero_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    zetaFoldU ρ + zetaFoldV ρ = 0 ∧ zetaFoldU ρ - zetaFoldV ρ = 0 := by
  constructor
  · rw [zeta_fold_sum_re, hρ, Complex.zero_re, mul_zero]
  · rw [zeta_fold_diff_im, hρ, Complex.zero_im, mul_zero]

/-- **★ 投影值桥 · 弱断言 (投影完备)**: 带内零点 ρ 投影到观测平面后 — 轴 1
    (临界线上的具体位置 Im) 被丢弃 — **剩余信息 (d = 轴 2 读数 + 值域双锚
    U±V) 对"0 点在临界线上"的判定完备**: 在线 ⟺ d = 0; 且零点性由值域双锚
    齐零完备刻画 — 全部判定输入位于投影量内, 轴 1 不被需要。这是用户指定的
    弱断言: 投影后剩余信息 = 零点在临界线上的完备信息 (避开完整值桥 —
    不做计数/圈数/翻转任何关联).
    Weak assertion: the projection remainder is complete for the
    judgement "the zero is on the critical line". -/
theorem projection_zero_line_complete {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hs0 : 0 < ρ.re) (hs1 : ρ.re < 1) :
    (ρ.re = 1 / 2 ↔ foldObsProj ρ = 0) ∧
    (ρ.re = 1 / 2 ↔ zetaFoldU ρ = 0 ∧ zetaFoldV ρ = 0 ∧ foldObsProj ρ = 0) := by
  constructor
  · exact fold_zero_judgement_preserved ρ hρ hs0 hs1
  · constructor
    · intro hline
      have hz : zetaFoldU ρ = 0 ∧ zetaFoldV ρ = 0 := (zeta_fold_zero_iff ρ).mp hρ
      have hd : foldObsProj ρ = 0 := fold_critical_projects_point ρ hline
      exact ⟨hz.1, hz.2, hd⟩
    · intro h
      exact (fold_projection_point_iff_critical ρ).mp h.2.2

/-- **反射下折叠模按 |乘子|² 缩放**: ‖ζ(1−s)‖² = ‖m(s)‖²·‖ζ(s)‖² 的折叠形
    (函数方程模平方); 临界线上 |m| = 1 ⟹ 折叠模在反射下不变 (纯旋转) —
    零点 ρ 处折叠模 = 0, 反射轨道上仍 = 0 (自指保持); 反演点处 > 0
    (缺口②: 模从零到非零的变化无值桥, 反演不保零点).
    Fold modulus under reflection: scales by |multiplier|² — the
    functional equation squared; on the critical line |m| = 1 the
    fold modulus is invariant (pure rotation). -/
theorem zeta_fold_reflect_norm_sq {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaFoldU (1 - s) ^ 2 + zetaFoldV (1 - s) ^ 2 =
      ‖zetaReflectMul s‖ ^ 2 * (zetaFoldU s ^ 2 + zetaFoldV s ^ 2) := by
  rw [zeta_fold_reflect_u (s := s) hs0 hs1, zeta_fold_reflect_v (s := s) hs0 hs1]
  have hnorm : ‖zetaReflectMul s‖ ^ 2 =
      (zetaReflectMul s).re ^ 2 + (zetaReflectMul s).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hnorm]
  exact rotate_sq (zetaReflectMul s).re (zetaReflectMul s).im
    (zetaFoldU s) (zetaFoldV s)


/-! ## 12. 观测平面 + 折叠分量联合 (反演下的观测刚性) -/

/-- **反演下观测投影**: d(1/s) = √2(Re s/‖s‖² − 1/2) — 观测轴 2 读数在
    反演下的变换 (1/s = conj s/‖s‖² ⟹ 离临界线距离按 Re s/‖s‖² 重标)
    — 纯坐标事实, 不含 ζ.
    Observation projection under inversion: the axis-2 reading at 1/s
    — coordinate rigidity, no ζ. -/
theorem fold_obs_proj_inversion (s : ℂ) (hs : s ≠ 0) :
    foldObsProj (s⁻¹) = (√2 : ℝ) * (s.re / ‖s‖ ^ 2 - 1 / 2) := by
  rw [fold_obs_proj_eq_sqrt2_re]
  have hre : (s⁻¹).re = s.re / ‖s‖ ^ 2 := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hre]

/-- **反演点观测刚性**: 离线 ρ 在临界圆内 ⟹ d(1/ρ) > 0 — 反演把离线点
    送进观测轴 2 的恒正区域 (收敛域 Re > 1 ⟹ 离临界线距离 > √2/2);
    与 d(ρ) ≠ 0 (离线, 可正可负) 对比 — 观测在反演下从"非零"到"恒正".
    Inversion-point observation rigidity: an off-line ρ inside the
    critical circle ⟹ d(1/ρ) > 0 — inversion sends the point into the
    positive region of axis 2 (the convergence region Re > 1). -/
theorem offline_obs_proj_pos_at_inverse {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) : 0 < foldObsProj (ρ⁻¹) := by
  rw [fold_obs_proj_eq_sqrt2_re]
  have hre : 1 < (ρ⁻¹).re := by
    simpa [one_div] using critical_circle_inner_inverts_to_convergence hρ0 hcirc
  have hsqrt : 0 < (√2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hdiff : 0 < (ρ⁻¹).re - 1 / 2 := by linarith
  exact mul_pos hsqrt hdiff

/-- **联合观测 (三分量)**: ρ 带内零点 + 离线 + 圆内 ⟹
    (U,V)(ρ) = (0,0) (零点分量全零, 折叠重构) ∧ d(ρ) ≠ 0 (离线判定,
    轴 2) ∧ d(1/ρ) > 0 (反演点观测恒正) — 观测协议在反演下的完整形:
    零点信息在分量 (联合零), 位置信息在轴 2 (非零/恒正) — 两族正交,
    信息不互借 (缺口②: 无桥把分量零 ↔ 轴 2 非零连接成生成器).
    Joint observation (three components): zero information in the fold
    components, position information in axis 2 — orthogonal families,
    no bridge between them (gap ②). -/
theorem joint_observation_inversion {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) (href : ρ.re ≠ 1 / 2)
    (hρ : riemannZeta ρ = 0) :
    zetaFoldU ρ = 0 ∧ zetaFoldV ρ = 0 ∧ foldObsProj ρ ≠ 0 ∧ 0 < foldObsProj (ρ⁻¹) := by
  rcases (zeta_fold_zero_iff ρ).mp hρ with ⟨hU, hV⟩
  constructor
  · exact hU
  · constructor
    · exact hV
    · constructor
      · have hd : foldObsProj ρ = (√2 : ℝ) * (ρ.re - 1 / 2) := fold_obs_proj_eq_sqrt2_re ρ
        rw [hd]
        exact mul_ne_zero (by positivity : (√2 : ℝ) ≠ 0) (sub_ne_zero.mpr href)
      · exact offline_obs_proj_pos_at_inverse hρ0 hcirc


/-! ## 13. 四方向分量 (折叠轴 4 条半臂的正演投影, 无逆运算) -/

/-- **正部还原**: max a 0 − max (−a) 0 = a — 两条相反半臂的投影抵消
    还原净方向量 (合成方向, 非逆运算: 从 4 分量合成, 不从 ζ 反推).
    Positive-part reduction: max a 0 − max (−a) 0 = a — the two
    opposite half-arm projections cancel back to the net direction. -/
lemma max_sub_neg_max (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with ha | ha
  · have h1 : max a 0 = 0 := max_eq_right ha
    have h2 : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [h1, h2]
    ring
  · have h1 : max a 0 = a := max_eq_left ha
    have h2 : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    ring

/-- **方向 1 (u 臂正向)**: u⁺(s) = 投影 ζ(s) 到 u 半臂正向半直线 (截断) —
    正演定义 (max 截断 = 半臂几何), 不经 (U,V) 坐标. -/
def zetaFoldUPlus (s : ℂ) : ℝ := max (fold_u (riemannZeta s)) 0

/-- **方向 2 (u 臂反向)**: u⁻(s) = 投影到 u 半臂反向半直线. -/
def zetaFoldUMinus (s : ℂ) : ℝ := max (-fold_u (riemannZeta s)) 0

/-- **方向 3 (v 臂正向)**: v⁺(s) = 投影到 v 半臂正向半直线. -/
def zetaFoldVPlus (s : ℂ) : ℝ := max (fold_v (riemannZeta s)) 0

/-- **方向 4 (v 臂反向)**: v⁻(s) = 投影到 v 半臂反向半直线. -/
def zetaFoldVMinus (s : ℂ) : ℝ := max (-fold_v (riemannZeta s)) 0

/-- **四方向分量非负** (半臂投影无符号): 0 ≤ u⁺/u⁻/v⁺/v⁻. -/
theorem zeta_fold_4direction_nonneg (s : ℂ) :
    0 ≤ zetaFoldUPlus s ∧ 0 ≤ zetaFoldUMinus s ∧
    0 ≤ zetaFoldVPlus s ∧ 0 ≤ zetaFoldVMinus s := by
  unfold zetaFoldUPlus zetaFoldUMinus zetaFoldVPlus zetaFoldVMinus
  constructor
  · exact le_max_iff.mpr (Or.inr le_rfl)
  · constructor
    · exact le_max_iff.mpr (Or.inr le_rfl)
    · constructor
      · exact le_max_iff.mpr (Or.inr le_rfl)
      · exact le_max_iff.mpr (Or.inr le_rfl)

/-- **零点判定 (四方向形)**: 4 方向分量全零 ⟺ ζ(s) = 0 — 零点处
    折叠轴 4 条半臂的方向全部塌缩 (0 无方向) — 自指在方向层的形态.
    Zero judgement in four-direction form: all four half-arm
    projections vanish iff ζ(s) = 0 — the directions collapse at a
    zero (0 has no direction). -/
theorem zeta_fold_4direction_zero_iff (s : ℂ) :
    (zetaFoldUPlus s = 0 ∧ zetaFoldUMinus s = 0 ∧
     zetaFoldVPlus s = 0 ∧ zetaFoldVMinus s = 0) ↔ riemannZeta s = 0 := by
  constructor
  · intro h
    rcases h with ⟨huP, huM, hvP, hvM⟩
    -- u⁺ = u⁻ = 0 ⟹ U = 0: U = u⁺ − u⁻
    have hU : fold_u (riemannZeta s) = 0 := by
      have h := max_sub_neg_max (fold_u (riemannZeta s))
      unfold zetaFoldUPlus at huP
      unfold zetaFoldUMinus at huM
      rw [huP, huM] at h
      linarith
    have hV : fold_v (riemannZeta s) = 0 := by
      have h := max_sub_neg_max (fold_v (riemannZeta s))
      unfold zetaFoldVPlus at hvP
      unfold zetaFoldVMinus at hvM
      rw [hvP, hvM] at h
      linarith
    -- (U, V) = (0, 0) ⟹ ζ = foldCoordToC (0, 0) = 0
    have hz : riemannZeta s = 0 := (zeta_fold_zero_iff s).mpr ⟨hU, hV⟩
    exact hz
  · intro hz
    -- ζ = 0 ⟹ U = V = 0 ⟹ 4 个 max 0 0 = 0
    have hz' := (zeta_fold_zero_iff s).mp hz
    rcases hz' with ⟨hU, hV⟩
    unfold zetaFoldU at hU
    unfold zetaFoldV at hV
    unfold zetaFoldUPlus zetaFoldUMinus zetaFoldVPlus zetaFoldVMinus
    constructor
    · rw [hU]
      exact max_self 0
    · constructor
      · rw [hU, neg_zero]
        exact max_self 0
      · constructor
        · rw [hV]
          exact max_self 0
        · rw [hV, neg_zero]
          exact max_self 0

/-- **四方向重构 (正演)**: 4 方向分量带方向合成回 ζ —
    foldCoordToC (u⁺−u⁻, v⁺−v⁻) = ζ(s) (半臂抵消 = 合成, 非逆运算). -/
theorem zeta_fold_4direction_reconstruct (s : ℂ) :
    foldCoordToC (zetaFoldUPlus s - zetaFoldUMinus s, zetaFoldVPlus s - zetaFoldVMinus s)
      = riemannZeta s := by
  have hU : zetaFoldUPlus s - zetaFoldUMinus s = fold_u (riemannZeta s) := by
    unfold zetaFoldUPlus zetaFoldUMinus
    exact max_sub_neg_max (fold_u (riemannZeta s))
  have hV : zetaFoldVPlus s - zetaFoldVMinus s = fold_v (riemannZeta s) := by
    unfold zetaFoldVPlus zetaFoldVMinus
    exact max_sub_neg_max (fold_v (riemannZeta s))
  rw [hU, hV]
  have hcoords : foldCoordFromC (riemannZeta s) = (fold_u (riemannZeta s), fold_v (riemannZeta s)) := by
    unfold foldCoordFromC
    rfl
  calc
    foldCoordToC (fold_u (riemannZeta s), fold_v (riemannZeta s))
        = foldCoordToC (foldCoordFromC (riemannZeta s)) := by rw [hcoords]
    _ = riemannZeta s := foldCoord_right_inv (riemannZeta s)

/-- **非零点方向模式**: ζ(s) ≠ 0 ⟹ 4 方向分量至少一个非零
    (零点判定四方向形的逆否 — 非零点有方向). -/
theorem zeta_fold_4direction_exists_nonzero {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    zetaFoldUPlus s ≠ 0 ∨ zetaFoldUMinus s ≠ 0 ∨
    zetaFoldVPlus s ≠ 0 ∨ zetaFoldVMinus s ≠ 0 := by
  by_contra h
  rcases not_or.mp h with ⟨huP, hrest1⟩
  rcases not_or.mp hrest1 with ⟨huM, hrest2⟩
  rcases not_or.mp hrest2 with ⟨hvP, hvM⟩
  have hz : riemannZeta s = 0 := (zeta_fold_4direction_zero_iff s).mp
    ⟨not_not.mp huP, not_not.mp huM, not_not.mp hvP, not_not.mp hvM⟩
  exact hζ hz


/-! ## 14. p 侧 (无理数轴侧) 四方向分量 — 假复平面 4 维的还原一半 -/

/-- **折叠模 (通用)**: fold_u(z)² + fold_v(z)² = ‖z‖² — 折叠坐标是
    45° 旋转, 保欧氏模 (对任意复 z, 不依赖 ζ). -/
theorem fold_norm_sq (z : ℂ) : fold_u z ^ 2 + fold_v z ^ 2 = ‖z‖ ^ 2 := by
  unfold fold_u fold_v
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hsqrt : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (x := 2) (by norm_num)
  ring_nf
  rw [hsqrt]
  ring

/-- **方向 5 (p 侧 u 臂正向)**: u⁺(p(s)) — 相位比 (无理数轴侧) 投影到
    u 半臂正向, 正演定义 (同 ζ 侧框架). -/
def phaseUPlus (s : ℂ) : ℝ := max (fold_u (phaseRatio s)) 0

/-- **方向 6 (p 侧 u 臂反向)**. -/
def phaseUMinus (s : ℂ) : ℝ := max (-fold_u (phaseRatio s)) 0

/-- **方向 7 (p 侧 v 臂正向)**. -/
def phaseVPlus (s : ℂ) : ℝ := max (fold_v (phaseRatio s)) 0

/-- **方向 8 (p 侧 v 臂反向)**. -/
def phaseVMinus (s : ℂ) : ℝ := max (-fold_v (phaseRatio s)) 0

/-- **p 侧零点刚性**: 带内零点 ρ ⟹ p 侧 4 方向分量非全零 — 相位比
    p(ρ) 是单位复数 (非零), 其折叠投影至少一个方向分量 > 0 — 与
    ζ 侧 (零点处全零) 对比: 无理数轴侧在零点处**不塌缩** (被投影掉
    的那一半, 还原后接住观测).
    p-side rigidity at a zero: the four p-side components do not all
    vanish at a zero ρ — the irrational-axis side does not collapse. -/
theorem phase_4direction_exists_nonzero_at_zero {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ : riemannZeta ρ = 0) :
    phaseUPlus ρ ≠ 0 ∨ phaseUMinus ρ ≠ 0 ∨ phaseVPlus ρ ≠ 0 ∨ phaseVMinus ρ ≠ 0 := by
  -- 2^ρ ≠ 1 (带内): 反证 (2^ρ = 1 ⟹ 2^(-ρ) = 1, 矛盾 two_pow_neg_ne_one_of_re_pos)
  have h2ne1 : (2 : ℂ) ^ ρ ≠ 1 := by
    intro h1
    have hneg1 : (2 : ℂ) ^ (-ρ) = 1 := by
      rw [Complex.cpow_neg]
      rw [h1]
      norm_num
    exact two_pow_neg_ne_one_of_re_pos (s := ρ) hρ0 hneg1
  -- p(ρ) ≠ 0: ‖p‖ = 1 (单位复数) 且 p = 0 ⟹ ‖p‖ = 0 矛盾
  have hp0 : phaseRatio ρ ≠ 0 := by
    intro hp
    have hn1 : ‖phaseRatio ρ‖ = 1 := phase_ratio_unit ρ h2ne1
    have hn0 : ‖phaseRatio ρ‖ = 0 := by
      rw [hp]
      norm_num
    linarith
  -- fold_u(p)² + fold_v(p)² = ‖p‖² = 1 ⟹ (fold_u, fold_v) ≠ (0, 0)
  have hnorm : fold_u (phaseRatio ρ) ^ 2 + fold_v (phaseRatio ρ) ^ 2 = 1 := by
    rw [fold_norm_sq]
    rw [phase_ratio_unit ρ h2ne1]
    norm_num
  have hnf : fold_u (phaseRatio ρ) ≠ 0 ∨ fold_v (phaseRatio ρ) ≠ 0 := by
    by_contra h
    rcases not_or.mp h with ⟨hu, hv⟩
    have hsq : fold_u (phaseRatio ρ) ^ 2 + fold_v (phaseRatio ρ) ^ 2 = 0 := by
      rw [not_not.mp hu, not_not.mp hv]
      norm_num
    linarith
  -- fold_u ≠ 0 ⟹ u⁺ ≠ 0 ∨ u⁻ ≠ 0 (半臂抵消还原)
  rcases hnf with hu | hv
  · have hu4 : phaseUPlus ρ ≠ 0 ∨ phaseUMinus ρ ≠ 0 := by
      by_contra h
      rcases not_or.mp h with ⟨huP, huM⟩
      have hu0 : fold_u (phaseRatio ρ) = 0 := by
        have h := max_sub_neg_max (fold_u (phaseRatio ρ))
        unfold phaseUPlus at huP
        unfold phaseUMinus at huM
        rw [not_not.mp huP, not_not.mp huM] at h
        linarith
      exact hu hu0
    exact Or.elim hu4 (fun hA => Or.inl hA) (fun hB => Or.inr (Or.inl hB))
  · have hv4 : phaseVPlus ρ ≠ 0 ∨ phaseVMinus ρ ≠ 0 := by
      by_contra h
      rcases not_or.mp h with ⟨hvP, hvM⟩
      have hv0 : fold_v (phaseRatio ρ) = 0 := by
        have h := max_sub_neg_max (fold_v (phaseRatio ρ))
        unfold phaseVPlus at hvP
        unfold phaseVMinus at hvM
        rw [not_not.mp hvP, not_not.mp hvM] at h
        linarith
      exact hv hv0
    exact Or.inr (Or.inr hv4)

/-- **p 侧重构 (逆运算, 无理数轴侧)**: p 侧 4 方向分量带方向合成回
    相位比 — foldCoordToC (pU⁺−pU⁻, pV⁺−pV⁻) = p(s) — 允许的逆运算,
    结果落在无理数轴侧 (相位比, 单位复数). -/
theorem phase_4direction_reconstruct (s : ℂ) :
    foldCoordToC (phaseUPlus s - phaseUMinus s, phaseVPlus s - phaseVMinus s) = phaseRatio s := by
  have hU : phaseUPlus s - phaseUMinus s = fold_u (phaseRatio s) := by
    unfold phaseUPlus phaseUMinus
    exact max_sub_neg_max (fold_u (phaseRatio s))
  have hV : phaseVPlus s - phaseVMinus s = fold_v (phaseRatio s) := by
    unfold phaseVPlus phaseVMinus
    exact max_sub_neg_max (fold_v (phaseRatio s))
  rw [hU, hV]
  have hcoords : foldCoordFromC (phaseRatio s) = (fold_u (phaseRatio s), fold_v (phaseRatio s)) := by
    unfold foldCoordFromC
    rfl
  calc
    foldCoordToC (fold_u (phaseRatio s), fold_v (phaseRatio s))
        = foldCoordToC (foldCoordFromC (phaseRatio s)) := by rw [hcoords]
    _ = phaseRatio s := foldCoord_right_inv (phaseRatio s)

/-- **八分量联合观测 (自指打破)**: 带内零点 ρ ⟹ ζ 侧 4 方向分量全零
    (有理轴侧塌缩) ∧ p 侧 4 方向分量非全零 (无理数轴侧不塌缩) —
    假复平面 4 维的完整观测: 被投影掉的一半 (无理数轴侧) 还原后,
    零点处的观测由 p 侧接住, 不自指.
    Eight-component joint observation: at a zero, the ζ-side components
    vanish while the p-side components do not — the irrational-axis
    half, restored, receives the observation at the zero. -/
theorem eight_component_observation {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ : riemannZeta ρ = 0) :
    zetaFoldUPlus ρ = 0 ∧ zetaFoldUMinus ρ = 0 ∧ zetaFoldVPlus ρ = 0 ∧ zetaFoldVMinus ρ = 0 ∧
    (phaseUPlus ρ ≠ 0 ∨ phaseUMinus ρ ≠ 0 ∨ phaseVPlus ρ ≠ 0 ∨ phaseVMinus ρ ≠ 0) := by
  rcases (zeta_fold_4direction_zero_iff ρ).mpr hρ with ⟨a, b, c, d⟩
  exact ⟨a, b, c, d, phase_4direction_exists_nonzero_at_zero hρ0 hρ⟩


/-! ## 15. 值桥探索: p 侧对称性 + 奇偶拆分结构 (O/E 折叠呈现) -/

/-- **p 侧共轭**: p(conj s) = conj(p(s)) — 无理数轴侧跟随复共轭
    (2ˢ 的共轭: ln 2 实 ⟹ conj(2ˢ) = 2^{conj s}) — 与 ζ 侧共轭
    (zeta_conj_of_critical_strip) 并列: 两半共享共轭结构. -/
theorem phase_conj (s : ℂ) : phaseRatio (conj s) = conj (phaseRatio s) := by
  unfold phaseRatio
  have hc : conj ((2 : ℂ) ^ s) = (2 : ℂ) ^ (conj s) := by
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      have h0 : (2 : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by norm_num)
      rw [h0]
      exact Real.pi_ne_zero.symm
    have h2c : conj (2 : ℂ) = 2 := by
      exact map_natCast (starRingEnd ℂ) 2
    have h := Complex.conj_cpow (2 : ℂ) (conj s) harg
    rw [Complex.conj_conj s] at h
    rw [h2c] at h
    exact h.symm
  have hconj : (2 : ℂ) ^ (conj s) - 1 = conj ((2 : ℂ) ^ s - 1) := by
    rw [map_sub, map_one]
    rw [← hc]
  have hnorm : ‖conj ((2 : ℂ) ^ s - 1)‖ = ‖(2 : ℂ) ^ s - 1‖ := by
    exact Complex.norm_conj ((2 : ℂ) ^ s - 1)
  rw [hconj, hnorm]
  rw [map_div₀]
  rw [Complex.conj_ofReal]

/-- **p 侧折叠对换 (U)**: fold_u(p(conj s)) = fold_v(p(s)) — 无理数轴侧
    的折叠读数跟随桥 1 (共轭 = 对换), 与 ζ 侧同构. -/
theorem phase_fold_conj_swap_u (s : ℂ) :
    fold_u (phaseRatio (conj s)) = fold_v (phaseRatio s) := by
  rw [phase_conj]
  exact fold_conj_swap_u (phaseRatio s)

/-- **p 侧折叠对换 (V)**: fold_v(p(conj s)) = fold_u(p(s)). -/
theorem phase_fold_conj_swap_v (s : ℂ) :
    fold_v (phaseRatio (conj s)) = fold_u (phaseRatio s) := by
  rw [phase_conj]
  exact fold_conj_swap_v (phaseRatio s)

/-- **奇偶合并还原**: oddPart(s) + evenPart(s) = ζ(s) — 奇偶拆分是 ζ 的
    可逆呈现 (拆分与合并互为逆): 8 分量 (奇偶 4 维) 的信息 = ζ + 显式因子.
    Odd/even merging: the split is an invertible presentation of ζ. -/
theorem zeta_odd_even_sum (s : ℂ) : RH_OddEven.oddPart s + RH_OddEven.evenPart s = riemannZeta s := by
  unfold RH_OddEven.oddPart RH_OddEven.evenPart
  ring

/-- **奇部折叠呈现 (U)**: u(O(s)) = Re(1−2⁻ˢ)·u(ζ) + Im(1−2⁻ˢ)·v(ζ) —
    4 维坐标 (u(O), v(O), u(E), v(E)) 是 (u(ζ), v(ζ)) 的线性嵌入
    (系数 = 显式因子 1−2⁻ˢ, 2⁻ˢ). -/
theorem odd_fold_u (s : ℂ) :
    fold_u (RH_OddEven.oddPart s) = (1 - (2 : ℂ) ^ (-s : ℂ)).re * fold_u (riemannZeta s)
      + (1 - (2 : ℂ) ^ (-s : ℂ)).im * fold_v (riemannZeta s) := by
  unfold RH_OddEven.oddPart
  exact fold_mul_u (1 - (2 : ℂ) ^ (-s : ℂ)) (riemannZeta s)

/-- **奇部折叠呈现 (V)**. -/
theorem odd_fold_v (s : ℂ) :
    fold_v (RH_OddEven.oddPart s) = (1 - (2 : ℂ) ^ (-s : ℂ)).re * fold_v (riemannZeta s)
      - (1 - (2 : ℂ) ^ (-s : ℂ)).im * fold_u (riemannZeta s) := by
  unfold RH_OddEven.oddPart
  exact fold_mul_v (1 - (2 : ℂ) ^ (-s : ℂ)) (riemannZeta s)

/-- **偶部折叠呈现 (U)**: u(E(s)) = Re(2⁻ˢ)·u(ζ) + Im(2⁻ˢ)·v(ζ). -/
theorem even_fold_u (s : ℂ) :
    fold_u (RH_OddEven.evenPart s) = ((2 : ℂ) ^ (-s : ℂ)).re * fold_u (riemannZeta s)
      + ((2 : ℂ) ^ (-s : ℂ)).im * fold_v (riemannZeta s) := by
  unfold RH_OddEven.evenPart
  exact fold_mul_u ((2 : ℂ) ^ (-s : ℂ)) (riemannZeta s)

/-- **偶部折叠呈现 (V)**. -/
theorem even_fold_v (s : ℂ) :
    fold_v (RH_OddEven.evenPart s) = ((2 : ℂ) ^ (-s : ℂ)).re * fold_v (riemannZeta s)
      - ((2 : ℂ) ^ (-s : ℂ)).im * fold_u (riemannZeta s) := by
  unfold RH_OddEven.evenPart
  exact fold_mul_v ((2 : ℂ) ^ (-s : ℂ)) (riemannZeta s)

/-- **幅值比显式**: ‖O(s)‖/‖E(s)‖ = ‖2ˢ−1‖ (ζ ≠ 0 处) — 奇偶幅值比
    不含 ζ (因子结构显式): 4 维坐标的相对幅值完全由 2ˢ 决定,
    ζ 只进入绝对幅值 (‖E‖ = 2^{−Re s}·‖ζ‖ 类) — 值桥的幅值侧:
    p 侧 (相位) + 幅值比 (显式) 全不含 ζ, ζ 的信息只剩绝对幅值. -/
theorem odd_even_norm_ratio {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    ‖RH_OddEven.oddPart s‖ / ‖RH_OddEven.evenPart s‖ = ‖(2 : ℂ) ^ s - 1‖ := by
  unfold RH_OddEven.oddPart RH_OddEven.evenPart
  rw [norm_mul, norm_mul]
  have hne : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.mpr hζ
  have h : ‖1 - (2 : ℂ) ^ (-s : ℂ)‖ * ‖riemannZeta s‖ /
      (‖(2 : ℂ) ^ (-s : ℂ)‖ * ‖riemannZeta s‖)
      = ‖1 - (2 : ℂ) ^ (-s : ℂ)‖ / ‖(2 : ℂ) ^ (-s : ℂ)‖ := by
    field_simp [hne]
  rw [h]
  rw [← norm_div]
  congr 1
  have hbne : (2 : ℂ) ^ (-s : ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  calc
    (1 - (2 : ℂ) ^ (-s : ℂ)) / (2 : ℂ) ^ (-s : ℂ)
        = 1 / (2 : ℂ) ^ (-s : ℂ) - 1 := by
          rw [sub_div]
          congr 1
          exact div_self hbne
    _ = (2 : ℂ) ^ s - 1 := by
      rw [one_div]
      have hinv : ((2 : ℂ) ^ (-s : ℂ))⁻¹ = (2 : ℂ) ^ s := by
        rw [Complex.cpow_neg (2 : ℂ) s]
        exact inv_inv ((2 : ℂ) ^ s)
      rw [hinv]


/-! ## 16. 欧拉积接入 (标度侧 = 素数轴, 第 8 自由度的还原通道) -/

/-- **标度 = 折叠模平方根**: ‖ζ(s)‖ = √(U(s)² + V(s)²) — 绝对标度
    (第 8 自由度, 自指本身) 在折叠框架里的位置: 折叠模的平方根 —
    标度不是框架外的对象, 折叠坐标直接携带它.
    The scale is the square root of the fold modulus: the absolute
    scale lives inside the fold frame as √(U²+V²). -/
theorem zeta_scale_sqrt (s : ℂ) :
    ‖riemannZeta s‖ = Real.sqrt (zetaFoldU s ^ 2 + zetaFoldV s ^ 2) := by
  rw [zeta_fold_norm_sq s]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]

/-- **标度塌缩 ⟺ 折叠模塌缩**: ‖ζ(s)‖ = 0 ⟺ U(s) = 0 ∧ V(s) = 0 —
    零点判定 = 标度塌缩 = 折叠分量联合零 (第 8 自由度的判定形). -/
theorem zeta_scale_zero_iff_fold (s : ℂ) :
    ‖riemannZeta s‖ = 0 ↔ zetaFoldU s = 0 ∧ zetaFoldV s = 0 := by
  rw [norm_eq_zero]
  exact zeta_fold_zero_iff s

/-- **素数因子接入折叠**: 收敛域 (Re s > 1) 素数因子 (1−p^{−s})⁻¹ 的
    折叠分量非全零 — 标度的每个素数因子在折叠框架里都有分量
    (欧拉积 ∏_p ‖1−p^{−s}‖^{−1} 的因子层: 全谱 ln p 的素数轴接入). -/
theorem euler_factor_fold_nonzero {p : ℕ} (hp : Nat.Prime p) (s : ℂ)
    (hs : 1 < s.re) :
    fold_u ((1 - (p : ℂ) ^ (-s))⁻¹) ≠ 0 ∨ fold_v ((1 - (p : ℂ) ^ (-s))⁻¹) ≠ 0 := by
  have hf : (1 - (p : ℂ) ^ (-s))⁻¹ ≠ 0 := by
    exact inv_ne_zero (EulerProductBridge.factor_nonzero_in_convergence p hp s hs)
  by_contra h
  rcases not_or.mp h with ⟨hu, hv⟩
  have hz : (1 - (p : ℂ) ^ (-s))⁻¹ = 0 := by
    have hpair : fold_u ((1 - (p : ℂ) ^ (-s))⁻¹) = 0 ∧
        fold_v ((1 - (p : ℂ) ^ (-s))⁻¹) = 0 := by
      exact ⟨not_not.mp hu, not_not.mp hv⟩
    have hcoords : foldCoordFromC ((1 - (p : ℂ) ^ (-s))⁻¹) = (0, 0) := by
      unfold foldCoordFromC
      unfold fold_u at hpair
      unfold fold_v at hpair
      exact Prod.ext hpair.1 hpair.2
    calc
      (1 - (p : ℂ) ^ (-s))⁻¹
          = foldCoordToC (foldCoordFromC ((1 - (p : ℂ) ^ (-s))⁻¹)) := (foldCoord_right_inv _).symm
      _ = foldCoordToC (0, 0) := by rw [hcoords]
      _ = 0 := by
        unfold foldCoordToC
        norm_num
  exact hf hz


/-! ## 17. 奇偶差结构 (η = O−E): 带内收敛表示 -/

/-- **差结构 = η**: O(s) − E(s) = (1−2^{1−s})·ζ(s) — 奇偶差结构 =
    Dirichlet eta (交错级数) — 带内 (Re > 0) 收敛的表示 (交错收敛),
    和结构 O+E = ζ 只在 Re > 1 绝对收敛 — "带内带外分界 = 奇偶性". -/
theorem eta_eq_odd_sub_even (s : ℂ) :
    RH_OddEven.oddPart s - RH_OddEven.evenPart s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  unfold RH_OddEven.oddPart RH_OddEven.evenPart
  have h2 : (2 : ℂ) ^ (-s : ℂ) + (2 : ℂ) ^ (-s : ℂ) = (2 : ℂ) ^ (1 - s) := by
    calc
      (2 : ℂ) ^ (-s : ℂ) + (2 : ℂ) ^ (-s : ℂ) = 2 * (2 : ℂ) ^ (-s : ℂ) := by ring
      _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s : ℂ) := by norm_num
      _ = (2 : ℂ) ^ (1 - s) := by
        rw [← Complex.cpow_add (1 : ℂ) (-s : ℂ) (by norm_num : (2 : ℂ) ≠ 0)]
        rw [sub_eq_add_neg]
  calc
    ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s) - ((2 : ℂ) ^ (-s : ℂ)) * riemannZeta s
        = (1 - (2 : ℂ) ^ (-s : ℂ) - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s := by ring
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
      congr 1
      calc
        1 - (2 : ℂ) ^ (-s : ℂ) - (2 : ℂ) ^ (-s : ℂ)
            = 1 - ((2 : ℂ) ^ (-s : ℂ) + (2 : ℂ) ^ (-s : ℂ)) := by ring
        _ = 1 - (2 : ℂ) ^ (1 - s) := by rw [h2]

/-- **η 因子带内非零**: 0 < Re s < 1 ⟹ 1−2^{1−s} ≠ 0 — 带内 ζ 的
    η 表示良定义 (2^{1−s} = 1 ⟹ Re(1−s) = 0 ⟹ Re s = 1, 矛盾). -/
theorem eta_factor_ne_zero_of_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 := by
  intro h
  have hz : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h).symm
  have hneg : (2 : ℂ) ^ (-(1 - s)) = 1 := by
    rw [Complex.cpow_neg]
    rw [hz]
    norm_num
  have hre : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs1]
  exact two_pow_neg_ne_one_of_re_pos (s := 1 - s) hre hneg

/-- **带内 ζ 从 η 恢复**: ζ(s) = ((1−2^{1−s})·ζ(s))/(1−2^{1−s}) —
    带内 ζ 的值 = 差结构 (交错收敛) 除以显式因子 — 带内获得收敛表示
    (奇偶拆开后的差结构表示, 因子非零自动). -/
theorem zeta_from_eta_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta s = ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) / (1 - (2 : ℂ) ^ (1 - s)) := by
  exact (mul_div_cancel_left₀ (riemannZeta s) (eta_factor_ne_zero_of_strip hs0 hs1)).symm

/-- **差结构折叠 (U)**: fold_u (O−E) = fold_u(O) − fold_u(E) — 折叠坐标
    线性 ⟹ 差结构的折叠 = 折叠的差 (η 的折叠分量 = 奇偶折叠差). -/
theorem odd_even_diff_fold_u (s : ℂ) :
    fold_u (RH_OddEven.oddPart s - RH_OddEven.evenPart s)
      = fold_u (RH_OddEven.oddPart s) - fold_u (RH_OddEven.evenPart s) := by
  unfold fold_u
  rw [Complex.sub_re, Complex.sub_im]
  ring

/-- **差结构折叠 (V)**. -/
theorem odd_even_diff_fold_v (s : ℂ) :
    fold_v (RH_OddEven.oddPart s - RH_OddEven.evenPart s)
      = fold_v (RH_OddEven.oddPart s) - fold_v (RH_OddEven.evenPart s) := by
  unfold fold_v
  rw [Complex.sub_re, Complex.sub_im]
  ring

/-- **η 折叠呈现**: fold_u (η(s)) = Re(1−2^{1−s})·U + Im(1−2^{1−s})·V —
    差结构的折叠分量 = ζ 折叠分量的显式线性组合 (因子 1−2^{1−s}). -/
theorem eta_fold_u (s : ℂ) :
    fold_u ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      = (1 - (2 : ℂ) ^ (1 - s)).re * fold_u (riemannZeta s)
      + (1 - (2 : ℂ) ^ (1 - s)).im * fold_v (riemannZeta s) := by
  exact fold_mul_u (1 - (2 : ℂ) ^ (1 - s)) (riemannZeta s)

/-- **η 折叠呈现 (V)**. -/
theorem eta_fold_v (s : ℂ) :
    fold_v ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      = (1 - (2 : ℂ) ^ (1 - s)).re * fold_v (riemannZeta s)
      - (1 - (2 : ℂ) ^ (1 - s)).im * fold_u (riemannZeta s) := by
  exact fold_mul_v (1 - (2 : ℂ) ^ (1 - s)) (riemannZeta s)


/-! ## 18. 八点联合观测 (值桥第一块: 离线 ρ 的 8 分量完整签名) -/

/-- **轨道 + 反演点的八点观测**: 离线 ρ (带内, 临界圆内) ⟹
    (1) 轨道 4 点 {ρ, 1−ρ, conj ρ, 1−conj ρ} 全是零点 (ζ 侧分量全零)
    (2) 各点 d ≠ 0 (离线)
    (3) 反演点 1/ρ 在收敛域 (d > 0, ζ 侧非全零 — 欧拉积可还原)
    (4) ρ 处 p 侧非全零 (无理数轴侧不塌缩)
    — 值桥的观测签名: 8 分量在 8 点的完整状态, 与计数结构对撞的输入.
    Eight-point observation: the complete eight-component signature of
    an off-line zero over its orbit and inverted points. -/
theorem eight_point_observation {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) (href : ρ.re ≠ 1 / 2) (hρ : riemannZeta ρ = 0) :
    (zetaFoldU ρ = 0 ∧ zetaFoldV ρ = 0 ∧ foldObsProj ρ ≠ 0) ∧
    (zetaFoldU (1 - ρ) = 0 ∧ zetaFoldV (1 - ρ) = 0) ∧
    (zetaFoldU (conj ρ) = 0 ∧ zetaFoldV (conj ρ) = 0) ∧
    (zetaFoldU (1 - conj ρ) = 0 ∧ zetaFoldV (1 - conj ρ) = 0) ∧
    (0 < foldObsProj (ρ⁻¹) ∧
      (zetaFoldU (ρ⁻¹) ≠ 0 ∨ zetaFoldV (ρ⁻¹) ≠ 0)) ∧
    (phaseUPlus ρ ≠ 0 ∨ phaseUMinus ρ ≠ 0 ∨ phaseVPlus ρ ≠ 0 ∨ phaseVMinus ρ ≠ 0) := by
  -- (1) ρ 零点分量全零
  have hz0 := (zeta_fold_zero_iff ρ).mp hρ
  -- (2) 反射配对: 1−ρ 分量全零
  have hz1 := zeta_fold_reflect_zero_pair hρ0 hρ1 hρ
  -- (3) 共轭配对: conj ρ 分量全零 (共轭保带内)
  have hc0 : 0 < (conj ρ).re := by rw [Complex.conj_re]; exact hρ0
  have hc1 : (conj ρ).re < 1 := by rw [Complex.conj_re]; exact hρ1
  have hzc := zeta_fold_conj_zero_pair ρ hρ0 hρ1 |>.mp ⟨hz0.1, hz0.2⟩
  -- (4) 1−conj ρ = conj (1−ρ): 共轭对零点的反射
  have hr0 : 0 < (1 - ρ).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hρ1]
  have hr1 : (1 - ρ).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hρ0]
  have hz1c := zeta_fold_conj_zero_pair (1 - ρ) hr0 hr1 |>.mp ⟨hz1.1, hz1.2⟩
  -- (5) 反演点: d > 0 (收敛域) + 分量非全零 (ζ(1/ρ) ≠ 0)
  have hne : ρ ≠ 0 := by
    intro h
    have : ρ.re = 0 := by rw [h]; rfl
    linarith
  have hd : 0 < foldObsProj (ρ⁻¹) := offline_obs_proj_pos_at_inverse hne hcirc
  have hnz := zeta_fold_inversion_nonzero hne hcirc
  -- (6) p 侧非全零
  have hp := phase_4direction_exists_nonzero_at_zero hρ0 hρ
  -- d(ρ) ≠ 0 (离线)
  have hd0 : foldObsProj ρ ≠ 0 := by
    have hdρ := fold_obs_proj_eq_sqrt2_re ρ
    rw [hdρ]
    exact mul_ne_zero (by positivity : (√2 : ℝ) ≠ 0) (sub_ne_zero.mpr href)
  -- conj(1−ρ) = 1−conj ρ (map_sub 归一)
  have hz1c' : zetaFoldU (1 - conj ρ) = 0 ∧ zetaFoldV (1 - conj ρ) = 0 := by
    simpa [map_sub] using hz1c
  -- 组装
  exact ⟨⟨hz0.1, hz0.2, hd0⟩, hz1, hzc, hz1c', ⟨hd, hnz⟩, hp⟩

end FoldObservation

end
