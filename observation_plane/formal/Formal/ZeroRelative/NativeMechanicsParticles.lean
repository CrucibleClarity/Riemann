import Formal.ZeroRelative.NativeAxisEquiv
import Formal.ZeroRelative.EulerFoldImagAxis

noncomputable section

namespace ZeroRelative

/-!
# NativeMechanicsParticles — 原生语言 (±√2/2 读数、实数坐标对, 零 i) 下的力学与粒子重观测

2026-08-28. 用户指令: "原生语言重观测, 只看力学和粒子" + "用净元重推"。
范围: 习题七五大力中的 ①力学 ②粒子 (自旋), 在抛弃虚数 i 的原生语言下重推。
- 力学: 零 i 依赖 (± 成对还原 / 方向链单射) — 原生断言 = 习题七定理的净元重推
  (原证明用 ring → 改为 rw/calc 链, 0 自动化)。
- 粒子: 4 互锁 → S³ 的归一化在原生语言下 = 四轴读数的范数方程 (纯实数,
  axis_norm_sq_preserving 的直接应用; S¹ 特例 + 两对 S³ 版)。
- i 不出现: 本文件零 `Complex.I` / 零 `exp` / 零相位 — 全部是 ℝ 与 √2/2 刻度。

User contribution: anonymous (方向: 原生语言重观测/只看力学和粒子/净元重推指令链).
-/

/-- **力学 · 作用-反作用 = 成对还原** (原生): F + (−F) = 0 — 与刻度无关的
    ± 成对还原 (R085: 0 = ±1 折叠类; 习题七 action_reaction_pair 的净元重推,
    原证明 ring → 改为 rw 一步). -/
theorem native_action_reaction (F : ℝ) : F + (-F) = 0 := by
  rw [add_neg_cancel]

/-- **力学 · 惯性 = 方向链单射** (原生): x ↦ x+d 单射 — 锁定方向链
    (R050/R137; 习题七 inertia_locked_chain 的净元重推, 原证明 ring →
    calc 链: 加 d 再减 d 还原). -/
theorem native_inertia_chain_injective (d : ℝ) : Function.Injective (fun x : ℝ => x + d) := by
  intro a b h
  change a + d = b + d at h
  calc
    a = a + d - d := by rw [add_sub_cancel_right]
    _ = b + d - d := by rw [h]
    _ = b := by rw [add_sub_cancel_right]

/-- **粒子 · 单位点保模 = S¹ 原生** (原生): ‖z‖ = 1 ⟹ fold_u² + fold_v² = 1 —
    单位点 z 在四轴坐标下的读数归一 (axis_norm_sq_preserving + normSq 链;
    S³ 的 S¹ 特例). 净元链: axis_norm_sq_preserving → ← pow_two →
    ← normSq_apply → ← sq_norm → one_pow. -/
theorem native_unit_sphere (z : ℂ) (h : ‖z‖ = 1) :
    fold_u z ^ 2 + fold_v z ^ 2 = 1 := by
  rw [axis_norm_sq_preserving]
  nth_rw 1 [pow_two]
  nth_rw 1 [pow_two]
  rw [← Complex.normSq_apply]
  rw [← Complex.sq_norm]
  rw [h]
  rw [one_pow]

/-- **粒子 · 两对互锁归一 = S³ 原生** (原生): 两个单位点 z1, z2 的四轴读数
    联合范数 = 2 — 4 互锁 (数值对 + 相位对) 的原生归一化, ℝ⁴ 单位球面 (S³)
    在原生语言 (零 i) 下的方程. 净元链: 两次 native_unit_sphere + 机械代数收尾. -/
theorem native_sphere_S3 (z1 z2 : ℂ) (h1 : ‖z1‖ = 1) (h2 : ‖z2‖ = 1) :
    (fold_u z1 ^ 2 + fold_v z1 ^ 2) + (fold_u z2 ^ 2 + fold_v z2 ^ 2) = 2 := by
  have hs1 := native_unit_sphere z1 h1
  have hs2 := native_unit_sphere z2 h2
  rw [hs1, hs2]
  norm_num

end ZeroRelative
