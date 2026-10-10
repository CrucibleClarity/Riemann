import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Pat 视角的路径问题 (iso 30) — 用户 2026-08-19, 从未形式化过

问题: 从同一个起点出发, 达到相同的终点, 路径不同, 给出的数的定义不同吗?

精确结构 (覆盖映射 t ↦ e^(it)):
  回路族 γ_n(t) = e^(2πnt·I), n ∈ ℤ (绕 n 圈)。
  所有回路同起点同终点 (投影): γ_n(0) = γ_n(1) = 1。
  提升: g_n(t) = 2πnt, exp(g_n(t)·I) = γ_n(t)。
  提升终点 (层): g_n(1) = 2πn。

两个层面的答案 (完备性):
  (A) 商层面 (单相位数域): 所有回路给同一个数 — 路径无关 (良定义)。
      不同回路的终点投影相同 (都是 1), 商掉平移对称性后同属 1 的类。
  (B) 提升/层层面 (多相位): 不同回路 (n ≠ m) 提升到不同层 (2πn ≠ 2πm) —
      路径相关, 路径信息保留在层中。

定义完备: 两个层面都表达 — 单相位数 (商, 路径无关) + 多相位层 (提升, 路径相关)。

English: isolation file (iso 30): the path problem -- lift layer path-dependent, quotient layer path-independent -/

noncomputable section
open Complex
open scoped Real

namespace PathProblem

/-- 相位等价: θ₁ 与 θ₂ 相差 2π 的整数倍 (同一相位点的不同代表)。 
English: Phase equivalence: θ₁ and θ₂ differ by an integer multiple of 2π (different representatives of the same phase point). -/
def PhaseEquiv (θ₁ θ₂ : ℝ) : Prop := ∃ n : ℤ, θ₁ = θ₂ + 2 * Real.pi * n

/-- 相位等价是等价关系。 
English: Phase equivalence is an equivalence relation. -/
theorem phaseEquiv_equivalence : Equivalence PhaseEquiv := by
  constructor
  · intro θ
    exact ⟨0, by ring⟩
  · intro θ₁ θ₂ h
    rcases h with ⟨n, hn⟩
    exact ⟨-n, by rw [hn]; simp only [Int.cast_neg]; ring⟩
  · intro θ₁ θ₂ θ₃ h₁₂ h₂₃
    rcases h₁₂ with ⟨n, hn⟩
    rcases h₂₃ with ⟨m, hm⟩
    exact ⟨n + m, by rw [hn, hm]; simp only [Int.cast_add]; ring⟩

/-- 相位商结构 (单相位数域): 商掉平移对称性。 
English: Phase quotient structure (single-phase number domain): quotienting out the translation symmetry. -/
def phaseSetoid : Setoid ℝ := Setoid.mk PhaseEquiv phaseEquiv_equivalence

/-- 回路族: 从投影 1 出发回到投影 1 的 n 圈回路 γ_n(t) = e^(2πnt·I)。 
English: Loop family: the n-turn loop γ_n(t) = e^(2πnt·I) starting from projection 1, returning to projection 1. -/
def loopPath (n : ℤ) (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * n * t * Complex.I)

/-- 同起点: 所有回路从投影 1 出发, γ_n(0) = 1。 
English: Same start: all loops start from projection 1, γ_n(0) = 1. -/
theorem loopPath_start (n : ℤ) : loopPath n 0 = 1 := by
  simp [loopPath]

/-- 同终点 (投影): 所有回路回到投影 1, γ_n(1) = 1。
不同路径, 相同的起点与终点 (投影) — 路径问题的前提。 
English: Same end (projection): all loops return to projection 1, γ_n(1) = 1. Different paths, same start and end (projection) — the premise of the path problem. -/
theorem loopPath_end (n : ℤ) : loopPath n 1 = 1 := by
  -- exp (2πn·I): 2πn·I = ↑n·(2π·I) → exp_int_mul → exp(2π·I)^n = 1
  simp [loopPath]
  have h_eq : 2 * ↑π * ↑n * I = (n : ℂ) * (2 * ↑π * I) := by
    ring
  rw [h_eq, Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  simp

/-- 提升: g_n(t) = 2πnt 是 γ_n 的提升 (exp(g_n(t)·I) = γ_n(t))。 
English: Lift: g_n(t) = 2πnt is a lift of γ_n (exp(g_n(t)·I) = γ_n(t)). -/
theorem loopPath_lift (n : ℤ) (t : ℝ) :
    Complex.exp (2 * Real.pi * n * t * Complex.I) = loopPath n t :=
  rfl

/-- 提升终点 = 层: g_n(1) = 2πn。 
English: Lift endpoint = layer: g_n(1) = 2πn. -/
theorem loopPath_layer (n : ℤ) : 2 * Real.pi * n * 1 = 2 * Real.pi * n := by
  ring

/-- 层层面: 不同回路 (n ≠ m) 提升到不同层 — 路径相关,
路径信息保留在层中 (2πn ≠ 2πm)。 
English: Layer level: different loops (n ≠ m) lift to different layers — path-dependent, path information retained in the layer (2πn ≠ 2πm). -/
theorem loopPath_layer_distinct {n m : ℤ} (h : n ≠ m) :
    2 * Real.pi * n ≠ 2 * Real.pi * m := by
  intro h_eq
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_pos.ne'
  have hn : (n : ℝ) = (m : ℝ) :=
    mul_left_cancel₀ hpi (by simpa [mul_assoc] using h_eq)
  have hnm : n = m := by exact_mod_cast hn
  exact h hnm

/-- 商层面: 所有回路给同一个单相位数 (1 的类) — 路径无关 (良定义)。
不同路径 (任意圈数) 的终点投影相同, 商掉平移对称性后同属一类。 
English: Quotient level: all loops give the same single-phase number (class of 1) — path-independent (well-defined). Different paths (any winding number) project to the same endpoint; after quotienting translation symmetry, same class. -/
theorem loopPath_same_class (n : ℤ) :
    Quotient.mk phaseSetoid (2 * Real.pi * n * 1) = Quotient.mk phaseSetoid 0 := by
  apply Quotient.sound
  -- 2πn ~ 0: 2πn = 0 + 2π·n
  exact ⟨n, by ring⟩

/-- 完备性: 定义同时表达两个层面 —
  (A) 商层面: 不同路径同数 (loopPath_same_class, 路径无关);
  (B) 层层面: 不同路径不同层 (loopPath_layer_distinct, 路径相关)。
  单相位数 (商) 与多相位层 (提升) 都覆盖, 路径问题被完整解决。 
English: Completeness: definition expresses both levels — (A) quotient: different paths, same number (loopPath_same_class, path-independent); (B) layer: different paths, different layers (loopPath_layer_distinct, path-dependent). Both single-phase and multi-phase covered — path problem fully solved. -/
theorem path_problem_complete (n m : ℤ) (h : n ≠ m) :
    Quotient.mk phaseSetoid (2 * Real.pi * n * 1) =
        Quotient.mk phaseSetoid (2 * Real.pi * m * 1) ∧
      2 * Real.pi * n ≠ 2 * Real.pi * m := by
  constructor
  · calc
      Quotient.mk phaseSetoid (2 * Real.pi * n * 1) = Quotient.mk phaseSetoid 0 :=
        loopPath_same_class n
      _ = Quotient.mk phaseSetoid (2 * Real.pi * m * 1) := (loopPath_same_class m).symm
  · exact loopPath_layer_distinct h

end PathProblem
