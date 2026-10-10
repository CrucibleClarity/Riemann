import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality

/-!
# 对称性消去的是什么: 相位叠加 (iso 29)

用户观点 (2026-08-19): "首先需要形式化的一点, 就是对称性消去的是什么, 相位叠加。"

精确数学化 (覆盖映射 t ↦ e^(it) 的结构):
  相位叠加 = 纤维的多值性: 每个点 e^(iθ) 携带 ℵ₀ 个相位代表 {θ + 2πn : n ∈ ℤ}。
  对称性   = 平移 T_n(θ) = θ + 2πn: 保持投影 e^(iθ) 不变 (对称操作只换代表, 不动相位点)。
  消去     = 商掉平移对称性: 每个轨道 (相位叠加的全体代表) 压成一个单相位类;
             多值相位在商空间中变成单值 (Quotient.sound: 所有代表落到同一类)。

每位置叠加多少相位 (讨论, 用户: 全数域叠加, 阿列夫1):
  纤维代表参数 = ℤ (ℵ₀ 个自然数相位, 同 iso 28 card_phaseLayers)。
  但相位参数空间可达全数域: I^(c·I) = e^(-cπ/2) 把 c ∈ ℝ 编码进相位结构
  (iso 28 i_cpow_imaginary_real, 参数映射单射), 每位置参数空间基数 = |ℝ| = 𝔠。
  叠加天花板: 每位置 κ 个选择 (2 ≤ κ ≤ 𝔠) → κ^ℵ₀ = 𝔠 (iso 28 phase_any_choices),
  故无论每位置是 ℵ₀ 个自然数相位、ℵ₁ 个、还是全数域 𝔠 个, 叠加结果都是 𝔠。
  "阿列夫1" 解读: ℵ₁^ℵ₀ = 𝔠 已证 (iso 28 aleph1_pow_aleph0);
  全数域解读: 𝔠^ℵ₀ = 𝔠 (iso 28 continuum_phase_ceiling) — 全数域的叠加还是全数域。

English: isolation file (iso 29): symmetry cancels phase superposition; the single-phase number field -/

noncomputable section
open Complex
open scoped Cardinal Real

namespace SymmetryCancelPhase

/-- 相位代表: 点 e^(iθ) 的第 n 个相位代表 θ + 2πn (n ∈ ℤ, 相位叠加的一个成员)。 
English: Phase representative: the n-th phase representative θ + 2πn of the point e^(iθ) (n ∈ ℤ; a member of the phase superposition). -/
def phaseRepresentative (θ : ℝ) (n : ℤ) : ℝ := θ + 2 * Real.pi * n

/-- 对称性: 平移 T_n(θ) = θ + 2πn 保持单位圆投影 e^(iθ) 不变
    (对称操作只改变相位代表, 不改变相位点 — 这就是 "对称性" 的精确内容)。 
English: Symmetry: the translation T_n(θ) = θ + 2πn preserves the unit-circle projection e^(iθ) (a symmetry operation changes only the phase representative, not the phase point — this is the precise content of “symmetry”). -/
theorem translate_preserves_exp (θ : ℝ) (m : ℤ) :
    Complex.exp (((θ + 2 * Real.pi * m) : ℝ) * Complex.I) =
      Complex.exp (θ * Complex.I) := by
  calc
    Complex.exp (((θ + 2 * Real.pi * m) : ℝ) * Complex.I) =
        Complex.exp ((θ : ℂ) * I + (2 * Real.pi * m : ℝ) * I) := by
      congr 1
      norm_num [Complex.ofReal_add, Complex.ofReal_mul]
      ring
    _ = Complex.exp (θ * I) * Complex.exp ((2 * Real.pi * m : ℝ) * I) := by
      rw [Complex.exp_add]
    _ = Complex.exp (θ * I) * 1 := by
      have hz : (2 * Real.pi * m : ℝ) * I = (m : ℂ) * (2 * Real.pi * I) := by
        norm_num [Complex.ofReal_mul]
        ring
      rw [hz, Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
      simp
    _ = Complex.exp (θ * I) := by simp

/-- 对称操作的复合 = 加法 (T_m ∘ T_n = T_{m+n}, ℤ 群结构)。 
English: Composition of symmetry operations = addition (T_m ∘ T_n = T_{m+n}, the ℤ group structure). -/
theorem translate_comp (θ : ℝ) (m n : ℤ) :
    phaseRepresentative (phaseRepresentative θ n) m = phaseRepresentative θ (m + n) := by
  unfold phaseRepresentative
  simp only [Int.cast_add]
  ring

/-- 纤维的参数是单射: 不同的整数参数给出不同的相位代表 (每点 e^(iθ) 恰有 ℵ₀ 个代表)。 
English: The fiber parameterization is injective: different integer parameters give different phase representatives (each point e^(iθ) has exactly ℵ₀ representatives). -/
theorem phaseRepresentative_injective (θ : ℝ) :
    Function.Injective (fun n : ℤ => phaseRepresentative θ n) := by
  intro a b h
  unfold phaseRepresentative at h
  have hz : 2 * Real.pi * a = 2 * Real.pi * b := by linarith
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hz' : (2 * Real.pi : ℝ) * (a : ℝ) = (2 * Real.pi : ℝ) * (b : ℝ) := by
    simpa using hz
  exact_mod_cast (mul_left_cancel₀ hpi hz')

/-- 相位等价: θ₁ 与 θ₂ 相差 2π 的整数倍 (同一相位点的不同代表 = 相位叠加的成员)。 
English: Phase equivalence: θ₁ and θ₂ differ by an integer multiple of 2π (different representatives of the same phase point = members of the phase superposition). -/
def PhaseEquiv (θ₁ θ₂ : ℝ) : Prop := ∃ n : ℤ, θ₁ = θ₂ + 2 * Real.pi * n

/-- 相位等价是等价关系 (相位叠加的对称群 ℤ 作用)。 
English: Phase equivalence is an equivalence relation (the ℤ action of the symmetry group of phase superposition). -/
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

/-- 相位商结构: 商掉平移对称性得到的 Setoid。 
English: Phase quotient structure: the Setoid obtained by quotienting out the translation symmetry. -/
def phaseSetoid : Setoid ℝ := Setoid.mk PhaseEquiv phaseEquiv_equivalence

/-- 每个代表属于其轨道类: 相位叠加的每个成员都与基点相位等价。 
English: Each representative belongs to its orbit class: every member of the phase superposition is equivalent to the basepoint phase. -/
theorem representative_mem_orbit (θ : ℝ) (n : ℤ) :
    PhaseEquiv (phaseRepresentative θ n) θ := by
  unfold phaseRepresentative
  exact ⟨n, by ring⟩

/-- 消去 = 商: 同一相位点的所有代表 (相位叠加) 商到同一个单相位类。
    — 这就是 "对称性消去相位叠加" 的精确形式:
    平移对称性被商掉, 多值相位变成单值 (单相位)。 
English: Cancellation = quotient: all representatives of a phase point quotient to one single-phase class — the precise form of “symmetry cancels phase superposition”: translation symmetry is quotiented, multi-valued phase becomes single-valued. -/
theorem superposition_collapses_to_single_phase (θ : ℝ) (m : ℤ) :
    Quotient.mk phaseSetoid (phaseRepresentative θ m) = Quotient.mk phaseSetoid θ := by
  exact Quotient.sound (representative_mem_orbit θ m)

/-- 商空间覆盖全部轨道 (消去操作是全的: 每个轨道类都有代表)。 
English: The quotient space covers all orbits (the cancellation is surjective: every orbit class has a representative). -/
theorem phaseEquiv_quotient_surjective :
    Function.Surjective (Quotient.mk phaseSetoid) := by
  intro q
  exact Quotient.inductionOn q (fun θ => ⟨θ, rfl⟩)

/-- 全数域参数空间: 每位置的相位参数可来自全数域 ℝ, 基数 𝔠 = 2^ℵ₀
    (I^(c·I) 给出具体构造, iso 28; "全数域叠加" 的选择空间)。 
English: Full-number-field parameter space: the phase parameter at each position may come from the full number field ℝ, of cardinality 𝔠 = 2^ℵ₀ (I^(c·I) gives an explicit construction, iso 28; the choice space of “full-field superposition”). -/
theorem card_phase_params_real : #ℝ = 𝔠 :=
  Cardinal.mk_real

/-- 全数域叠加的不动点: 每位置叠加全数域 (𝔠 个相位), ℵ₀ 个位置,
叠加结果仍是全数域: 𝔠^ℵ₀ = 𝔠 (iso 28 continuum_phase_ceiling 同款)。 
English: Fixed point of full-field superposition: superposing the full number field (𝔠 phases) at each of ℵ₀ positions still yields the full number field: 𝔠^ℵ₀ = 𝔠 (same as iso 28 continuum_phase_ceiling). -/
theorem continuum_superposition_fixed_point : 𝔠 ^ ℵ₀ = 𝔠 :=
  Cardinal.continuum_power_aleph0

/-- 每位置 ℵ₁ 个相位 (用户: "阿列夫1"): 叠加结果仍是连续统 ℵ₁^ℵ₀ = 𝔠
    (iso 28 aleph1_pow_aleph0 同款; ℵ₁ ≤ 𝔠 恒真, 被天花板吸收)。 
English: ℵ₁ phases per position (the user's “aleph 1”): the superposition remains the continuum, ℵ₁^ℵ₀ = 𝔠 (same as iso 28 aleph1_pow_aleph0; ℵ₁ ≤ 𝔠 always holds and is absorbed by the ceiling). -/
theorem aleph1_superposition : ℵ_ 1 ^ ℵ₀ = 𝔠 := by
  apply le_antisymm
  · calc
      ℵ_ 1 ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ :=
        Cardinal.power_le_power_right Cardinal.aleph_one_le_continuum
      _ = 𝔠 := Cardinal.continuum_power_aleph0
  · calc
      𝔠 = 2 ^ ℵ₀ := Cardinal.two_power_aleph0.symm
      _ ≤ ℵ_ 1 ^ ℵ₀ := Cardinal.power_le_power_right (by
        exact (Cardinal.natCast_lt_aleph0 (n := 2)).le.trans
          (Cardinal.aleph0_le_aleph 1))


/-!
### 无相位叠加的数域 (统一结论, 用户 2026-08-19)

三种路径 — 三桥 (自然数=圈数, 依赖基点)、对称消去 (纤维多值性)、
自然数相位叠加 (每位置未锁定相位) — 本质都是同一个歧义:
覆盖映射 t ↦ e^(it) 的定义模糊 (每点 ℵ₀ 个相位代表)。

因此有必要定义无相位叠加的数域 = 单相位数域:
商空间 Quotient phaseSetoid (商掉平移对称性), 每个类 = 一个轨道
= 单位圆上的一个点 (无歧义)。exp_phase_equiv_iff 给出精确对应:
相位等价 ⟺ 投影相同 (exp 的核 = 2πiℤ, mathlib
exp_eq_exp_iff_exists_int) — 类与投影一一对应, 歧义消除。
-/

/-- 相位等价 ⟺ 同一投影: e^(iθ₁) = e^(iθ₂) ↔ PhaseEquiv θ₁ θ₂
(exp 的核 = 2πiℤ, mathlib exp_eq_exp_iff_exists_int)。
商空间 (无相位叠加数域) 的每个类 = 单位圆上的一个点。 
English: Phase equivalence ⟺ same projection: e^(iθ₁) = e^(iθ₂) ↔ PhaseEquiv θ₁ θ₂ (kernel of exp = 2πiℤ, mathlib exp_eq_exp_iff_exists_int). Each class of the quotient space (the phase-superposition-free number field) is one point of the unit circle. -/
theorem exp_phase_equiv_iff (θ₁ θ₂ : ℝ) :
    Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) ↔ PhaseEquiv θ₁ θ₂ := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      -- θ₁*I = θ₂*I + n*(2π*I) → 虚部: θ₁ = θ₂ + 2πn
      have h_im := congrArg Complex.im hn
      simpa [Complex.ofReal_mul, Complex.ofReal_intCast, mul_comm, mul_left_comm,
        mul_assoc] using h_im⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- θ₁ = θ₂ + 2πn → θ₁*I = θ₂*I + n*(2π*I)
    rw [hn]
    norm_num [Complex.ofReal_add, Complex.ofReal_mul]
    ring

/-- 无相位叠加数域: 每个轨道类对应唯一的投影点 (类 ⟺ 投影一一对应,
歧义消除 — 轨道内所有代表商到同一类, 类间投影不同)。 
English: Phase-superposition-free number field: orbit classes and projected points correspond bijectively (ambiguity removed — all representatives of an orbit quotient to one class, projections differ between classes). -/
theorem single_phase_class_iff_projection (θ₁ θ₂ : ℝ) :
    Quotient.mk phaseSetoid θ₁ = Quotient.mk phaseSetoid θ₂ ↔
      Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
  constructor
  · intro h
    exact (exp_phase_equiv_iff θ₁ θ₂).mpr (Quotient.exact h)
  · intro h
    exact Quotient.sound ((exp_phase_equiv_iff θ₁ θ₂).mp h)


/-!
### 单相位数域的唯一性 (用户: 任何单相位数定义最终与 Pat 同构)

商空间的泛性质: Pat 的单相位数域 = Quotient phaseSetoid (商掉平移对称性)。
任何单相位数定义 = 映射 f : ℝ → X 满足:
  (1) 类上常值 (无相位叠加: 同投影的代表给同一个数);
  (2) 分离 (不同类 → 不同数, 不丢失信息);
  (3) 满射 (覆盖全部数)。
泛性质: f 唯一穿过商空间 (∃! g, f = g ∘ mk), 且 g 是双射 —
所以 X ≃ Quotient phaseSetoid: 所有单相位数定义与 Pat 同构 (唯一性)。
-/

/-- 泛性质 (存在): 类上常值的 f 穿过商空间。 
English: Universal property (existence): a function constant on classes factors through the quotient space. -/
theorem quotient_lift_exists (X : Type) (f : ℝ → X)
    (h : ∀ {θ₁ θ₂ : ℝ}, PhaseEquiv θ₁ θ₂ → f θ₁ = f θ₂) :
    ∃ g : Quotient phaseSetoid → X, f = g ∘ Quotient.mk phaseSetoid := by
  refine ⟨Quotient.lift f (fun _ _ hab => h hab), ?_⟩
  funext θ
  rfl

/-- 泛性质 (唯一): 穿过商的映射唯一。 
English: Universal property (uniqueness): the map through the quotient is unique. -/
theorem quotient_lift_unique (X : Type) (f : ℝ → X)
    (h : ∀ {θ₁ θ₂ : ℝ}, PhaseEquiv θ₁ θ₂ → f θ₁ = f θ₂) :
    ∀ g : Quotient phaseSetoid → X,
      f = g ∘ Quotient.mk phaseSetoid → g = Quotient.lift f (fun _ _ hab => h hab) := by
  intro g hg
  funext q
  induction q using Quotient.inductionOn with
  | h θ =>
    calc
      g (Quotient.mk phaseSetoid θ) = f θ := by
        exact (congrFun hg θ).symm
      _ = Quotient.lift f (fun a b hab => h hab) (Quotient.mk phaseSetoid θ) := rfl

/-- 单相位数域的唯一性: 任何无相位叠加的数定义 f : ℝ → X
(类上常值 + 分离 + 满射) 唯一穿过商空间。 
English: Uniqueness of the single-phase number field: any phase-superposition-free number definition f : ℝ → X (constant on classes + separating + surjective) factors through the quotient space uniquely. -/
theorem single_phase_field_unique (X : Type) (f : ℝ → X)
    (h_const : ∀ {θ₁ θ₂ : ℝ}, PhaseEquiv θ₁ θ₂ → f θ₁ = f θ₂)
    (_h_sep : ∀ {θ₁ θ₂ : ℝ}, f θ₁ = f θ₂ → PhaseEquiv θ₁ θ₂)
    (_h_surj : Function.Surjective f) :
    ∃! g : Quotient phaseSetoid → X, f = g ∘ Quotient.mk phaseSetoid := by
  refine ⟨Quotient.lift f (fun a b hab => h_const hab), ?_, ?_⟩
  · funext θ
    rfl
  · intro g hg
    exact quotient_lift_unique X f (fun {θ₁ θ₂} hab => h_const hab) g hg

/-- 同构: 穿过商空间的映射是双射, X ≃ Pat 单相位数域。
任何单相位数定义都与 Pat 同构 (在同构意义下唯一)。 
English: Isomorphism: the map through the quotient space is a bijection, X ≃ the Pat single-phase number field. Any single-phase number definition is isomorphic to Pat (unique up to isomorphism). -/
theorem single_phase_field_equiv (X : Type) (f : ℝ → X)
    (h_const : ∀ {θ₁ θ₂ : ℝ}, PhaseEquiv θ₁ θ₂ → f θ₁ = f θ₂)
    (h_sep : ∀ {θ₁ θ₂ : ℝ}, f θ₁ = f θ₂ → PhaseEquiv θ₁ θ₂)
    (h_surj : Function.Surjective f) :
    Nonempty (Quotient phaseSetoid ≃ X) := by
  let g : Quotient phaseSetoid → X := Quotient.lift f (fun a b hab => h_const hab)
  have hg_bi : Function.Bijective g := by
    constructor
    · intro a b h
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      apply Quotient.sound
      apply h_sep
      simpa [g] using h
    · intro x
      refine ⟨Quotient.mk phaseSetoid (Classical.choose (h_surj x)), ?_⟩
      simpa [g] using Classical.choose_spec (h_surj x)
  exact ⟨Equiv.ofBijective g hg_bi⟩


/-!
### 1 的投影丢失结构 (用户: 最后未解决的问题)

1 = e^(i·0) = e^(i·2π) = e^(i·4π) = … — 1 的纤维 = {2πn : n ∈ ℤ}
(ℵ₀ 个相位代表全部投影到 1)。投影映射 t ↦ e^(it) 必然丢失
层结构 (圈数 n):

  可证伪性: "投影保持全部结构" (投影是单射) 这个命题为假 —
  q(0) = q(2π) 而 0 ≠ 2π (projection_loses_structure)。
  丢失的精确形式: 1 的纤维 = 2πℤ, ℵ₀ 个代表压成 1 个点 (fiber_of_one)。

这不是缺陷: 丢失的正是平移对称性下的层 (圈数), 即商掉的对象
(iso 29 的 phaseSetoid 商); 单相位数域 = 接受丢层、换取无歧义
(锁定: 每个类选一个代表)。拓扑本质: 覆盖映射的基本群 π₁(S¹) ≅ ℤ,
丢的正是圈数。
-/

/-- 投影不是单射: "投影保持全部结构" 可证伪 —
q(0) = q(2π) 而 0 ≠ 2π (exp 的 2π 周期性)。 
English: The projection is not injective: “the projection preserves all structure” is falsified — q(0) = q(2π) but 0 ≠ 2π (2π-periodicity of exp). -/
theorem projection_loses_structure :
    ¬ Function.Injective (fun t : ℝ => Complex.exp (t * Complex.I)) := by
  intro h
  -- 反例: q(0) = q(2π) 而 0 ≠ 2π
  have h01 : (fun t : ℝ => Complex.exp (t * Complex.I)) 0 =
      (fun t : ℝ => Complex.exp (t * Complex.I)) (2 * Real.pi) := by
    simp [Complex.exp_two_pi_mul_I]
  have hzero : (0 : ℝ) = 2 * Real.pi := h h01
  have hneq : (0 : ℝ) ≠ 2 * Real.pi := ne_of_lt (mul_pos (by norm_num) Real.pi_pos)
  exact hneq hzero

/-- 1 的纤维 = 2πℤ: 投影到 1 的相位代表恰是 {2πn : n ∈ ℤ} (ℵ₀ 个)。
投影把 ℵ₀ 个代表压成 1 个点 — "1 的投影丢失结构" 的精确形式。 
English: The fiber of 1 = 2πℤ: the phase representatives projecting to 1 are exactly {2πn : n ∈ ℤ} (ℵ₀ of them). The projection squeezes ℵ₀ representatives into one point — the precise form of “the projection of 1 loses structure”. -/
theorem fiber_of_one (t : ℝ) :
    Complex.exp (t * Complex.I) = 1 ↔ ∃ n : ℤ, t = 2 * Real.pi * n := by
  rw [← Complex.exp_zero]
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    have h_im := congrArg Complex.im hn
    refine ⟨n, ?_⟩
    simpa [Complex.ofReal_mul, Complex.ofReal_intCast, mul_comm, mul_left_comm,
      mul_assoc] using h_im
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    norm_num [Complex.ofReal_mul]
    ring

end SymmetryCancelPhase
