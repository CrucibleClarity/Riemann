import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

import Formal.ZeroRelative.proof
import Formal.ZeroRelative.FoldObservation

open Metric
open Complex

open PrimeCircle.RiemannUnifiedObservation.RiemannUnifiedObservation.RiemannUnifiedObservation

noncomputable section

namespace EtaPhaseSplit

/-! ## 层 2: η 路径/因子路径与提升 (端点项对账的路径层)

η = 因子·ζ (因子 = 1 − 2^{1−s}) 沿临界线 1/2 + T·s·i 的单位化路径,
以及因子自身单位化路径的连续提升 — etaLift/factorLift (模式:
proof.lean 的 uPath/uLift, isCoveringMap_exp.liftPath)。
配套: 层 1 单位分解 (eta_unit_split) ⟹ 点级
exp(etaLift s) = exp(factorLift s) · exp(uLift s) ⟹ 提升差 ∈ expKernel
(层 3); 连续+连通 ⟹ 常数层 ⟹ 端点差可加 (层 4)。
-/

/-- **因子沿临界线非零**: 1 − 2^{1−s} ≠ 0 (s = 1/2 + ti) —
    带内 (0 < Re < 1) 由 eta_factor_ne_zero_of_strip, 点级版本 (无路径). -/
theorem factor_ne_zero_on_line (t : ℝ) :
    (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) ≠ 0 := by
  apply FoldObservation.eta_factor_ne_zero_of_strip
  · norm_num
  · norm_num

/-- **因子单位化路径**: 因子/‖因子‖ 沿临界线 1/2 + T·s·i —
    连续, 值在 ℂ\{0} (因子带内非零). -/
def factorPath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I))) /
      ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)))‖ : ℂ),
    by
      exact div_ne_zero (factor_ne_zero_on_line (T * s.1))
        (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (factor_ne_zero_on_line (T * s.1))))⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hmain : Continuous (fun w : ℂ => (2 : ℂ) ^ (1 - w)) := by
      have hdef : (fun w : ℂ => (2 : ℂ) ^ (1 - w)) = (fun w : ℂ => Complex.exp (Complex.log 2 * (1 - w))) := by
        funext w
        rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      rw [hdef]
      fun_prop
    have hcpow : Continuous (fun s : ℝ => (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I))) :=
      hmain.comp hsfun
    have hfac : Continuous (fun s : ℝ => ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I))) : ℂ)) :=
      Continuous.sub continuous_const hcpow
    have hnorm : Continuous (fun s : ℝ => (‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)))‖ : ℂ)) :=
      continuous_ofReal.comp hfac.norm
    have hunitOn : ContinuousOn (fun s : ℝ =>
        (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I))) /
          ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)))‖) (Set.Icc 0 1) := by
      refine hfac.continuousOn.div hnorm.continuousOn ?_
      intro s hs
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (factor_ne_zero_on_line (T * s)))
    have hunit : Continuous (fun s : unitInterval =>
        (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I))) /
          ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)))‖) :=
      hunitOn.restrict
    exact Continuous.subtype_mk hunit
      (fun s => div_ne_zero (factor_ne_zero_on_line (T * s.1))
        (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (factor_ne_zero_on_line (T * s.1)))))

/-- **η 单位化路径**: η/‖η‖ = (因子/‖因子‖)·(ζ/‖ζ‖) 沿临界线 —
    直接定义为两个连续单位化路径的乘积 (层 1 分解的路径版, 连续性自动). -/
def etaPath (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨((factorPath T s : {z : ℂ // z ≠ 0}).1) * ((uPath T hz s : {z : ℂ // z ≠ 0}).1),
    by
      exact mul_ne_zero (factorPath T s).2 (uPath T hz s).2⟩
  continuous_toFun := by
    have hcp : Continuous (fun s : unitInterval => ((factorPath T s : {z : ℂ // z ≠ 0}).1 : ℂ)) := by
      simpa using (factorPath T).continuous.subtype_val
    have hcu : Continuous (fun s : unitInterval => ((uPath T hz s : {z : ℂ // z ≠ 0}).1 : ℂ)) := by
      simpa using (uPath T hz).continuous.subtype_val
    exact Continuous.subtype_mk (Continuous.mul hcp hcu)
      (fun s => mul_ne_zero (factorPath T s).2 (uPath T hz s).2)

/-- **η 单位化的提升起点** (η(0)/(η(0)‖) 的对数). -/
noncomputable def etaLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : ℂ :=
  Complex.log ((etaPath T hz 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_etaLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    Complex.exp (etaLift0 T hz) = (etaPath T hz 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [etaLift0]
  exact Complex.exp_log (etaPath T hz 0).2

private lemma etaLift_γ0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    etaPath T hz 0 = (⟨Complex.exp (etaLift0 T hz), Complex.exp_ne_zero (etaLift0 T hz)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_etaLift0 T hz).symm

/-- **η 的连续幅角提升**: exp(θ_η(s)) = η/‖η‖ (1/2 + T·s·i). -/
noncomputable def etaLift (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (etaPath T hz) (etaLift0 T hz) (etaLift_γ0 T hz)

/-- **提升性质**: exp(θ_η(s)) = η/‖η‖ (1/2 + T·s·i). -/
lemma etaLift_lifts (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (etaLift T hz s) = (etaPath T hz s : {z : ℂ // z ≠ 0}).1 := by
  have h := (isCoveringMap_exp.liftPath_lifts (etaPath T hz) (etaLift0 T hz) (etaLift_γ0 T hz))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [etaLift]
  simpa using hs

/-- **提升起点**: θ_η(0) = log 起点. -/
lemma etaLift_zero (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    etaLift T hz 0 = etaLift0 T hz := by
  exact isCoveringMap_exp.liftPath_zero (etaPath T hz) (etaLift0 T hz) (etaLift_γ0 T hz)

/-- **因子单位化的提升起点** (因子(0)/‖因子(0)‖ 的对数). -/
noncomputable def factorLift0 (T : ℝ) : ℂ :=
  Complex.log ((factorPath T 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_factorLift0 (T : ℝ) :
    Complex.exp (factorLift0 T) = (factorPath T 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [factorLift0]
  exact Complex.exp_log (factorPath T 0).2

private lemma factorLift_γ0 (T : ℝ) :
    factorPath T 0 = (⟨Complex.exp (factorLift0 T), Complex.exp_ne_zero (factorLift0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_factorLift0 T).symm

/-- **因子的连续幅角提升**: exp(θ_因子(s)) = 因子/‖因子‖ (1/2 + T·s·i). -/
noncomputable def factorLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (factorPath T) (factorLift0 T) (factorLift_γ0 T)

/-- **提升性质**: exp(θ_因子(s)) = 因子/‖因子‖ (1/2 + T·s·i). -/
lemma factorLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (factorLift T s) = (factorPath T s : {z : ℂ // z ≠ 0}).1 := by
  have h := (isCoveringMap_exp.liftPath_lifts (factorPath T) (factorLift0 T) (factorLift_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [factorLift]
  simpa using hs

/-- **提升起点**: θ_因子(0) = log 起点. -/
lemma factorLift_zero (T : ℝ) :
    factorLift T 0 = factorLift0 T := by
  exact isCoveringMap_exp.liftPath_zero (factorPath T) (factorLift0 T) (factorLift_γ0 T)



/-- **层 1: 单位分解 (乘积版)** — (u·v)/‖u·v‖ = (u/‖u‖)·(v/‖v‖)
    通用: norm_mul + ← ofReal_mul + div_mul_div_comm. 实例: η = 因子·ζ,
    etaPath 即定义为 factorPath·uPath 的乘积 (层 2), 故 η 侧单位分解 = 本引理. -/
lemma unit_split_of_mul (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v) / (‖u * v‖ : ℂ) = (u / (‖u‖ : ℂ)) * (v / (‖v‖ : ℂ)) := by
  rw [norm_mul]
  rw [Complex.ofReal_mul]
  rw [div_mul_div_comm]

/-! ## 层 3: 点级 exp 恒等式 (η = 因子·ζ 的相位加法核心)

η/‖η‖ = (因子/‖因子‖)·(ζ/‖ζ‖) (层 1) 提升后逐点:
exp(θ_η(s)) = exp(θ_因子(s) + θ_ζ(s)) — η 侧幅角 = 因子幅角 + ζ 幅角
(η 侧原值, 零同构/零分析 — 纯 exp 加法). -/

/-- **层 3a: exp(θ_η) = exp(θ_因子)·exp(θ_ζ)** — 点级, η = 因子·ζ 的
    相位加法的 exp 形态: 提升差 ∈ expKernel 的输入 (先证 exp 恒等,
    再证差 ∈ 2πiℤ). -/
theorem etaLift_exp_eq_mul (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (etaLift T hz s) =
      Complex.exp (factorLift T s) * Complex.exp (uLift T hz s) := by
  rw [etaLift_lifts, factorLift_lifts, uLift_lifts]
  rfl

/-- **层 3b: 提升差 ∈ expKernel** — η 侧提升 = 因子提升 + ζ 提升 + 2πiℤ
    (exp 恒等 ⟹ exp 差 = 1 ⟹ expKernel). -/
theorem etaLift_factorLift_uLift_diff_expKernel (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    etaLift T hz s - (factorLift T s + uLift T hz s) ∈ expKernel := by
  change Complex.exp (etaLift T hz s - (factorLift T s + uLift T hz s)) = 1
  rw [Complex.exp_sub]
  rw [Complex.exp_add]
  rw [etaLift_exp_eq_mul T hz s]
  rw [div_self (mul_ne_zero (Complex.exp_ne_zero (factorLift T s))
      (Complex.exp_ne_zero (uLift T hz s)))]

/-- **通用群元: 减法分配** — (a−b) + (c−d) = (a+c) − (b+d)
    (任意 AddCommGroup, 手写: sub_eq_add_neg ×2 + neg_add_rev + 结合/交换律). -/
lemma sub_add_sub {G : Type*} [AddCommGroup G] (a b c d : G) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  -- 纯群记号 (只有 + −; 无虚数/无理数定义) — 显式 rw 链 (sub_eq_add_neg 展开
  -- + neg_add_rev + 结合/交换律), 零 simp/ring/abel.
  rw [sub_eq_add_neg]
  rw [sub_eq_add_neg]
  rw [sub_eq_add_neg]
  have hneg : -(b + d) = -b + -d := by
    rw [neg_add_rev]
    rw [add_comm]
  rw [hneg]
  rw [add_assoc]
  rw [add_assoc]
  rw [add_comm (-b) (c + -d)]
  rw [add_assoc]
  rw [add_comm a (c + (-d + -b))]
  rw [add_comm (-d) (-b)]
  rw [add_comm]

/-! ## 层 4: 端点差可加 (端点项对账核心)

f = θ_η − (θ_因子 + θ_ζ) 连续 + exp f = 1 (层 3b expKernel) ⟹ f 常数
(IsPreconnected.constant, 模式照抄 proof.lean T6d) ⟹ f(0) = f(1) ⟹
Δθ_η = Δθ_因子 + Δθ_ζ — η 侧圈数 = 因子圈数 + ζ 圈数 (端点项对账的起点).
-/

/-- **层 4: η 侧端点差可加** — Δθ_η = Δθ_因子 + Δθ_ζ:
    f(s) = θ_η(s) − (θ_因子(s) + θ_ζ(s)) ∈ expKernel (层 3b) ⟹
    f 连续入离散集 ⟹ IsPreconnected.constant ⟹ f(0) = f(1) ⟹ 端点差可加,
    无条件 (除 hz: 路径上 ζ ≠ 0). -/
theorem etaLift_endpoint_add (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    etaLift T hz 1 - etaLift T hz 0 =
      (factorLift T 1 - factorLift T 0) + (uLift T hz 1 - uLift T hz 0) := by
  let f : unitInterval → ℂ := fun s => etaLift T hz s - (factorLift T s + uLift T hz s)
  have hk : ∀ s : unitInterval, f s ∈ expKernel := by
    intro s
    dsimp [f]
    exact etaLift_factorLift_uLift_diff_expKernel T hz s
  let f' : unitInterval → {z : ℂ // z ∈ expKernel} := fun s => ⟨f s, hk s⟩
  have hf' : Continuous f' := by
    have hf : Continuous f := by
      dsimp [f]
      exact (etaLift T hz).continuous.sub ((factorLift T).continuous.add (uLift T hz).continuous)
    exact Continuous.subtype_mk hf (fun s => hk s)
  have hc : f' 0 = f' 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hf'.continuousOn (by trivial) (by trivial)
  have hf01 : f 0 = f 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  dsimp [f] at hf01
  calc
    etaLift T hz 1 - etaLift T hz 0
        = (etaLift T hz 1 - (factorLift T 1 + uLift T hz 1)) +
            (factorLift T 1 + uLift T hz 1) - etaLift T hz 0 := by ring
    _ = (etaLift T hz 0 - (factorLift T 0 + uLift T hz 0)) +
            (factorLift T 1 + uLift T hz 1) - etaLift T hz 0 := by
      rw [← hf01]
    _ = (factorLift T 1 - factorLift T 0) + (uLift T hz 1 - uLift T hz 0) := by ring

end EtaPhaseSplit
