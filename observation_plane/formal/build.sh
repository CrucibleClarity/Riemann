#!/usr/bin/env bash
# build.sh — v3 artifact 分层构建
#
# 一切文件 0pat (只 import Mathlib), 无包内互依赖 — 每文件独立可编译。
# 分层: ①黎曼链主文件 (proof.lean = 221 声明合并版) ②隔离 iso 系列
# ③PreciseMigration (v3 新增, 基点精确移动定理族) ④对称工具族
# (四方法: 对称消去/对称延拓/三桥/对称计数, v1 发布, v3 引用)。
#
# 用法: bash build.sh              # 全部
#       bash build.sh 主链          # 只构建指定层
set -euo pipefail
cd "$(dirname "$0")"
LAKE="${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}"

run_batch() {
  local label="$1"; shift
  echo "== [$(date +%H:%M:%S)] $label"
  "$LAKE" build "$@" 2>&1 | tail -3
}

main() {
  run_batch "主链 proof.lean" Formal.ZeroRelative.proof
  run_batch "隔离 iso (28/29/30/31/41 + continuation)" \
    Formal.ZeroRelative.continuum_projection_iso \
    Formal.ZeroRelative.symmetry_cancel_phase_iso \
    Formal.ZeroRelative.path_problem_iso \
    Formal.ZeroRelative.phase_succ_iso \
    Formal.ZeroRelative.zeta_odd_even_continuity_iso \
    Formal.ZeroRelative.zeta_continuation_iso
  run_batch "PreciseMigration (v3 新增)" Formal.ZeroRelative.PreciseMigration
  run_batch "对称工具族 (四方法 50 定理)" \
    Formal.ZeroRelative.SymmetryCancellation \
    Formal.ZeroRelative.SymmetryExtension \
    Formal.ZeroRelative.ThreeBridges \
    Formal.ZeroRelative.SymmetryCounting
}

if [ $# -gt 0 ]; then
  case "$1" in
    主链) run_batch "主链 proof.lean" Formal.ZeroRelative.proof ;;
    iso) run_batch "隔离 iso" Formal.ZeroRelative.continuum_projection_iso \
      Formal.ZeroRelative.symmetry_cancel_phase_iso \
      Formal.ZeroRelative.path_problem_iso \
      Formal.ZeroRelative.phase_succ_iso \
      Formal.ZeroRelative.zeta_odd_even_continuity_iso \
      Formal.ZeroRelative.zeta_continuation_iso ;;
    精确移动) run_batch "PreciseMigration" Formal.ZeroRelative.PreciseMigration ;;
    对称工具族) run_batch "对称工具族" \
      Formal.ZeroRelative.SymmetryCancellation \
      Formal.ZeroRelative.SymmetryExtension \
      Formal.ZeroRelative.ThreeBridges \
      Formal.ZeroRelative.SymmetryCounting ;;
    *) echo "未知层: $1 (主链/iso/精确移动/对称工具族)"; exit 1 ;;
  esac
else
  main
fi
echo "== 全部完成"
