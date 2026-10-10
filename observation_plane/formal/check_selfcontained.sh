#!/usr/bin/env bash
# check_selfcontained.sh — 铁律检查器 (v3 artifact 自包含守护)
#
# 铁律: 包内 lean 只 import Mathlib.* 或包内模块 (Formal.ZeroRelative.*) —
# 包外自定义库 = 违规。多数文件为 0pat (只引用 Mathlib 原生库);
# 少数文件引用包内模块 (模块间依赖由 lakefile.toml 解析)。
# 静态检查 (不 build)。
# 用法: bash check_selfcontained.sh [Formal/ZeroRelative/*.lean ...]  (默认全部)
set -uo pipefail
cd "$(dirname "$0")"
LEAN_DIR="Formal/ZeroRelative"

fail=0
checked=0
if [ $# -eq 0 ]; then
  set -- "$LEAN_DIR"/*.lean
fi
for f in "$@"; do
  [ -f "$f" ] || continue
  checked=$((checked + 1))
  name="$(basename "$f")"
  in_doc=0
  while IFS= read -r line; do
    case "$line" in
      "/-!"*) in_doc=1 ;;
    esac
    if [ "$in_doc" -eq 1 ]; then
      case "$line" in
        *"-/"*) in_doc=0 ;;
      esac
      continue
    fi
    case "$line" in
      "import "*)
        imp="${line#import }"
        case "$imp" in
          Mathlib|Mathlib.*|Formal.ZeroRelative.*) ;;  # 白名单: Mathlib (含整库) + 包内模块
          *)
            echo "VIOLATION: $name import 包外 '$imp'"
            fail=1
            ;;
        esac
        ;;
    esac
  done < "$f"
done

if [ "$fail" -eq 0 ]; then
  echo "铁律 OK: $checked 文件, import 白名单 (Mathlib + 包内模块) 全过"
  exit 0
else
  echo "铁律违反 — 自包含破裂 (见上)"
  exit 1
fi
