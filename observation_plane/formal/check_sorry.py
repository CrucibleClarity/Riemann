#!/usr/bin/env python3
"""check_sorry.py — 0 sorry 机检 (文本级, 忽略注释与字符串)

用途: 复核发布包"0 sorry"声明。Lean 的块注释可以嵌套, 注释里常出现
"sorry" 一词 (如 "0 sorry" 字样), 因此不能直接 grep — 本脚本先剥除
注释与字符串, 再在剩余代码中查找 sorry / admit / axiom。

用法:
    python3 check_sorry.py [目录或文件 ...]    # 默认: 本脚本所在目录

退出码: 0 = 全部干净; 1 = 发现命中 (逐条打印 文件:行号:内容)。
"""
import os
import sys


def strip_comments_and_strings(text: str) -> str:
    """剥除 Lean 注释 (-- 行注释与可嵌套的 /- -/ 块注释) 与字符串字面量。"""
    out = []
    i, n = 0, len(text)
    depth = 0          # 块注释嵌套深度
    in_str = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:                    # 块注释内
            if c == "/" and nxt == "-":
                depth += 1; i += 2; continue
            if c == "-" and nxt == "/":
                depth -= 1; i += 2; continue
            out.append("\n" if c == "\n" else " ")
            i += 1; continue
        if in_str:                       # 字符串内
            if c == "\\" and nxt:
                out.append(" "); out.append(" "); i += 2; continue
            if c == '"':
                in_str = False; out.append('"'); i += 1; continue
            out.append("\n" if c == "\n" else " ")
            i += 1; continue
        if c == "/" and nxt == "-":
            depth = 1; i += 2; continue
        if c == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == '"':
            in_str = True; out.append('"'); i += 1; continue
        out.append(c); i += 1
    return "".join(out)


def find_hits(path: str):
    with open(path, encoding="utf-8", errors="replace") as fh:
        raw = fh.read()
    code = strip_comments_and_strings(raw)
    hits = []
    for lineno, line in enumerate(code.splitlines(), 1):
        for token in ("sorry", "admit", "axiom"):
            j = 0
            while True:
                j = line.find(token, j)
                if j < 0:
                    break
                before = line[j - 1] if j > 0 else " "
                after = line[j + len(token)] if j + len(token) < len(line) else " "
                if not (before.isalnum() or before in "_'") and not (
                    after.isalnum() or after in "_'"
                ):
                    hits.append((lineno, token, line.strip()[:100]))
                    break
                j += len(token)
    return hits


def main() -> int:
    roots = sys.argv[1:] or [os.path.dirname(os.path.abspath(__file__))]
    files = []
    for root in roots:
        if os.path.isfile(root):
            files.append(root)
        else:
            for dirpath, _dirs, names in os.walk(root):
                files += [
                    os.path.join(dirpath, f)
                    for f in names
                    if f.endswith(".lean")
                ]
    bad = 0
    for path in sorted(files):
        for lineno, token, line in find_hits(path):
            bad += 1
            print(f"{path}:{lineno}: {token}: {line}")
    if bad == 0:
        print(f"0 sorry OK: {len(files)} 个 .lean, 代码区无 sorry/admit/axiom")
        return 0
    print(f"发现 {bad} 处命中 (见上)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
