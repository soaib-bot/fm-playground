import os
from collections import defaultdict
from typing import List, Set, Tuple, Dict

ELOC = True


def normalize_exts(exts: List[str]) -> Set[str]:
    norm = set()
    for e in exts:
        if not e:
            continue
        if not e.startswith("."):
            e = "." + e
        norm.add(e.lower())
    return norm


def should_exclude(path_parts: Tuple[str, ...], exclude_names: Set[str]) -> bool:
    # If any path part matches an excluded directory name, exclude.
    for part in path_parts:
        if part in exclude_names:
            return True
    return False


def strip_comments_and_blank_lines(lines: List[str], ext: str) -> List[str]:
    """Return a list of effective (non-blank, non-comment) lines for a file given its extension.

    Supports Python (# single-line, triple-quoted block strings used as comments when not assigned),
    Java/TypeScript/JavaScript (// single-line, /* */ block comments).
    """
    out = []
    ext = ext.lower()

    if ext == ".py":
        in_block = False
        block_delim = None
        for raw in lines:
            s = raw.strip()
            if not s:
                continue
            # handle triple-quoted block strings likely used as comments
            if not in_block:
                if s.startswith('"""') or s.startswith("'''"):
                    # start of block; may also end on same line
                    if (s.count('"""') == 2) or (s.count("'''") == 2):
                        continue
                    in_block = True
                    block_delim = s[:3]
                    # if there's content after start delimiter, skip it as comment
                    continue
                if s.startswith("#"):
                    continue
                # inline comments: keep only code before #
                if "#" in s:
                    code = s.split("#", 1)[0].strip()
                    if code:
                        out.append(code)
                else:
                    out.append(s)
            else:
                # we are inside a block comment started by triple quotes
                if block_delim and block_delim in s:
                    # end block
                    in_block = False
                    block_delim = None
                # everything inside block is ignored
                continue

    else:
        # For java/ts/js: strip // comments and /* */ blocks
        in_block = False
        for raw in lines:
            s = raw
            i = 0
            out_line = ""
            while i < len(s):
                if not in_block and s[i : i + 2] == "//":
                    # rest of line is comment
                    break
                if not in_block and s[i : i + 2] == "/*":
                    in_block = True
                    i += 2
                    continue
                if in_block and s[i : i + 2] == "*/":
                    in_block = False
                    i += 2
                    continue
                if not in_block:
                    out_line += s[i]
                i += 1
            if not in_block:
                if out_line.strip():
                    out.append(out_line.strip())

    return out


def count_effective_lines(
    root: str, exts: Set[str], exclude_dirs: Set[str]
) -> Tuple[List[Tuple[str, str, int]], Dict[str, int], int]:
    """Walk `root` and count effective lines for files whose extensions are in `exts`.

    Returns (per_file_list, per_ext_dict, total)
    where per_file_list is [(path, ext, effective_line_count), ...]
    """
    per_file = []  # list of tuples (path, ext, lines)
    per_ext = defaultdict(int)
    total = 0

    root = os.path.abspath(root)
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]

        rel_parts = (
            tuple(os.path.relpath(dirpath, root).split(os.sep))
            if dirpath != root
            else ()
        )
        if should_exclude(rel_parts, exclude_dirs):
            continue

        for fn in filenames:
            fp = os.path.join(dirpath, fn)
            _, ext = os.path.splitext(fn)
            if exts and ext.lower() not in exts:
                continue
            try:
                with open(fp, "r", errors="replace") as f:
                    raw_lines = f.readlines()
            except Exception:
                per_file.append((fp, ext or "", -1))
                continue

            effective = strip_comments_and_blank_lines(raw_lines, ext)
            count = len(effective)
            per_file.append((fp, ext or "", count))
            per_ext[ext.lower()] += count
            total += count

    return per_file, per_ext, total


def count_nonempty_lines(
    root: str, exts: Set[str], exclude_dirs: Set[str]
) -> Tuple[List[Tuple[str, str, int]], Dict[str, int], int]:
    """Walk `root` and count non-empty (non-blank) lines for files whose extensions are in `exts`.

    Unlike `count_effective_lines`, this keeps comment lines — only blank/empty lines are excluded.
    Returns (per_file_list, per_ext_dict, total)
    """
    per_file = []  # list of tuples (path, ext, lines)
    per_ext = defaultdict(int)
    total = 0

    root = os.path.abspath(root)
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]

        rel_parts = (
            tuple(os.path.relpath(dirpath, root).split(os.sep))
            if dirpath != root
            else ()
        )
        if should_exclude(rel_parts, exclude_dirs):
            continue

        for fn in filenames:
            fp = os.path.join(dirpath, fn)
            _, ext = os.path.splitext(fn)
            if exts and ext.lower() not in exts:
                continue
            try:
                with open(fp, "r", errors="replace") as f:
                    raw_lines = f.readlines()
            except Exception:
                per_file.append((fp, ext or "", -1))
                continue

            # Count lines that contain any non-whitespace character
            count = sum(1 for l in raw_lines if l.strip())
            per_file.append((fp, ext or "", count))
            per_ext[ext.lower()] += count
            total += count

    return per_file, per_ext, total


def main():
    exts = ["py", "java", "ts", "js"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["lib", "tests"]
    exclude_set = set(exclude_list)

    per_file, per_ext, total = count_effective_lines(
        "limboole-api", exts_set, exclude_set
    )

    print("Effective line counts per file:")
    for fp, ext, lines in per_file:
        if lines >= 0:
            print(f"{lines:8d} {ext:6} {fp}")
        else:
            print(f"   ERROR {ext:6} {fp}")

    print("\nSummary by extension:")
    for ext, lines in sorted(per_ext.items(), key=lambda t: (-t[1], t[0])):
        print(f"{ext or '(no ext)':8s} {lines:7d}")
    print("------------------------")
    print(f"{'TOTAL':8s} {total:7d}")


def backend():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "migrations"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "backend", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "backend", exts_set, exclude_set
        )
    print(f"Backend total lines: {total}")
def frontend():
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["dist", "node_modules", "public", "tools", "src/assets"]
    exclude_set = set(exclude_list)
    if ELOC:
      per_file, per_ext, total = count_effective_lines(
          "frontend", exts_set, exclude_set
      )
    else:
      per_file, per_ext, total = count_nonempty_lines(
          "frontend", exts_set, exclude_set
      )
    print(f"Frontend total lines: {total}")
    
    
def alloy_api():
    exts = ["java"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = [".gradle", "bin", "build", "gradle", "lib"]
    exclude_set = set(exclude_list)
    
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "alloy-api", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "alloy-api", exts_set, exclude_set
        )
    print(f"Alloy API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/alloy", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/alloy", exts_set, exclude_set
        )
    print (f"Alloy UI total lines: {total}")
    
    
def limboole_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "lib", "tests"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "limboole-api", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "limboole-api", exts_set, exclude_set
        )
    print(f"Limboole API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/limboole", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/limboole", exts_set, exclude_set
        )
    print(f"Limboole UI total lines: {total}")

def limboole_diff_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "lib", "tests"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "limboole-diff-api", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "limboole-diff-api", exts_set, exclude_set
        )
    print(f"Limboole Diff API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/limboole-diff", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/limboole-diff", exts_set, exclude_set
        )
    
    print(f"Limboole Diff UI total lines: {total}")
def nuxmv_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "lib", "tests"]
    exclude_set = set(exclude_list)

    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "nuxmv-api", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "nuxmv-api", exts_set, exclude_set
        )
    print(f"Nuxmv API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/nuxmv", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/nuxmv", exts_set, exclude_set
        )
    print(f"Nuxmv UI total lines: {total}")
def smt_diff_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__",  "tests"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "smt-diff-api", exts_set, exclude_set
      )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "smt-diff-api", exts_set, exclude_set
      )
    print(f"SMT Diff API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/smt-diff", exts_set, exclude_set
    )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/smt-diff", exts_set, exclude_set
    )
    print(f"SMT Diff UI total lines: {total}")
def spectra_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "lib", "tests"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "spectra-api", exts_set, exclude_set
      )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "spectra-api", exts_set, exclude_set
      )
    print(f"Spectra API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/spectra", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/spectra", exts_set, exclude_set
        )
    print(f"Spectra UI total lines: {total}")
def z3_api():
    exts = ["py"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["__pycache__", "tests"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "z3-api", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "z3-api", exts_set, exclude_set
        )
    print(f"Z3 API total lines: {total}")
    ##### UI #####
    exts = ["ts", "js", "tsx", "jsx"]
    exts = [("." + e) if not e.startswith(".") else e for e in exts]
    exts_set = set(e.lower() for e in exts)
    exclude_list = ["langium"]
    exclude_set = set(exclude_list)
    if ELOC:
        per_file, per_ext, total = count_effective_lines(
            "frontend/tools/smt", exts_set, exclude_set
        )
    else:
        per_file, per_ext, total = count_nonempty_lines(
            "frontend/tools/smt", exts_set, exclude_set
        )

    print(f"SMT UI total lines: {total}")


if __name__ == "__main__":
    alloy_api()
    backend()
    frontend()
    limboole_api()
    limboole_diff_api()
    nuxmv_api()
    smt_diff_api()
    spectra_api()
    z3_api()
