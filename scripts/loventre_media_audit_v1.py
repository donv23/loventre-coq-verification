#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import csv
import datetime as dt
import hashlib
import json
import os
import re
import time
from pathlib import Path
from typing import Dict, List, Tuple

IMG_EXT = {
    ".png", ".jpg", ".jpeg", ".webp", ".gif", ".tif", ".tiff", ".bmp", ".heic"
}

TEXT_EXT = {
    ".md", ".tex", ".txt", ".py", ".v", ".json", ".yaml", ".yml"
}

SKIP_DIR_NAMES = {
    ".git", ".venv", "venv", "__pycache__", ".mypy_cache", ".pytest_cache",
    "node_modules"
}

RE_INCLUDEGRAPHICS = re.compile(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}")
RE_MD_IMAGE = re.compile(r"!\[[^\]]*\]\(([^)]+)\)")
RE_ANY_IMAGE_PATH = re.compile(r"([A-Za-z0-9_\-./\\ ]+\.(?:png|jpg|jpeg|webp|gif|tif|tiff|bmp|heic))", re.IGNORECASE)

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def iso_mtime(path: Path) -> str:
    ts = path.stat().st_mtime
    return dt.datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")

def safe_walk(root: Path, progress_every_dirs: int = 250):
    dir_count = 0
    file_count = 0
    start = time.time()

    for dirpath, dirnames, filenames in os.walk(root):
        # prune dirs
        pruned = []
        for d in list(dirnames):
            if d in SKIP_DIR_NAMES or d.startswith("."):
                pruned.append(d)
        for d in pruned:
            dirnames.remove(d)

        dir_count += 1
        file_count += len(filenames)

        if dir_count % progress_every_dirs == 0:
            elapsed = time.time() - start
            print(f"[PROGRESS] {root} | dirs={dir_count} files={file_count} elapsed={elapsed:.1f}s")

        yield Path(dirpath), filenames

def is_image_file(p: Path) -> bool:
    return p.suffix.lower() in IMG_EXT

def is_text_file(p: Path) -> bool:
    return p.suffix.lower() in TEXT_EXT

def normalize_ref(s: str) -> str:
    s = s.strip().strip('"').strip("'")
    s = s.split("#")[0].split("?")[0]
    return s

def scan_images(roots: List[Path], do_hash: bool) -> Tuple[List[Dict], Dict[str, List[str]]]:
    rows = []
    by_basename: Dict[str, List[str]] = {}

    total_found = 0
    start = time.time()

    for r in roots:
        if not r.exists():
            print(f"[WARN] Root inesistente: {r}")
            continue

        print(f"[SCAN] Immagini in: {r}")
        for dpath, filenames in safe_walk(r):
            for fn in filenames:
                p = dpath / fn
                if not p.is_file():
                    continue
                if is_image_file(p):
                    try:
                        st = p.stat()
                        rec = {
                            "path": str(p),
                            "basename": p.name,
                            "ext": p.suffix.lower(),
                            "size_bytes": int(st.st_size),
                            "mtime": iso_mtime(p),
                            "sha256": sha256_file(p) if do_hash else ""
                        }
                        rows.append(rec)
                        by_basename.setdefault(p.name, []).append(str(p))
                        total_found += 1
                        if total_found % 500 == 0:
                            elapsed = time.time() - start
                            print(f"[FOUND] immagini={total_found} elapsed={elapsed:.1f}s")
                    except Exception:
                        pass

    return rows, by_basename

def extract_refs_from_text(path: Path) -> List[Tuple[int, str, str]]:
    refs = []
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return refs

    lines = text.splitlines()
    for i, line in enumerate(lines, start=1):
        for m in RE_INCLUDEGRAPHICS.finditer(line):
            refs.append((i, "includegraphics", normalize_ref(m.group(1))))
        for m in RE_MD_IMAGE.finditer(line):
            refs.append((i, "md_image", normalize_ref(m.group(1))))
        for m in RE_ANY_IMAGE_PATH.finditer(line):
            refs.append((i, "any_image_path", normalize_ref(m.group(1))))
    return refs

def resolve_ref(doc_path: Path, ref: str, by_basename: Dict[str, List[str]]) -> Tuple[str, str]:
    cand = (doc_path.parent / ref).expanduser()
    try:
        cand = cand.resolve()
    except Exception:
        pass

    if cand.exists() and cand.is_file():
        return ("resolved", str(cand))

    base = Path(ref).name
    hits = by_basename.get(base, [])
    if len(hits) == 1:
        return ("resolved", hits[0])
    if len(hits) > 1:
        return ("ambiguous", ";".join(hits))
    return ("missing", "")

def scan_references(roots: List[Path], by_basename: Dict[str, List[str]]) -> List[Dict]:
    out = []
    total_docs = 0
    start = time.time()

    for r in roots:
        if not r.exists():
            continue

        print(f"[SCAN] Referenze in: {r}")
        for dpath, filenames in safe_walk(r):
            for fn in filenames:
                p = dpath / fn
                if not p.is_file():
                    continue
                if is_text_file(p):
                    total_docs += 1
                    refs = extract_refs_from_text(p)
                    for (lineno, kind, ref) in refs:
                        status, resolved = resolve_ref(p, ref, by_basename)
                        out.append({
                            "doc_path": str(p),
                            "line": lineno,
                            "kind": kind,
                            "ref": ref,
                            "status": status,
                            "resolved_path": resolved
                        })
                    if total_docs % 800 == 0:
                        elapsed = time.time() - start
                        print(f"[DOCS] scanned={total_docs} refs={len(out)} elapsed={elapsed:.1f}s")
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="", help="Cartella output (default: Desktop/LOVENTRE_MEDIA_AUDIT_YYYYMMDD-HHMMSS)")
    ap.add_argument("--root", action="append", default=[], help="Root da scansionare (ripetibile)")
    ap.add_argument("--hash", action="store_true", help="Calcola sha256 per ogni immagine (più lento)")
    args = ap.parse_args()

    home = Path.home()

    if args.out:
        out_dir = Path(args.out).expanduser()
    else:
        stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
        out_dir = home / "Desktop" / f"LOVENTRE_MEDIA_AUDIT_{stamp}"

    out_dir.mkdir(parents=True, exist_ok=True)

    roots = [Path(p).expanduser() for p in args.root] if args.root else [Path.cwd()]

    print("=== LOVENTRE MEDIA AUDIT v1.1 (PROGRESS) ===")
    print("Roots:")
    for r in roots:
        print(" -", r)

    images, by_basename = scan_images(roots, do_hash=args.hash)
    refs = scan_references(roots, by_basename)

    img_csv = out_dir / "MEDIA_IMAGES_INDEX.csv"
    img_json = out_dir / "MEDIA_IMAGES_INDEX.json"
    ref_csv = out_dir / "MEDIA_DOC_REFERENCES.csv"
    ref_json = out_dir / "MEDIA_DOC_REFERENCES.json"

    with img_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["path","basename","ext","size_bytes","mtime","sha256"])
        w.writeheader()
        for r in images:
            w.writerow(r)

    img_json.write_text(json.dumps(images, indent=2, ensure_ascii=False), encoding="utf-8")

    with ref_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["doc_path","line","kind","ref","status","resolved_path"])
        w.writeheader()
        for r in refs:
            w.writerow(r)

    ref_json.write_text(json.dumps(refs, indent=2, ensure_ascii=False), encoding="utf-8")

    resolved = sum(1 for r in refs if r["status"] == "resolved")
    ambiguous = sum(1 for r in refs if r["status"] == "ambiguous")
    missing = sum(1 for r in refs if r["status"] == "missing")

    def is_screenshot_name(name: str) -> bool:
        n = name.lower()
        return n.startswith("schermata") or "screenshot" in n or "screen shot" in n

    screenshots = [r for r in images if is_screenshot_name(r["basename"])]

    summary = {
        "roots_scanned": [str(r) for r in roots if r.exists()],
        "images_found": len(images),
        "screenshots_found": len(screenshots),
        "doc_refs_found": len(refs),
        "refs_resolved": resolved,
        "refs_ambiguous": ambiguous,
        "refs_missing": missing,
        "outputs": {
            "MEDIA_IMAGES_INDEX.csv": str(img_csv),
            "MEDIA_DOC_REFERENCES.csv": str(ref_csv),
            "SUMMARY.json": str(out_dir / "SUMMARY.json")
        }
    }

    (out_dir / "SUMMARY.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")

    print("=== DONE ===")
    print("Output:", out_dir)
    print("Immagini trovate:", len(images))
    print("Screenshot trovati:", len(screenshots))
    print("Referenze nei documenti:", len(refs))
    print("Risolte:", resolved, "| Ambigue:", ambiguous, "| Mancanti:", missing)

if __name__ == "__main__":
    main()

