#!/usr/bin/env python3
"""Fail-closed, local verification of the exact public source snapshot.

This is a reproducibility tool, not Palomar's protected submission service.
Raw compiler output and temporary protected Comparator configuration remain
outside the public repository. See tools/README.md for the checks' limits.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from urllib.parse import unquote, urlsplit

sys.dont_write_bytecode = True
SCRIPT_DIRECTORY = Path(__file__).resolve().parent
PROJECT_DIRECTORY = SCRIPT_DIRECTORY.parent
TOOLS = PROJECT_DIRECTORY / "tools" if SCRIPT_DIRECTORY.name == "scripts" else SCRIPT_DIRECTORY
sys.path.insert(0, str(TOOLS / "vendor" / "palomar"))
from scripts.submission_contract import load_formalization_metadata
from scripts.source_requirements import inspect_lean_sources, lean_source_files, physical_lines

PALOMAR_REVISION = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
MATHLIB_REVISION = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXCLUDED_DIRECTORIES = {".git", ".lake", "__pycache__", ".venv", "verification-output"}
GENERATED_REPORTS = {"docs/source-manifest.json", "docs/verification.json"}
COMPILED_SUFFIXES = {".a", ".bc", ".dll", ".dylib", ".ilean", ".ir", ".o", ".obj", ".olean", ".so", ".trace", ".pyc"}


class Blocked(RuntimeError):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def public_files(root: Path) -> list[Path]:
    paths = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        # Symlinks are included in the inspection and never traversed.
        for name in dirs:
            p = Path(directory) / name
            if name not in EXCLUDED_DIRECTORIES and p.is_symlink():
                paths.append(p)
        dirs[:] = sorted(n for n in dirs if n not in EXCLUDED_DIRECTORIES and not (Path(directory) / n).is_symlink())
        paths.extend(Path(directory) / name for name in sorted(files))
    return sorted(paths)


def snapshot(root: Path) -> dict:
    rows = []
    for path in public_files(root):
        relative = path.relative_to(root).as_posix()
        if relative in GENERATED_REPORTS:
            continue
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"source snapshot contains a nonregular file: {relative}")
        data = path.read_bytes()
        rows.append({"path": relative, "bytes": len(data), "sha256": digest(data)})
    encoded = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return {"schema_version": 1, "algorithm": "sha256", "source_fingerprint": digest(encoded),
            "excluded_directories": sorted(EXCLUDED_DIRECTORIES),
            "excluded_generated_reports": sorted(GENERATED_REPORTS), "files": rows}


def strip_lean_noncode(text: str) -> str:
    """Mask nested comments and strings, preserving physical line locations."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; i += 2; depth += 1; continue
            if text.startswith("-/", i):
                out[i:i+2] = "  "; i += 2; depth -= 1; continue
            if text[i] != "\n": out[i] = " "
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = out[i+1] = " "; i += 2; continue
            if text[i] == '"': string = False
            if text[i] != "\n": out[i] = " "
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; i += 2; depth = 1; continue
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end-i); i = end; continue
        elif text[i] == '"':
            out[i] = " "; string = True
        i += 1
    return "".join(out)


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def comparator_config(root: Path) -> dict:
    path = root / "comparator.json"
    if path.is_symlink() or not path.is_file(): raise ValueError("comparator.json is not a regular file")
    if path.stat().st_size > 1024**2: raise ValueError("comparator.json exceeds 1 MiB")
    config = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    allowed = required | {"definition_names", "enable_nanoda"}
    if not isinstance(config, dict) or not required <= config.keys() or config.keys() - allowed:
        raise ValueError("Comparator fields differ from the current submitter contract; external_kernels is forbidden")
    plain = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
    for field in ("challenge_module", "solution_module"):
        if not isinstance(config[field], str) or not plain.fullmatch(config[field]):
            raise ValueError(f"invalid Comparator module: {field}")
        if not (root / (config[field].replace(".", "/") + ".lean")).is_file():
            raise ValueError(f"missing configured {field}")
    if config["challenge_module"] == config["solution_module"]: raise ValueError("Challenge and Solution must differ")
    theorems, definitions = config["theorem_names"], config.get("definition_names", [])
    if not isinstance(theorems, list) or not theorems or not isinstance(definitions, list):
        raise ValueError("theorem_names must be nonempty and definition_names must be an array")
    # This project uses plain names. Rejecting other canonical Lean spellings
    # is intentionally stricter than Palomar's general identifier validator.
    if not all(isinstance(n, str) and plain.fullmatch(n) for n in theorems + definitions):
        raise ValueError("this project's Comparator declaration names must use plain canonical identifiers")
    axioms = config["permitted_axioms"]
    if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms) or not set(axioms) <= STANDARD_AXIOMS:
        raise ValueError("Comparator permits a forbidden axiom")
    return config


class Verifier:
    def __init__(self, root: Path, output: Path, timeout: int):
        self.root, self.output, self.timeout = root, output, timeout
        output.mkdir(parents=True, exist_ok=True)
        self.report = {"schema_version": 1, "checked_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "policy": {"formalization_profile_version": 4, "palomar_submission_revision": PALOMAR_REVISION,
                "source": "https://github.com/PalomarRegistry/PalomarSubmission", "checked_utc_date": "2026-10-09"},
            "checks": [], "status": "not_run", "limitations": [
                "This local check does not reproduce Palomar's protected canonical-Challenge sandbox or registration service.",
                "Mechanical verification does not establish mathematical fidelity or human mathematical review."]}
        self.counter = 0

    def command(self, argv: list[str], *, cwd: Path | None = None, label: str = "command",
                timeout_seconds: int | None = None,
                stdout_path: Path | None = None) -> subprocess.CompletedProcess:
        self.counter += 1
        log = self.output / f"{self.counter:03d}-{label}.log"
        start = time.monotonic()
        limit = self.timeout if timeout_seconds is None else timeout_seconds
        try:
            if stdout_path is None:
                proc = subprocess.run(argv, cwd=cwd or self.root, text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, timeout=limit, check=False)
            else:
                if not stdout_path.resolve().is_relative_to(self.output):
                    raise ValueError("streamed command output must stay in the external evidence directory")
                with stdout_path.open("w", encoding="utf-8") as handle:
                    proc = subprocess.run(argv, cwd=cwd or self.root, text=True, stdout=handle,
                        stderr=subprocess.PIPE, timeout=limit, check=False)
                proc.stdout = proc.stderr or ""
        except (FileNotFoundError, PermissionError, subprocess.TimeoutExpired) as error:
            log.write_text(str(error) + "\n", encoding="utf-8")
            raise Blocked(f"{label} could not complete: {error}") from error
        log.write_text(proc.stdout, encoding="utf-8")
        self.report.setdefault("commands", []).append({"argv": argv, "exit_code": proc.returncode,
            "timeout_seconds": limit,
            "elapsed_seconds": round(time.monotonic()-start, 3), "log_sha256": digest(log.read_bytes()), "log_file": log.name})
        if stdout_path is not None:
            self.report["commands"][-1]["streamed_stdout_sha256"] = digest(stdout_path.read_bytes())
            self.report["commands"][-1]["streamed_stdout_bytes"] = stdout_path.stat().st_size
        return proc

    def require_command(self, argv: list[str], *, cwd: Path | None = None, label: str = "command") -> str:
        proc = self.command(argv, cwd=cwd, label=label)
        if proc.returncode: raise ValueError(f"{label} exited {proc.returncode}; see external log")
        return proc.stdout

    def check(self, name: str, action) -> bool:
        try:
            evidence = action()
            self.report["checks"].append({"check": name, "status": "pass", "evidence": evidence})
            return True
        except Blocked as error:
            self.report["checks"].append({"check": name, "status": "blocked", "reason": str(error)})
        except Exception as error:
            self.report["checks"].append({"check": name, "status": "fail", "reason": str(error)})
        return False

    def structure(self):
        total = 0
        for path in public_files(self.root):
            relative = path.relative_to(self.root).as_posix()
            if path.is_symlink() or not path.is_file(): raise ValueError(f"nonregular public file: {relative}")
            total += path.stat().st_size
            if path.suffix in COMPILED_SUFFIXES or path.name.endswith((".olean.private", ".olean.server")):
                raise ValueError(f"compiled/cache artifact in public tree: {relative}")
            if path.suffix in {".zip", ".tar", ".zst", ".log"}: raise ValueError(f"packaging artifact/raw log in public tree: {relative}")
            if path.read_bytes()[:100].startswith(b"version https://git-lfs.github.com/spec/v1"):
                raise ValueError(f"Git LFS pointer in public tree: {relative}")
        if total > 500*1024**2: raise ValueError("public source exceeds Palomar's 500 MiB cap")
        if (self.root / ".gitmodules").exists(): raise ValueError("Git submodules are not part of this reproducible package")
        for path in public_files(self.root):
            if path.name == ".gitattributes" and re.search(r"\bfilter\s*=\s*lfs\b", path.read_text(encoding="utf-8")):
                raise ValueError("Git LFS attributes are not part of this reproducible package")
        if (self.root / ".git").exists():
            tracked = self.require_command(["git", "ls-files", "--stage"], label="git-index")
            if any(line.startswith("160000 ") for line in tracked.splitlines()): raise ValueError("Git index contains a submodule")
        for filename in ("LICENSE", "README.md", "formalization.yaml", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json"):
            if not (self.root / filename).is_file(): raise ValueError(f"missing required public file: {filename}")
        if (self.root / "LICENSE").stat().st_size > 1024**2: raise ValueError("LICENSE exceeds 1 MiB")
        conventional = re.compile(r"^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$", re.I)
        licenses = [p.name for p in self.root.iterdir() if conventional.fullmatch(p.name)]
        if licenses != ["LICENSE"]: raise ValueError("expected exactly one conventional root license file, LICENSE")
        text = " ".join((self.root / "LICENSE").read_text(encoding="utf-8").split())
        upstream = " ".join((TOOLS / "vendor" / "palomar" / "LICENSE").read_text(encoding="utf-8").split())
        grant = upstream[upstream.index("Permission is hereby granted"):]
        if not text.startswith("MIT License") or "Copyright" not in text or grant not in text:
            raise ValueError("root LICENSE does not contain the complete standard MIT grant and disclaimer")
        if (self.root / "lakefile.lean").exists(): raise ValueError("this package requires one lakefile.toml, with no competing lakefile.lean")
        if (self.root / "lakefile.toml").stat().st_size > 1024**2: raise ValueError("lakefile.toml exceeds Palomar's 1 MiB cap")
        source_evidence, issues = inspect_lean_sources(self.root)
        if issues: raise ValueError("; ".join(str(issue) for issue in issues[:10]))
        return {"public_bytes": total, "repository_cap_bytes": 500*1024**2, "lean_sources": source_evidence}

    def metadata(self):
        data = load_formalization_metadata(self.root / "formalization.yaml")
        return {"validator": f"vendored PalomarSubmission {PALOMAR_REVISION}",
                "PyYAML": __import__("yaml").__version__, "project_name": data["project"]["name"],
                "review_status": data["review"]["status"]}

    def source_safety(self):
        config = comparator_config(self.root)
        challenge = self.root / (config["challenge_module"].replace(".", "/") + ".lean")
        lines, size = physical_lines(challenge.read_text(encoding="utf-8")), challenge.stat().st_size
        if lines > 1000 or size > 100*1024: raise ValueError("Challenge exceeds its 1,000 line / 100 KiB cap")
        count = 0
        for path in lean_source_files(self.root):
            code = strip_lean_noncode(path.read_text(encoding="utf-8"))
            patterns = r"\baxiom\b" if path == challenge else r"\b(?:sorry|admit|sorryAx|axiom)\b"
            match = re.search(patterns, code)
            if match:
                raise ValueError(f"forbidden proof hole or custom axiom in {path.relative_to(self.root)}:{code[:match.start()].count(chr(10))+1}")
            if path != challenge and re.search(r"(?:^|\n)\s*(?:public\s+)?(?:meta\s+)?import\s+" + re.escape(config["challenge_module"]) + r"\b", code):
                raise ValueError(f"implementation imports the Challenge placeholders: {path.relative_to(self.root)}")
            count += 1
        return {"files_scanned": count, "intentional_Challenge_placeholders_allowed": True,
            "lexical_check_is_not_a_transitive_axiom_audit": True,
            "challenge_bytes": size, "challenge_lines": lines,
            "preferred_review_surface_exceeded": size > 32*1024 or lines > 300, "comparator": config}

    def pins(self):
        toolchain = (self.root / "lean-toolchain").read_text().strip()
        if toolchain != TOOLCHAIN: raise ValueError(f"expected pinned toolchain {TOOLCHAIN}, found {toolchain}")
        config = tomllib.loads((self.root / "lakefile.toml").read_text())
        requirements = config.get("require", [])
        if not isinstance(requirements, list) or len(requirements) != 1:
            raise ValueError("this package requires exactly the declared canonical mathlib dependency")
        mathlib = next((p for p in requirements if p.get("name") == "mathlib"), None)
        if not mathlib or mathlib.get("rev") != MATHLIB_REVISION or mathlib.get("git") != "https://github.com/leanprover-community/mathlib4.git":
            raise ValueError("lakefile.toml differs from the exact canonical mathlib pin")
        manifest = json.loads((self.root / "lake-manifest.json").read_text(), object_pairs_hook=unique_object)
        if manifest.get("packagesDir") != ".lake/packages" or manifest.get("lakeDir") != ".lake":
            raise ValueError("manifest dependency/build paths differ from the confined .lake locations")
        packages = manifest.get("packages", [])
        if not isinstance(packages, list) or not packages: raise ValueError("manifest packages must be a nonempty array")
        seen = set()
        for package in packages:
            name = package.get("name")
            if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) or name in seen:
                raise ValueError(f"unsafe or duplicate manifest package name: {name}")
            seen.add(name)
            if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", str(package.get("rev", ""))):
                raise ValueError(f"dependency lacks an exact Git SHA: {package.get('name')}")
            if not isinstance(package.get("url"), str) or not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"]):
                raise ValueError(f"dependency does not use a canonical HTTPS GitHub repository URL: {name}")
            if package.get("subDir") is not None or package.get("manifestFile") != "lake-manifest.json":
                raise ValueError(f"unexpected package subdirectory or manifest path: {name}")
        pinned = next((p for p in packages if p.get("name") == "mathlib"), None)
        if not pinned or pinned["rev"] != MATHLIB_REVISION: raise ValueError("manifest mathlib pin mismatch")
        return {"lean_toolchain": toolchain, "mathlib_revision": MATHLIB_REVISION,
            "manifest_fixedToolchain_update_flag": manifest.get("fixedToolchain"),
            "dependency_pins": [{k: p.get(k) for k in ("name", "url", "rev", "inherited")} for p in packages]}

    def links(self):
        count = 0
        for path in public_files(self.root):
            if path.suffix.lower() != ".md": continue
            # Avoid examples in fenced code; URLs are not network-tested.
            text = re.sub(r"```.*?```", "", path.read_text(encoding="utf-8"), flags=re.S)
            for raw in re.findall(r"\[[^\]]*\]\(([^\s)]+)(?:\s+[^)]*)?\)", text):
                parts = urlsplit(raw.strip("<>"))
                if parts.scheme or parts.netloc: continue
                if not parts.path: continue
                target = (path.parent / unquote(parts.path)).resolve()
                if not target.is_relative_to(self.root): raise ValueError(f"local link leaves public tree: {path.relative_to(self.root)} -> {raw}")
                if not target.exists(): raise ValueError(f"broken local link: {path.relative_to(self.root)} -> {raw}")
                count += 1
        return {"local_file_links_checked": count, "external_URLs_and_fragment_anchors": "not network-verified"}

    def runtime(self):
        for tool in ("lake", "lean"):
            if not shutil.which(tool): raise Blocked(f"required executable unavailable: {tool}")
        version = self.require_command(["lean", "--version"], label="lean-version").strip()
        if "4.35.0-rc2" not in version: raise ValueError("active Lean binary does not match lean-toolchain")
        prefix = Path(self.require_command(["lean", "--print-prefix"], label="lean-prefix").strip()).resolve()
        tools = {}
        for name in ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"):
            path = prefix / "bin" / name
            if not path.is_file() or not os.access(path, os.X_OK): raise Blocked(f"pinned toolchain does not bundle executable {name}")
            tools[name] = {"path": str(path), "sha256": digest(path.read_bytes())}
        evidence = {"lean_version": version, "prefix": str(prefix), "executables": tools}
        if os.environ.get("LD_PRELOAD"):
            evidence["environment_specific_LD_PRELOAD"] = [{"path": value,
                "sha256": digest(Path(value).read_bytes()) if Path(value).is_file() else None}
                for value in os.environ["LD_PRELOAD"].split(":")]
        self.prefix = prefix
        return evidence

    def dependency_checkouts(self):
        manifest = json.loads((self.root / "lake-manifest.json").read_text())
        packages_root = self.root / manifest.get("packagesDir", ".lake/packages")
        packages = {p["name"]: p for p in manifest["packages"]}
        mathlib = packages_root / "mathlib"
        if not mathlib.is_dir(): raise Blocked("dependency checkouts unavailable; run lake update and lake exe cache get")
        if (mathlib / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("canonical mathlib and project toolchains differ")
        canonical = json.loads((mathlib / "lake-manifest.json").read_text())
        expected = {p["name"]: p for p in canonical["packages"]}
        if set(packages) != set(expected) | {"mathlib"}: raise ValueError("project dependencies differ from canonical mathlib's pinned manifest closure")
        for name, item in expected.items():
            actual = packages[name]
            if actual.get("rev") != item.get("rev") or actual.get("url") != item.get("url"):
                raise ValueError(f"dependency pin differs from canonical mathlib closure: {name}")
        rows = []
        for name, item in packages.items():
            path = packages_root / name
            if not path.is_dir(): raise Blocked(f"missing dependency checkout: {name}")
            rev = self.require_command(["git", "rev-parse", "HEAD"], cwd=path, label=f"pin-{name}").strip()
            if rev != item["rev"]: raise ValueError(f"dependency checkout SHA mismatch: {name}")
            clean = self.require_command(["git", "status", "--porcelain", "--untracked-files=all"], cwd=path, label=f"clean-{name}")
            # Build outputs are ignored by canonical packages; any remaining
            # modification could change source resolution and is rejected.
            if clean.strip(): raise ValueError(f"dependency checkout has uncommitted or untracked files: {name}")
            rows.append({"name": name, "revision": rev})
        self.packages_root, self.package_names = packages_root.resolve(), set(packages)
        return {"checkouts": rows, "canonical_mathlib_manifest_closure_exact": True,
            "canonical_release_pin_is_frozen_in_this_tool": True}

    def parsed_headers(self, paths: list[Path]) -> list[dict]:
        output = self.require_command(["lean", "--deps-json", *map(str, paths)], label="headers")
        entries = json.loads(output.strip())["imports"]
        if len(entries) != len(paths): raise ValueError("compiler returned wrong number of source headers")
        results = []
        for path, item in zip(paths, entries, strict=True):
            result = item.get("result")
            if item.get("errors") or not isinstance(result, dict): raise ValueError(f"compiler rejected source header: {path}")
            results.append(result)
        return results

    def compiler_headers(self):
        files = [p for p in lean_source_files(self.root) if p.name != "lakefile.lean"]
        for start in range(0, len(files), 64):
            batch = files[start:start+64]
            for path, result in zip(batch, self.parsed_headers(batch), strict=True):
                if not result.get("isModule"): raise ValueError(f"compiler rejects module-system header: {path.relative_to(self.root)}")
        return {"compiler_headers_checked": len(files)}

    def challenge_imports(self):
        config = comparator_config(self.root)
        source_path = self.require_command(["lake", "env", "printenv", "LEAN_SRC_PATH"], label="source-path").strip()
        roots = [(Path(p) if Path(p).is_absolute() else self.root / p).resolve()
                 for p in source_path.split(os.pathsep) if p]
        roots.extend([self.prefix / "src" / "lean", self.prefix / "src" / "lean" / "lake"])
        challenge = self.root / (config["challenge_module"].replace(".", "/") + ".lean")
        seen, frontier, rows = set(), [challenge], []
        direct = []
        while frontier:
            batch, frontier = frontier[:64], frontier[64:]
            results = self.parsed_headers(batch)
            for path, result in zip(batch, results, strict=True):
                if path in seen: continue
                seen.add(path)
                imports = [entry["module"] for entry in result.get("imports", [])]
                if path == challenge: direct = sorted(set(imports))
                if path == challenge:
                    identity = "project/" + path.relative_to(self.root).as_posix()
                elif path.is_relative_to(self.packages_root):
                    identity = "dependencies/" + path.relative_to(self.packages_root).as_posix()
                else:
                    identity = "toolchain/" + path.relative_to(self.prefix).as_posix()
                rows.append({"source_identity": identity, "sha256": digest(path.read_bytes())})
                for name in imports:
                    candidates = [r / (name.replace(".", "/") + ".lean") for r in roots]
                    selected = next((p.resolve() for p in candidates if p.is_file()), None)
                    if selected is None: raise Blocked(f"cannot resolve transitive Challenge import source: {name}")
                    if selected.is_relative_to(self.root) and not selected.is_relative_to(self.packages_root):
                        raise ValueError(f"Challenge imports local implementation source: {name}")
                    trusted = selected.is_relative_to(self.prefix / "src") or any(selected.is_relative_to(self.packages_root / n) for n in self.package_names)
                    if not trusted: raise ValueError(f"Challenge source outside canonical dependency/core allowlist: {name}: {selected}")
                    if selected not in seen and selected not in frontier: frontier.append(selected)
        rows.sort(key=lambda r: r["source_identity"])
        return {"direct_imports_including_implicit_Init": direct, "transitive_source_count": len(rows),
            "transitive_content_fingerprint": digest(json.dumps(rows, sort_keys=True).encode()),
            "trusted_roots": "pinned Lean core and exact canonical mathlib manifest closure", "all_imports_resolved": True}

    def build(self):
        files = [p for p in lean_source_files(self.root) if p.name != "lakefile.lean"]
        targets = ["+" + module_name(p, self.root) + ":olean" for p in files]
        self.require_command(["lake", "build", *targets], label="all-source-build")
        return {"regular_Lean_sources_built": len(files), "targets": targets}

    def coverage(self):
        if not (self.root / "CoverageCheck.lean").is_file(): raise ValueError("missing CoverageCheck.lean")
        self.require_command(["lake", "env", "lean", "CoverageCheck.lean"], label="coverage")
        numbered = self.root / "NumberedClaims.lean"
        numbered_checks = []
        if numbered.is_file():
            self.require_command(["lake", "env", "lean", "NumberedClaims.lean"], label="numbered-claims")
            targets = {
                "theorem_2_3_a": ("Theorem 2.3(a): expanded uniform upper target", "substantive"),
                "theorem_2_3_b": ("Theorem 2.3(b): expanded intermediate-class lower target", "substantive"),
                "rho_formula": ("rate parameter formula", "definitional_normalization"),
                "scale_formula": ("rate scale formula", "definitional_normalization"),
                "scale_logarithm": ("exact logarithmic scale identity", "substantive"),
                "lemma_4_1": ("Lemma 4.1: full generating identity", "substantive"),
                "lemma_4_1_at_one": ("Lemma 4.1: specialization at one", "substantive"),
                "lemma_4_6": ("Lemma 4.6: window sum", "substantive"),
                "lemma_5_1": ("Lemma 5.1: affine-density testing path, retaining conditional hypotheses", "substantive"),
                "lemma_6_1": ("Lemma 6.1: sinc/lattice target with bandwidth hypotheses", "substantive"),
                "proposition_7_1_rough": ("Proposition 7.1: rough risk conclusion with concrete input package", "substantive"),
                "proposition_7_1_parametric": ("Proposition 7.1: parametric risk conclusion with concrete input package", "substantive"),
            }
            code = strip_lean_noncode(numbered.read_text(encoding="utf-8"))
            declarations = set(re.findall(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_']*)", code))
            if set(targets) - declarations:
                raise ValueError("numbered target module is missing expected typed declarations: " + ", ".join(sorted(set(targets)-declarations)))
            numbered_checks = [{"declaration": "RoughRegimeVerification." + name,
                                "target_scope": scope, "classification": classification}
                               for name, (scope, classification) in targets.items()]
        return {"declaration_inventory_checked": True, "numbered_claims_exact_target_check": numbered.is_file(),
            "named_typed_checks": numbered_checks,
            "numbered_claims_scope": "only the explicit typed declarations in NumberedClaims.lean; other coverage table rows are not mechanically certified by this check" if numbered.is_file() else "no NumberedClaims.lean target check ran; selected headline type comparison belongs to Comparator",
            "limitation": "inventory existence is not semantic equivalence; only typed exact-target declarations establish the respective numbered targets"}

    def axioms(self):
        if not (self.root / "Audit.lean").is_file(): raise ValueError("missing Audit.lean")
        text = self.require_command(["lake", "env", "lean", "Audit.lean"], label="axiom-audit")
        payloads = []
        # Lean's Json.mkObj does not preserve field insertion order. Its
        # compact inventory may follow an ordinary compiler message prefix.
        for line in text.splitlines():
            start = line.find("{")
            if start < 0: continue
            try: value, _ = json.JSONDecoder().raw_decode(line[start:])
            except ValueError: continue
            if isinstance(value, dict) and value.get("axiom_audit_passed") is True: payloads.append(value)
        if len(payloads) != 1: raise ValueError("Audit.lean must return exactly one successful machine-readable transitive axiom audit")
        expected_modules = sum(1 for p in lean_source_files(self.root)
            if module_name(p, self.root) in {"RoughRegime", "Solution", "NumberedClaims"}
            or module_name(p, self.root).startswith("RoughRegime."))
        for payload in payloads:
            if payload.get("genuine_project_proof_bodies_loaded") is not True:
                raise ValueError("axiom audit did not retain genuine project theorem proof bodies")
            if payload.get("project_module_count") != expected_modules or expected_modules == 0:
                raise ValueError("axiom audit does not cover every local proof module")
            if payload.get("theorem_count", 0) == 0 or payload.get("theorem_count") != len(payload.get("theorems", [])):
                raise ValueError("axiom audit theorem inventory is empty or inconsistent")
            if payload.get("external_dependency_axiom_method") != "canonical upstream compiler-generated transitive axiom inventories":
                raise ValueError("axiom audit lacks the external dependency-method qualification")
            for row in payload.get("theorems", []):
                if not set(row["axioms"]) <= STANDARD_AXIOMS: raise ValueError(f"forbidden transitive axiom: {row['theorem']}")
        config = comparator_config(self.root)
        names = {row["theorem"] for payload in payloads for row in payload.get("theorems", [])}
        missing = set(config["theorem_names"]) - names
        if missing: raise ValueError("selected Comparator theorems missing from axiom audit: " + ", ".join(sorted(missing)))
        inventory = self.output / "axiom-inventory.json"
        write_json(inventory, payloads)
        selected = [row for payload in payloads for row in payload.get("theorems", [])
                    if row["theorem"] in set(config["theorem_names"])]
        return {"project_module_count": sum(p.get("project_module_count", 0) for p in payloads),
            "theorem_count": sum(p.get("theorem_count", 0) for p in payloads),
            "genuine_project_proof_bodies_loaded": True,
            "external_dependency_axiom_method": payloads[0]["external_dependency_axiom_method"],
            "allowed_axioms": sorted(STANDARD_AXIOMS), "axiom_audit_passed": True,
            "external_full_inventory_sha256": digest(inventory.read_bytes()),
            "selected_theorem_axioms": selected}

    def boundary_kernel_diagnostic(self):
        """Replay boundary and literal-definition proofs, explicitly unsandboxed."""
        module = "RoughRegime.LiteralHolder"
        declarations = ["closure_interior_cube", "hasFDerivWithinAt_cube_of_interior_jet",
            "interiorJet_iff_contDiffOn", "InteriorTaylorJet.ftaylorSeries",
            "InteriorTaylorJet.contDiffOn", "InteriorTaylorJet.eq_iteratedFDerivWithin",
            "InteriorTaylorJet.coordinate_eq", "holderNorm_eq_interiorJetHolderNorm",
            "holderOrder_eq_zero_of_le_one", "holderRegularity_le_one_iff",
            "coordinateEvaluation_injective", "continuousOn_coordinate_iff",
            "coordinateTensor_apply", "coordinateEvaluation_reconstruction",
            "coordinateReconstruction_evaluation", "continuousOn_coordinateReconstruction",
            "coordinateGradient_apply_basis", "reconstruction_curryLeft",
            "hasFDerivAt_coordinateReconstruction", "coordinateJetSeries_zero",
            "CoordinatePartialJet.toInteriorTaylorJet_of_fderiv",
            "CoordinatePartialJet.coordinate_eq_of_fderiv",
            "literalDerivativeSup_eq_of_coefficients", "literalHolderSeminorm_eq_of_coefficients",
            "CoordinatePartialJet.fderivInterior", "CoordinatePartialJet.toInteriorTaylorJet",
            "CoordinatePartialJet.coordinate_eq", "continuousOn_coordinateDerivative_of_contDiffOn",
            "hasLineDerivAt_coordinateDerivative_of_contDiffOn", "update_eq_add_coordinate",
            "hasDerivAt_coordinateDerivative_update_of_contDiffOn",
            "coordinatePartialRegularity_iff_contDiffOn", "CoordinatePartialJet.unique",
            "holderNorm_eq_literalHolderNorm"]
        names = ["RoughRegime.Model." + n for n in declarations]
        names.extend("RoughRegime.Calculus." + n for n in ["gradient_apply",
            "gradient_continuousOn", "gradient_cons", "continuous_partials_hasStrictFDerivAt",
            "gradient_comp_piLp", "continuous_partials_hasStrictFDerivAt_euclidean"])
        # The same primitive roots used by the pinned Lake Comparator. These
        # ensure that kernel primitive declarations travel with the export.
        primitives = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
            "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
            "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List",
            "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam",
            "semiOutParam", "outParam", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
        export = self.output / "boundary-bridges.ndjson"
        proc = self.command(["lake", "env", str(self.prefix / "bin" / "leanexport"), module,
            "--", *names, *sorted(STANDARD_AXIOMS), *primitives],
            label="boundary-export", stdout_path=export)
        if proc.returncode: raise ValueError(f"boundary exporter exited {proc.returncode}")
        config = self.output / "boundary-nanoda.json"
        write_json(config, {"use_stdin": False, "export_file_path": str(export),
            "permitted_axioms": sorted(STANDARD_AXIOMS), "unpermitted_axiom_hard_error": True,
            "num_threads": 4, "nat_extension": True, "string_extension": True})
        for label, args in (
            ("boundary-con-ron", ["con-ron", "--verified", "--jobs=4", str(export)]),
            ("boundary-nanoda", ["nanoda_bin", str(config)]),
            ("boundary-Lean", ["leanchecker", "--silent", "--from-export", str(export)])):
            self.require_command([str(self.prefix / "bin" / args[0]), *args[1:]], label=label)
        return {"module": module, "theorem_names": names,
            "export_sha256": digest(export.read_bytes()), "export_bytes": export.stat().st_size,
            "Lean_NanoDa_and_verified_con_ron_completed": True,
            "supplementary_unsandboxed_diagnostic_only": True,
            "Palomar_compliant_verification_claim": False,
            "scope": "finite-order boundary, coordinate reconstruction, genuine ordinary-partial calculus, and exact literal Holder regularity/norm equivalence"}

    def comparator(self, *, diagnostic: bool = False):
        if not diagnostic and not shutil.which("bwrap"):
            raise Blocked("the primary Comparator check requires bwrap; no automatic unsandboxed fallback is permitted")
        if not diagnostic:
            # Fail before Lake's asynchronous pipe reader if this environment
            # rejects bubblewrap namespace creation. This probe is not a proof
            # check and is never applied to the explicitly unsandboxed option.
            preflight = self.command(["bwrap", "--ro-bind", "/", "/", "--", "/bin/true"],
                label="comparator-namespace-preflight", timeout_seconds=min(self.timeout, 10))
            if preflight.returncode:
                detail = " ".join(preflight.stdout.strip().split())[:1000] or "bubblewrap rejected the namespace probe"
                raise Blocked(f"primary Comparator namespace preflight failed (exit {preflight.returncode}): {detail}")
        config = comparator_config(self.root)
        config.pop("enable_nanoda", None)
        config["external_kernels"] = {"nanoda": [str(self.prefix / "bin" / "nanoda_bin")], "con-ron": [str(self.prefix / "bin" / "con-ron")]}
        with tempfile.TemporaryDirectory(prefix="palomar-comparator-", dir=self.output) as tmp:
            path = Path(tmp) / "protected-comparator.json"
            write_json(path, config)
            argv = ["lake", "comparator", "--config", str(path)]
            if diagnostic:
                argv.append("--inadvisably-no-sandbox")
            proc = self.command(argv, label="comparator-diagnostic" if diagnostic else "comparator")
        if proc.returncode:
            if proc.returncode == 2 or re.search(r"^(?:bwrap: |Error while interacting with |error: Error while interacting with )", proc.stdout, re.M):
                raise Blocked(f"Comparator/independent-kernel infrastructure unavailable (exit {proc.returncode}); see external log")
            if re.search(r"^(?:error: (?:Const |Constant |Challenge |Solution |Illegal axiom)|Lean default kernel rejected the solution)", proc.stdout, re.M):
                raise ValueError(f"Comparator rejected the solution (exit {proc.returncode}); see external log")
            raise Blocked(f"Comparator did not verify the solution (exit {proc.returncode}); independent-kernel disagreement or other infrastructure failure; see external log")
        return {"exit_code": proc.returncode, "external_kernels": config["external_kernels"],
            "namespace_preflight_exit_code": None if diagnostic else preflight.returncode,
            "namespace_preflight_scope": "skipped for the explicitly requested unsandboxed diagnostic" if diagnostic else "namespace availability only; proof checks are performed separately by Comparator",
            "Lean_and_both_required_independent_kernels_completed": True,
            "supplementary_unsandboxed_diagnostic_only": diagnostic,
            "Palomar_compliant_verification_claim": False if diagnostic else "local required-kernel check; service sandbox not reproduced",
            "configuration_strategy": "protected temporary copy strips enable_nanoda and installs both bundled kernels",
            "service_protected_canonical_Challenge_sandbox": "not reproduced by this local tool"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=PROJECT_DIRECTORY)
    parser.add_argument("--output", type=Path, help="evidence directory outside the public source tree")
    parser.add_argument("--static-only", "--static", dest="static_only", action="store_true", help="do not claim build or kernel verification")
    parser.add_argument("--diagnostic-comparator", action="store_true",
                        help="add a separately reported unsandboxed diagnostic; never repairs a failed primary check")
    parser.add_argument("--timeout", type=int, default=7200, help="seconds allowed per command")
    args = parser.parse_args()
    root = args.root.resolve()
    output = (args.output or root.parent / "verification-output").resolve()
    if output.is_relative_to(root): parser.error("--output must be outside the public source tree")
    verifier = Verifier(root, output, args.timeout)
    try: before = snapshot(root)
    except Exception as error:
        write_json(output / "verification.json", {"status": "fail", "error": str(error)})
        print(f"FAIL: {error}"); return 1
    verifier.report["source_fingerprint"] = before["source_fingerprint"]
    write_json(output / "source-manifest.json", before)
    if (root / ".git").exists():
        result = verifier.command(["git", "rev-parse", "HEAD"], label="source-revision")
        verifier.report["git_revision_at_start"] = result.stdout.strip() if result.returncode == 0 else None
        status = verifier.command(["git", "status", "--porcelain", "--untracked-files=all"], label="source-git-status")
        verifier.report["git_worktree_clean_at_start"] = status.returncode == 0 and not status.stdout.strip()
        verifier.report["git_revision_identifies_exact_source"] = result.returncode == 0 and verifier.report["git_worktree_clean_at_start"]
        verifier.report["source_identity_note"] = "the source fingerprint and per-file manifest identify the checked content; an unclean worktree is not identified by HEAD alone"
    static_ok = True
    for name, action in (("repository_structure_and_current_source_limits", verifier.structure),
                         ("exact_formalization_metadata_contract", verifier.metadata),
                         ("comparator_and_lexical_proof_safety", verifier.source_safety),
                         ("exact_dependency_pins", verifier.pins), ("local_documentation_links", verifier.links)):
        static_ok = verifier.check(name, action) and static_ok
    if not args.static_only and static_ok:
        runtime_ok = verifier.check("pinned_runtime_and_required_kernel_executables", verifier.runtime)
        runtime_ok = verifier.check("canonical_dependency_checkouts", verifier.dependency_checkouts) and runtime_ok
        if runtime_ok:
            headers_ok = verifier.check("compiler_confirms_all_module_headers", verifier.compiler_headers)
            imports_ok = verifier.check("Challenge_direct_and_transitive_import_provenance", verifier.challenge_imports)
            built = verifier.check("all_submitted_Lean_sources_build", verifier.build) if headers_ok and imports_ok else False
            if built:
                verifier.check("coverage_and_numbered_exact_targets", verifier.coverage)
                verifier.check("all_project_and_selected_transitive_axioms", verifier.axioms)
                verifier.check("Comparator_Lean_NanoDa_con_ron", verifier.comparator)
                if args.diagnostic_comparator:
                    verifier.check("supplementary_unsandboxed_Comparator_diagnostic",
                                   lambda: verifier.comparator(diagnostic=True))
                    verifier.check("supplementary_unsandboxed_boundary_bridge_kernels",
                                   verifier.boundary_kernel_diagnostic)
            else:
                for name in ("coverage_and_numbered_exact_targets", "all_project_and_selected_transitive_axioms", "Comparator_Lean_NanoDa_con_ron"):
                    verifier.report["checks"].append({"check": name, "status": "not_run", "reason": "a complete current-source build did not pass"})
    else:
        verifier.report["checks"].append({"check": "runtime_verification", "status": "not_run", "reason": "static-only requested" if args.static_only else "static source checks failed"})
    unchanged = verifier.check("source_snapshot_unchanged_during_verification", lambda: {
        "source_fingerprint": after["source_fingerprint"]} if (after := snapshot(root))["source_fingerprint"] == before["source_fingerprint"]
        else (_ for _ in ()).throw(ValueError("public source changed while verification was running")))
    statuses = [c["status"] for c in verifier.report["checks"]]
    verifier.report["status"] = "fail" if "fail" in statuses else "blocked" if "blocked" in statuses else "incomplete" if "not_run" in statuses else "pass"
    verifier.report["verification_scope"] = "static-only" if args.static_only else "full-local"
    verifier.report["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    write_json(output / "verification.json", verifier.report)
    print(f"{verifier.report['status'].upper()}: {output / 'verification.json'}")
    return 0 if verifier.report["status"] == "pass" or (args.static_only and static_ok and unchanged) else 1


if __name__ == "__main__":
    raise SystemExit(main())
