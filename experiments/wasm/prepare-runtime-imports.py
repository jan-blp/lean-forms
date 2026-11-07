import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
packages = {p["name"]: p for p in json.loads((root / "lake-manifest.json").read_text())["packages"]}
revisions = {
    "batteries": "66e469188fe07963e5cf666c7d4433f45b8131c5",
    "mathlib": "56a005855ea17e0b0958f73ec801ae140b0a1679",
}

for name, expected in revisions.items():
    package = root / ".lake/packages" / name
    patch = Path(__file__).with_name(f"{name}-runtime-imports.patch")
    if packages[name]["rev"] != expected:
        sys.exit(f"{name}: update the runtime import patch for the new dependency revision")
    revision = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
    if revision != expected:
        sys.exit(f"{name}: checkout does not match lake-manifest.json")
    command = ["git", "-C", str(package), "apply"]
    if subprocess.run(command + ["--reverse", "--check", str(patch)], capture_output=True).returncode == 0:
        continue
    check = subprocess.run(command + ["--check", str(patch)], capture_output=True, text=True)
    if check.returncode:
        sys.exit(f"{name}: runtime import patch conflicts with local changes\n{check.stderr}")
    subprocess.run(command + [str(patch)], check=True)
    print(f"Applied {name} runtime import patch")
