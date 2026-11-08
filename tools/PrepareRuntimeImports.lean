import Lean

/-!
Patch Mathlib and Batteries in `.lake/packages` to mark tactic imports as meta-only.
These tactics are needed during compilation, not when running forms; this keeps
the Wasm build from compiling and linking unnecessary tactic code.
Checks dependency versions before patching; safe to run repeatedly.

Run from the repository root, like the Wasm Makefile.
-/

open Lean

private structure Package where
  name : String
  rev? : Option String := none
  deriving FromJson

private structure Manifest where
  packages : Array Package
  deriving FromJson

private structure RuntimePatch where
  name : String
  revision : String

private def git (package : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", package.toString] ++ args }

private def RuntimePatch.apply (patch : RuntimePatch) (manifest : Manifest) : IO Unit := do
  let { name, revision } := patch
  let some entry := manifest.packages.find? (·.name == name)
    | throw (IO.userError s!"{name}: missing from lake-manifest.json")
  unless entry.rev? == some revision do
    throw (IO.userError s!"{name}: update the runtime import patch for the new dependency revision")
  let package := System.FilePath.mk ".lake/packages" / name
  let patchPath ← IO.FS.realPath (System.FilePath.mk "wasm" / s!"{name}-runtime-imports.patch")
  let checkout ← git package #["rev-parse", "HEAD"]
  unless checkout.exitCode == 0 do
    throw (IO.userError checkout.stderr)
  unless checkout.stdout.trimAscii.toString == revision do
    throw (IO.userError s!"{name}: checkout does not match lake-manifest.json")
  let applied ← git package #["apply", "--reverse", "--check", patchPath.toString]
  if applied.exitCode == 0 then return
  let check ← git package #["apply", "--check", patchPath.toString]
  unless check.exitCode == 0 do
    throw (IO.userError s!"{name}: runtime import patch conflicts with local changes\n{check.stderr}")
  let result ← git package #["apply", patchPath.toString]
  unless result.exitCode == 0 do
    throw (IO.userError result.stderr)
  IO.println s!"Applied {name} runtime import patch"

def main : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let manifest : Manifest ← IO.ofExcept (fromJson? json)
  let patches : Array RuntimePatch := #[
    { name := "batteries", revision := "66e469188fe07963e5cf666c7d4433f45b8131c5" },
    { name := "mathlib", revision := "56a005855ea17e0b0958f73ec801ae140b0a1679" }]
  for patch in patches do
    patch.apply manifest
