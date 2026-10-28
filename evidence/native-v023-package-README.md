# H00 two-route Lean construction v0.2.3

This is a focused repair of MeasureResolvent after the supplied v0.2.2 native
diagnostics. It changes exactly one Lean file and three proof bodies:

- Remove a tactic after transform_zero has already closed its goal.
- Convert RCLike.im to Complex.im explicitly in the integral identity.
- Transport the real moment equality through Complex.ofReal, using an explicitly
  real-valued integral, before rewriting the complex resolvent coefficient.

Every theorem statement and hypothesis is unchanged. All other Lean files,
including the reported compiled-and-audited ActualLimitBridge and
AngularGeometry modules, are byte-preserved. Their user-reported PASS markers
and receipt paths are retained under evidence/v0_2_3_measure_fix. The overall
v0.2.2 run failed; no endpoint or final aggregate audit PASS is claimed.

No local Lean, Lake, compiler or CI was executed. These repairs require native
compilation and the exact axiom audit. The source retains both H00-to-literal-RH
endpoints and their equivalences. H00 remains assumed; finite-checker
soundness/completeness and the longer Widder/angular branch remain open.

## Storage and reuse

Native target: LOCAL_COMPILER, Windows Lean 4.33.0.
Workspaces: E:\RH-SLOW\workspaces
New anchor writes: E:\RH-SLOW\anchors
Optional checked import: E:\RH-FAST\anchors

The runner differs from v0.2.2 only in package/version identifiers. Cache
identity checks, audit enforcement, Lake source mapping, locks and shutdown
are unchanged. Existing valid E:\RH-SLOW anchors are reused first. The old
E:\RH-FAST anchors remain a read-only checked import source. No anchor is
deleted or manually trusted. The changed module and affected dependents must
rebuild and pass their audit.

## Run

Place the ZIP in Downloads and paste into Windows Command Prompt:

```cmd
cd /d "%USERPROFILE%\Downloads" && (if not exist "E:\RH-SLOW\workspaces" mkdir "E:\RH-SLOW\workspaces") && tar -xf "RH_H00_TWO_ROUTES_LEAN_v0_2_3_construction.zip" -C "E:\RH-SLOW\workspaces" && set "LEAN_ANCHORINGS_IMPORT_ROOT=E:\RH-FAST\anchors" && cmd /k call "E:\RH-SLOW\workspaces\RH_H00_TWO_ROUTES_LEAN_v0_2_3_construction\run.cmd"
```

Retain run-result.json, run-build.log and run-audit.log. This package contains
no new native PASS record. The 117-module compile order and 641 audit targets
remain unchanged.
