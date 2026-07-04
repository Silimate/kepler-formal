# SystemVerilog Support

This document tracks the SystemVerilog flow in `kepler-formal`.

Status:

- supported for RTL-level and gate-level SEC
- supported through direct source lists or flists with explicit tops
- LEC and non-SEC SystemVerilog coverage may still evolve with the frontend

## Current scope

The SystemVerilog path supports sequential equivalence checking on RTL-level
and gate-level designs. It uses the same `verification: sec` mode and SEC
engines documented in [sec-flags-spec.md](../sec-flags-spec.md).

Current entry points include:

- CLI:
  - `-systemverilog`
  - `-sv`
- YAML `format`:
  - `systemverilog`
  - `sv`

## Current CLI forms

```bash
# Classic (single file per design)
build/src/bin/kepler-formal <-systemverilog/-sv> [--verilog_preprocessing] <netlist1> <netlist2> [<library-file>...]

# Multi-file SystemVerilog designs
build/src/bin/kepler-formal <-systemverilog/-sv> [--verilog_preprocessing] --design1 <file...> --design2 <file...> \
  [--liberty <library-file>...]

# slang flists with explicit tops
build/src/bin/kepler-formal -systemverilog \
  --sv_design1_flist <file> --sv_design1_top <name> \
  --sv_design2_flist <file> --sv_design2_top <name> \
  -v sec
```

`--verilog_preprocessing` is also accepted as `--verilog-preprocessing`.

## Flist mode

For SystemVerilog designs that are already driven by a slang command file or flist, use:

- `sv_design1_flist`
- `sv_design2_flist`
- `sv_design1_top`
- `sv_design2_top`

This mode is flist-based. Do not combine it with:

- `input_paths`
- `--design1`
- `--design2`

## YAML examples

Multi-file SystemVerilog example:

```yaml
format: systemverilog
verification: sec
input_paths:
  - [design0_pkg.sv, design0_top.sv]
  - [design1_pkg.sv, design1_top.sv]
liberty_files:
  - stdcells.lib.gz
  - primitives.py
```

Flist example:

```yaml
format: systemverilog
verification: sec
sv_design1_flist: /path/to/design1.f
sv_design1_top: top1
sv_design2_flist: /path/to/design2.f
sv_design2_top: top2
liberty_files:
  - stdcells.lib.gz
```

## Notes

- Use `verification: sec` or `-v sec` for RTL-level SystemVerilog equivalence
  checking.
- If you are documenting broad usage for new users, prefer the top-level
  [README](../../README.md).
