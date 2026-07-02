# TYPES family spike (C3.2) — analysis only

## Probes (native PeTTa vs LeaTTa --petta, 2026-07-02)

Bare `get-type` AGREES on all 6 probe shapes (symbol decl, arrow, applied
function, grounded literal, parametric constructor with type-var
instantiation, undeclared → `%Undefined%`). So `get-type` itself is NOT the
divergence. Per-file diffs on the four TYPES-tagged files show the real
split:

| File | leatta-only residue | Cause |
|---|---|---|
| `types` | `(Error … (BadArgType 2 A T))` | HE **runtime type-CHECKING** rejects a call PeTTa evaluates permissively |
| `functiontypes` | `(Error … (BadArgType 2 Expression Number))` | same — HE `typeMismatch` fires where PeTTa does not |
| `matchtypes` | extra `"Matched!"`/`true` | LeaTTa produces MORE results (type-gated match admits where PeTTa's translation does not) |
| `meta_types` | `false` vs `true` | type-predicate disagreement downstream of checking |

## Verdict: two families, neither a cheap grounding arm

- **TYPECHECK-1** (the real one): the minimal kernel enforces argument
  type-checking (`typeMismatch`/`BadArgType`, gradual-typing machinery in
  `getTypes`/`argMask`); native PeTTa is **more permissive** — it does not
  reject on argument type at call time (DIV-007/`b5` "leniency" family from
  the registry, confirmed here on native). This is a *dialect switch*, not a
  builtin: a `typecheckStrict : Bool` profile field that, when false, makes
  `typeMismatch` a no-op (return the call for evaluation instead of a
  `BadArgType` error). Structural but SMALL — one profile field + the branch
  in the kernel's type gate, mirrors the existing `successTrue`/`ifArity2`
  pattern exactly.
- **TYPES-STRUCTURAL** (`matchtypes`, `meta_types`): result-set differences
  downstream of type-gated match/meta-evaluation — entangled with MODE-1
  (relational match) and the translator surface. NOT a clean flag.

## Go / no-go

- **TYPECHECK-1: GO, ~75%** — a `typecheckStrict := false` petta field is the
  same shape as the shipped dialect switches; expected to flip `types` and
  `functiontypes` (2 files) plus reduce spurious `BadArgType` residue in
  several DIFF-COUNT files. ~half a session. Deferred to the next coverage
  chunk (this milestone is analysis-only per the goal).
- **TYPES-STRUCTURAL: NO-GO as a profile arm** — belongs with the MODE-1 /
  Prolog-layer campaign; ledger as its own family.

Retag: `types`, `functiontypes` → TYPECHECK-1 (armable); `matchtypes`,
`meta_types` → TYPES-STRUCTURAL (Prolog-layer). `parametric_types`,
`recursive_types`, `types_dependent`, `types_nondet` to be re-probed when
TYPECHECK-1 ships (likely a mix).
