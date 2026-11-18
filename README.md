# lsm-tree — RawPage header offset out-of-bounds read

End-to-end proof of concept for an out-of-bounds heap access in
[`IntersectMBO/lsm-tree`](https://github.com/IntersectMBO/lsm-tree), reachable through the public
`importSnapshot` API.

| | |
|---|---|
| Target | `IntersectMBO/lsm-tree` at `63a63054` (`Merge pull request #897`) |
| Package | `lsm-tree` `1.1.1.0` |
| Toolchain | GHC `9.6.6`, cabal `3.10.3.0`, Ubuntu 24.04 |
| Class | CWE-125, out-of-bounds read |
| Impact demonstrated | process abort, `SIGSEGV`, in the release build configuration |
| Advisory | `GHSA-vrqw-c78x-8j8q` (private, filed 2026-11-18) |
| Run cited | [44159258480](https://github.com/0xasuma/lsm-rawpage-oob-poc/actions/runs/44159258480) |

## What the bug is

A data page header stores `numKeys`, `numBlobs` and `keysOffset` as three little-endian `Word16`
fields at bytes 0, 2 and 4. `rawPageKeysOffset` returns `keysOffset` and it is used directly as a
byte offset when building the key-offset vector:

```
src-core/Database/LSMTree/Internal/RawPage.hs:337-345
  mkPrimVector (off + div2 dirOffset) (dirNumKeys + 1) ba
```

Nothing checks that `keysOffset` is within the 4096-byte page. The only guard in the chain is an
`assert` in `mkPrimVector` (`Vector.hs:37-42`), and two things defeat it:

1. `isValidSlice` compares against the `ByteArray` bounds, not the page boundary. If the page is a
   slice of a larger allocation, an offset past the page but inside the array passes.
2. Haskell's `assert` is discarded under `-O`, which implies `-fignore-asserts`.
   `cabal.project.debug` adds `-fno-ignore-asserts`; `cabal.project.release`, the production
   configuration, does not.

The checksum layer does not help. `Run.openFromDisk` verifies CRC32C for every file in the bundle,
and the `.checksums` files are part of the bundle, so whoever supplies the bundle supplies the
checksums too.

## What the harness does

`Poc.hs` does not hand-build a snapshot format. It asks the library to produce a legitimate bundle,
then edits one field and repairs the bundle's own checksums:

1. Insert six entries, `saveSnapshot "snap1"`, `exportSnapshot`.
2. Overwrite `keysOffset` at byte 4 of page 0 in every `.keyops` file with `0xFFF0` (65520) on a
   4096-byte page.
3. Recompute each `CRC32C (<file kind>)` entry in the `.checksums` files from the edited bytes.
4. `importSnapshot` — returns without throwing, CRC check passes.
5. `withTableFromSnapshot` + `lookups` on six keys — returns `Nothing` and raises nothing, because
   this path allocates from an arena with `blockSize = 0x100000` (1 MiB), so offset 65520 is still
   inside the allocation.
6. Insert 34 more entries to force a merge. This drives `RunReader.readDiskPage`, which allocates
   exactly 4096 bytes.
7. Result: `SIGSEGV`.

Passing `--control` skips steps 2 and 3. That is the negative control.

## Reproduce

The workflow pins the upstream commit and prints `git log --oneline -1`, so the audited revision is
verifiable in the log:

```bash
gh workflow run poc.yml
gh run watch
gh run download --name poc-logs
```

Or locally, with the upstream clone at `63a63054`:

```bash
git clone https://github.com/IntersectMBO/lsm-tree.git upstream
cd upstream && git checkout 63a6305
mkdir -p lsm-tree/poc && cp ../Poc.hs lsm-tree/poc/Poc.hs
cat ../poc-stanza.txt >> lsm-tree/lsm-tree.cabal
cabal build poc-oob --project-file=cabal.project.release --constraint="blockio +serialblockio"
```

## Expected result

Four configurations, identical input, identical code. The only variables are the build
configuration and whether steps 2 and 3 ran.

| Build configuration | Bundle untouched (control) | Bundle modified |
|---|---|---|
| `cabal.project.release` (production) | `RUN_EXIT=0` | `RUN_EXIT=139`, `SIGNAL=11` |
| `cabal.project.release` + `-fno-ignore-asserts` | `RUN_EXIT=0` | `RUN_EXIT=0`, `Assertion failed` caught by `try` |

Production run, last lines before the process died:

```
[4] force a merge -> RunReader sequential path (exactly-4096-byte pages)
RUN_EXIT=139
SIGNAL=11
```

Same binary with asserts restored, same input:

```
[4] force a merge -> RunReader sequential path (exactly-4096-byte pages)
  exception during merge  = Assertion failed
  STEP4: bounded

TOP-LEVEL: completed normally
RUN_EXIT=0
```

Both control runs exit 0, which rules out the harness itself as the cause.

## What is not claimed

- No write primitive. No code path uses a header offset for writing, so RCE is not claimed.
- No proven exfiltration through the public API. On the batch path the result was `Nothing`, not
  leaked bytes. At the internal API level `rawPageIndex` does return bytes outside the page — with a
  directory placed at offset 4096 and the payload at byte 5000 it returns `76,69,65,75,45`, the
  ASCII string `LEAK-` — but steering those bytes into attacker-readable output would need a
  heap-spray experiment that has not been done.
- No remote or pre-auth vector. This is a library, not a service. An attacker has to get the victim
  to import a bundle the attacker supplied.

## Suggested remediation

Validate `numKeys`, `keysOffset`, `valuesOffset` and `blobsOffset` against `pageSize` when a page is
parsed, before any of them is used as an offset, and reject with `FileFormatError`. Independently,
add `-fno-ignore-asserts` to `cabal.project.release`, or replace the `assert` in `mkPrimVector` with
an unconditional bounds check.

## Files

| File | Purpose |
|---|---|
| `Poc.hs` | the harness |
| `poc-stanza.txt` | cabal test-suite stanza appended to `lsm-tree.cabal` |
| `.github/workflows/poc.yml` | 2x2 matrix runner, uploads the four logs |
