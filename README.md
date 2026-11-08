# The Little Leaner — companion code

Code for *The Little Leaner: Dependent Types and Proofs in Lean 4, One Question at a Time*
by Volodymyr Pavlyshyn. Every program in the book is cut from this repository, and every
output, error, and goal printed in the book is a golden file here that the test checks.

| Path | What |
|---|---|
| `lib/Pond.lean` | the running example: eight critters and who eats whom |
| `ch01/` … `ch10/` | examples per chapter; `FILE.out` is what Lean prints for `FILE.lean` |
| `solutions/` | solutions to every exercise, `chNN.lean` with its output `chNN.out` |
| `tests/run_lean.py` | the golden-file test |

## Run

Install [elan](https://lean-lang.org), then:

```bash
lake build                       # builds the pond (and fetches Lean 4.35.0)
lake env lean ch01/hello.lean    # one example
python3 tests/run_lean.py        # every example against its golden output
```

Open the folder in VS Code with the Lean 4 extension to see every goal live. The
`trace_state` lines in the examples print the goal at that point; the book shows those
goals and leaves the lines out.

Core Lean only: no Mathlib, nothing else to download.

Code: Apache-2.0. The book: CC BY 4.0.
