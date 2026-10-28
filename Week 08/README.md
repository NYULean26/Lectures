# Week 08: Functors, applicatives, and IO

- [Worksheet](Lecture08.lean)
- [Solutions](Lecture08_Solution.lean)
- [Lecture slides](Lecture08.pdf)
- [Option' instances and laws](option-prime-reference.lean)
- [Instructor copy](Lecture08_Instructor.lean)

Open each Lean file independently in this repository's Lean environment.
Fill a definition, then uncomment its checks. Sections A–E are the core; F–I are optional.

From the repository root, run the first checkpoint before filling any holes:

```sh
lake env lean --run 'Week 08/Lecture08.lean' read
```

Enter `6`, then `2`, on separate lines.

| Checkpoint | Ready when |
| --- | --- |
| `read` | Immediately |
| `check` | B1, C1, C2, D1 are complete |
| `run` (optional) | B1, C1, C2, D1, F1 are complete |
| `even` | Supplied optional demonstration |

To demonstrate the full report without completing optional F1, use the solution file.

For `check` and `run`, enter two lines per row (`x`, then `y`), ending with EOF
(Ctrl-D on an empty terminal line). Proof holes may remain; running an unfinished
computational definition can fail. The file's active `#eval` commands also print
before the checkpoint starts.

```sh
printf '6\n2\n4\n1\n' | lake env lean --run 'Week 08/Lecture08_Solution.lean' run
```

Based on [FPiL 4.5, 5.2–5.3, 6.2–6.4](https://lean-lang.org/functional_programming_in_lean/)
and [LoVe 7](https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe07_EffectfulProgramming_Demo.lean).
