---
layout: default
title: TernaryFrames
---

# TernaryFrames

Formalization of ternary frames and incoherence-space semantics in Lean 4.

## Start Here

- API documentation: [`/docs`](./docs/)
- Project repository: [GitHub](https://github.com/lucyhorowitz/TernaryFrames)

## Reading Order

1. `TernaryFrames/Basic.lean`: ternary frames and semantic connectives.
2. `TernaryFrames/IncoherenceSpace.lean`: positions, incoherence, entailment, and fusion.
3. `TernaryFrames/Containment.lean`: containment conditions and closed-set structure.
4. `TernaryFrames/DayConvolution.lean`: tensor on closed sets and quantale structure.
5. `TernaryFrames/ISSTernaryFrame.lean`: incoherence spaces as ternary frames.
6. `TernaryFrames/NMMS.lean`: NMMS and NMMS^ctr proof systems.
7. `TernaryFrames/Soundness.lean`: soundness and completeness results.

## How To Read A File

For each file, look for:

1. The module docstring at the top (`/-! ... -/`) for motivation and section map.
2. Definition docstrings (`/-- ... -/`) for key objects.
3. "Main theorem" statements near the end of each section.
