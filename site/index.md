---
layout: default
title: Home
---

# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields Q(√d) and the classification of their ring of integers.

## About

This project formalizes:
- Definition of quadratic number fields Q(√d)
- Ring of integers classification for quadratic fields
- Euclidean domain structure
- Norm computations

## Quick Links

- [GitHub Repository](https://github.com/FrankieeW/QuadraticNumberFields)
- [Lean](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib)

## Build

```bash
cd Lean
lake exe cache get
lake build
```

## Reference

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
