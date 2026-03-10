---
layout: default
title: Resources
---

# Resources

## Learning Materials

### Textbooks

**Algebraic Number Theory:**
- *Algebraic Number Theory* by Jürgen Neukirch
  - Comprehensive treatment of algebraic number theory
  - Chapter 1 covers quadratic fields in detail

- *A Course in Computational Algebraic Number Theory* by Henri Cohen
  - Practical algorithms for computations
  - Excellent for implementation details

- *Introduction to Algebraic Number Theory* by Edmund Landau
  - Classical approach to the subject
  - Clear exposition of foundational results

**Quadratic Forms:**
- *The Sensual Quadratic Form* by John H. Conway
  - Geometric perspective on quadratic forms
  - Connection to quadratic number fields

### Online Resources

**Lean 4 and mathlib:**
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/) - Official documentation
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - Tutorial for mathematical formalization
- [mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/) - API reference
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) - Community discussion

**Number Theory:**
- [LMFDB](https://www.lmfdb.org/) - L-functions and Modular Forms Database
  - Extensive data on number fields
  - Computational invariants

- [Number Theory Web](http://www.numbertheory.org/)
  - Online seminars and resources
  - Research papers and preprints

## Related Formalizations

### In Lean

**mathlib contributions:**
- `NumberTheory.NumberField` - General number field theory
- `RingTheory.DedekindDomain` - Dedekind domains and their properties
- `NumberTheory.ClassNumber` - Class groups and class numbers
- `NumberTheory.Cyclotomic` - Cyclotomic fields

**Related projects:**
- [Fermat's Last Theorem for Regular Primes](https://github.com/leanprover-community/flt-regular)
- [Liquid Tensor Experiment](https://github.com/leanprover-community/liquid)

### In Other Proof Assistants

**Coq:**
- [Mathematical Components](https://math-comp.github.io/)
  - Formalization of finite group theory
  - Applications to Galois theory

**Isabelle/HOL:**
- [Archive of Formal Proofs - Number Theory](https://www.isa-afp.org/topics/number-theory.html)
  - Various number-theoretic results
  - Quadratic reciprocity

**Agda:**
- [agda-unimath](https://unimath.github.io/agda-unimath/)
  - Univalent foundations approach

## Software Tools

### Computer Algebra Systems

**SageMath:**
```python
# Working with quadratic fields in Sage
K.<a> = QuadraticField(-3)
O = K.ring_of_integers()
O.basis()  # [1, 1/2*a + 1/2]
```

**Magma:**
```
// Quadratic field in Magma
K := QuadraticField(-3);
R := MaximalOrder(K);
ClassNumber(K);
```

**PARI/GP:**
```
? K = bnfinit(x^2 + 3);
? K.clgp  \\ class group structure
```

### Lean Development

**VS Code Setup:**
1. Install [VS Code](https://code.visualstudio.com/)
2. Install the [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
3. Clone this repository
4. Open in VS Code
5. Lean will automatically set up the environment

**Building this project:**
```bash
lake exe cache get  # Download mathlib cache
lake build          # Build the project
```

## Mathematical Background

### Prerequisites

To understand this formalization, familiarity with the following topics is helpful:

**Algebra:**
- Ring theory (ideals, homomorphisms, quotients)
- Field theory (field extensions, minimal polynomials)
- Galois theory (automorphisms, normal extensions)

**Number Theory:**
- Divisibility and primes
- Modular arithmetic
- Quadratic residues

**Formalization:**
- Dependent type theory
- Proof tactics
- Mathematical libraries

### Further Study

**Next topics to explore:**
1. **Class field theory** - Generalization to abelian extensions
2. **Iwasawa theory** - p-adic aspects of number fields
3. **Modular forms** - Connection to L-functions
4. **Arakelov theory** - Geometric approach to number theory

## Historical Notes

### Timeline

**Ancient:**
- Pythagorean triples: $a^2 + b^2 = c^2$ (related to $\mathbb{Z}[i]$)

**17th-18th Century:**
- Fermat's two-square theorem (1640s)
- Euler's work on binary quadratic forms (1750s)
- Lagrange on continued fractions (1770s)

**19th Century:**
- Gauss's *Disquisitiones Arithmeticae* (1801)
  - Binary quadratic forms
  - Composition law
- Dirichlet's unit theorem (1846)
  - Structure of unit groups
- Dedekind's theory of ideals (1870s)
  - Ideal factorization
  - Class groups
- Kronecker-Weber theorem (1886)
  - Abelian extensions of $\mathbb{Q}$

**20th Century:**
- Class field theory (1920s-1930s)
  - Artin, Hasse, Takagi
- Stark-Heegner theorem (1967-1969)
  - Classification of imaginary quadratic fields with class number 1
- Cohen-Lenstra heuristics (1983)
  - Statistical predictions about class groups

**21st Century:**
- Computational advances
- Formalization in proof assistants
- This project (2026)!

## Community

### Contributing

We welcome contributions! Areas where help is needed:

1. **Additional examples** - More concrete computations
2. **Euclidean domains** - Formalize the Euclidean property
3. **Class numbers** - Compute class groups
4. **Documentation** - Improve explanations and tutorials
5. **Testing** - Verify computations with known results

See the [GitHub Issues page](https://github.com/FrankieeW/QuadraticNumberFields/issues) to report bugs or discuss new features.

### Discussion

- GitHub Issues: [Report bugs or request features](https://github.com/FrankieeW/QuadraticNumberFields/issues)
- Lean Zulip: [#mathlib](https://leanprover.zulipchat.com/#narrow/stream/116395-maths) stream

## Acknowledgments

This formalization builds on:
- **mathlib contributors** - Extensive library of mathematical results
- **Lean community** - Tools, documentation, and support
- **Previous formalizations** - Dedekind domains, number fields

Special thanks to the Lean Zulip community for guidance on the $(1+\sqrt{1+4k})/2$ representation.

## Citation

If you use this formalization in your research, please cite:

```bibtex
@misc{quadratic-number-fields-lean,
  author = {Wang, Frankie},
  title = {Quadratic Number Fields in Lean 4},
  year = {2026},
  publisher = {GitHub},
  url = {https://github.com/FrankieeW/QuadraticNumberFields}
}
```

[← Back to Home](index.html)
