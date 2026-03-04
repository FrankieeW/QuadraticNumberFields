---
layout: default
title: Examples and Applications
---

# Examples and Applications

## Classical Examples of Quadratic Number Fields

### Example 1: Gaussian Integers ($d = -1$)

The **Gaussian integers** form one of the most well-known examples of quadratic number fields.

**Field:** $\mathbb{Q}(i)$ where $i = \sqrt{-1}$

**Classification:**
- Since $-1 \equiv 3 \pmod{4}$, we have Case 1
- $\mathcal{O}_{\mathbb{Q}(i)} = \mathbb{Z}[i] = \{a + bi : a, b \in \mathbb{Z}\}$

**Norm:** For $z = a + bi$:
$$N(z) = z \cdot \overline{z} = (a + bi)(a - bi) = a^2 + b^2$$

**Units:** The units in $\mathbb{Z}[i]$ are exactly $\{\pm 1, \pm i\}$
- These are the elements with norm $\pm 1$
- Form a cyclic group of order 4

**Primes:** A rational prime $p$ behaves in $\mathbb{Z}[i]$ as follows:
- $p = 2$: ramifies as $2 = -i(1+i)^2$
- $p \equiv 1 \pmod{4}$: splits as $p = \pi \overline{\pi}$ where $\pi$ is a Gaussian prime
- $p \equiv 3 \pmod{4}$: remains prime in $\mathbb{Z}[i]$

**Applications:**
- Pythagorean triples: $a^2 + b^2 = c^2$ correspond to factorizations in $\mathbb{Z}[i]$
- Sums of two squares: A prime $p$ is a sum of two squares iff $p = 2$ or $p \equiv 1 \pmod{4}$

### Example 2: Eisenstein Integers ($d = -3$)

The **Eisenstein integers** are closely related to hexagonal lattices and the sixth roots of unity.

**Field:** $\mathbb{Q}(\sqrt{-3})$

**Classification:**
- Since $-3 \equiv 1 \pmod{4}$, we have Case 2
- Let $\omega = \frac{-1 + \sqrt{-3}}{2}$, a primitive cube root of unity
- $\mathcal{O}_{\mathbb{Q}(\sqrt{-3})} = \mathbb{Z}[\omega] = \{a + b\omega : a, b \in \mathbb{Z}\}$

**Properties of $\omega$:**
- $\omega^2 + \omega + 1 = 0$
- $\omega^3 = 1$
- $\overline{\omega} = \omega^2 = -1 - \omega$

**Norm:** For $z = a + b\omega$:
$$N(z) = z\overline{z} = (a + b\omega)(a + b\omega^2) = a^2 + ab(\omega + \omega^2) + b^2\omega^3 = a^2 - ab + b^2$$

**Units:** The units in $\mathbb{Z}[\omega]$ are $\{\pm 1, \pm \omega, \pm \omega^2\}$
- These are the sixth roots of unity
- Form a cyclic group of order 6

**Geometric interpretation:**
- The Eisenstein integers form a hexagonal lattice in the complex plane
- Each non-zero element has 6 associates (obtained by multiplying by units)

**Applications:**
- Hexagonal tilings and crystal structures
- Coding theory (Eisenstein integers provide efficient lattice codes)

### Example 3: $\mathbb{Q}(\sqrt{2})$ - The Simplest Real Quadratic Field

**Field:** $\mathbb{Q}(\sqrt{2})$

**Classification:**
- Since $2 \equiv 2 \pmod{4}$, we have Case 1
- $\mathcal{O}_{\mathbb{Q}(\sqrt{2})} = \mathbb{Z}[\sqrt{2}] = \{a + b\sqrt{2} : a, b \in \mathbb{Z}\}$

**Norm:** For $\alpha = a + b\sqrt{2}$:
$$N(\alpha) = (a + b\sqrt{2})(a - b\sqrt{2}) = a^2 - 2b^2$$

**Units:** Unlike imaginary quadratic fields, $\mathbb{Q}(\sqrt{2})$ has **infinitely many units**!
- Fundamental unit: $u = 1 + \sqrt{2}$ with $N(u) = -1$
- All units: $\pm u^n$ for $n \in \mathbb{Z}$
- Examples: $1 + \sqrt{2}$, $3 + 2\sqrt{2}$, $7 + 5\sqrt{2}$, ...

**Pell's Equation:** The units in $\mathbb{Z}[\sqrt{2}]$ correspond to integer solutions of Pell's equation:
$$x^2 - 2y^2 = \pm 1$$

Minimal solution: $(x, y) = (1, 1)$ giving $u = 1 + \sqrt{2}$

**Applications:**
- Approximations to $\sqrt{2}$: convergents of continued fraction
- Construction of Pell equation solvers

### Example 4: $\mathbb{Q}(\sqrt{5})$ and the Golden Ratio

**Field:** $\mathbb{Q}(\sqrt{5})$

**Classification:**
- Since $5 \equiv 1 \pmod{4}$, we have Case 2
- Let $\phi = \frac{1 + \sqrt{5}}{2}$ (the golden ratio)
- $\mathcal{O}_{\mathbb{Q}(\sqrt{5})} = \mathbb{Z}[\phi] = \{a + b\phi : a, b \in \mathbb{Z}\}$

**Properties of $\phi$:**
- $\phi^2 = \phi + 1$
- $\phi = 1.618...$
- $\phi$ is the limit of ratios of consecutive Fibonacci numbers

**Norm:** For $\alpha = a + b\phi$ with $\phi = \frac{1+\sqrt{5}}{2}$:
$$N(\alpha) = a^2 + ab - b^2$$

**Fundamental unit:** $\phi = \frac{1 + \sqrt{5}}{2}$ with $N(\phi) = -1$

**Connection to Fibonacci numbers:**
The $n$-th Fibonacci number satisfies:
$$F_n = \frac{\phi^n - \overline{\phi}^n}{\sqrt{5}}$$

**Applications:**
- Fibonacci sequences and recurrence relations
- Golden ratio in art and architecture
- Penrose tilings

## Euclidean Quadratic Fields

A quadratic field $\mathbb{Q}(\sqrt{d})$ is called **Euclidean** if its ring of integers admits a Euclidean division algorithm.

**Complete list of Euclidean imaginary quadratic fields:**
- $d \in \{-1, -2, -3, -7, -11\}$

**Examples of Euclidean real quadratic fields:**
- $d \in \{2, 3, 5, 6, 7, 11, 13, 17, 19, 21, 29, 33, ...\}$
- Whether there are infinitely many is an open question!

## Unique Factorization

A ring of integers $\mathcal{O}_K$ has **unique factorization** if every non-zero, non-unit element factors uniquely (up to order and units) into irreducibles.

**Imaginary quadratic fields with unique factorization:**
- $d \in \{-1, -2, -3, -7, -11, -19, -43, -67, -163\}$
- These are exactly 9 values (proved by Stark, Baker, Heegner)

**Example of non-unique factorization:** $\mathbb{Q}(\sqrt{-5})$
- In $\mathbb{Z}[\sqrt{-5}]$, we have:
$$6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$$
- Both factorizations are into irreducibles, showing failure of unique factorization

## Class Numbers

The **class number** $h_K$ measures the failure of unique factorization in $\mathcal{O}_K$.

**Examples:**
- $h_{\mathbb{Q}(i)} = 1$ (unique factorization)
- $h_{\mathbb{Q}(\sqrt{-5})} = 2$ (minimal failure)
- $h_{\mathbb{Q}(\sqrt{-23})} = 3$

Fields with class number 1 have unique factorization.

[← Back to Home](index.html)
