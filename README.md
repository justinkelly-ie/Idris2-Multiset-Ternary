# 🌴 Idris2-Naray

**Constructive Dependent Type Formalization of Binary ($n=2$, $\mathbb{F}_2$) and Ternary ($n=3$, $\mathbb{F}_3$) Alphabets, Narayana Polynomials, and Elaborator Reflection in [Idris 2](https://github.com/idris-lang/Idris2).**

[![Idris2](https://img.shields.io/badge/Idris2-Reflection-blue.svg)](https://github.com/idris-lang/Idris2)
[![Finitism](https://img.shields.io/badge/Finitism-Narayana-purple.svg)]()

---

## 🏛️ Overview

`Idris2-Naray` formalizes the constructivist transition between the binary field $\mathbb{F}_2 = \{0, 1\}$ (from [`idris2-Boole`](../Idris2-Boole)) and the balanced ternary field $\mathbb{F}_3 = \{-1, 0, 1\}$ (from [`Idris2-Universe2`](../Idris2-Universe2)).

### Core Features

1. **Dependent Alphabet Type (`NarayAlphabet n`)**:
   - $n=2 \implies \mathbb{F}_2 = \{0, 1\}$, idempotent ring ($x^2 = x$), unit group $\mathbb{F}_2^\times \cong C_1$, 4 metric states ($2^2 = 4$).
   - $n=3 \implies \mathbb{F}_3 = \{-1, 0, 1\}$, balanced ternary field ($x^3 = x$), parity unit group $\mathbb{F}_3^\times \cong C_2$, 27 metric states ($3^3 = 27$).
2. **Narayana Numbers & Catalan Refinement**:
   - Exact computation of $N(n, k) = \frac{1}{n} \binom{n}{k} \binom{n}{k-1}$.
   - Verified Catalan summation theorem: $\sum_{k=1}^n N(n, k) = C_n$.
   - Narayana polynomial generating functions $N_n(t) = \sum_{k=1}^n N(n, k) t^{k-1}$.
3. **Elaborator Reflection Macros (`%macro`)**:
   - Static compile-time verification of field unit group orders, Narayana-Catalan sums, and metric state capacities ($n^n$).
4. **QTT Linear State Evolution**:
   - Enforces thermodynamic multiplicity `(1 state : NarayState n)`.

---

## 📁 Module Organization

| Module | Description |
|---|---|
| [`Core.NarayAlphabet`](src/Core/NarayAlphabet.idr) | Dependent alphabet type `NarayAlphabet n`, finite field arithmetic over $\mathbb{F}_2$ and $\mathbb{F}_3$. |
| [`Math.NarayanaPolynomial`](src/Math/NarayanaPolynomial.idr) | Narayana numbers $N(n, k)$, Catalan numbers $C_n$, vector peak distributions, and polynomial evaluation. |
| [`Reflect.NarayElab`](src/Reflect/NarayElab.idr) | Elaborator reflection macros (`%macro`) for static compile-time proof audits. |
| [`Linear.NarayState`](src/Linear/NarayState.idr) | QTT linear state transitions preserving state multiplicity `1`. |

---

## 🛠️ Building

To build the library with pack:

```bash
toolbox run -c fedora-toolbox-44 /var/home/justin/.local/bin/idris2 --build Idris2-Naray.ipkg
```

---

© Justin Kelly. All rights reserved.
