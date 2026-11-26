# Mathematical & Verification Glossary (`docs/glossary.md`)

- **2-Blade (`e_i + e_j`):** A sum of two distinct imaginary canonical basis elements ($1 \le i < j < 2^n$) in $\mathrm{CD}_n(\gamma)$.
- **Bad Affine 2-Plane:** A 4-element affine 2-plane $\{a, b, c, d\} \subset \mathbb{F}_2^n$ ($a \oplus b \oplus c \oplus d = 0$) on which at least one of its three unordered pairings fails bilinear norm cancellation $\sigma(a,c)\sigma(b,d) + \sigma(a,d)\sigma(b,c) = 0$.
- **BDI Ceiling (`bdiMaxAnnihilator`):** The Biss–Dugger–Isaksen (2008) upper bound $2^n - 4n + 4$ on $\dim \mathrm{Ann}(x)$ for nonzero $x \in \mathrm{CD}_n$ ($n \ge 4$).
- **Box-Kite (`7 × K_{2,2,2}`):** One of the 7 disjoint octahedral connected components (6 vertices, 12 edges each) of the 42 sedenion zero-divisor assessors discovered by de Marrais (2000), partitioned by XOR strut signature $s = i \oplus j \in \{9,\dots,15\}$.
- **Flip Mask (`flip(γ)`):** An $n$-bit integer encoding signature $\gamma \in \{\pm 1\}^n$ where bit $r$ is `1` iff doubling step $r$ is split ($\gamma_r = +1$) and `0` iff Euclidean ($\gamma_r = -1$).
- **Hurwitz–Radon Function (`ρ(2^n)`):** For $n = 4a + b$ ($0 \le b \le 3$), $\rho(2^n) = 8a + 2^b$, governing the maximal real composition formula $[2^n, \rho(2^n), 2^n]$.
- **Interior Spectral Gap:** A nullity multiple of $4$ strictly between $0$ and $2^{n-1}$ with zero count $H_n^\gamma(v) = 0$ in a split-signature algebra $\mathrm{CD}_n(\gamma)$ (first emerging at dimension $64$).
- **Mirror-Pair Conservation:** Universal invariance of $H_n^\gamma(v) + H_n^\gamma(2^{n-1}-v)$ across all $2^n$ signatures $\gamma$ (Theorem `T1e`).
- **Palomar Comparator:** Statement-fidelity verification protocol comparing `PalomarChallenge` against sorry-free `PalomarSolution` across 6 independent Lean 4.35.0 proof kernels.
- **Right-Compatibility Graph (`G_n^comp`):** Graph on $\{0, \dots, 2^n - 1\}$ with an edge between distinct $j, x$ iff $(j, x)$ is universally compatible on the right against all of $\mathrm{CD}_n$; its exact clique number is $\omega(G_n^{\mathrm{comp}}) = n + 5$ for all $n \ge 3$.
