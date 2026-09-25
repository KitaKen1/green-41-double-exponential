# A Lean proof of the double-exponential bound in Green's Problem 41

This repository formalizes a solution to the **double-exponential target** of Ben Green's
Problem 41 (the pyjama problem), as registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/41.lean).
Let `minCopies ε` be the least number of rotated copies of the pyjama set

```text
E(ε) = { z ∈ ℂ : |Re z − k| ≤ ε for some k ∈ ℤ }
```

that cover the plane. The theorem is that there are constants `C` and `ε₀ > 0` with

```text
minCopies ε ≤ exp(exp(ε^(−C)))   for all 0 < ε ≤ ε₀.
```

Kravitz and Leng proved the triple-exponential bound `exp exp exp(ε^(−C))`; this removes one
exponential.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-41-double-exponential%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen41DoubleExponentialLean4Web.lean)
(checked with "Latest Mathlib with Lean v4.35.0-rc3"; the file is long, so elaboration takes a few minutes)

This does **not** solve the exact-value theorem `Green41.green_41` or the polynomial variant
`Green41.green_41.variants.polynomial_bound`.

## Formal Conjectures target

The file in `lean/` imports the Formal Conjectures statement and proves it with the answer
`True`. The definitions `pyjamaSet`, `coveringCopies` and `minCopies` are the ones imported
from Formal Conjectures.

```lean
theorem Green41Proof.green_41_double_exponential_bound_solved : answer(True) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (ε ^ (-C)))
```

Thus the theorem `Green41.green_41.variants.double_exponential_bound` can be changed from
`research open` to `research solved` by replacing its answer hole with `True` and using this
proof. The constants produced are `C = 102` and `ε₀ = 1 / (10 + log(10000 · 101))`.

## Mathematical explanation (AI generated)

**Notation.** For $`x\in\mathbb{R}`$ write $`\|x\|`$ for the distance from $`x`$ to $`\mathbb{Z}`$. For
$`|u|=1`$ put

```math
S_u(\varepsilon)=\{z\in\mathbb{C}:\ \|\mathrm{Re}(uz)\|\lt \varepsilon\}.
```

Since $`S_u(\varepsilon)\subseteq \bar u\,E(\varepsilon)`$, it suffices to find a finite set $`\Omega`$ of
unit complex numbers with $`\bigcup_{u\in\Omega}S_u(\varepsilon)=\mathbb{C}`$; then
$`\mathrm{minCopies}\,\varepsilon\le|\Omega|`$.

The rotations come from the Gaussian primes $`P=1+2i`$ (norm $`5`$) and $`Q=2+3i`$ (norm $`13`$):

```math
\theta_5=P/\bar P,\qquad \theta_{13}=Q/\bar Q,\qquad \rho(s,t)=\theta_5^{\,s}\theta_{13}^{\,t}\quad(s,t\ge0).
```

Comparing $`P`$-adic and $`Q`$-adic valuations shows that the $`\rho(s,t)`$ are pairwise distinct.
Throughout, $`c=100`$, $`\eta=5^{-\varepsilon^{-c}}`$ and $`\delta=13^{-c\,\eta^{-5}}`$. For $`q\in\mathbb{Z}[i]`$ let
$`v_{\bar P}(q)`$ and $`v_{\bar Q}(q)`$ be its $`\bar P`$- and $`\bar Q`$-adic valuations. Put
$`|q|_5=5^{-v_{\bar P}(q)}`$ and $`|q|_{13}=13^{-v_{\bar Q}(q)}`$.

### 1. The minor-arc proposition

The whole argument rests on the following statement. Section 6 proves it.

> **Proposition A.** Let $`0<\varepsilon,\varpi<1/10`$ and $`s_1,t_1,s_2,t_2\le N_0`$. Put
> $`r=\rho(s_1,t_1)-\rho(s_2,t_2)`$. Let $`w\in\mathbb{C}`$ and $`q\in\mathbb{Z}[i]`$ satisfy
> ```math
> |q-rw|\le\eta/10\qquad\text{and}\qquad 2\varpi\le|q|_5+|q|_{13}\le\delta.
> ```
> Then $`w\in S_{\rho(s,t)}(\varepsilon)`$ for some $`s,t\le N_0+\log_5(1/\varpi)+c\,\eta^{-5}`$.

This is the consequence of Kravitz–Leng, Proposition 5.7 that is needed here. Section 6 gives
an elementary proof, which does not use the solenoid $`\widehat{\mathbb{Z}[i][1/\bar P,1/\bar Q]}`$,
$`p`$-adic numbers or entropy.

### 2. Confinement near a lattice

**Pigeonhole.** Choose the following:

- $`G\ge\max(20/\eta,\,2/\delta)`$;
- $`u,v`$ with $`5^u,13^v\ge G`$, and $`M=5^u13^v`$;
- $`K`$ with $`(K+1)^2>M^2G^2`$.

For $`w\in\mathbb{C}`$, classify the $`(K+1)^2`$ points $`\rho(s,t)w`$ ($`s,t\le K`$) by two data: the
residue modulo $`M`$ of the nearest Gaussian integer, and the cell of the fractional offset in a
grid of mesh $`1/G`$. Two points $`x=\rho(s_1,t_1)w`$ and $`y=\rho(s_2,t_2)w`$ fall into the same
class. Then $`q=[x]-[y]`$ lies in $`M\mathbb{Z}[i]\subseteq\bar P^{\,u}\bar Q^{\,v}\mathbb{Z}[i]`$, and
$`|q-rw|<2/G\le\eta/10`$ with $`r=\rho(s_1,t_1)-\rho(s_2,t_2)\neq0`$. In particular
$`|q|_5+|q|_{13}\le\delta`$.

**Common denominator.** Put $`\Delta=\bar P^{K}\bar Q^{K}`$. The numbers
$`\Delta\rho(s,t)=P^s\bar P^{K-s}Q^t\bar Q^{K-t}`$ are Gaussian integers of absolute value
$`65^{K/2}`$. Let $`L`$ be the product of the norms $`N(\Delta\rho(s_1,t_1)-\Delta\rho(s_2,t_2))`$
over all pairs of distinct labels. Then $`L/r\in\mathbb{Z}[i]`$ for every nonzero orbit difference
$`r`$, and $`|r|\ge65^{-K/2}`$.

> **Lemma B (confinement).** Let $`h\ge1`$, $`D=\bar P^{h}\bar Q^{h}`$, $`H=65^{K/2}`$ and
> $`T=K+\log_5(2\cdot13^h)+c\,\eta^{-5}`$. If $`w\notin S_{\rho(s,t)}(\varepsilon)`$ for all
> $`s,t\le T`$, then $`w`$ lies within distance $`H`$ of the lattice $`(D/L)\,\mathbb{Z}[i]`$.

*Proof.* Take $`q`$ and $`r`$ as above, and apply Proposition A with $`\varpi=13^{-h}/2`$. Its
conclusion is excluded by hypothesis, so its lower bound must fail:
$`|q|_5+|q|_{13}<13^{-h}`$, that is, $`D\mid q`$. Then $`q/r=(L/r)\,q/L\in(D/L)\mathbb{Z}[i]`$ and
$`|w-q/r|=|rw-q|/|r|<(2/G)\,65^{K/2}\le H`$. $`\square`$

### 3. Rational rotations covering a disc

> **Lemma C.** For $`R\ge16`$ there is a finite set $`U`$ of rational unit complex numbers
> $`a/\bar a`$ ($`a\in\mathbb{Z}[i]`$) with the following properties:
>
> - $`1\in U`$ and $`|a|\le 128R/\varepsilon+4`$;
> - $`|U|\le 3+16\pi/\varepsilon+17(4/\varepsilon+2)(\log_2R+1)`$;
> - every $`e`$ with $`|e|\le R`$ lies in $`S_u(\varepsilon)`$ for some $`u\in U`$.

*Proof sketch.* The function $`g(\varphi)=\mathrm{Re}(e^{i\varphi}e)`$ has a zero
$`\varphi_0\in[-\pi/2,\pi/2]`$ with $`|g'(\varphi_0)|=|e|`$.

- If $`|e|\le16`$, a grid of mesh $`\varepsilon/16`$ contains an angle within $`\varepsilon/32`$ of
  $`\varphi_0`$.
- If $`2^k\le|e|<2^{k+1}`$ with $`k\ge4`$, start at one of the $`17`$ angles $`j\pi/16`$ near
  $`\varphi_0`$ and step by $`\varepsilon/2^{k+1}`$. Along the arc $`|g'|\ge|e|/2`$, so $`g`$ moves by at
  least $`1`$ while each step moves it by less than $`\varepsilon`$. Hence some step lands within
  $`\varepsilon/2`$ of an integer.

Finally replace $`e^{i\varphi}`$ by $`a/\bar a`$, where $`a`$ is the Gaussian integer nearest to
$`q\,e^{i\varphi/2}`$ with $`q\approx128R/\varepsilon`$. This changes $`\mathrm{Re}(ue)`$ by at most
$`\varepsilon/64`$. $`\square`$

### 4. From a neighbourhood of a lattice to the whole plane

> **Lemma D.** Let $`\Theta`$ be finite, and assume that every point not covered by
> $`\{S_\theta(\varepsilon):\theta\in\Theta\}`$ lies within $`H`$ of $`(D/L)\mathbb{Z}[i]`$. Let $`U`$ be
> as in Lemma C with $`R=2LH`$, and assume $`|D|>2LH\cdot\max|a|`$. Put
> $`\nu=\frac1{2L}+i\sqrt{1-\frac1{4L^2}}`$, so that $`|\nu|=1`$ and $`\nu+\bar\nu=1/L`$. Then
> ```math
> \Omega=\Theta U\nu\ \cup\ \Theta U\bar\nu\ \cup\ U
> ```
> covers $`\mathbb{C}`$, and $`|\Omega|\le(2|\Theta|+1)|U|`$.

*Proof.* Suppose $`z`$ is not covered, and let $`v\in\{\nu,\bar\nu\}`$ and $`u=a/\bar a\in U`$.
The points $`vz`$ and $`uvz`$ are not covered by $`\Theta`$, so

```math
vz=\tfrac DL k_v+e_v,\qquad uvz=\tfrac DL k_{uv}+e_{uv}
```

with $`k_v,k_{uv}\in\mathbb{Z}[i]`$ and $`|e_v|,|e_{uv}|\le H`$. Then
$`D(a k_v-\bar a k_{uv})=L(\bar a e_{uv}-a e_v)`$, hence
$`|a k_v-\bar a k_{uv}|\le 2LH|a|/|D|<1`$. So $`u k_v=k_{uv}\in\mathbb{Z}[i]`$.

Adding the equations for $`v=\nu`$ and $`v=\bar\nu`$ and multiplying by $`L`$ gives $`z=Dk+e`$, where
$`k=k_\nu+k_{\bar\nu}`$ and $`|e|\le2LH=R`$. Choose $`u\in U`$ with
$`\|\mathrm{Re}(ue)\|<\varepsilon`$. Since $`uk\in\mathbb{Z}[i]`$, we get
$`\|\mathrm{Re}(uz)\|=\|\mathrm{Re}(ue)\|<\varepsilon`$. This contradicts $`u\in\Omega`$.
$`\square`$

### 5. Parameters

Take the following values:

- $`G=\lceil\max(20/\eta,\,2/\delta,\,1/\varepsilon,\,c\,\eta^{-5})\rceil+66`$;
- $`u=\lceil\log_5G\rceil`$ and $`v=\lceil\log_{13}G\rceil`$;
- $`K=G^4`$, which gives $`(K+1)^2>65^2G^6\ge M^2G^2`$;
- $`L`$ as above, with $`\log L\le(K+1)^4\log(4\cdot65^K)`$;
- $`H=65^{K/2}`$, $`R=2LH+16`$ and $`Q=128R/\varepsilon+4`$;
- $`h=2\lceil\log_{65}(2LHQ+1)\rceil`$, so that $`|D|=65^{h/2}>2LHQ`$;
- $`\Theta=\{\rho(s,t):s,t\le T\}`$.

Lemmas B, C and D then give

```math
\mathrm{minCopies}\,\varepsilon\ \le\ (2(T+1)^2+1)\,|U|\ \le\ G^{88}.
```

Moreover $`G\le91\exp(12(1+c)\eta^{-5}+1/\varepsilon)`$ with $`\eta^{-5}=5^{5\varepsilon^{-c}}`$.
This is at most $`\exp(\exp(\varepsilon^{-(c+2)}))`$ once $`\varepsilon\le1/(10+\log(10000(1+c)))`$.
With $`c=100`$ this is the theorem with $`C=102`$.

### 6. Proof of Proposition A

Assume $`|q|_5\ge|q|_{13}`$; the other case is symmetric under
$`(P,5,\theta_5)\leftrightarrow(Q,13,\theta_{13})`$. Then $`v:=v_{\bar P}(q)\le\log_5(1/\varpi)`$,
while $`v_{\bar Q}(q)\ge c\,\eta^{-5}`$ is huge.

**(a) Residues and orders.** For $`n\ge1`$ the integer $`\mathrm{Re}(P^n)`$ is prime to $`5`$.
Put $`r_n\equiv\mathrm{Im}(P^n)/\mathrm{Re}(P^n)\pmod{5^n}`$. Then $`r_n^2\equiv-1`$,
and $`\psi_n(x+iy)=x+y\,r_n`$ is a ring homomorphism $`\mathbb{Z}[i]\to\mathbb{Z}/5^n`$ with kernel
$`P^n\mathbb{Z}[i]`$. Moreover
$`\mathrm{Re}(z\bar P^n)\equiv\mathrm{Re}(P^n)\,\psi_n(z)\pmod{5^n}`$, so

```math
\mathrm{Re}(z/P^n)\equiv\mathrm{Re}(P^n)\,\psi_n(z)/5^n\pmod 1.
```

On $`\mathbb{Z}[i]/P^n`$, multiplication by $`\theta_{13}`$ is multiplication by
$`b=\psi_n(Q)/\psi_n(\bar Q)`$, and $`b\equiv8\pmod{25}`$. Since $`8`$ has order $`4`$ modulo $`5`$ and
$`8^4\not\equiv1\pmod{25}`$, lifting the exponent shows that $`b`$ has order $`4\cdot5^{k-1}`$ modulo
$`5^k`$ for every $`k`$. The same holds on $`\mathbb{Z}[i]/\bar P^{\,k}`$, where the multiplier is
$`\equiv22\pmod{25}`$. In the other case one uses $`\theta_5\equiv11\pmod{169}`$, of order
$`12\cdot13^{k-1}`$.

**(b) Labels.** Fix $`n`$, $`\alpha\le n`$ and $`\beta`$, and put $`g=\bar P^{\alpha}\bar Q^{\beta}/P^n`$.
The *label* of $`x\in\mathbb{C}`$ is $`\Lambda(x)=\psi_n(\lfloor x/g\rfloor)\in\mathbb{Z}/5^n`$, with the
floor taken coordinatewise. For $`j\le\alpha`$ and $`t\le\beta`$ one has
$`\theta_5^{j}\theta_{13}^{t}\,g\,m=G_m/P^{n-j}`$ with $`G_m\in\mathbb{Z}[i]`$. Together with (a) this
gives an explicit unit $`X_j\in(\mathbb{Z}/5^n)^\times`$ with

```math
\bigl\|\mathrm{Re}(\theta_5^{j}\theta_{13}^{t}x)-\mathrm{val}(X_jb^t\Lambda(x))/5^{\,n-j}\bigr\|\lt \sqrt2\,|g|.
```

So the stripe value of $`\theta_5^{j}\theta_{13}^{t}x`$ can be read off from the label of $`x`$.

**(c) The orbit meets every label.** This step replaces Kravitz–Leng Theorem 5.1. Write
$`q=\bar P^{\,v}\bar Q^{E}q_2`$ with $`\bar P\nmid q_2`$ and $`E=4\cdot5^{n+3}+\beta`$. Let
$`D_0=n-\alpha+4`$ and $`j=v+D_0`$.

For $`t<4\cdot5^{n+3}`$ we have $`\theta_5^{j}\theta_{13}^{t}q=\bar Q^{\beta}W_t/\bar P^{D_0}`$, where
$`W_t\in\mathbb{Z}[i]`$ is prime to $`\bar P`$. Modulo $`\bar P^{\,n+4}`$ the $`W_t`$ are $`W_0`$ times the
powers of $`\theta_{13}`$, so by (a) they run through all units.

Given a label $`\lambda`$, pick $`W`$ prime to $`\bar P`$ within distance $`2`$ of
$`\bar P^{D_0}\bar Q^{-\beta}`$ times the centre of the cell of $`\lambda`$. Then pick $`t`$ with
$`W_t\equiv W\pmod{\bar P^{\,n+4}}`$. Now $`\theta_5^{j}\theta_{13}^{t}(rw)`$ lies in the cell of
$`\lambda`$ modulo the lattice $`\bar P^{\alpha}\bar Q^{\beta}\mathbb{Z}[i]=gP^n\mathbb{Z}[i]`$. That
lattice does not change labels, and the error $`|rw-q|\le\eta/10`$ is far smaller than $`|g|`$.

Since $`\theta_5^{j}\theta_{13}^{t}rw=x-x'`$ for two points $`x,x'`$ of the orbit $`Z`$ of $`w`$, every
$`\lambda\in\mathbb{Z}/5^n`$ is the label of a difference of two orbit points.

**(d) Counting.** We have $`\lfloor(x-x')/g\rfloor=\lfloor x/g\rfloor-\lfloor x'/g\rfloor-d`$ with
$`d\in\{0,1,i,1+i\}`$. Hence
$`\mathbb{Z}/5^n\subseteq Y-Y-\psi_n\{0,1,i,1+i\}`$ for $`Y=\Lambda(Z)`$, and so $`5^n\le4|Y|^2`$.

**(e) Digit pigeonhole.** This is Gayfulin–Moshchevitin, Lemma 4. Put $`\ell=4f`$ and
$`n=8(A+\ell)`$, and look at the levels $`n,\,n-\ell,\,n-2\ell,\dots`$ down to a level in
$`[A,A+\ell)`$. Suppose that at every level $`s`$, each residue modulo $`5^{s-\ell}`$ had fewer than
$`5^f`$ lifts modulo $`5^s`$ in $`Y`$. Telescoping would then make $`|Y|`$ too small for (d). So at
some level $`s\ge A+\ell`$ there are at least $`5^f`$ elements of $`Y`$, distinct modulo $`5^s`$ and all
congruent to one $`\lambda`$ modulo $`5^{s-\ell}`$.

Write these elements as $`\lambda+5^{s-\ell}z`$ and take $`j=n-s`$ in (b). Their stripe values
after $`\theta_5^{\,n-s}\theta_{13}^{\,t}`$ are $`\tilde b^{\,t}(\gamma+y/5^\ell)`$ modulo $`1`$. Here:

- $`\tilde b`$ is an integer lift of $`b`$;
- $`\gamma=\tilde X\lambda/5^s`$;
- $`y=\tilde Xz`$ runs over a set $`\mathcal Y`$ of at least $`5^f`$ residues, distinct modulo $`5^\ell`$.

**(f) The discrete core.** This replaces the entropy input of
Bourgain–Lindenstrauss–Michel–Venkatesh. Let $`S=4\cdot5^{\ell-1}`$, and let $`N\in\mathbb{N}`$
satisfy $`N\varepsilon^2\ge2`$ and $`25N^3<4|\mathcal Y|`$. Suppose that every point
$`\xi_{t,y}=\tilde b^{\,t}(\gamma+y/5^\ell)`$ with $`t<S`$ and $`y\in\mathcal Y`$ is at distance at
least $`\varepsilon/2`$ from $`\mathbb{Z}`$.

Put $`e(x)=e^{2\pi ix}`$ and $`F(\xi)=\bigl|\sum_{a<N}e(a\xi)\bigr|^2`$. Then $`F(\xi_{t,y})\le1/\varepsilon^2\le N/2`$
for all these points. On the other hand, expanding $`F`$,

```math
\sum_{t,y}F(\xi_{t,y})=\sum_{a,a'\lt N}\ \sum_{t\lt S}\sigma_t(a-a'),\qquad \sigma_t(m)=\sum_{y\in\mathcal Y}e(m\,\xi_{t,y}).
```

The diagonal $`a=a'`$ contributes $`NS|\mathcal Y|`$. Now let $`0<|m|<N`$. The value
$`|\sigma_t(m)|`$ does not depend on $`\gamma`$, and the map $`t\mapsto\tilde b^{\,t}\bmod 5^\ell`$
is injective on $`[0,S)`$. Hence

```math
\sum_{t\lt S}|\sigma_t(m)|^2\le\sum_{u\bmod 5^\ell}\Bigl|\sum_{y}e(muy/5^\ell)\Bigr|^2=5^\ell\,\#\{(y,y'):5^\ell\mid m(y-y')\}\le5^\ell|\mathcal Y|\,|m|.
```

For the last step: the residues $`y'`$ with $`5^\ell\mid m(y-y')`$ are pairwise at least
$`5^\ell/|m|`$ apart. By Cauchy–Schwarz, $`\bigl|\sum_t\sigma_t(m)\bigr|\le5^\ell\sqrt{|\mathcal Y||m|}`$.

Hence $`NS|\mathcal Y|-N^2\,5^\ell\sqrt{|\mathcal Y|N}\le S|\mathcal Y|N/2`$. This forces
$`|\mathcal Y|\le\frac{25}4N^3`$, a contradiction. So some $`\xi_{t,y}`$ lies within $`\varepsilon/2`$
of an integer.

**(g) Conclusion.** Let $`x=\rho(s',t')w`$ be the corresponding orbit point. By (b),
$`\|\mathrm{Re}(\theta_5^{\,n-s}\theta_{13}^{\,t}x)\|<\varepsilon/2+\sqrt2|g|<\varepsilon`$, so
$`w\in S_{\rho(s'+n-s,\,t'+t)}(\varepsilon)`$. The parameters are:

- $`K_0=\lceil1/\varepsilon\rceil`$ and $`N=2K_0^2`$;
- $`f=6\lceil\log_5K_0\rceil+4`$, so $`5^f\ge625K_0^6>\frac{25}4N^3`$;
- $`\beta=S`$;
- $`A=2\beta+2\lceil\log_5K_0\rceil+3`$, so $`|g|^2\le\varepsilon^2/125`$;
- $`\alpha=n-A`$.

The exponents are at most $`N_0+v+A+4+n`$ and $`N_0+4\cdot5^{n+3}+S`$. Both are below
$`N_0+\log_5(1/\varpi)+c\,\eta^{-5}`$, because $`n+4\le\frac52\,\varepsilon^{-100}`$. $`\square`$

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `40a8592c...` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `5e0c4e52...`) |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked. The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem. Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is solved here:

```text
There are C and ε₀ > 0 with minCopies ε ≤ exp(exp(ε^(−C))) for 0 < ε ≤ ε₀.
```

What remains open:

```text
Determine minCopies ε exactly (Green41.green_41).
Is minCopies ε ≤ ε^(−C) for some C (Green41.green_41.variants.polynomial_bound)?
```

The trivial lower bound is of order `1/(2ε)`.

## Sources

- B. Green, *100 open problems*, Problem 41
- [Formal Conjectures: `GreensOpenProblems/41.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/41.lean)
- N. Kravitz and J. Leng, *Quantitative pyjama*,
  [arXiv:2510.17744](https://arxiv.org/abs/2510.17744)
- F. Manners, *A solution to the pyjama problem*, Invent. Math. 202 (2015)
- D. Gayfulin and N. Moshchevitin, *On Furstenberg's Diophantine result*,
  [arXiv:2301.08212](https://arxiv.org/abs/2301.08212)
- J. Bourgain, E. Lindenstrauss, P. Michel and A. Venkatesh, *Some effective results for ×a×b*,
  Ergodic Theory Dynam. Systems 29 (2009)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

The covering argument (steps 1–4) was drafted with assistance from OpenAI ChatGPT. The
proof of the minor-arc input and the Lean formalization were developed with AI assistance.
