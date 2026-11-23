# Formalization targets — the confirmed claims

Source: `Graph-Theory-LLM-Proofs/verification/SUMMARY.md` (adversarial review of the 77
`proved`/`disproved` self-reports, generated 2026-09-03). Each of those self-reports was
re-derived from scratch by an independent adversarial referee; **51** survived as
mathematically correct.

Those 51 are collected here, in three sections ordered by how useful they are as targets:

| § | n | batch | what it means |
| --- | ---: | --- | --- |
| [1](#1-publishable--confirmed-and-flagged-would_publish-12) | 12 | `CONFIRMED` + `would_publish` | correct, apparently new, and judged publishable |
| [2](#2-confirmed-but-not-flagged-publishable-13) | 13 | `CONFIRMED` | correct and apparently new, but narrow in scope |
| [3](#3-correct-but-already-known-26) | 26 | `ALREADY_KNOWN` | correct, but the result is not new |

Within each section, entries are in arXiv-id order. Every entry gives a link to the catalog
page, the non-standard definitions needed, and the result as a **self-contained theorem
statement** — not "the conjecture holds", but the full quantified statement with the constants
and constructions filled in, ready to be transcribed into Rocq. Where a proof depends on an
external result, or where the scope is narrower than the headline suggests, a *Caveat* line
says so.

---

## 1. Publishable — `CONFIRMED` and flagged `would_publish` (12)

These 12 were confirmed correct, fairly interpreted and apparently new by the referee, and
were also the ones the solver itself judged worth publishing.

### 1.1. `1611.03196__03` — Fair representation, Conjecture 1.15

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__03/
**Source:** Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv, *Fair representation by
independent sets* (arXiv:1611.03196v1), Conjecture 1.15. Verdict: `proved`.

*Definitions.* All standard (bipartite graph, maximum degree $\Delta(G)$, matching). The
edge sets $E_1,\dots,E_m \subseteq E(G)$ are **arbitrary** — no disjointness, no partition
requirement (this is the point of the "under-representation" formulation).

**Theorem.** For every $m \ge 1$, every finite bipartite graph $G$ with
$D = \Delta(G) \ge 1$, and all edge sets $E_1,\dots,E_m \subseteq E(G)$, there exists a
matching $S \subseteq E(G)$ such that
$$
|S| \;\ge\; \frac{|E(G)|}{D} - 32(m+1)^3
\qquad\text{and}\qquad
|S \cap E_i| \;\le\; \left\lceil \frac{|E_i|}{D} \right\rceil \quad (1 \le i \le m).
$$

*Proof route.* König's edge-colouring theorem, Carathéodory reduction to at most $m+2$
matchings, and iterated proportional interpolation between two matchings, which rests on the
Stromquist–Woodall proportional interval-splitting theorem (a prerequisite if formalized
from scratch).

*Caveat.* The authors' sharper suggestion $c(m) = m/2$ remains open.

---

### 1.2. `1702.01094__01` — Scott–Seymour, uniquely-covered vertices in an induced path

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.01094__01/
**Source:** Scott, Seymour, *Induced subgraphs of graphs with large chromatic number. IX.
Rainbow paths* (arXiv:1702.01094v2), question in the Conclusion. Verdict: `disproved`.

*Definitions.* A **stable-set cover** of $G$ is a family $\mathcal{A}$ of stable
(independent) subsets of $V(G)$ with $\bigcup \mathcal{A} = V(G)$, **not necessarily
pairwise disjoint**. A path $P$ has the **private-cover property** with respect to
$\mathcal{A}$ if
$$
\forall v \in V(P)\ \ \exists X \in \mathcal{A} \ :\ X \cap V(P) = \{v\}.
$$

**Theorem.** For every integer $s \ge 3$ and every $C$, there exist a finite connected
triangle-free graph $G$ with $\chi(G) > C$ and a stable-set cover $\mathcal{A}$ of
$G$ such that **no** induced path of $G$ on $s$ vertices has the private-cover
property — indeed no induced path of $G$ on at least three vertices does.

*Proof route.* A deterministic obstruction built from a proper colouring of the
distance-two graph $D(G)$, applied to high-girth high-chromatic random graphs.

*Caveat.* The graphs are obtained by the probabilistic method, so the statement is
existential, not constructive.

---

### 1.3. `1812.02420__02` — Fractional dichromatic number, Problem 3.21 at $p = 2$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.02420__02/
**Source:** Hochstättler, Schröder, Steiner, *On the Complexity of Digraph Colourings and
Vertex Arboricity* (arXiv:1812.02420, DMTCS 22:1, 2020), Problem 3.21. Verdict: `proved`.

*Definitions.* Digraphs are loopless but may have parallel and **antiparallel** arcs; a
**digon** (a pair of antiparallel arcs) counts as a directed cycle. Let $\mathcal{A}(D)$
be the family of vertex sets inducing an acyclic subdigraph of $D$. The **fractional
dichromatic number** $\vec{\chi}_f(D)$ is the optimum of the covering LP
$$
\min \sum_{A \in \mathcal{A}(D)} x_A
\quad\text{subject to}\quad
\sum_{A \ni v} x_A \ge 1 \ \ (\forall v \in V(D)),
\qquad x \ge 0.
$$

**Theorem.** The decision problem $\mathrm{FDC}(2)$ — instance: a (multi-)digraph $D$;
question: is $\vec{\chi}_f(D) \le 2$? — is **NP-complete**. NP-hardness already holds for
the restricted class of two-layer digraphs in which corresponding vertices of the two layers
are joined by digons and there are no other arcs between the layers.

*Proof route.* Hardness reduces from 2-dichromatic colourability (Bokal et al.); membership
in NP uses that a basic optimal solution of the covering LP has at most $|V(D)|$ positive
variables, of polynomial bit-size by Cramer's rule and Hadamard's bound.

*Caveat.* The reduction uses digons, so the digon-free (oriented) variant is not settled —
but Problem 3.21 explicitly takes multi-digraphs as instances.

---

### 1.4. `1812.02420__03` — Directed Kneser graphs, Problem 5.40

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.02420__03/
**Source:** same paper as §1.3, Problem 5.40. Verdict: `disproved` (complete classification).

*Definitions.* Same digon convention as above. A digraph $\vec{K}(k,b)$ on vertex set
$\binom{[k]}{b}$ has the **Problem 5.40 property** if for every subfamily
$\mathcal{F} \subseteq \binom{[k]}{b}$,
$$
\vec{K}(k,b)[\mathcal{F}] \ \text{is acyclic}
\quad\Longleftrightarrow\quad
\bigcap_{B \in \mathcal{F}} B \neq \varnothing .
$$

**Theorem.** For positive integers $k \ge b$, a digraph on vertex set $\binom{[k]}{b}$
with the Problem 5.40 property exists **if and only if**
$$
b \le 2 \qquad\text{or}\qquad k \le b+1 .
$$
In particular none exists for $(k,b) = (5,3)$.

*Proof route.* Key structural lemma: in any such digraph, an inclusion-minimal family
$\mathcal{M}$ with $\bigcap \mathcal{M} = \varnothing$ and $|\mathcal{M}| \ge 3$
induces exactly the arcs of a directed Hamilton cycle.

---

### 1.5. `1902.10878__01` — Asymmetry of the biconstrained function $\psi$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1902.10878__01/
**Source:** Chudnovsky, Hompe, Scott, Seymour, Spirkl, *Concatenating bipartite graphs*
(arXiv:1902.10878v3), prose question after Theorem 2.3. Verdict: `disproved`.

*Definitions.* A **tripartition** $(A,B,C)$ of a graph $G$ is a partition of $V(G)$
into three nonempty **stable** sets with **no edges between $A$ and $C$**. It is
**$(x,y)$-biconstrained** if
$$
\begin{aligned}
|N_B(a)| &\ge x|B| \quad (a \in A), &\qquad |N_A(b)| &\ge x|A| \quad (b \in B),\\
|N_C(b)| &\ge y|C| \quad (b \in B), &\qquad |N_B(c)| &\ge y|B| \quad (c \in C).
\end{aligned}
$$
For $c \in C$, let $N^2_A(c) = \{a \in A : N_B(a) \cap N_B(c) \neq \varnothing\}$ be the
set of vertices of $A$ at distance exactly two from $c$. Then
$$
\psi(x,y) \;=\; \inf_{(G,A,B,C)\ (x,y)\text{-biconstrained}} \ \max_{c \in C} \frac{|N^2_A(c)|}{|A|}.
$$

**Theorem.** For every odd integer $q \ge 7$,
$$
\psi\!\left(\frac{2}{q},\frac{q-2}{q}\right)
\;\le\; 1 - \frac{2(q-2)}{q(q+1)}
\;<\; 1 - \frac{1}{q}
\;=\; \psi\!\left(\frac{q-2}{q},\frac{2}{q}\right).
$$
In particular $\psi(2/7,\,5/7) \le 23/28 < 6/7 = \psi(5/7,\,2/7)$, so there exist
$x,y \in (0,1]$ with $\psi(x,y) \neq \psi(y,x)$.

*Proof route.* An explicit 42-vertex biconstrained triple for the upper bound, plus a
rigidity argument (with a machine-checked finite core) for
$\psi((q-2)/q,\,2/q) = 1 - 1/q$.

*Caveat.* The exact value of $\psi(2/7,5/7)$ is not determined; the analogous "exact case"
($\xi$) symmetry question remains open.

---

### 1.6. `2103.15175__00` — Multicolor list Ramsey numbers, Fox–He–Luo–Xu conjecture

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.15175__00/
**Source:** Fox, He, Luo, Xu, *Multicolor list Ramsey numbers grow exponentially*
(arXiv:2103.15175v2), Section 3.1 conjecture (tightness of Theorem 8). Verdict: `proved`.

*Definitions.* For a family $\mathcal{H}$ of graphs, $R_\ell(\mathcal{H},k)$ is the
minimum $n$ for which there is a list assignment
$L : E(K_n) \to \binom{\mathbb{N}}{k}$ such that **every** $L$-colouring (each edge
receiving a colour from its own list) contains a monochromatic member of $\mathcal{H}$.
Let $\mathcal{H}_s$ be the family of all finite graphs with chromatic number $> s$.

**Theorem.** For all $s \ge 2$ and $k \ge 1$,
$$
R_\ell(\mathcal{H}_s, k) = s^k + 1 .
$$

*Proof route.* Upper bound: the constant list $L(e) = \{1,\dots,k\}$ on $K_{s^k+1}$.
Lower bound (the new content), via a greedy **separation lemma**: for $n \le s^k$ and any
$k$-list assignment on $E(K_n)$ there are maps $f_c : V \to [s]$, one per colour
$c$, such that every pair $u \neq v$ is separated by some $f_c$ with
$c \in L(uv)$ — a union bound with $|B_i| = s^{q-k}$ and
$(s^k-1)s^{q-k} < s^q$.

---

### 1.7. `2208.06858__01` — Levine's hat problem, monotone relaxation (Conjecture 2.2)

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__01/
**Source:** Alon, Friedgut, Kalai, Kindler, *The success probability in Levine's hat problem,
and independent sets in graphs* (arXiv:2208.06858v2), Conjecture 2.2. Verdict: `disproved`.

*Definitions.* Let $\Omega_n = \{0,1\}^n$ carry the uniform measure. A family
$\mathcal{A} \subseteq \Omega_n$ is **monotone** if it is upward closed, and **balanced**
if $|\mathcal{A}| = 2^{n-1}$. In the monotone relaxation of the $t$-player game, player
$i$, after seeing the other players' stacks $x_{-i}$, chooses a balanced monotone family
$\mathcal{A}_i(x_{-i}) \subseteq \Omega_n$ and succeeds iff
$x_i \in \mathcal{A}_i(x_{-i})$; the team wins iff all players succeed. Then
$$
p_{\mathrm{monotone}}(t) \;=\; \lim_{n \to \infty} \ \max_{\text{strategies}} \ \Pr[\text{all } t \text{ players succeed}]
$$
(the limit exists and equals the supremum over $n$).

**Theorem.** For every finite $t \ge 1$,
$$
p_{\mathrm{monotone}}(t) = \frac{1}{2}.
$$
In particular $p_{\mathrm{monotone}}(t)$ does not tend to $0$ as $t \to \infty$.

*Proof route.* The upper bound $\le 1/2$ is immediate (each player alone succeeds with
probability exactly $1/2$). The matching lower bound is a "block-tribes" construction —
balanced monotone families synchronised across players — using
$n \approx m(\log 2)2^{mt}$ hats.

*Caveat.* Conjecture 2.1 ($p_{\mathrm{intersecting}}$) and Levine's original Conjecture 1.1
($p_{\mathrm{dict}}$) are untouched.

---

### 1.8. `2310.04265__09` — Clique number of tournaments, Question 5.9

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__09/
**Source:** Aboulker, Aubian, Charbit, Lopes, *Clique number of tournaments*
(arXiv:2310.04265v2), Question 5.9. Verdict: `disproved`.

*Definitions.* For a linear order $\prec$ of $V(D)$, the **backedge graph** $D^\prec$
is the undirected graph with $uv \in E(D^\prec)$ iff $u \prec v$ and $vu \in A(D)$.
The **clique number of a tournament** is
$$
\vec{\omega}(D) = \min_{\prec} \ \omega(D^\prec).
$$
A tournament is $k$-$\vec{\omega}$-**critical** if $\vec{\omega} = k$ while every
proper subtournament has $\vec{\omega} < k$.

**Theorem.** For every $n \ge 3$, the circulant tournament on $2n+1$ vertices
$$
T_n = \mathrm{Cay}\!\left(\mathbb{Z}_{2n+1},\, S_n\right),
\qquad S_n = \{1,\dots,n-1,\,n+1\},
\qquad x \to y \iff y - x \in S_n,
$$
satisfies $\vec{\omega}(T_n) = 3$, while every proper subtournament
$A \subsetneq T_n$ satisfies $\vec{\omega}(A) \le 2$.

**Corollary.** There is no function $\ell : \mathbb{N} \to \mathbb{N}$ such that every
tournament $T$ with $\vec{\omega}(T) \ge k$ has a subtournament $A$ with
$|A| \le \ell(k)$ and $\vec{\omega}(A) \ge k$ — already $k = 3$ admits
$3$-$\vec{\omega}$-critical tournaments of arbitrarily large order.

---

### 1.9. `2401.00299__02` — Partitioning the hypercube into 2-dimensional subcubes

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2401.00299__02/
**Source:** Alon, Balogh, Potapov, *Partitioning the hypercube into smaller hypercubes*
(arXiv:2401.00299), Problem "2dim" (Problem 1.11 in v1/v2). Verdict: `proved`.

*Definitions.* $Q_d = \{0,1\}^d$. A **coordinate $r$-dimensional subcube** is a set
obtained by fixing $d-r$ coordinates; for $r = 2$ these are exactly the vertex sets
inducing an induced $C_4$ in $Q_d$. Let $f_2(d)$ be the number of (unordered)
partitions of $Q_d$ into coordinate 2-dimensional subcubes, and $f_{0,2}(m)$ the number
of partitions of $Q_m$ into parts that are singletons or coordinate 2-dimensional
subcubes.

**Theorem.** As $d \to \infty$,
$$
\log f_2(d) = (1+o(1))\, 2^{d-1} \log d,
\qquad\text{equivalently}\qquad
f_2(d) = d^{(1+o(1))\,2^{d-1}} .
$$

*Proof route.* The new ingredient is a four-layer **lifting lemma**,
$$
f_2(m+2) \;\ge\; \left( \frac{f_{0,2}(m)}{2^{2^m}} \right)^{4},
$$
which removes singleton parts while preserving the leading entropy; it is combined with the
known lower bound on $f_{0,2}$ (see caveat).

*Caveat.* The proof is **modulo the source paper's own Proposition 1.10**,
$\log f_{0,2}(m) \ge (1-o(1))\,2^{m-1}\log m$, which would have to be assumed or formalized
separately. Second-order $2^{\Theta(2^{d-1})}$ factors are not determined.

---

### 1.10. `2405.03455__00` — Erdős–Szekeres with collinear points: dependence on $\ell$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2405.03455__00/
**Source:** Conlon, Fox, He, Mubayi, Suk, Verstraëte, *Big line or big convex polygon*
(arXiv:2405.03455, Comput. Geom. 131, 2026), open problem at the end of the introduction.
Verdict: `proved`.

*Definitions.* $ES_\ell(n)$ is the minimum $N$ such that every $N$-point set in the
plane contains either $\ell$ collinear points or $n$ points in convex position. The
source paper proves
$$
(3\ell-1)\cdot 2^{n-5} \;<\; ES_\ell(n) \;<\; \ell^2 \cdot 2^{\,n + C\sqrt{n\log n}}.
$$

**Theorem A (transfer inequality — the self-contained core).** For all integers
$k,\ell,n \ge 3$,
$$
ES_\ell(n) \;\le\; \left\lceil\, \ell \left(4\,ES_k(n)\right)^{(k-1)/(k-2)} \right\rceil .
$$

**Theorem B.** There is an absolute constant $C_1 > 0$ such that for all integers
$\ell, n \ge 3$,
$$
ES_\ell(n) \;\le\; \ell\, 2^{\,n + C_1\sqrt{n \log n}},
\qquad\text{hence}\qquad
\tfrac{1}{12}\,\ell\, 2^n \;<\; ES_\ell(n) \;\le\; \ell\, 2^{\,n + C_1\sqrt{n\log n}} ,
$$
so the dependence on $\ell$ is uniformly linear, with no restriction on the relative sizes
of $\ell$ and $n$. Theorem B follows from Theorem A with $k = n$ together with the
source paper's bound on $ES_n(n)$.

*Proof route.* Theorem A rests on an alteration lemma: any $N$-point set with fewer than
$\ell$ points on every line contains a subset with no $k$ collinear points of size at
least $\tfrac14 (N/\ell)^{(k-2)/(k-1)}$.

*Caveat.* The $2^{O(\sqrt{n\log n})}$ gap in $n$ remains — but it is exactly the gap that
is open for the classical $ES(n)$ itself, so it is not part of the $\ell$-dependence
question.

---

### 1.11. `2408.02400__00` — Chromatic minus cochromatic number, Problem 1.5

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2408.02400__00/
**Source:** Steiner, *On the difference between the chromatic and cochromatic number*
(arXiv:2408.02400v2), Problem 1.5. Verdict: `proved` (affirmative answer).

*Definitions.* The **cochromatic number** $\zeta(G)$ is the minimum number of parts in a
partition of $V(G)$ in which each part is a clique **or** a stable set; $\omega$ and
$\chi$ are standard. The **Mycielskian** $\mu(H)$ has vertices $v^0, v^1$
($v \in V(H)$) and a root $r$, with edges $u^0v^0$, $u^0v^1$, $u^1v^0$ for
$uv \in E(H)$, and $rv^1$ for every $v \in V(H)$.

**Theorem.** For every integer $k \ge 4$ there exists a graph $G_k$ with
$$
\omega(G_k) = 4, \qquad \zeta(G_k) = k, \qquad \chi(G_k) = k + 3 .
$$
(The asked-for range is $k \ge 5$; the construction also covers $k = 4$.)

*Proof route.* A 13-vertex circulant-complement seed with
$(\omega,\zeta,\chi) = (4,4,7)$, iterated through the cochromatic Mycielski lemma:
$\zeta(\mu(H)) \ge \zeta(H)+1$, with equality when $H$ has a minimum cochromatic
partition containing an independent part (and then $\mu(H)$ has one too), while
$\omega$ is preserved and $\chi$ increases by exactly $1$.

---

### 1.12. `2512.10438__00` — Color-avoiding paths in tournaments, Problem 5.1

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2512.10438__00/
**Source:** Fox, Sudakov, Wigderson, *Color-avoiding directed paths in tournaments*
(arXiv:2512.10438v2), Problem 5.1. Verdict: `proved` (affirmative answer).

*Definitions.* The **length** of a path is its **number of vertices**. For a
$q$-edge-colouring $\chi$ of a tournament, let $p(\chi)$ be the maximum number of
vertices of a directed path whose edges use at most $q-1$ colours (a **colour-avoiding**
path). Then
$$
f_{q,q-1}(N) = \min_{\chi} p(\chi)
$$
over all $q$-edge-colourings of the **transitive** $N$-vertex tournament, while
$g_{q,q-1}(N)$ is the same minimum over **all** $N$-vertex tournaments.

**Theorem.** $f_{6,5}(9) = 8$, and there exists a **non-transitive** 6-edge-coloured
tournament $T$ on $9$ vertices with $p(T) = 7$. Hence there are integers $q \ge 4$
and $N$ for which some non-transitive $q$-edge-coloured $N$-vertex tournament has
longest colour-avoiding path strictly shorter than $f_{q,q-1}(N)$.

*Proof route.* Both halves are finite and exhaustively machine-checkable; the lower bound
$f_{6,5}(9) \ge 8$ is a word-combinatorics argument on the eight consecutive edge colours
of the transitive order.

*Caveat.* The example is non-transitive but not strongly connected (Problem 5.1 imposes no
connectivity condition). The asymptotic question $g_{q,q-1}$ versus $f_{q,q-1}$ as
$N \to \infty$ remains open.

---

## 2. Confirmed but not flagged publishable (13)

The referee confirmed the mathematics of these 13 too, but the solver did not judge them
publishable. The usual reason is scope rather than correctness — the claim settles a
deliberately hedged aside, a parenthetical belief, or a literal reading of a statement whose
intended form survives. Each entry says which, under *Why not flagged*.

### 2.1. `1601.01886__00` — Path-partitions of trees: the factor 2 in Lemma 4

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1601.01886__00/
**Source:** Gągol, Joret, Kozik, Micek, *Pathwidth and nonrepetitive list coloring*
(arXiv:1601.01886), prose remark after Lemma 4. Verdict: `proved`.

*Definitions.* A **path-partition** $\mathcal{P}$ of a tree $T$ is a partition of $V(T)$ into
sets each inducing a path; contracting every part gives the **quotient tree**
$T/\mathcal{P}$. Write
$$
\lambda(T) \;:=\; \min_{\mathcal{P},\ R \in \mathcal{P}} \ \max_{P \in \mathcal{P}} \ d_{T/\mathcal{P}}(R,P),
$$
the minimum height when the root part has depth $0$. If instead height counts the number of
parts on a root-to-leaf chain — the convention of Lemma 4 — then $H(T) = \lambda(T)+1$.

**Theorem.** For every integer $k \ge 1$:

1. every tree $T$ with $\operatorname{pw}(T) \le k$ satisfies $\lambda(T) \le 2k-1$;
2. there is a tree $T_k$ with $\operatorname{pw}(T_k) = k$ and $\lambda(T_k) = 2k-1$.

Consequently $H(T_k) = 2k$: the bound of Lemma 4 is attained exactly and the factor $2$ is
unavoidable.

*Proof route.* A path-removal characterization of tree pathwidth:
$\operatorname{pw}(T) \le k$ iff there is a path $P \subseteq T$ such that every component of
$T - V(P)$ has pathwidth at most $k-1$. Computationally verified up to $|V| = 764$.

*Why not flagged.* The sharp value depends on the height convention — $2k$ when counting
parts, $2k-1$ when counting quotient edges — and the writeup itself raises and settles the
ambiguity rather than resolving a crisp open question.

---

### 2.2. `1704.00125__01` — APX-hardness on classes without sublinear separators

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1704.00125__01/
**Source:** Dvořák, *Thin graph classes and polynomial-time approximation schemes*
(arXiv:1704.00125), prose problem. Verdict: `disproved`.

*Definitions.* A **balanced separator** $X$ of an $n$-vertex graph $G$ is a vertex set such
that every component of $G-X$ has at most $2n/3$ vertices. A class has **sublinear
separators** if every $n$-vertex member admits a balanced separator of size $o(n)$,
uniformly over the class. **Subgraph-closed** means closed under taking subgraphs;
**expansion** is measured through shallow-minor density.

**Theorem.** Let
$$
\mathcal{C} = \{G : G \text{ is bipartite and } \Delta(G) \le 20\}.
$$
Then $\mathcal{C}$ is subgraph-closed; Maximum Independent Set is solvable **exactly** in
polynomial time on $\mathcal{C}$; $\mathcal{C}$ does **not** have sublinear separators (it
contains infinitely many $N$-vertex graphs whose smallest balanced separator has size more
than $N/12$); and $\mathcal{C}$ has genuinely exponential expansion. Hence, assuming
$P \neq NP$, Maximum Independent Set is not APX-hard on $\mathcal{C}$, so neither the
"no sublinear separators" nor the "exponential expansion" version of the proposed hardness
principle holds.

*Proof route.* Polynomiality is König's theorem, $\alpha(G) = |V(G)| - \nu(G)$ for bipartite
$G$; the separator lower bound comes from bounded-degree expanders.

*Why not flagged.* It is assembled from textbook facts and kills only the "for example"
formalization of a deliberately hedged prose question; the underlying research programme is
untouched.

---

### 2.3. `1809.05439__00` — Extra colours at a vertex in triangle-free planar set-colourings

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1809.05439__00/
**Source:** Dvořák, Hu, *Fractional coloring of planar graphs of girth five*
(arXiv:1809.05439), hedged remark after Theorem 5. Verdict: `disproved`.

*Definitions.* A **set-colouring** is a map $\varphi : V(G) \to 2^{[9]}$ in which adjacent
vertices receive **disjoint** sets.

**Theorem.** It is **not** true that for every triangle-free planar graph $G$ and every
$x \in V(G)$ there is a set-colouring $\varphi : V(G) \to 2^{[9]}$ with
$|\varphi(v)| \ge 3$ for every $v \in V(G)$ and $|\varphi(x)| = 5$. An explicit
counterexample $G$ has $23$ vertices and $35$ edges: take two copies $H^1, H^2$ of the
wheel with five spokes with every spoke subdivided once, identified at the common hub $x$
(so $H^j$ has hub $x$, subdivision vertices $u^j_i$ and rim $v^j_0 \cdots v^j_4$,
$i \in \mathbb{Z}_5$); add a vertex $z_j$ adjacent to $u^j_0, u^j_1$ in each copy; add the
edge $z_1 z_2$.

*Proof route.* A rigidity lemma for the single subdivided wheel: with
$P = \varphi(x)$, $Q = [9] \setminus P$, one gets $\varphi(u_i) = Q \setminus \{q_i\}$ for a
unique $q_i \in Q$, with $q_i \in \varphi(v_i)$ and $q_i \neq q_{i+1}$. Machine-verified.

*Why not flagged.* $G$ is triangle-free but contains $4$-cycles, so the girth-five
strengthening — the actual subject of the paper — is untouched.

---

### 2.4. `1902.06473__00` — Classical and quantum sorting lower bounds are within a constant

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1902.06473__00/
**Source:** Cardinal, Joret, Roland, *Information-theoretic lower bounds for quantum sorting*
(arXiv:1902.06473), Conclusion. Verdict: `proved` (medium confidence).

*Definitions.* Let $P$ be an $n$-element poset and $e(P) = |\mathcal{L}(P)|$ its number of
linear extensions. Let $C(P)$ be the **chain polytope**
$$
C(P) = \Big\{ z \in \mathbb{R}^P_{\ge 0} \ : \ \sum_{v \in D} z_v \le 1 \ \text{ for every chain } D \subseteq P \Big\},
$$
with normalized Lebesgue measure, and put
$$
h(z) = -\frac{1}{n}\sum_{v \in P} \ln z_v,
\qquad
H(P) = \min_{z \in C(P)} h(z),
\qquad
QH(P) = \frac{1}{\operatorname{vol} C(P)} \int_{C(P)} h(z)\, dz .
$$
Finally $\operatorname{LB}(P) = n(\ln n - H(P))$ and
$\operatorname{QLB}(P) = n(H_n - QH(P))$, where $H_m = \sum_{j=1}^m 1/j$.

**Theorem.** For every finite poset $P$,
$$
\ln e(P) \;\le\; \operatorname{QLB}(P) \;\le\; \frac{\ln e(P)}{\ln 2},
$$
and hence, with the standard estimate $\ln e(P) \le \operatorname{LB}(P) \le 2\ln e(P)$,
$$
\tfrac{1}{2}\operatorname{LB}(P) \;\le\; \operatorname{QLB}(P) \;\le\; \tfrac{1}{\ln 2}\operatorname{LB}(P).
$$

*Proof route.* Stanley's rank log-concavity for the chain polytope. Verified on every poset
with at most $6$ elements plus random posets on $7$–$8$ elements.

*Why not flagged.* The catalog statement is truncated and garbled in the PDF source, so the
theorem is proved for a reconstructed reading (uniform chain-polytope averaging); the
solver's own confidence is `medium`.

---

### 2.5. `1904.12273__01` — Heavy paths for long odd holes

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1904.12273__01/
**Source:** Chudnovsky, Scott, Seymour, *Detecting a long odd hole* (arXiv:1904.12273),
hedged "might be true" extension. Verdict: `disproved`.

*Definitions.* A **hole** is an induced cycle of length at least four. A vertex
$v \notin V(C)$ is **$C$-major** if $N(v) \cap V(C)$ is not contained in a three-vertex
subpath of $C$.

**Theorem.** For every fixed long-hole threshold $t \ge 7$ there is **no** integer $b(t)$
with the following property: whenever $C$ is a shortest odd hole of $G$ of length at least
$t$ and $M$ is a set of $C$-major vertices one of which is nonadjacent to all the others,
some subpath $Q$ of $C$ with at most $b(t)$ edges contains a neighbour of every vertex of
$M$. Failure occurs already with $|M| = 4$: for odd $q \ge 3$, build $C$ from three
internally disjoint paths $A_1, A_2, A_3$ of $q$ edges each (so $|V(C)| = 3q$ is odd), add a
triangle $y_1y_2y_3$ with $N_C(y_i) = V(A_i)$, and add $x$ complete to $V(C)$ and
anticomplete to $\{y_1,y_2,y_3\}$; take $M = \{x, y_1, y_2, y_3\}$.

*Why not flagged.* It refutes an extension the authors explicitly could not prove and
worked around ("this extension might be true, but we were unable to prove it"), rather than
a stated conjecture.

---

### 2.6. `1907.06019__01` — Extremal mutually annihilating pairs in the exterior algebra

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1907.06019__01/
**Source:** Scott, Wilmer, *Combinatorics in the exterior algebra and the Bollobás Two
Families Theorem* (arXiv:1907.06019), prose question after Theorem 2.4. Verdict: `proved`.

*Definitions.* Let $V$ be an $n$-dimensional real vector space. Subspaces
$U \subseteq \bigwedge^r V$ and $W \subseteq \bigwedge^s V$ are **mutually annihilating** if
$u \wedge w = 0$ for all $u \in U$, $w \in W$. For $0 \neq v \in V$, the **exterior star** is
$$
\operatorname{St}_k(v) \;:=\; v \wedge \textstyle\bigwedge^{k-1} V \ \subseteq\ \textstyle\bigwedge^{k} V .
$$

**Theorem.** Let $1 \le r, s < n/2$. If $U \subseteq \bigwedge^r V$ and
$W \subseteq \bigwedge^s V$ are mutually annihilating and
$$
\dim U \cdot \dim W = \binom{n-1}{r-1}\binom{n-1}{s-1},
$$
then there is a nonzero $v \in V$ with $U = \operatorname{St}_r(v)$ and
$W = \operatorname{St}_s(v)$. Conversely, every such pair is mutually annihilating and
attains equality.

*Proof route.* The equality case for cross-intersecting set families (agreeing with
Matsumoto–Tokushige 1989 and with exhaustive computation), plus a rigidity lemma confirmed
by exact nullspace computations.

*Why not flagged.* The inequality of the source paper's Theorem 2.4 is taken as input, and
the boundary cases $r = n/2$ or $s = n/2$ are not addressed.

---

### 2.7. `2204.10119__01` — Minimum degree 6, maximum degree 8, and $K_6$ minors

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.10119__01/
**Source:** Chudnovsky, Scott, Seymour, Spirkl, *Bipartite graphs with no $K_6$ minor*
(arXiv:2204.10119), parenthetical aside after Conjecture 1.3. Verdict: `disproved`.

*Definitions.* An **apex graph** is a graph $Q$ having a vertex $z$ with $Q - z$ planar. A
**$4$-clique amalgam** of $Q_1, Q_2$ is $Q = Q_1 \cup Q_2$ where
$S = V(Q_1) \cap V(Q_2)$ is a clique of size at most four and there are no edges between
$V(Q_1) \setminus S$ and $V(Q_2) \setminus S$.

**Theorem.** There is a non-null simple connected graph $G$ with
$$
|V(G)| = 28, \qquad |E(G)| = 88, \qquad \text{degree sequence } 6^{22}\,7^{4}\,8^{2},
$$
so $6 \le d_G(v) \le 8$ for every $v \in V(G)$, and $G$ has no $K_6$ minor.

*Proof route.* Two lemmas — an apex graph has no $K_6$ minor, and a $\le 4$-clique amalgam
of $K_6$-minor-free graphs is $K_6$-minor-free — applied to an amalgam of two apex graphs
over a common $K_4$. Fully machine-verified, with certified planar embeddings.

*Why not flagged.* It refutes a parenthetical "as far as we know" belief rather than
Conjecture 1.3 itself, and it exploits a $4$-clique separator, so any $5$-connected
strengthening survives.

---

### 2.8. `2209.09107__00` — Alon–Tarsi orientations with large out-degrees

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2209.09107__00/
**Source:** Bradshaw, Chen, Ma, Mohar, Wu, *List-avoiding orientations* (arXiv:2209.09107),
Question 6.1. Verdict: `disproved`.

*Definitions.* For an orientation $D$, let $\mathcal{E}(D)$ be the family of Eulerian
spanning subdigraphs of $D$ (including the empty one). Then $D$ is an **Alon–Tarsi**
orientation if
$$
\operatorname{diff}(D) \;=\; \sum_{A \in \mathcal{E}(D)} (-1)^{|A|} \;\neq\; 0 .
$$

**Theorem.** There are graphs $G$ having **no** spanning subgraph with an Alon–Tarsi
orientation $D$ in which
$$
d^+_D(v) \;\ge\; \tfrac{1}{2}\bigl(\deg_G(v) - 1\bigr) \qquad \text{for every } v .
$$
Indeed every Eulerian graph with an odd number of edges is such a $G$; the smallest is
$C_3$, and the same applies to every odd cycle.

*Proof route.* Lemma: if $D$ is an Eulerian orientation with an odd number of edges then
$\operatorname{diff}(D) = 0$, because $A \mapsto D \setminus A$ is a parity-reversing
involution on $\mathcal{E}(D)$. Integrality then forces $d^+_D(v) \ge \deg_G(v)/2$, i.e. an
Eulerian orientation of $G$ itself. Verified exhaustively by computer.

*Why not flagged.* It refutes Question 6.1 exactly as printed, with no outer floor; with
$d^+_D(v) \ge \lfloor (\deg_G(v)-1)/2 \rfloor$ a degree-two vertex needs out-degree $0$ and
the counterexample evaporates. The paper's Conjecture 1.1 is untouched.

---

### 2.9. `2304.03567__04` — Forward covers of strong digraphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2304.03567__04/
**Source:** Bessy, Thomassé, Viennot, *Temporalizing digraphs via linear-size balanced
bi-trees* (arXiv:2304.03567), Conjecture 1. Verdict: `disproved`.

*Definitions.* For a linear ordering $\prec$ of $V(D)$, a directed path
$v_0 v_1 \cdots v_\ell$ is **forward** if $v_0 \prec v_1 \prec \cdots \prec v_\ell$. An
unordered pair $\{x,y\}$ is **forward connected** under $\prec$ if there is a forward
directed path from its $\prec$-earlier endpoint to its later one. A **forward cover** of $D$
is a family of orderings such that every unordered vertex pair is forward connected in at
least one of them.

**Theorem.** For every $m \ge 3$, let $D_m$ be the digraph on the $3m$ vertices
$\{c_i, a_i, b_i : i \in \mathbb{Z}_m\}$ with arcs
$$
c_i \to c_{i+1}, \qquad c_i \to a_i \to c_{i+1}, \qquad c_i \to b_i \to c_{i+1}
\qquad (i \in \mathbb{Z}_m).
$$
Then $D_m$ is a strongly connected simple oriented graph on $n = 3m$ vertices, and it has $m$
vertex pairs such that any single ordering forward-connects at most one of them. Hence every
forward cover of $D_m$ has size at least $m = n/3$, so no $O(\log n)$ bound holds.

*Why not flagged.* The refutation is against the source paper's verbatim definition of
forward cover; that definition is worth re-checking for an omitted qualification before the
result is treated as final.

---

### 2.10. `2307.15512__00` — Meyniel-type bound for hypergraph cop number

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.15512__00/
**Source:** Erde, Kang, Lehner, Mohar, Schmid, *Catching a robber on a random $k$-uniform
hypergraph* (arXiv:2307.15512), Conjecture 1.4. Verdict: `disproved`.

*Definitions.* In the hypergraph Cops-and-Robber game, players occupy vertices, a move is
allowed between two vertices lying in a common hyperedge, and capture occurs when a cop
occupies the robber's vertex; $c(H)$ is the cop number. The **2-section** $\partial H$ has
$u \sim v$ iff $u,v$ lie in a common hyperedge; the two games have identical legal moves, so
$c(H) = c(\partial H)$.

**Theorem.** There is no constant $C$ with $c(H) \le C\sqrt{n/k}$ for every connected
$k$-uniform hypergraph $H$ on $n$ vertices. Concretely, for all large $N$ there are
connected $k$-graphs on $n = 2N$ vertices with
$$
k = \Big\lfloor \tfrac{\sqrt{N}}{2} \Big\rfloor = \Theta(\sqrt{n}),
\qquad
\sqrt{n/k} = \Theta(N^{1/4}),
\qquad
c(H) = \Omega\!\left(N^{1/4}\log N\right),
$$
so that $c(H)\big/\sqrt{n/k} = \Omega(\log N) \to \infty$.

*Proof route.* Take disjoint $P, R$ of size $N$, let $P$ induce a clique, and make every
pair meeting $R$ an edge independently with probability $\rho = N^{-1/4}$; every edge is then
placed inside a $k$-clique so the graph is realized as a 2-section.

*Why not flagged.* The construction is probabilistic, hence existential (a deterministic
version is the lexicographically first labelled graph meeting two finite conditions).

---

### 2.11. `2310.04265__11` — Substitution closure of $\vec{\chi}$-bounded classes

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__11/
**Source:** Aboulker, Aubian, Charbit, Lopes, *Clique number of tournaments*
(arXiv:2310.04265), Conjecture 6.1. Verdict: `disproved`.

*Definitions.* $\vec{\chi}(D)$ is the **dichromatic number**, the least number of parts in a
partition of $V(D)$ into acyclic sets; equivalently $\vec{\chi}(D) = \min_\prec \chi(D^\prec)$
over the backedge graphs $D^\prec$ (defined as in §1.8), while
$\vec{\omega}(D) = \min_\prec \omega(D^\prec)$. A class is **$\vec{\chi}$-bounded** if
$\vec{\chi}$ is bounded by a function of $\vec{\omega}$ on it. **Substitution** replaces a
vertex by a digraph; the **substitution closure** is the closure under iterated substitution.

**Theorem.** There is a hereditary class $\mathcal{C}$ of oriented graphs with
$$
\vec{\chi}(J) = \vec{\omega}(J) \le 2 \qquad \text{for every nonempty } J \in \mathcal{C}
$$
(so $\mathcal{C}$ is $\vec{\chi}$-bounded, even by the identity) whose substitution closure
contains digraphs $G_n$ with
$$
\vec{\omega}(G_n) = 2 \qquad\text{and}\qquad \vec{\chi}(G_n) = n+2 \qquad (n \ge 0).
$$
Hence the substitution closure of a $\vec{\chi}$-bounded class need not be
$\vec{\chi}$-bounded.

*Construction.* For a finite simple graph $H$ with ordered vertices $x_1,\dots,x_m$, let
$S(H)$ be the oriented graph obtained by adding one vertex $a_{ij}$ per edge $x_ix_j$
($i<j$) together with the arcs
$$
x_i \to a_{ij}, \qquad a_{ij} \to x_j, \qquad x_j \to x_i ,
$$
and no others. Put
$\mathcal{C} = \{J : J \cong \text{an induced subdigraph of } S(H) \text{ for some finite triangle-free } H\}$.
The amplifier $F_H(G)$ substitutes a copy of $G$ into every edge-vertex $a_{ij}$ of $S(H)$;
with $H_n$ triangle-free of chromatic number $n+3$, set $G_{n+1} = F_{H_n}(G_n)$.

*Why not flagged.* It refutes Conjecture 6.1 for general digraphs as stated; the tournament
version (Question 3.10) is not addressed.

---

### 2.12. `2508.08870__00` — Distinct distances in typical $d$-dimensional norms

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2508.08870__00/
**Source:** Alon, Pinchasi, *Distinct Directions and Distinct Distances in $\mathbb{R}^d$*
(arXiv:2508.08870), Conjecture 1.5. Verdict: `disproved`.

*Definitions.* For a norm $\|\cdot\|$ on $\mathbb{R}^d$ and a finite
$P \subset \mathbb{R}^d$, put
$D_{\|\cdot\|}(P) = \bigl|\{\|x-y\| : x,y \in P,\ x \neq y\}\bigr|$. Following the quoted
statement, "$d$-dimensional" means only that $P$ does not lie in an affine hyperplane.

**Theorem.** For every $d \ge 2$ and **every** norm $\|\cdot\|$ on $\mathbb{R}^d$ there are
arbitrarily large finite $P \subset \mathbb{R}^d$, not contained in an affine hyperplane,
with
$$
D_{\|\cdot\|}(P) \;\le\; \left(d-1+\frac{1}{2(d-1)}\right) n - O_d(1), \qquad n = |P| ,
$$
and the coefficient stays below $d$ by a fixed margin,
$d - \bigl(d-1+\tfrac{1}{2(d-1)}\bigr) = 1 - \tfrac{1}{2(d-1)} > 0$. For $d = 2$ take the two
parallel progressions
$$
P_m = \{(i,0) : 0 \le i < m\} \cup \{(i,1) : 0 \le i < m\},
$$
which is noncollinear with $n = 2m$ and satisfies
$D_{\|\cdot\|}(P_m) \le 3m-2 = \tfrac{3}{2}n - 2$ in every norm. For general $d$, with
$r = d-1$, take $P_m = A_m + S$ where
$A_m = \{0, e_1, \dots, (m-1)e_1\}$ and $S = \{\pm e_2, \dots, \pm e_d\}$.

*Proof route.* The universal bound
$D_{\|\cdot\|}(P) \le \bigl(|P-P|-1\bigr)/2$, since $(P-P)\setminus\{0\}$ splits into pairs
$\{v,-v\}$ with $\|v\| = \|-v\|$; then count $|P_m - P_m|$ exactly.

*Why not flagged.* It refutes Conjecture 1.5 under the affine-span reading of
"$d$-dimensional" that the statement literally gives; an omitted general-position hypothesis
would change the problem.

---

### 2.13. `2603.02786__03` — Packing arithmetic progressions: the constant $1/2$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2603.02786__03/
**Source:** Alon, Dębski, Grytczuk, Przybyło, *Packing arithmetic progressions*
(arXiv:2603.02786), Conjecture 6 (first clause). Verdict: `disproved`.

*Definitions.* For $1 \le d \le k$ let $B_d = \{d, 2d, \dots, nd\}$. Then $M_k(n)$ is the
minimum length of an interval containing pairwise disjoint **integral** translates
$t_d + B_d$ for all $d = 1,\dots,k$.

**Theorem.** If $k \to \infty$ and $k = o(n)$, then
$$
M_k(n) \;\ge\; \left(\frac{6619}{10800} - o(1)\right)\frac{nk^2}{\ln k}
\;=\; \left(\frac{6619}{5400} - o(1)\right)\frac{nk^2}{2\ln k} .
$$
Since $\tfrac{6619}{5400} = 1.225740\ldots > 1$, this contradicts the conjectured asymptotic
$M_k(n) \sim \dfrac{nk^2}{2\ln k}$ for $k \ll n$. An explicit counterexample sequence is
$n = k^4$.

*Proof route.* An elementary weighted core-overlap counting argument.

*Why not flagged.* It refutes only the constant $1/2$ in the first clause of Conjecture 6,
and remains consistent with every bound the paper proves.

---

## 3. Correct but already known (26)

These 26 were reviewed `ALREADY_KNOWN`: the mathematics is correct and was verified step by
step, but the result is not new. As SUMMARY puts it, this pile indicts catalog freshness more
than the model — most were scooped by 2024–2026 papers the 2026-05 auto-review missed, several
by mere weeks, and a few were already settled inside the source papers themselves. They remain
usable as formalization targets, but there is no priority to claim; each entry records
**Prior art**, the reference that pre-empts it.

> **Seven entries additionally failed the interpretation check** (`interp. ok = n` in
> SUMMARY's table): §3.4, §3.10, §3.11, §3.13, §3.15, §3.22 and §3.26. There the catalog
> statement itself is a misquotation of the source, so the theorem proved is not the open
> problem. They are marked *Misquoted target* and are the least useful entries in this file.

### 3.1. `1610.00239__00` — Bounded-norm compression of inner products

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00239__00/
**Source:** Alon, Klartag, *Optimal compression of approximate inner products and dimension
reduction* (arXiv:1610.00239), Conjecture 2.4. Verdict: `proved`.

**Theorem.** There are absolute constants $C, K > 0$ such that the following holds. Let
$x_1,\dots,x_n$ and $y_1,\dots,y_m$ lie in the unit ball of a real Hilbert space $H$, and let
$0 < \varepsilon < 1$. Then there are $p_1,\dots,p_n, q_1,\dots,q_m \in \mathbb{R}^t$ with
$$
t \le C\,\frac{\log(2+\varepsilon^2 n)}{\varepsilon^2},
\qquad
\|p_i\|_2, \|q_j\|_2 \le K,
\qquad
\bigl|\langle p_i,q_j\rangle - \langle x_i,y_j\rangle\bigr| \le \varepsilon .
$$
Moreover, once $p_1,\dots,p_n$ are fixed the conclusion holds simultaneously for every $y$ in
the unit ball, with a suitable $q = q(y)$. Taking $m = n$ gives the conjecture.

**Prior art.** Confirmed by Vishesh Jain, arXiv:2608.13782 (posted 2026-08-13), Remark (iii)
— two and a half weeks before this attack ran.

---

### 3.2. `1709.09050__01` — Cop number of outerplanar graphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1709.09050__01/
**Source:** Bonato, Mohar, *Topological directions in Cops and Robbers*
(arXiv:1709.09050), classification problem. Verdict: `proved`.

*Definitions.* $c(G)$ is the cop number. A vertex $v$ is a **corner** dominated by $u \neq v$
if $N_G[v] \subseteq N_G[u]$; $G$ is cop-win iff it is dismantlable by repeated corner removal.

**Theorem.** For every finite simple connected outerplanar graph $G$,
$$
c(G) =
\begin{cases}
1, & \text{if } G \text{ is chordal},\\
2, & \text{if } G \text{ contains an induced cycle of length at least } 4 .
\end{cases}
$$
Equivalently, $G$ is $1$-cop-win iff every block of $G$ with at least three vertices is a
maximal outerplanar graph.

**Prior art.** Published as Theorem 3.9 of Bonato, Breen, Brimkov, Carlson, English, Geneson,
Hogben, Perry, Reinhart, arXiv:1903.10087 (J. Combinatorics 13(1), 2022), which explicitly
resolves this problem from the Bonato–Mohar survey.

---

### 3.3. `1802.03727__00` — Separation choosability grows with minimum degree

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.03727__00/
**Source:** Esperet, Kang, Thomassé, *Separation choosability and dense bipartite induced
subgraphs* (arXiv:1802.03727), Conjecture 1.3. Verdict: `proved`.

*Definitions.* A $k$-list assignment $L$ is **separated** if $|L(u) \cap L(v)| \le 1$ for
every $uv \in E(G)$; the **separation choosability**
$\operatorname{ch}_{\mathrm{sep}}(G)$ is the least $k$ such that every separated $k$-list
assignment is colourable.

**Theorem.** There is an absolute $c > 0$ such that every graph $G$ of sufficiently large
minimum degree $d$ satisfies
$$
\operatorname{ch}_{\mathrm{sep}}(G) \;\ge\; c\,\frac{\log d}{\log\log d}.
$$
This is stronger than the conjectured "$\to \infty$" form.

**Prior art.** The conjecture as stated already follows from published work: Kwan, Letzter,
Sudakov, Tran, arXiv:1810.12144 (Combinatorica 2020) proved Esperet–Kang–Thomassé's
Conjecture 1.4, which the source paper itself notes implies Conjecture 1.3. The writeup's
quantitative strengthening and its chromatic-number route do appear to be new.

---

### 3.4. `1902.10878__00` — The "wild conjecture" for $\phi$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1902.10878__00/
**Source:** Chudnovsky, Hompe, Scott, Seymour, Spirkl, *Concatenating bipartite graphs*
(arXiv:1902.10878), informal remark. Verdict: `disproved`. **Misquoted target.**

**Theorem.** It is not true that for all $x,y \in (0,1]$ there is an integer $k \ge 1$ with
$$
\phi(x,y) \;=\; F_k(x,y) \;:=\; \frac{\lceil kx\rceil + \lceil ky\rceil - 1}{k} .
$$
Failure occurs at $(x,y) = (2/5,\,1/4)$.

**Prior art / misquotation.** This is the "wild conjecture" that the source paper itself
already declares false, refuting it with an explicit $(13/27,\,1/9)$ example in its own
introduction. The genuinely open problem — the correct characterisation of $\phi$ — is
untouched.

---

### 3.5. `1907.06019__00` — Extremal self-annihilating subspaces

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1907.06019__00/
**Source:** Scott, Wilmer, *Combinatorics in the exterior algebra and the Bollobás Two
Families Theorem* (arXiv:1907.06019), question after Theorem 2.4. Verdict: `proved`.

*Definitions.* $W \subseteq \bigwedge^r V$ is **self-annihilating** if $w \wedge w' = 0$ for
all $w, w' \in W$.

**Theorem.** Let $V$ be $n$-dimensional over $\mathbb{R}$ and $1 \le r < n/2$. If
$W \subseteq \bigwedge^r V$ is self-annihilating with $\dim W = \binom{n-1}{r-1}$, then there
is a nonzero $v \in V$ with $W = v \wedge \bigwedge^{r-1} V$, and the line $\mathbb{R}v$ is
uniquely determined by $W$.

**Prior art.** Already proved — over any field, and in a stronger Hilton–Milner form — by
Bulavka, Gandini, Woodroofe, arXiv:2406.17857 (June 2024), Trans. London Math. Soc. 12
(2025), e70022. (This is the companion of `1907.06019__01` in §2.6, which *is*
confirmed new.)

---

### 3.6. `1909.11578__02` — Density of symmetric intersecting families of vectors

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/1909.11578__02/
**Source:** Eberhard, Kahn, Narayanan, Spirkl, *On symmetric intersecting families of vectors*
(arXiv:1909.11578), stated problem. Verdict: `disproved`.

*Definitions.* **Symmetric** means invariant under some transitive group of coordinate
permutations (the source paper's definition, not invariance under the full symmetric group).

**Theorem.** There are no constants $c, \delta > 0$ (even depending on $k$) such that every
symmetric intersecting $A \subseteq [k]^n$ satisfies $\log_k |A| \le n - cn^{\delta}$. For
$k \ge 3$ there are cyclically symmetric intersecting families of density $n^{-O_k(1)}$, so no
deficit $\omega(\log n)$ is possible. The planar core is
$\mathcal{F}_n = \{S \subseteq \mathbb{Z}_n : \ell(S) > \ell(S^c)\}$, where $\ell(S)$ is the
longest cyclic interval inside $S$ — increasing, intersecting, rotation-invariant.

**Prior art.** Essentially known: the runs family is Ellis–Kalai–Narayanan arXiv:1702.02607,
and Keller–Lifshitz–Marcus arXiv:2307.01356 publish the lifted transitive-symmetric vector
family of density $\exp(-O(k \log k \log n))$, "following a strategy suggested in [EKNS19,
Section 4]".

---

### 3.7. `2004.07214__00` — Enumerating minimal dominating sets for $S_t$-free posets

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2004.07214__00/
**Source:** Bonamy, Defrain, Micek, Nourine, *Enumerating minimal dominating sets in the
(in)comparability graphs of bounded dimension posets* (arXiv:2004.07214), Conjecture 7.1.
Verdict: `proved`.

*Definitions.* $S_t$ is the **standard example**: the poset on
$\{a_1,\dots,a_t,b_1,\dots,b_t\}$ with $a_i < b_j$ exactly when $i \neq j$.
$\operatorname{Inc}(P)$ is the incomparability graph of $P$.

**Theorem.** For every fixed $t$ and every $S_t$-free poset $P$, the minimal dominating sets
of $G = \operatorname{Inc}(P)$ can be enumerated with delay $n^{O(t)}$ and polynomial space —
stronger than the conjectured output-polynomial bound. Ingredients: every linear extension of
$P$ is a linear mim-width layout of $G$ of width at most $t-1$; on a graph with a bounded
linear mim-width layout, existence of a minimal dominating set respecting prescribed
inclusions and exclusions is polynomial-time decidable.

**Prior art.** The "main new observation" (Lemma 1) is literally Proposition 3.6 of
Kang–Kwon–Strømme–Telle (TCS 2017), which together with Golovach et al. (Algorithmica 2018)
resolved Conjecture 7.1 before it was posed.

---

### 3.8. `2009.12189__00` — Fractional vertex-arboricity of planar graphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2009.12189__00/
**Source:** Bonamy, Kardoš, Kelly, Postle, *Fractional vertex-arboricity of planar graphs*
(arXiv:2009.12189), Conjecture 1.1. Verdict: `disproved`.

*Definitions.* With $\mathcal{F}(G)$ the family of vertex sets inducing forests,
$$
\operatorname{va}_f(G) = \min\Big\{\sum_{F \in \mathcal{F}(G)} x_F \;:\; x \ge 0,\ \sum_{F \ni v} x_F \ge 1 \ \forall v\Big\},
$$
with the LP dual $\max\{\sum_v z_v : z \ge 0,\ \sum_{v \in F} z_v \le 1\ \forall F \in \mathcal{F}(G)\}$.

**Theorem.** Not every planar graph has $\operatorname{va}_f \le 2$. Indeed, let $G$ be a
simple plane triangulation on $n \ge 4$ vertices that is not vertex-2-arborable; then
$$
\operatorname{va}_f(G) \;\ge\; \frac{4n-12}{2n-7} \;=\; 2 + \frac{2}{2n-7} \;>\; 2 ,
$$
so the dual of any non-Hamiltonian cubic polyhedral graph is a counterexample. The explicit
25-vertex Tutte dual has $\operatorname{va}_f = 33/16$.

**Prior art.** Already refuted by Naserasr, Pham, Pujol, Zhou, arXiv:2505.16808 (May 2025),
and a fortiori by the August 2026 counterexamples to the Albertson–Berman conjecture.

---

### 3.9. `2108.00991__00` — Threshold Ramsey multiplicity of paths

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.00991__00/
**Source:** Conlon, Fox, Sudakov, Wei, *Threshold Ramsey multiplicity for paths and even
cycles* (arXiv:2108.00991), Conjecture 3. Verdict: `disproved`.

*Definitions.* $m(H)$ is the threshold Ramsey multiplicity: the minimum number of
monochromatic copies of $H$ over all $2$-colourings of $K_{r(H)}$.

**Theorem.** For large $k$ it is **not** the case that $m(P_k) = k!/2$ for even $k$ and
$m(P_k) = \tfrac{k-1}{4}(k-1)!$ for odd $k$. Both formulas are beaten by elementary
perturbations of the two-block colourings of $K_{r(P_k)}$, where
$r(P_k) = k + \lfloor k/2 \rfloor - 1$. Verified by brute force for $k = 4,\dots,8$.

**Prior art.** Already disproved, with strictly stronger bounds, by Huang, Yang, Chen,
arXiv:2606.01996 (1 June 2026).

---

### 3.10. `2111.00532__00` — Pure pairs from transversal triangles

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2111.00532__00/
**Source:** Scott, Seymour, Spirkl, *Pure pairs. IX. Transversal trees* (arXiv:2111.00532),
Question 1.3. Verdict: `proved`. **Misquoted target.**

*Definitions.* A **blockade** $\mathcal{B} = (B_1,\dots,B_k)$ is a sequence of disjoint vertex
sets; its **width** is $W = \min_i |B_i|$. A **pure pair** is a pair $X, Y$ that is complete
or anticomplete.

**Theorem.** Let $\mathcal{B} = (B_1,B_2,B_3)$ be a blockade of width $W$ in $G$. If $G$ has
no triangle with one vertex in each block, then two distinct blocks contain an
**anticomplete** pair $X, Y$ with $|X| = |Y| = \lfloor \sqrt{W} \rfloor$. Hence
$c = \varepsilon = 1/2$ answer the question as extracted.

**Prior art / misquotation.** The catalog dropped the linear requirement
$|X| \ge \varepsilon W$; the weakened statement proved here is the $K_3$ case of
Erdős–Hajnal–Pach, which is Theorem 1.2 of the same source paper. The actual open question
remains open.

---

### 3.11. `2111.00532__01` — Pure pairs from transversal copies of an ordered graph

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2111.00532__01/
**Source:** same paper as §3.10, informal question. Verdict: `proved`. **Misquoted target.**

*Definitions.* For an ordered graph $H$ with $h_1 < \cdots < h_k$ and a blockade
$\mathcal{B} = (B_1,\dots,B_k)$ of width $W$, an **ordered $\mathcal{B}$-transversal copy** of
$H$ is a choice $v_i \in B_i$ with $v_iv_j \in E(G) \iff h_ih_j \in E(H)$ for all $i<j$.

**Theorem.** For every ordered graph $H$ on $k \ge 2$ vertices: if a blockade
$\mathcal{B} = (B_1,\dots,B_k)$ of width $W$ admits no ordered $\mathcal{B}$-transversal copy
of $H$, then there are distinct $i,j$ and a pure pair $X \subseteq B_i$, $Y \subseteq B_j$ with
$$
|X|, |Y| \;\ge\; \frac{1}{2(k-1)^{1/(k-1)}}\, W^{1/(k-1)} .
$$
So the extracted question has answer "all finite ordered graphs", with $c(H) = 1/(|H|-1)$.

**Prior art / misquotation.** This is exactly Theorem 1.2 of the source paper (the
Erdős–Hajnal–Pach theorem, Geombinatorics 10 (2000), 64–68). The catalog garbled the actual
open question, which is the asymmetric strengthening $|X| \ge \varepsilon W$,
$|Y| \ge \varepsilon W^c$; that remains open.

---

### 3.12. `2204.12330__00` — Uniform twin-width is strictly stronger

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.12330__00/
**Source:** Bonnet, Geniet, Tessera, Thomassé, *Twin-width VII: groups* (arXiv:2204.12330),
informal claim. Verdict: `proved`.

**Theorem.** Let $G = \operatorname{Sym}_{\mathrm{fin}}(\mathbb{Z})$ be the group of finitely
supported permutations of $\mathbb{Z}$. Then
$$
\operatorname{tww}(G) < \infty
\qquad\text{but}\qquad
\operatorname{utww}(G) = \infty ,
$$
and likewise for the finitary alternating group. More generally: if a countable locally finite
group $G$ contains finite subgroups $H_i$ whose least dimension $D(H_i)$ of a nontrivial
complex representation tends to infinity, then $G$ has finite twin-width and infinite uniform
twin-width.

**Prior art.** Established three weeks before this review by Kontogeorgiou, Miraftab,
*Quasirandomness and Uniform Twin-Width*, arXiv:2608.10150 (10 Aug 2026) — same
quasirandomness route, same $D^{1/4}$ exponent.

---

### 3.13. `2208.10074__00` — Product structure with bounded tree-depth

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.10074__00/
**Source:** Dvořák, Wood, *Product structure of graph classes with strongly sublinear
separators* (arXiv:2208.10074), Open Problem 6 (tree-depth form). Verdict: `disproved`.
**Misquoted target.**

*Definitions.* $\boxtimes$ is the strong product; $\operatorname{td}(H)$ is tree-depth — the
least height of a rooted forest $F$ with $H$ a subgraph of the closure of $F$.

**Theorem.** It is **false** that every hereditary class with $O(n^{1-\epsilon})$ separators
has all its $n$-vertex members inside $H \boxtimes K_m$ with $\operatorname{td}(H)$ bounded and
$m = O(n^{1-\epsilon})$ — already for planar graphs with $\epsilon = 1/2$. Quantitatively, for
every constant $C > 0$, if the $N \times N$ grid $Q_N$ is a subgraph of $H \boxtimes K_m$ with
$m \le CN$, then
$$
\operatorname{td}(H) \;\ge\; \log_2\log N - O_C(1),
$$
i.e. a clique factor of order $O(\sqrt{n})$ forces tree-depth $\Omega(\log\log n)$.

**Prior art / misquotation.** This is exactly Theorem 20 of the source paper itself (the
$d = 2$ case), which explicitly notes that the tree-depth strengthening of Open Problem 6 is
false. The actual open conjecture is about bounded **tree-width** and is untouched.

---

### 3.14. `2306.04710__01` — $\vec{\chi}$-finiteness of $\{\Delta(1,m,m'), F\}$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2306.04710__01/
**Source:** Carbonero, Koerts, Moore, Spirkl, *On heroes in digraphs with forbidden induced
forests* (arXiv:2306.04710), stated problem. Verdict: `proved`.

**Theorem.** Let $F$ be any orientation of $K_{1,4}$ and $m, m' \ge 1$. Then
$$
\sup\{\vec{\chi}(D) : D \text{ is } \{\Delta(1,m,m'), F\}\text{-free}\} = \infty ,
$$
so no pair $(m,m')$ makes $\{\Delta(1,m,m'), F\}$ $\vec{\chi}$-finite. The load-bearing step
is that there are oriented graphs of arbitrarily large dichromatic number containing no
directed triangle and having claw-free underlying graph (built as random orientations of the
line graph of $K_{n,n}$).

**Prior art.** That load-bearing theorem was already proved by Aubian and Kuffner,
arXiv:2602.08736 (Feb 2026), from which the $\Delta(1,m,m')$ resolution follows immediately.

---

### 3.15. `2308.15387__00` — Component sizes under few colours

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2308.15387__00/
**Source:** Alon, Bucić, Christoph, Krivelevich, *The power of many colours*
(arXiv:2308.15387), stated conjecture. Verdict: `disproved`. **Misquoted target.**

*Definitions.* For an $r$-edge-colouring $\chi$ of $K_n$ and $C \subseteq [r]$, let $G_C$ be
the spanning subgraph of edges with colours in $C$. Then
$$
f(n,r,s) = \min_{\chi : E(K_n) \to [r]} \ \max_{C \subseteq [r],\ |C| \le s} \ \{\text{largest component order of } G_C\} .
$$

**Theorem.** The formula $f(n,r,s) = \frac{s^2(\log r)^{1-o_r(1)}}{r}\,n$ fails at the low end
of the stated range $1 \le s \le \sqrt{r}/\log r$. Binary construction: for $d \ge 1$,
$r = 2^d - 1$ and $n = t2^d$, indexing $2^d$ equal classes $V_x$ ($x \in \mathbb{F}_2^d$) and
colouring the edges between $V_x$ and $V_y$ by $x+y$,
$$
f(n,r,s) \;\le\; \frac{2^s}{2^d}\,n \;=\; \frac{2^s}{r+1}\,n \qquad (1 \le s \le d).
$$

**Prior art / misquotation.** The construction is verbatim the source paper's own
Proposition 3.1 (Liu–Morris–Prince 2007), and it refutes only an evident slip in the stated
range — the paper's own Theorem 1.1 already contradicts the literal $s = 1$ endpoint. The
intended question, for $\log\log r \lesssim s \le \sqrt{r}/\log r$, is untouched.

---

### 3.16. `2405.14795__00` — Sharp threshold for rainbow stackings

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2405.14795__00/
**Source:** Alon, Defant, Kravitz, *Rainbow Stackings of Random Edge-Colorings*
(arXiv:2405.14795), stated problem. Verdict: `proved`.

*Definitions.* With $N = \binom{n}{2}$ and
$p_k(r) = (r)_k/r^k = \prod_{j=0}^{k-1}(1 - j/r)$ the probability that $k$ independent uniform
colours from $[r]$ are distinct, set the first-moment parameter
$\mu_n(r) = (n!)^{m-1} p_m(r)^N$.

**Theorem.** For fixed $m \ge 2$ and integer $r = r(n)$,
$$
\mu_n(r) \to 0 \implies \Pr[\text{a rainbow stacking exists}] \to 0,
\qquad
\mu_n(r) \to \infty \implies \Pr[\cdot] \to 1 .
$$
Since $\log \mu_n(r)$ moves by $\Theta(\log^2 n)$ per unit step of $r$ near its root, this
gives the requested single threshold, at
$$
\rho_m(n) = \frac{mN}{2\log(n!)} + \frac{2m-1}{6} + o(1) \sim \frac{mn}{4\log n} .
$$

**Prior art.** The same result — same constant, essentially the same second-moment method —
was established by Liu, Ma, Xiang, Yan, arXiv:2606.31376 (30 June 2026).

---

### 3.17. `2410.13008__00` — Annular drawings with winding number one

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.13008__00/
**Source:** Seymour, *When all directed cycles have length three* (arXiv:2410.13008),
Conjecture 1.2. Verdict: `disproved`.

**Theorem.** The conjecture is false. Explicit counterexample on $\mathbb{Z}_{12}$:
$$
A(D) = \{i \to i+1,\ i \to i+2 : i \in \mathbb{Z}_{12}\} \cup \{4 \to 0,\ 10 \to 6\} .
$$
$D$ is strongly 2-connected and admits an annular drawing in which every directed cycle has
winding number one, but no crossing-free such drawing exists: its two forced facial directed
triangles have the same facial orientation, whereas boundary-parallel cycles at opposite ends
of an annulus must have opposite facial orientations in the capped sphere. Verified
exhaustively, and it survives the unsigned reading of "winding number one".

**Prior art.** Already disproved by Daniel Carter in early 2025; Seymour's own revised paper
(16 April 2025, Princeton website) relabels 1.2 "False conjecture".

---

### 3.18. `2503.23191__00` — Two-block paths in oriented graphs of large semidegree

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2503.23191__00/
**Source:** Penev, Taruni, Thomassé, Trujillo-Negrete, Tyomkyn, *Two-block paths in oriented
graphs of large semidegree* (arXiv:2503.23191), Question 5.1. Verdict: `disproved`.

*Definitions.* $\delta^0(G) = \min_v \min(d^+(v), d^-(v))$ is the minimum semidegree. An
**antidirected** path is one whose every internal vertex is a source or a sink.

**Theorem.** It is **not** true that every oriented graph $G$ with $\delta^0(G) \ge k/2$
contains every non-antidirected orientation of the $k$-edge path. Failure at $k = 4$: the
balanced blow-up of the directed triangle with parts $|A_0| = |A_1| = |A_2| = 2$ and all arcs
$A_0 \to A_1 \to A_2 \to A_0$ has $\delta^0(G) = 2 = k/2$, yet contains no copy of
$x_0 \to x_1 \leftarrow x_2 \leftarrow x_3 \to x_4$ (which is not antidirected, as
$x_3 \to x_2 \to x_1$ is directed).

**Prior art.** The identical observation was published by the source paper's own authors in
arXiv:2503.23191v2 (1 Aug 2026), whose revised Question 5.1 — excluding "bouncing" paths —
remains open.

---

### 3.19. `2505.24100__00` — Halfway induced saturation for even cycles

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.24100__00/
**Source:** Fan, Hajebi, Hajebi, Spirkl, *Halfway to induced saturation for even cycles*
(arXiv:2505.24100), Question 1.7. Verdict: `proved`.

**Theorem.** For every integer $k \ge 3$, the graph
$$
G_k = K_k \,\square\, C_{2k-1}
$$
(Cartesian product) has non-edges, contains no induced $C_{2k}$, and for every non-edge $xy$
contains an induced $x$–$y$ path on $2k$ vertices — so $G_k + xy$ contains an induced
$C_{2k}$. Taking $k = t-1$ answers Question 1.7 affirmatively for $C_{2t-2}$, and the
construction works for every even cycle of length at least six. Verified computationally for
$k = 3,\dots,8$.

**Prior art.** The affirmative answer has been in the literature since Tennenhouse (2016), as
the source authors themselves acknowledge in arXiv:2606.24763 (Theorem 1.5); it is also
subsumed by Choi, arXiv:2608.24202 (Aug 2026).

---

### 3.20. `2506.07264__01` — Positive square energy of odd unicyclic graphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2506.07264__01/
**Source:** Akbari, Kumar, Mohar, Pragada, Zhang, *Refinement of a conjecture on positive
square energy of graphs* (arXiv:2506.07264), stated conjecture. Verdict: `proved`.

*Definitions.* $s^+(G)$ and $s^-(G)$ are the sums of squares of the positive, resp. negative,
eigenvalues of the adjacency matrix. For a graph $H$ of order $h$ with $m_j(H)$ its number of
$j$-edge matchings, $\mu_H(x) = \sum_{j \ge 0} (-1)^j m_j(H) x^{h-2j}$ is the matching
polynomial.

**Theorem.** Let $G$ be a connected simple unicyclic graph of order $n$ whose unique cycle has
odd length $k$. Then
$$
\begin{cases}
s^+(G) > n > s^-(G), & k \equiv 3 \pmod 4,\\
s^+(G) < n < s^-(G), & k \equiv 1 \pmod 4 .
\end{cases}
$$

**Prior art.** Already proved, by essentially the same matching-polynomial / Coulson-integral
argument, in Ning & Zeng, arXiv:2605.24668 (23 May 2026).

---

### 3.21. `2507.04254__00` — Modular edge colourings of $0_k$-graphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2507.04254__00/
**Source:** Berthe, Bonamy, Botler, Carenini, Colucci, Dumas, Ghasemi, Viana Neto, *On Modular
Edge Colourings of Graphs* (arXiv:2507.04254), Conjecture 13. Verdict: `disproved`.

*Definitions.* A **$0_k$-graph** is a graph all of whose nonzero degrees are divisible by $k$.
A **modular $k$-edge-colouring** is an edge-colouring in which, for every colour $c$, every
nonzero degree in the $c$-coloured subgraph is $\equiv 1 \pmod k$; $\chi'_k(G)$ is the least
number of colours.

**Theorem.** It is **not** true that $\chi'_k(G) \le k + o(k)$ for every $0_k$-graph $G$. For
every even $k$ there is a finite simple **bipartite** $0_k$-graph $G_k$ with
$$
\chi'_k(G_k) \;\ge\; \left\lceil \tfrac{7k}{6} \right\rceil .
$$
The engine is a palette-counting lemma: for a bipartite $0_k$-graph with parts $X, Y$, no
isolated vertices, $n = |X|+|Y|$ and $\rho = \operatorname{dist}(|X|-|Y|,\, k\mathbb{Z})$, any
modular $k$-edge-colouring with $m < 2k$ colours satisfies $n(m-k) \ge m\rho$.

**Prior art.** Already refuted in August 2026: arXiv:2608.10687 (Guo–Wu, stronger bound
$(4-2\sqrt{2}+o(1))k$) and arXiv:2608.02239 (Liu–Xu–Yang, refuting the underlying BCK
conjecture with bound $\sim 3k/2$).

---

### 3.22. `2511.02892__03` — Strong 6-edge-colouring of diamond-free claw-free cubic graphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__03/
**Source:** Barát, Dvořák, Haxell, Kardoš, Lužar, Onderko, Rajník, Soták, Ulyanov, *Open
problems of the 33rd Workshop on Cycles and Colourings* (arXiv:2511.02892), Question.
Verdict: `disproved`. **Misquoted target.**

*Definitions.* A **strong edge-colouring** has every colour class an induced matching;
equivalently it is a proper vertex-colouring of $L(H)^2$.

**Theorem.** Not every diamond-free claw-free cubic graph is strongly $6$-edge-colourable. The
triangular prism $P$ (triangles $a_1a_2a_3$, $b_1b_2b_3$ plus the matching $a_ib_i$) is cubic,
claw-free and diamond-free, and any two of its nine edges conflict, so $L(P)^2 \cong K_9$ and
$$
\chi'_s(P) = 9 .
$$

**Prior art / misquotation.** The prism is the exception already flagged in the problem's own
preamble (Lv–Li–Zhang 2022), so this refutes only a strawman literal reading. The intended
question was later genuinely disproved by an 18-vertex non-prism example, arXiv:2607.23462
(July 2026).

---

### 3.23. `2512.17232__00` — Induced $A$-path packing versus neighbourhood covers

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2512.17232__00/
**Source:** Hickingbotham, Joret, *An Induced $A$-Path Theorem* (arXiv:2512.17232),
Conjecture 6. Verdict: `disproved`.

**Theorem.** It is **not** true that for every $k \in \mathbb{N}$, every graph $G$ and all
$X,Y \subseteq V(G)$ either contains $k$ pairwise anti-complete $(X,Y)$-paths or admits
$Z \subseteq V(G)$ with $|Z| \le k-1$ such that $G - N_G[Z]$ has no $(X,Y)$-path. A 16-vertex
counterexample at $k = 2$ — on $\{x_i,a_i,b_i,y_i : i \in \mathbb{Z}_4\}$ with
$X = \{x_i\}$, $Y = \{y_i\}$ and four induced "corridors" — has maximum anti-complete packing
$1$ but minimum closed-neighbourhood separator $2$. Taking $r = k-1$ disjoint copies shows any
valid replacement bound must allow at least $2(k-1)$ centres.

**Prior art.** Already in the literature: Albrechtsen, Huynh, Jacobs, Knappe, Wollan, SIAM J.
Discrete Math. 2024, Lemma 5 with $d = 2$. The source authors themselves revised the
conjecture to $|Z| \le k$ in arXiv v2 (2026-09-01), explicitly citing that construction.

---

### 3.24. `2512.17342__00` — Connectivity of the 5-flow reconfiguration graph

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2512.17342__00/
**Source:** Esperet, Hendrey, Lagoutte, Marseloo, Norin, Steiner, *Nowhere-zero flow
reconfiguration* (arXiv:2512.17342), Problem 1.1. Verdict: `disproved`.

*Definitions.* Fix a reference orientation of $G$. A nowhere-zero integer $5$-flow is an
integer circulation $f : E(G) \to \{-4,-3,-2,-1,1,2,3,4\}$. Two flows are **adjacent** when
they agree outside the edge set of one simple cycle; $\mathcal{F}(G,5)$ is the resulting
reconfiguration graph.

**Theorem.** $\mathcal{F}(G,5)$ need not be connected for $2$-edge-connected $G$: there is a
simple cubic bridgeless **planar** graph $G$ on $38$ vertices with two nowhere-zero integer
$5$-flows in different components of $\mathcal{F}(G,5)$. Route: produce an isolated
nowhere-zero $\mathbb{Z}_5$-flow, then lift two distinct modular flows to integer $5$-flows.
Verified by exhaustive enumeration of all 235,856 simple cycles, twice, independently.

**Prior art.** Problem 1.1 was already answered negatively by Theorem 3.4 of the source paper
itself (since v2, April 2026), as the prompt's own abstract announces.

---

### 3.25. `2602.16333__00` — Perimeter gap of vertex-transitive digraphs

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2602.16333__00/
**Source:** Bucić, Hendrey, Mohar, Steiner, Yepremyan, *Long cycles in vertex transitive
digraphs* (arXiv:2602.16333), stated conjecture. Verdict: `proved`.

*Definitions.* $\operatorname{circ}(D)$ is the length of a longest directed cycle, and the
**perimeter gap** is $\operatorname{gap}(D) = |V(D)| - \operatorname{circ}(D)$.

**Theorem.** For every integer $m \ge 3$ there is a strongly connected vertex-transitive
oriented digraph $\Gamma_m$ with
$$
|V(\Gamma_m)| = 12m
\qquad\text{and}\qquad
\operatorname{circ}(\Gamma_m) \le 11m ,
$$
so $\operatorname{gap}(\Gamma_m) \ge m = \tfrac{1}{12}|V(\Gamma_m)|$ and the conjecture holds
with $\varepsilon = 1/12$.

**Prior art.** Already resolved with the identical bound $n/12$ by Li and Methuku,
arXiv:2607.05807 (posted 2026-07-07), eight weeks before this attack ran on 2026-08-31.

---

### 3.26. `2604.09449__00` — Colour-balanced perfect matchings in $K_{n,n}$

**Catalog page:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/2604.09449__00/
**Source:** Hogan, Scott, Tsarev, *Colour-balanced subgraphs* (arXiv:2604.09449),
Conjecture 6.1 (v1 form). Verdict: `disproved`. **Misquoted target.**

*Definitions.* The catalog statement does not define $f_h$. Under the centred, unnormalised
$\ell_1$ discrepancy indicated by the catalog prose,
$$
f_h(M) = \Big\| \sum_{e \in M} h(e) \;-\; \frac{1}{n}\sum_{e \in E(K_{n,n})} h(e) \Big\|_1 .
$$

**Theorem.** Under that reading the conjecture fails with a **linear** lower bound. For even
$k$ and $n = k$, set $h(x_iy_j) = s_j e_i$ with signs $s_j = \pm 1$ balanced (so
$\|h(e)\|_1 = 1$ for every edge and the total edge-label is $0$). Every perfect matching
$M_\pi$ then has $\sum_{e \in M_\pi} h(e) \in \{\pm 1\}^k$, whence
$$
f_h(M_\pi) = \frac{k}{2} \qquad \text{for every perfect matching } M_\pi ,
$$
against the conjectured $O(\sqrt{k})$.

**Prior art / misquotation.** The refuted statement is the erroneous v1 form of Conjecture 6.1,
which the authors had already corrected in arXiv:2604.09449v2 (2026-07-11); the currently-open
colour-balanced conjecture is untouched. Note also that the conclusion is sensitive to the
undefined $f_h$: under the Euclidean norm the same construction gives only
$\|\sum_{e \in M}h(e)\|_2 = \sqrt{k}$, consistent with the conjecture.
