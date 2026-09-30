#import "main-defs.typ": *
#import "statements.typ": *

#chapter[Principal Series Representations] <ch:principal-series>

#source(31)
We will now use the subgroup $T_0^F subset B_0^F subset G^F$ to construct
complex representations of $G^F$. In this chapter and in
Chapter~@ch:harish-chandra we will denote, for any finite group $H$, the group
of linear characters $Hom(H, CC^*)$ by $hat(H)$. Later on we will consider
representations of $G^F$ over $overline(QQ)_ell$, where $ell$ is a prime
different from $p$.

Let $lambda in hat(T)_0^F$, and let $tilde(lambda) in hat(B)_0^F$ be the
pullback of $lambda$ to $B_0^F = T_0^F U_0^F$. We induce $tilde(lambda)$ to
$G^F$ and obtain a representation of $G^F$ denoted by
$Ind_(B_0^F)^(G^F)(tilde(lambda))$. The irreducible constituents of the
$Ind_(B_0^F)^(G^F)(tilde(lambda))$, where $lambda$ varies over $hat(T)_0^F$, are
called the principal series representations (or characters) of $G^F$.
#term-entry("Principal series")

We now recall Mackey's Theorem (see eg.~@bib:Feit1967, p.~51, or
@bib:Serre1977a, p.~59).

#theorem(title: [Mackey])[
  Suppose $K_1, K_2$ are subgroups of a finite group $H$, and suppose
  $H = union_x K_1 x K_2$, a union of disjoint double cosets. If $phi_1, phi_2$
  are representations of $K_1, K_2$ respectively then
  $(Ind_(K_1)^(H)(phi_1), Ind_(K_2)^(H)(phi_2))_H =
  sum_x (phi_1^x, phi_2)_(K_1^x ∩ K_2)$. In particular if $K_1 = K_2$ and
  $phi_1$ is irreducible then $Ind_(K_1)^(H)(phi_1)$ is irreducible if and only
  if the representations $phi_1^x$ and $phi_1$ of $K_1^x ∩ K_1$ are disjoint for
  every double-coset representative $x in.not K_1$.
] <th:mackey>

#source(32)
#definition[
  $lambda in hat(T)_0^F$ is _regular_ if it is not fixed by any non-trivial
  element of $W(T_0)^F$.
  #term-entry("Regular character")
]

#proposition[
  #enum(
    numbering: "(i)",
    [$Ind_(B_0^F)^(G^F)(tilde(lambda))$ is irreducible if and only if $lambda$
      is regular.],
    [$(Ind_(B_0^F)^(G^F)(tilde(lambda)),
        Ind_(B_0^F)^(G^F)(tilde(mu)))_(G^F) =
      |{w in W(T_0)^F | lambda^w = mu}|$. In particular,
      $(Ind_(B_0^F)^(G^F)(tilde(lambda)),
        Ind_(B_0^F)^(G^F)(tilde(mu))) = 0$ if $lambda, mu$ are not
      $W(T_0)^F$-conjugate.],
  )
] <prop:principal-series-inner-product>

#proof[
  This follows from Theorem~@th:mackey, using the Bruhat decomposition
  $G^F = union_(w in W(T_0)^F) B_0^F dot(w) B_0^F$
  (see Proposition~@prop:finite-bruhat).
]

#example[
  $G = GL_2$, $G^F = GL(2, q)$. Here we have
  $T_0^F = {mat(gamma^a, 0; 0, gamma^b)}$ where $gamma$ is a generator of
  $bb(F)_q^*$. So the characters of $T_0^F$ are given by
  $theta_(m,n): mat(gamma^a, 0; 0, gamma^b) -> gamma^(m a) dot gamma^(n b)$,
  where we also denote a complex primitive $(q - 1)$st root of unity by $gamma$.
  We have $B_0^F = {mat(gamma^a, *; 0, gamma^b)}$ and we give below the values
  of $Ind_(B_0^F)^(G^F)(tilde(theta)_(m,n)) = phi_(m,n)$, when $phi_(m,n)$ is
  irreducible, at representatives of the conjugacy classes of $G^F$. Here the
  element in the last column is conjugate to $mat(eta^a, 0; 0, eta^(a q))$ over
  $bb(F)_(q^2)$, where $eta$ is a generator of $bb(F)_(q^2)^*$. In the table
  $eta$ also denotes #source(33) a complex primitive $(q^2 - 1)$st root of
  unity. The second row denotes a family of irreducible characters of $G^F$
  known as the _discrete series_. This family of characters cannot be
  constructed in a straightforward way like the principal series, and
  corresponds in some sense to the other "non-split" torus of $G^F$. A precise
  definition of the discrete series will be given in the next chapter.

  #table(
    columns: (1.3fr, 0.6fr, 1fr, 1fr, 1.4fr, 1.4fr),
    align: center + horizon,
    table.header(
      [Class representative],
      $mat(1, 0; 0, 1)$,
      $mat(gamma^a, 0; 0, gamma^a)$,
      $mat(gamma^a, 1; 0, gamma^a)$,
      $mat(gamma^a, 0; 0, gamma^b)$,
      $mat(eta^a, 0; 0, eta^(a q))$,
    ),
    [], [], $(gamma^a != 1)$, [], $(gamma^a != gamma^b)$, $(a != 0 (q + 1))$,
    [Number of classes],
    $1$,
    $q - 2$,
    $q - 1$,
    $1 / 2 (q - 1)(q - 2)$,
    $1 / 2 q(q - 1)$,

    [$phi_(m,n)$ ($m, n = 1, 2, dots, q - 1$, $m != n$)],
    $q + 1$,
    $(q + 1) gamma^((m + n) a)$,
    $gamma^((m + n) a)$,
    $gamma^(m a + n b) + gamma^(n a + m b)$,
    $0$,

    [$psi_m$ ($m = 1, 2, dots, q^2 - 2$, $m$ not a multiple of $q + 1$)],
    $q - 1$,
    $(q - 1) gamma^(m a)$,
    $-gamma^(m a)$,
    $0$,
    $-(eta^(m a) + eta^(m a q))$,
  )
]

#heading(level: 2, numbering: none)[
  Some remarks on inducing from Borel subgroups
] <sec:inducing-borel-remarks>

+ The construction of inducing from a Borel subgroup (or more #source(34)
  generally from a parabolic subgroup) occurs also in the case of real
  semisimple Lie groups (from where the term "principal series" arises) and in
  the case of semisimple $p$-adic groups. (See e.g.~@bib:Lipsman1974, pp.~16,
  123.)
+ Consider the reductive algebraic group $G$ over $K = overline(bb(F)_q)$. Let
  $lambda in X(T_0)$. Let $V$ be the space of all morphisms $f: G -> K$ such
  that $f(g b) = tilde(lambda)(b^(-1)) f(g)$ ($g in G$, $b in B_0$), where
  $lambda$ is extended to a character $tilde(lambda)$ of $B_0$ (into $K^*$) as
  usual. $G$ acts on $V$ by left translations and this gives the representation
  $Ind_(B_0)^(G)(tilde(lambda))$. These representations play a big role in the
  "modular" representation theory of $G$ (ie., rational representations over
  $K$). All irreducible modular representations of $G$ are realized inside
  spaces of the form $V$. (See @bib:Steinberg1974, p.~85 or @bib:Steinberg1968a,
  p.~210.)
+ Let $frak(g)$ be a complex semisimple Lie algebra, $frak(h)$ a Cartan
  subalgebra, $frak(b)$ a Borel subalgebra with $frak(b) = frak(h) ⊕ frak(n)$
  where $frak(n)$ is nilpotent. Let $upright("U")(frak(g))$ be the universal
  enveloping algebra of $frak(g)$. If $lambda$ is a linear functional on
  $frak(h)$, we can lift it to a linear functional on $frak(b)$ by setting
  $lambda(h + n) = lambda(h)$, if $h in frak(h)$ and $n in frak(n)$. If $L$ is a
  $frak(b)$-module for $lambda$ the induced $frak(g)$-module is defined as
  $upright("U")(frak(g)) ⊗_(upright("U")(frak(b))) L$ (regarding
  $upright("U")(frak(g))$ as a right $upright("U")(frak(b))$-module). Now if we
  take $L$ to be a $frak(b)$-module for $lambda - delta$ (where $delta$ is half
  the sum of the positive roots) the induced module is called the Verma module
  of $frak(g)$ associated with $lambda$ and denoted by $M(lambda)$. These
  objects have been studied a great deal in recent years. (See @bib:Dixmier1977,
  Chapter 7.)
