#import "@preview/fletcher:0.5.8": diagram, edge

#let scheme-triangle() = diagram(
  cell-size: (18mm, 12mm),
  node-inset: 1mm,
  $X & & Y \ & S$,
  edge((0, 0), (2, 0), "->"),
  edge((0, 0), (1, 1), "->"),
  edge((2, 0), (1, 1), "->"),
)
#let fibre-product() = diagram(
  cell-size: (18mm, 12mm),
  node-inset: 1mm,
  $& X times_S Y \ X & & Y \ & S$,
  edge((1, 0), (0, 1), $p_1$, "->"),
  edge((1, 0), (2, 1), $p_2$, "->"),
  edge((0, 1), (1, 2), "->"),
  edge((2, 1), (1, 2), "->"),
)
#let site-triangle() = diagram(
  cell-size: (18mm, 12mm),
  node-inset: 1mm,
  $U & & V \ & X$,
  edge((0, 0), (2, 0), "->"),
  edge((0, 0), (1, 1), "->"),
  edge((2, 0), (1, 1), "->"),
)
#let neighbourhood-triangle() = diagram(
  cell-size: (22mm, 13mm),
  node-inset: 1mm,
  $"Spec" tilde(K) & & U \ & X$,
  edge((0, 0), (2, 0), "->"),
  edge((0, 0), (1, 1), $overline(x)$, "->"),
  edge((2, 0), (1, 1), "->"),
)
#let sheaf-equalizer() = diagram(
  cell-size: (40mm, 12mm),
  node-inset: 2mm,
  $Phi(U) & product_alpha Phi(U_alpha) & product_(alpha,beta) Phi(
    U_alpha
    times_U U_beta
  )$,
  edge((0, 0), (1, 0), "->"),
  edge((1, 0), (2, 0), "->", bend: 8deg),
  edge((1, 0), (2, 0), "->", bend: -8deg),
)
#let set-equalizer() = diagram(
  cell-size: (18mm, 12mm),
  node-inset: 1mm,
  $A & B & C$,
  edge((0, 0), (1, 0), $f$, "->"),
  edge((1, 0), (2, 0), $g$, "->", bend: 15deg),
  edge((1, 0), (2, 0), $h$, "->", bend: -15deg),
)
#let compactification-triangle() = diagram(
  cell-size: (22mm, 14mm),
  node-inset: 1mm,
  $X & & Y \ & tilde(X)$,
  edge((0, 0), (2, 0), $f$, "->"),
  edge((0, 0), (1, 1), $j$, "->"),
  edge((1, 1), (2, 0), $tilde(f)$, "->"),
)
#let adic-transition() = diagram(
  cell-size: (32mm, 18mm),
  node-inset: 2mm,
  $Phi_n & Phi_n ⊗_(ZZ/(ell^(n+1) ZZ)) ZZ/(ell^n ZZ) \ & Phi_(n-1)$,
  edge((0, 0), (1, 0), "->"),
  edge((0, 0), (1, 1), "->"),
  edge((1, 0), (1, 1), $tilde(arrow.r)$, "->"),
)
#let base-change-square() = diagram(
  cell-size: (25mm, 17mm),
  node-inset: 1mm,
  $X & X' \ S & S'$,
  edge((1, 0), (0, 0), $g'$, "->"),
  edge((0, 0), (0, 1), $f$, "->"),
  edge((1, 0), (1, 1), $f'$, "->"),
  edge((1, 1), (0, 1), $g$, "->"),
)
#let automorphism-square() = diagram(
  cell-size: (25mm, 17mm),
  node-inset: 1mm,
  $X & X \ Y & Y$,
  edge((0, 0), (1, 0), $g$, "->"),
  edge((0, 0), (0, 1), $f$, "->"),
  edge((1, 0), (1, 1), $f$, "->"),
  edge((0, 1), (1, 1), $g'$, "->"),
)
