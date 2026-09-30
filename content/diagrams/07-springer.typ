#import "@preview/fletcher:0.5.8": diagram, edge
#import "@preview/cetz:0.5.2": canvas, draw

// Schematic incidence patterns of the projective components.
#let springer-projective-lines(count) = align(center, canvas({
  import draw: *
  let components = if count == 2 {
    (((-1.5, -0.8), (1.5, 0.8)), ((-1.5, 0.8), (1.5, -0.8)))
  } else {
    (
      ((-1.5, 0.6), (1.5, 0.6)),
      ((-1.5, -0.6), (1.5, -0.6)),
      ((-0.8, -1), (0.8, 1)),
    )
  }
  for (i, endpoints) in components.enumerate() {
    line(..endpoints)
    if count == 3 and i < 2 {
      content(endpoints.last(), $ell_(#(i + 1))$, anchor: "west")
    }
  }
}))

#let springer-support-square() = diagram(
  cell-size: (40mm, 17mm),
  node-inset: 1mm,
  $Z & cal(Y) \ cal(B)_A times frak(t)'_0 & cal(B) times frak(t)'_0$,
  edge((0, 0), (1, 0), $i$, "->"),
  edge((0, 0), (0, 1), $f | Z$, "->"),
  edge((1, 0), (1, 1), $f$, "->"),
  edge((0, 1), (1, 1), $i$, "->"),
)
#let springer-torus-borel-square() = diagram(
  cell-size: (36mm, 18mm),
  node-inset: 1mm,
  $Z & rho^(-1)(cal(B)_A) times frak(t)'_0 & G / T \
  & cal(B)_A times frak(t)'_0 & cal(B)$,
  edge((0, 0), (1, 0), [projection], "->"),
  edge((1, 0), (2, 0), "->"),
  edge((1, 0), (1, 1), $rho$, "->"),
  edge((2, 0), (2, 1), $rho$, "->"),
  edge((1, 1), (2, 1), "->"),
)
#let springer-constant-sheaf-square() = diagram(
  cell-size: (36mm, 18mm),
  node-inset: 1mm,
  $cal(B) times frak(t)'_0 & cal(B) \ frak(t)'_0 & op("Spec") K$,
  edge((0, 0), (1, 0), $pi_1$, "->"),
  edge((0, 0), (0, 1), $sigma$, "->"),
  edge((1, 0), (1, 1), "->"),
  edge((0, 1), (1, 1), "->"),
)
#let springer-frobenius-diagram() = diagram(
  cell-size: (42mm, 18mm),
  node-inset: 1mm,
  $cal(Y) & cal(Y) \
  cal(B) times frak(t)'_0 & cal(B) times frak(t)'_0 \
  frak(t)'_0 & frak(t)'_0$,
  edge((0, 0), (1, 0), $F$, "->"),
  edge((0, 1), (1, 1), $F$, "->"),
  edge((0, 2), (1, 2), $F$, "->"),
  edge((0, 0), (0, 1), $f_B$, "->"),
  edge((1, 0), (1, 1), $f_(F B)$, "->"),
  edge((0, 1), (0, 2), $sigma$, "->"),
  edge((1, 1), (1, 2), $sigma$, "->"),
  edge((0, 0), (0, 2), $pi$, "->", bend: -40deg, label-side: right),
  edge((1, 0), (1, 2), $pi$, "->", bend: 40deg, label-side: left),
)
#let springer-tate-twist-diagram() = diagram(
  cell-size: (40mm, 20mm),
  node-inset: 1mm,
  $(R^i pi_! overline(QQ)_ell)_psi & H_c^(i - 2d)(cal(B)_A)(-d) &
  H_c^(i - 2d)(cal(B)_A) \
  (R^i pi_! F^* overline(QQ)_ell)_psi & H_c^(i - 2d)(cal(B)_A)(-d) &
  H_c^(i - 2d)(cal(B)_A)$,
  edge((0, 0), (1, 0), $alpha_(F B)^i$, "->"),
  edge((1, 0), (2, 0), $tilde(arrow.r)$, "->"),
  edge((0, 1), (1, 1), $alpha_B^i$, "->"),
  edge((1, 1), (2, 1), $tilde(arrow.r)$, "->"),
  edge((0, 0), (0, 1), $F^*$, "->"),
  edge((2, 0), (2, 1), $q^d F$, "->"),
)
