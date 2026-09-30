#import "@preview/fletcher:0.5.8": diagram, edge

#let torus-norm-diagram() = diagram(
  cell-size: (24mm, 16mm),
  node-inset: 1mm,
  edge-stroke: 0.5pt,
  $Y(T) & Y(T) & T^(F^n) \ Y(T) & Y(T) & T^F$,
  edge((0, 0), "r", $F^n - 1$, "->"),
  edge((1, 0), "r", "->"),
  edge((0, 0), "d", $N$, "->"),
  edge((1, 0), "d", "="),
  edge((2, 0), "d", $N$, "->"),
  edge((0, 1), "r", $F - 1$, "->"),
  edge((1, 1), "r", "->"),
)
