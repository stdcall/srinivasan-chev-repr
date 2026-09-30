#import "@preview/fletcher:0.5.8": diagram, edge, node

#let connected-action-triangle() = diagram(
  cell-size: (22mm, 14mm),
  node-inset: 1mm,
  edge-stroke: 0.5pt,
  node((0, 0), $H times Y$),
  node((1, 0), $H times Y$),
  node((0.5, 1), $H$),
  edge((0, 0), (1, 0), $f$, "->"),
  edge((0, 0), (0.5, 1), $pi$, "->", label-side: right),
  edge((1, 0), (0.5, 1), $pi$, "->", label-side: left),
)
#let connected-action-base-change() = diagram(
  cell-size: (25mm, 17mm),
  node-inset: 1mm,
  edge-stroke: 0.5pt,
  $H times Y & Y \ H & op("Spec") K$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", $pi$, "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)
