// The publisher's cover, set with vector shapes and a vector emblem.
#let cover() = page(
  width: 176mm,
  height: 267mm,
  margin: 0pt,
  header: none,
  footer: none,
  numbering: none,
  fill: rgb("ffbd00"),
)[
  #let navy = rgb("162a53")
  #let yellow = rgb("ffbd00")
  #set text(font: "Open Sans", weight: "bold", lang: "en")
  #place(top + left, dx: 23.5mm, rect(
    width: 152.5mm,
    height: 109.3mm,
    fill: navy,
    stroke: none,
  ))
  #place(top + left, dy: 109.3mm, rect(
    width: 23.5mm,
    height: 157.7mm,
    fill: navy,
    stroke: none,
  ))
  #place(top + left, dx: 23.5mm, dy: 109.3mm, rect(
    width: 152.5mm,
    height: 10.7mm,
    fill: rgb("ffdfa0"),
    stroke: none,
  ))
  #place(top + left, dy: 109.3mm, rect(
    width: 23.5mm,
    height: 10.7mm,
    fill: rgb("646584"),
    stroke: none,
  ))
  #place(top + left, dx: 23.5mm, dy: 97.8mm, rect(
    width: 11mm,
    height: 11.5mm,
    fill: rgb("646584"),
    stroke: none,
  ))
  #place(top + left, dx: 34mm, dy: 10.5mm, text(
    font: "Libertinus Serif",
    size: 29.5pt,
    weight: "bold",
    fill: white,
  )[
    Bhama Srinivasan
  ])
  #place(top + left, dx: 34mm, dy: 72mm)[
    #set par(leading: 0.4em)
    #text(size: 33.5pt, fill: yellow)[
      Representations of\ Finite Chevalley Groups
    ]
  ]
  #place(top + left, dx: 15.2mm, dy: 98mm, rotate(
    -90deg,
    origin: top + left,
    reflow: false,
    text(size: 19pt, fill: navy)[Lecture Notes in Mathematics],
  ))
  #place(top + left, dx: 5.5mm, dy: 112mm, text(
    font: "Libertinus Serif",
    weight: "regular",
    size: 24pt,
    fill: white,
  )[764])
  #place(top + left, dx: 34mm, dy: 126mm, text(size: 18pt, fill: navy)[A
    Survey])
  #place(top + left, dx: 33mm, dy: 238mm, image(
    "../assets/springer-mark.svg",
    width: 10.8mm,
    alt: "Springer publisher emblem",
  ))
  #place(top + left, dx: 45.5mm, dy: 240mm, text(
    font: "Libertinus Serif",
    size: 27pt,
    weight: "regular",
    fill: navy,
  )[Springer])
]
