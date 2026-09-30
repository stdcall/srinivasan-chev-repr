#import "numbering.typ": place-key, restart-counters
#import "statements.typ": numbered-display
#import "main-defs.typ": reference-rules

#let fit-wide-equations(body) = layout(size => {
  let natural = measure(body)
  if natural.width > size.width {
    let factor = size.width / natural.width * 100%
    scale(x: factor, y: factor, reflow: true, box(width: natural.width, body))
  } else { body }
})

#let book-style(body) = {
  set page(
    width: 176mm,
    height: 250mm,
    margin: (x: 21mm, top: 22mm, bottom: 22mm),
    numbering: "1",
    footer: context align(center, counter(page).display()),
  )
  set text(
    font: "Libertinus Serif",
    size: 12pt,
    lang: "en",
    region: "gb",
    fill: rgb("202020"),
  )
  set par(
    justify: true,
    leading: 0.65em,
    spacing: 0.8em,
    first-line-indent: 1.2em,
  )
  show link: set text(fill: rgb("202020"))
  set heading(numbering: (..n) => {
    let n = n.pos()
    if n.len() == 1 { "Chapter " + numbering("I", n.first()) + "." } else {
      "§ " + str(n.last()) + "."
    }
  })
  show heading: it => {
    if it.level == 1 { pagebreak(weak: true) }
    if it.numbering != none {
      restart-counters(it.level)
      context [#metadata((
          kind: "numbered",
          family: "heading",
          level: it.level,
          number: place-key(here()).slice(0, it.level),
        ))
        <numbered>]
    } else {
      [#metadata((
        kind: "unnumbered",
        family: "heading",
        level: it.level,
        number: none,
      ))<numbered>]
    }
    set par(justify: false, first-line-indent: 0pt)
    block(
      above: if it.level == 1 { 12mm } else { 5mm },
      below: if it.level == 1 { 9mm } else { 3mm },
      sticky: true,
      text(size: if it.level == 1 { 18pt } else { 13pt }, weight: "semibold")[
        #if it.numbering != none [
          #counter(heading).display(it.numbering)
        ]#it.body],
    )
  }
  show outline: set par(first-line-indent: 0pt)
  show outline.entry: set block(breakable: false)
  set math.equation(numbering: none, supplement: none)
  show math.equation: set text(font: "STIX Two Math")
  show math.equation.where(block: true): it => {
    if (
      it.has("label")
        and str(it.label).starts-with("eq:")
        and it.numbering == none
    ) { fit-wide-equations(numbered-display(it)) } else {
      fit-wide-equations(it)
    }
  }
  set table(stroke: 0.5pt, inset: (x: 0.45em, y: 0.5em))
  set table.cell(breakable: false)
  show table: set par(first-line-indent: 0pt, justify: false)
  show: reference-rules
  body
}
