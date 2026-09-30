#import "numbering.typ": family-counter, object-number, record

#let counted(family, format, series: none) = {
  let counting = if series == none { family-counter(family) } else {
    counter("numbered:" + series)
  }
  counting.step()
  context {
    let n = if series == none { object-number(family, here()) } else {
      counting.at(here())
    }
    if series == none { record(family) } else [#metadata((
      kind: "independent",
      family: family,
      number: n,
    ))<numbered>]
    format(n)
  }
}
#let statement(
  kind,
  family,
  body,
  title: none,
  numbered: true,
  italic: false,
  series: none,
) = block(above: 0.9em, below: 0.9em, breakable: true)[
  #set text(style: if italic { "italic" } else { "normal" })
  #let head = text(style: "normal")[
    #if not numbered [#metadata((
      kind: "unnumbered",
      family: family,
      number: none,
    ))<numbered>]
    #strong[#kind#if numbered [
        #counted(family, n => n.map(str).join("."), series: series)]#if (
        title != none
      ) [
        (#title)].]
  ]
  #let children = body.fields().at("children", default: (body,))
  #let display = children.position(c => c.func() == math.equation and c.block)
  #let paragraph = children.position(c => c.func() == parbreak)
  #if display != none and (paragraph == none or display < paragraph) {
    // A statement's opening words introduce its first display.
    block(above: 0pt, below: 0.8em, sticky: true)[
      #head #children.slice(0, display).join()
    ]
    children.slice(display).join()
  } else [#head #body]
]
#let theorem(body, title: none, numbered: true) = statement(
  "Theorem",
  "th",
  body,
  title: title,
  numbered: numbered,
  italic: false,
)
#let proposition(body, title: none, numbered: true) = statement(
  "Proposition",
  "prop",
  body,
  title: title,
  numbered: numbered,
  italic: false,
)
#let lemma(body, title: none, numbered: true) = statement(
  "Lemma",
  "lem",
  body,
  title: title,
  numbered: numbered,
  italic: false,
)
#let corollary(body, title: none, numbered: true) = statement(
  "Corollary",
  "cor",
  body,
  title: title,
  numbered: numbered,
  italic: false,
)
#let definition(body, title: none, numbered: false) = statement(
  "Definition",
  "def",
  body,
  title: title,
  numbered: numbered,
)
#let example(body, title: none, numbered: false, series: none) = statement(
  "Example",
  "exm",
  body,
  title: title,
  numbered: numbered,
  series: series,
)
#let remark(body, title: none, numbered: false) = statement(
  "Remark",
  "rem",
  body,
  title: title,
  numbered: numbered,
)
#let proof(body, head: emph[Proof.], qed: true) = {
  let children = body.fields().at("children", default: (body,))
  let visible = children
    .enumerate()
    .filter(pair => repr(pair.last().func()) not in ("space", "parbreak"))
  let last = visible.last(default: none)
  let previous = visible.at(-2, default: none)
  let punctuation = if last != none and last.last().func() == text {
    last.last().text
  }
  let display = if last != none and last.last().func() == math.equation {
    last
  } else if punctuation in (".", ",", ";") { previous }
  let end-display = (
    display != none
      and display.last().func() == math.equation
      and display.last().block
      and not display.last().has("label")
  )
  block(above: 0.6em, below: 0.9em, breakable: true)[
    #if head != none [#head ]#if end-display {
      children.slice(0, display.first()).join()
      grid(
        columns: (1fr, auto, 1fr),
        align: horizon,
        [],
        math.equation(
          block: true,
          display.last().body
            + if punctuation != none { text(punctuation) } else { [] },
        ),
        align(right, if qed { box[$square.stroked$] }),
      )
    } else [#body#if qed [~#box[$square.stroked$]]]
  ]
}
#let formula-item(body) = block(above: 0.7em, below: 0.7em)[
  #counted("eq", n => [(#n.map(str).join("."))]) #body
]
// The two induction claims in Chapter VIII have their own local series.
#let proof-claim(body) = block(above: 0.7em, below: 0.7em)[
  #counted("claim", n => [(#n.first())], series: "classification-claim") #body
]
#let numbered-display(it) = {
  family-counter("eq").step()
  context {
    record("eq")
    math.equation(
      block: true,
      number-align: end + horizon,
      numbering: _ => text(font: "Libertinus Serif", style: "normal")[(#(
          object-number("eq", here()).map(str).join(".")
        ))],
      it.body,
    )
  }
}
#let bib-item(body) = block(above: 0.5em, below: 0.5em)[
  #counted("bib", n => [#n.first().]) #body
]
