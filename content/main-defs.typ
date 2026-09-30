#import "numbering.typ": numbered-record, record-number
#import "index-helpers.typ": index-entries, term-entry

#let source(n, printed: none) = context metadata((
  kind: "source",
  file-page: n,
  printed-page: if printed == none { str(n - 10) } else { printed },
  position: here().position(),
))
#let chapter(body) = heading(level: 1, body)
#let number-text(body) = text(weight: "semibold", style: "normal", body)
#let reference-rules(body) = {
  // Keep a reference and its position record on the same line.
  show ref: it => box(context {
    let record = if it.element != none { numbered-record(it.target) }
    let number = if record != none { record-number(record) }
    let resolved = number != none
    let shown = if not resolved { "?" } else if (
      str(it.target).starts-with("ch:")
    ) { numbering("I", number.first()) } else if (
      str(it.target).starts-with("claim:")
    ) { "(" + number.map(str).join(".") + ")" } else {
      number.map(str).join(".")
    }
    let caption = it.supplement not in (auto, none, [])
    let destination = if resolved {
      if it.element.func() == math.equation { it.element.location() } else {
        record.location()
      }
    } else if caption and it.element != none {
      if record != none { record.location() } else { it.element.location() }
    }
    let linked = destination != none
    metadata((
      kind: "cross-reference",
      target: str(it.target),
      resolved: linked,
      printed: shown,
      position: here().position(),
      target-position: if linked { destination.position() },
    ))
    let content = if caption { it.supplement } else if (
      str(it.target).starts-with("eq:")
    ) { [(#number-text(shown))] } else { number-text(shown) }
    if linked { link(destination, content) } else { content }
  })
  body
}
#let editorial-notes = sys.inputs.at("editorial-notes", default: "on") != "off"
#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = if editorial-notes {
  editorial-note-counter.step()
  context {
    footnote(numbering: _ => (
      "*" + str(editorial-note-counter.get().first()) + ")"
    ))[
      #body~— _Ed._
    ]
    counter(footnote).update(n => n - 1)
  }
}
#let editorial-bibliography = [
  #show bibliography: none
  #bibliography("../editorial.bib", style: "chicago-notes")
]
#let GL = math.upright("GL")
#let SL = math.upright("SL")
#let PGL = math.upright("PGL")
#let PSL = math.upright("PSL")
#let SO = math.upright("SO")
#let SU = math.upright("SU")
#let Sp = math.upright("Sp")
#let Hom = math.op("Hom")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let Ind = math.op("Ind")
#let Res = math.op("Res")
#let diag = math.op("diag")
#let tr = math.op("tr")
#let rk = math.op("rk")
// Left superscripts denote conjugation of groups and their characters.
#let conj(by, object) = math.attach(object, tl: by)
