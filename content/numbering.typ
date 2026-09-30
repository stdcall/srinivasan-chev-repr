// Numbered results and displays share one chapter-local series.
// Chapter III begins with Theorem 3.1 and Proposition 3.2.
#let chapter-counter = counter(heading)
#let series-counter = counter("numbered:series")
#let bibliography-counter = counter("numbered:bib")
#let place-key(location) = chapter-counter.at(location)
#let family-counter(family) = if family == "bib" {
  bibliography-counter
} else { series-counter }
#let restart-counters(level) = if level == 1 { series-counter.update(0) }
#let object-number(family, location) = {
  let n = family-counter(family).at(location).first()
  if family == "bib" { (n,) } else {
    (chapter-counter.at(location).first(), n)
  }
}
#let record(family) = context [#metadata((
  kind: "numbered",
  family: family,
  number: object-number(family, here()),
))<numbered>]
#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}
#let record-number(record) = {
  if record.value.kind == "unnumbered" { none } else if (
    record.value.kind == "independent"
  ) { record.value.number } else if (
    record.value.family == "heading"
  ) {
    chapter-counter.at(record.location()).slice(0, record.value.level)
  } else { object-number(record.value.family, record.location()) }
}
