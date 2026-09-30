// Invisible marks are the sole source of index entries and page locators.
#let term-entry(
  term,
  sub: none,
  sort: none,
  display: none,
  sub-display: none,
  see: none,
  see-also: none,
) = {
  [#metadata((
    kind: "index-mark",
    path: if sub == none { (term,) } else { (term, sub) },
    sort: sort,
    display: display,
    sub-display: sub-display,
    see: see,
    see-also: see-also,
  ))<index-mark>]
}
#let locator(location) = box(context {
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    position: here().position(),
    target-position: location.position(),
  ))
  link(location, str(counter(page).at(location).first()))
})
#let index-entries = context {
  let entries = (:)
  for mark in query(<index-mark>) {
    let key = mark.value.path.join("\u{1f}")
    let entry = entries.at(key, default: (value: mark.value, locations: ()))
    let page-number = counter(page).at(mark.location()).first()
    if entry.locations.all(l => counter(page).at(l).first() != page-number) {
      entry.locations.push(mark.location())
    }
    entries.insert(key, entry)
  }
  let groups = (:)
  for entry in entries.values() {
    let term = entry.value.path.first()
    let group = groups.at(term, default: ())
    group.push(entry)
    groups.insert(term, group)
  }
  let suffix(entry) = {
    let result = if entry.value.see != none {
      [, _see_ #entry.value.see]
    } else { [, #entry.locations.map(locator).join[, ]] }
    if entry.value.see-also != none {
      result += [; _see also_ #entry.value.see-also]
    }
    result
  }
  for group in groups
    .values()
    .sorted(key: g => lower(
      if g.first().value.sort != none { g.first().value.sort } else {
        g.first().value.path.first()
      },
    ).replace("é", "e")) {
    let parent = group.find(e => e.value.path.len() == 1)
    let value = if parent != none { parent.value } else { group.first().value }
    let title = if value.display != none { value.display } else {
      value.path.first()
    }
    let tail = if parent != none { suffix(parent) }
    block(above: 0pt, below: 0.35em, breakable: false, {
      block(above: 0pt, below: 0.35em)[#title#tail]
      for entry in group
        .filter(e => e.value.path.len() > 1)
        .sorted(key: e => lower(e.value.path.last())) {
        block(above: 0pt, below: 0.35em, inset: (left: 1em))[
          #if entry.value.sub-display != none { entry.value.sub-display } else {
            entry.value.path.last()
          }#suffix(entry)
        ]
      }
    })
  }
}
