#set document(
  title: "Representations of Finite Chevalley Groups: A Survey",
  author: "Bhama Srinivasan",
  date: none,
)
#import "book-style.typ": book-style
#import "main-defs.typ": editorial-bibliography
#show: book-style
#import "cover.typ": cover
#cover()
#counter(page).update(1)
#include "frontmatter/publication.typ"
#set page(numbering: "I")
#include "00-introduction.typ"
#pagebreak()
#heading(level: 1, numbering: none)[Contents]
#outline(title: none, depth: 2)
#pagebreak()
#set page(numbering: "1")
#counter(page).update(1)
#include "01-algebraic-groups.typ"
#include "02-tori.typ"
#include "03-principal-series.typ"
#include "04-harish-chandra.typ"
#include "05-adic-cohomology.typ"
#include "06-lusztig-deligne.typ"
#include "07-characters.typ"
#include "08-classification.typ"
#include "80-references.typ"
#include "81-notation.typ"
#include "90-index.typ"
#editorial-bibliography
