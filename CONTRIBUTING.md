# Building and editing

Use Python 3.14, uv, Typst 0.15.1, Typstyle 0.15.1, and Tinymist 0.15.8.
Fonts and their licenses are included in `assets/fonts/`.

Run `uv sync --locked`, then `just build`. `just check` checks formatting,
source conventions, evaluated references, PDF links and bookmarks,
corrections, and the edition without editorial notes. `just fmt` formats
the sources. `just test` runs the focused infrastructure tests.

`content/main.typ` includes the parts in reading order. Chapter files are
ordinary Typst markup and import `main-defs.typ` and `statements.typ`.
Page design belongs in `book-style.typ`; numbering belongs in
`numbering.typ`. Keep source lines within 80 characters.

Use `#chapter[Title] <ch:meaningful-key>`. Chapters are numbered I–VIII.
Results, numbered displays, and numbered prose items share one series
within each chapter: Theorem 3.1, Proposition 3.2, and so on. Numbering
restarts only at a new chapter; sections use ordinary `==` headings.

Use `#theorem[Body] <th:key>`, `#proposition[Body] <prop:key>`,
`#lemma[Body] <lem:key>`, and `#corollary[Body] <cor:key>`.
An optional `title: [Name]` adds a parenthetical title. Definitions,
examples, and remarks are unnumbered by default; request `numbered: true`
only when their printed form is part of the chapter series. Local lists
use Typst enumerations. Proofs use `#proof[Body]`.

The two local claims in the final classification proof use
`#proof-claim[Body] <claim:key>` and a separate series `(1)`, `(2)`.
They do not advance the chapter series; references use `@claim:key`.

Labelled displays `$ ... $ <eq:key>` receive the next series number.
`#formula-item[Body] <eq:key>` handles a numbered item stated in prose.
Never type a result or formula number into a heading or reference.

Place a stable literal semantic label directly after its object. Use
native references `@th:key`, with `#[@th:key]` inside mathematics.
Descriptive links use `@th:key[description]`. Chapter links print Roman
numerals; result and formula links print the full chapter.number. Only
reference numbers are semibold; link text keeps its ordinary color.

Bibliography entries use `#bib-item[Text] <bib:AuthorYear>` in list order.
The same key must identify the entry in `references.bib`. The displayed
number is counted. Bibliographical locators in other works may be literal
and must be documented in `config/lint.json`.

Index entries come only from invisible inline marks such as
`term#term-entry("Term")`. Optional arguments are `sub`, `sort`, `see`,
and `see-also`. `#index-entries` generates entries and linked locators.
For an entry about a heading or statement, set `target: <its-label>` so
the locator leads to the object's beginning and uses its page number.
Do not maintain a second handwritten list of index entries.

Confirmed corrections belong in `corrections.json`: printed page and
place, original and corrected readings, reason, and verification.
Editorial explanations use `#ed-note[Text]` and are omitted with
`just build-no-notes`. Notes cite `editorial.bib` in full.

The final stage rejects unresolved references. PDF finalization preserves
page streams and geometry and validates every nested bookmark destination
as `/XYZ 0 top null`. Chapters starting a new page target the page top;
other bookmarks target the heading. Structural validation does not certify viewer
interaction. Build intermediates use an external cache, overridable with
`BOOK_BUILD_CACHE`;
`build/` contains distributable PDF editions.
