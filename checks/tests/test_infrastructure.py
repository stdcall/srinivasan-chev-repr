from pathlib import Path
import json
import sys
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from pypdf import PdfReader, PdfWriter
from pypdf.generic import Fit, NullObject
from build import normalize_outline_destinations, page_label_problems
from check_indexes import index_checks
from check_links import check_links
from project import settings, stage, editor_settings


class Infrastructure(unittest.TestCase):
    def test_statement_opening_and_first_display_stay_together(self):
        driver = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#import "/content/statements.typ": *
#show: book-style
#set page(width: 220pt, height: 220pt, margin: 20pt)
#block(height: 160pt)[Filler.]
#definition[For every $x$,
$ x = y $] <def:first-display>
#pagebreak()
@def:first-display[definition]
'''
        expression = ('query(metadata).map(it => it.value).filter(v => '
            'type(v) == dictionary and v.at("kind", default: none) '
            '== "cross-reference")')
        common = ['--root', str(ROOT), '--font-path',
                  str(ROOT / 'assets/fonts')]
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / 'statement.pdf'
            query = subprocess.run(['typst', 'eval', *common, expression,
                '--in', '-', '--format', 'json'], cwd=ROOT, input=driver,
                text=True, capture_output=True)
            self.assertEqual(query.returncode, 0, query.stderr)
            result = subprocess.run(['typst', 'compile', *common, '-',
                str(pdf)], cwd=ROOT, input=driver, text=True,
                capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            reader = PdfReader(pdf)
            self.assertNotIn('Definition', reader.pages[0].extract_text())
            self.assertIn('Definition', reader.pages[1].extract_text())
            self.assertIn('𝑥=𝑦', reader.pages[1].extract_text().replace(' ', ''))
            checked = check_links(pdf, json.loads(query.stdout))
            self.assertEqual(checked['references'][0]['to_page'], 2)

    def test_reference_position_follows_line_wrap(self):
        driver = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#import "/content/statements.typ": *
#show: book-style
#set page(width: 160pt, height: 220pt, margin: 15pt)
#chapter[First] <ch:first>
#theorem[Target.] <th:one>
#for n in range(10, 26) [#("x" * n) @th:one #parbreak()]
'''
        expression = ('query(metadata).map(it => it.value).filter(v => '
            'type(v) == dictionary and v.at("kind", default: none) '
            '== "cross-reference")')
        common = ['--root', str(ROOT), '--font-path',
                  str(ROOT / 'assets/fonts')]
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / 'references.pdf'
            query = subprocess.run(['typst', 'eval', *common, expression,
                '--in', '-', '--format', 'json'], cwd=ROOT, input=driver,
                text=True, capture_output=True)
            self.assertEqual(query.returncode, 0, query.stderr)
            compile_result = subprocess.run(['typst', 'compile', *common,
                '-', str(pdf)], cwd=ROOT, input=driver, text=True,
                capture_output=True)
            self.assertEqual(compile_result.returncode, 0,
                             compile_result.stderr)
            checked = check_links(pdf, json.loads(query.stdout))
            self.assertEqual(checked['semantic_references_checked'], 16)

    def test_shared_series_and_native_references_follow_insertions(self):
        driver = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#import "/content/statements.typ": *
#show: book-style
#chapter[First] <ch:first>
INSERT
#example(numbered: true, series: "examples")[Separate.] <exm:separate>
#theorem[One.] <th:one>
#proposition[Two.] <prop:two>
$ x = y $ <eq:three>
#chapter[Second] <ch:second>
#lemma[One.] <lem:one>
@ch:first @th:one @prop:two @eq:three @lem:one @exm:separate
'''
        expression = ('query(metadata).map(it => it.value).filter(v => '
            'type(v) == dictionary and v.at("kind", default: none) '
            '== "cross-reference").map(v => (v.target, v.printed))')
        def evaluate(insert):
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / 'driver.typ'
                path.write_text(driver.replace('INSERT', insert))
                result = subprocess.run(['typst', 'eval', '--root', str(ROOT),
                    '--font-path', str(ROOT / 'assets/fonts'), expression,
                    '--in', '-', '--format', 'json'], cwd=ROOT,
                    input=path.read_text(), text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                return dict(json.loads(result.stdout))
        before = evaluate('')
        after = evaluate('#lemma[Inserted.] <lem:inserted>')
        self.assertEqual(before['th:one'], '1.1')
        self.assertEqual(before['prop:two'], '1.2')
        self.assertEqual(before['eq:three'], '1.3')
        self.assertEqual(after['th:one'], '1.2')
        self.assertEqual(after['prop:two'], '1.3')
        self.assertEqual(after['eq:three'], '1.4')
        self.assertEqual(after['lem:one'], '2.1')
        self.assertEqual(after['ch:first'], 'I')
        self.assertEqual(before['exm:separate'], '1')
        self.assertEqual(after['exm:separate'], '1')
        inserted_example = evaluate('#example(numbered: true, '
            'series: "examples")[Inserted.] <exm:inserted>')
        self.assertEqual(inserted_example['exm:separate'], '2')
        self.assertEqual(inserted_example['th:one'], '1.1')

    def test_chapter_top_child_position_and_inherited_zoom(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'book.pdf'
            writer = PdfWriter()
            writer.add_blank_page(200, 300)
            parent = writer.add_outline_item('Chapter', 0,
                fit=Fit.xyz(left=0, top=270, zoom=1))
            writer.add_outline_item('Section', 0, parent=parent,
                fit=Fit.xyz(left=10, top=150, zoom=2))
            writer.write(path)
            original = PdfReader(path)
            edited = PdfWriter(path, incremental=True)
            self.assertEqual(normalize_outline_destinations(
                edited, original, top_level_page_start=True), 2)
            out = Path(tmp) / 'edited.pdf'
            edited.write(out)
            def validate(items, depth=0):
                for item in items:
                    if isinstance(item, list):
                        validate(item, depth + 1)
                    else:
                        dest = item.dest_array
                        self.assertEqual(str(dest[1]), '/XYZ')
                        self.assertEqual(float(dest[2]), 0)
                        self.assertEqual(float(dest[3]),
                                         300 if depth == 0 else 150)
                        self.assertIsInstance(dest[4], NullObject)
            validate(PdfReader(out).outline)

    def test_final_page_sequences_are_not_relaxed(self):
        self.assertFalse(page_label_problems(['', 'iii', 'iv', '1', '2']))
        self.assertTrue(page_label_problems(['iii', 'iv', '2']))
        self.assertTrue(page_label_problems(['1', '3']))

    def test_stage_and_editor_match(self):
        self.assertIn('--input=stage=' + stage(),
            editor_settings()['tinymist.typstExtraArgs'])
        self.assertEqual(settings()['pdf_navigation']['outline_left'], 0)

    def test_empty_final_index_is_an_error(self):
        self.assertTrue(index_checks([], final=True)[0])
        self.assertFalse(index_checks([], final=False)[0])

    def test_corrections_schema(self):
        entries = json.loads((ROOT / 'corrections.json').read_text())['entries']
        fields = {'id', 'printed_page', 'section', 'place', 'original',
                  'corrected', 'reason', 'verified_by'}
        ids = []
        for entry in entries:
            self.assertEqual(set(entry), fields)
            self.assertNotEqual(entry['original'], entry['corrected'])
            self.assertTrue(all(str(entry[k]).strip() for k in fields))
            ids.append(entry['id'])
        self.assertEqual(ids, [f'C{n:03d}' for n in range(1, len(ids)+1)])


if __name__ == '__main__':
    unittest.main()
