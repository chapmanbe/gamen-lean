#!/usr/bin/env python3
"""Extract the Boolean truth tables from the CQL and FHIRPath specs.

Writes `data/specs/cql-2.0.0-logical.json` and
`data/specs/fhirpath-3.0.0-boolean.json` from the published HTML, so the
tables are copied mechanically from the spec, never typed from memory.

    python3 tools/specs/extract_truth_tables.py CQL_HTML FHIRPATH_HTML

where the two HTML files were downloaded with

    curl -sL https://cql.hl7.org/09-b-cqlreference.html -o cql.html
    curl -sL https://hl7.org/fhirpath/en/ -o fhirpath.html

Each table's first row is the header (the right operand); each later row
starts with the left operand. Cell text is kept exactly as the spec prints
it; `valueMap` says which cell texts mean true, false and the third value.
`Tests/Main.lean` (`specTableCases`) checks each table against
`Gamen.ManyValued.strongKleene`.
"""

import hashlib
import html
import json
import re
import sys
from datetime import date


def cell_text(c):
    return html.unescape(re.sub(r"<[^>]+>", "", c)).replace("\xa0", " ").strip()


def parse_table(tbl):
    rows = re.findall(r"<tr>(.*?)</tr>", tbl, flags=re.S)
    return [[cell_text(c) for c in re.findall(r"<t[hd][^>]*>(.*?)</t[hd]>", r, flags=re.S)]
            for r in rows]


def table_after(page, anchor, stop_anchor):
    """The first <table> between heading `anchor` and heading `stop_anchor`."""
    i = page.index(f'id="{anchor}"')
    j = page.index(f'id="{stop_anchor}"', i) if stop_anchor else len(page)
    k = page.index("<table", i)
    if k > j:
        raise SystemExit(f"no table under #{anchor}")
    return parse_table(page[k:page.index("</table>", k)])


def entries(grid, arity):
    header, body = grid[0], grid[1:]
    if arity == 1:
        # Unary tables: header is [op] or [op, ""]; each row is [arg, result].
        return [[r[0], r[1]] for r in body]
    return [[r[0], header[c], r[c]] for r in body for c in range(1, len(header))]


def caption_after(page, anchor):
    i = page.index(f'id="{anchor}"')
    m = re.search(r"(Table\s*9\S*A?\d*)\s*-", html.unescape(page[i:i + 6000]))
    return m.group(1).replace("‑", "-") if m else None


def build(page, meta, ops):
    out = dict(meta)
    out["pageSha256"] = hashlib.sha256(page.encode("utf-8")).hexdigest()
    out["retrieved"] = date.today().isoformat()
    out["operators"] = []
    for name, anchor, stop, arity in ops:
        grid = table_after(page, anchor, stop)
        op = {"name": name, "anchor": "#" + anchor, "arity": arity}
        cap = caption_after(page, anchor) if meta["spec"].startswith("Clinical") else None
        if cap:
            op["tableId"] = cap
        op["table"] = entries(grid, arity)
        out["operators"].append(op)
    return out


def main(cql_path, fhir_path):
    cql = open(cql_path, encoding="utf-8").read()
    fhir = open(fhir_path, encoding="utf-8").read()
    cql_json = build(cql, {
        "spec": "Clinical Quality Language (CQL)",
        "version": "2.0.0",
        "url": "https://cql.hl7.org/09-b-cqlreference.html",
        "section": "Appendix B - CQL Reference, Logical Operators",
        "sectionAnchor": "#logical-operators-3",
        "layout": "binary rows are [left, right, result]; unary rows are [argument, result]",
        "valueMap": {"TRUE": "t", "FALSE": "f", "NULL": "u"},
    }, [("and", "and", "implies", 2), ("implies", "implies", "not", 2),
        ("not", "not", "or", 1), ("or", "or", "xor", 2), ("xor", "xor", None, 2)])
    fhir_json = build(fhir, {
        "spec": "FHIRPath",
        "version": "3.0.0",
        "url": "https://hl7.org/fhirpath/en/",
        "section": "Operators, Boolean logic",
        "sectionAnchor": "#boolean-logic",
        "note": "The spec gives these tables no ids; each is identified by its heading anchor.",
        "layout": "binary rows are [left, right, result]; unary rows are [argument, result]",
        "valueMap": {"true": "t", "false": "f", "empty": "u", "empty ({ })": "u"},
    }, [("and", "and", "or", 2), ("or", "or", "not--boolean", 2),
        ("not", "not--boolean", "xor", 1), ("xor", "xor", "implies", 2),
        ("implies", "implies", None, 2)])
    for path, obj in [("data/specs/cql-2.0.0-logical.json", cql_json),
                      ("data/specs/fhirpath-3.0.0-boolean.json", fhir_json)]:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(obj, f, indent=2, ensure_ascii=False)
            f.write("\n")
        print(path)


if __name__ == "__main__":
    main(*sys.argv[1:3])
