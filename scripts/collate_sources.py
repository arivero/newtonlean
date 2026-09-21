"""Collate TEI anchors with the local Newton Project presentation layers.

This is a conservative transcription collation.  It checks that selected XML
anchors are present, locates their nearest encoded page break, records marked
revision elements, and records whether local normalized and diplomatic HTML
contains the same anchor.  It deliberately does not compare page images or
turn an edition sequence into a proof dependency.
"""

from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
import hashlib
import json
import re
import xml.etree.ElementTree as ET
from urllib.parse import urljoin

from catalogue_m1 import render

ROOT = Path(__file__).resolve().parents[1]
SELECT = json.loads((ROOT / "research" / "selections.json").read_text())
PASSAGES = json.loads((ROOT / "research" / "passages.json").read_text())
PASSAGE_BY_ID = {p["id"]: p for p in PASSAGES}
XML_ID = "{http://www.w3.org/XML/1998/namespace}id"
XML_BASE = "{http://www.w3.org/XML/1998/namespace}base"
REVISION_TAGS = {
    "add",
    "choice",
    "corr",
    "del",
    "gap",
    "note",
    "orig",
    "reg",
    "sic",
    "supplied",
    "unclear",
}


def local(tag):
    return tag.rsplit("}", 1)[-1]


def compact(value):
    return " ".join(str(value or "").split())


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class AnchorParser(HTMLParser):
    """Collect text inside HTML elements whose id is a paragraph anchor."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.current = None
        self.depth = 0
        self.texts = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        ident = attrs.get("id")
        if ident and re.fullmatch(r"par\d+", ident):
            # Paragraph anchors are siblings.  Treat a new paragraph as the
            # end of a malformed or unclosed preceding element as well.
            self.current = ident
            self.depth = 1
            self.texts.setdefault(ident, [])
        elif self.current is not None:
            self.depth += 1

    def handle_startendtag(self, tag, attrs):
        # A self-closing descendant has no effect on the enclosing depth.
        return

    def handle_endtag(self, tag):
        if self.current is None:
            return
        if self.depth == 1:
            self.current = None
            self.depth = 0
        else:
            self.depth -= 1

    def handle_data(self, data):
        if self.current is not None:
            self.texts[self.current].append(data)


def html_anchors(path):
    if not path.is_file():
        return {"present": False, "path": str(path.relative_to(ROOT))}
    parser = AnchorParser()
    try:
        parser.feed(path.read_text(errors="replace"))
        parser.close()
    except Exception as exc:  # keep the source record reviewable on malformed HTML
        return {
            "present": True,
            "path": str(path.relative_to(ROOT)),
            "sha256": sha256(path),
            "parse_error": str(exc),
            "anchors": {},
        }
    anchors = {}
    for ident, pieces in parser.texts.items():
        text = compact(" ".join(pieces))
        anchors[ident] = {
            "chars": len(text),
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
        }
    return {
        "present": True,
        "path": str(path.relative_to(ROOT)),
        "sha256": sha256(path),
        "anchors": anchors,
    }


def title_of(root):
    title = root.find(".//{*}titleStmt/{*}title")
    return compact("".join(title.itertext())) if title is not None else ""


def source_metadata(root):
    bibl = root.find(".//{*}sourceDesc/{*}bibl")
    source_desc = compact("".join(bibl.itertext())) if bibl is not None else ""
    kind = bibl.get("subtype") if bibl is not None else None
    date = root.find(".//{*}profileDesc/{*}creation/{*}origDate")
    hands = [compact("".join(h.itertext())) for h in root.findall(".//{*}handNotes/{*}handNote")]
    ptr = root.find(".//{*}ptr[@type='library_facsimile']")
    return {
        "source_description": source_desc,
        "source_kind": kind or "unspecified",
        "orig_date": compact("".join(date.itertext())) if date is not None else "",
        "hand_notes": hands,
        "library_facsimile": ptr.get("target") if ptr is not None else None,
    }


def pages_and_anchors(root):
    facsimile = root.find("{*}facsimile")
    base = facsimile.get(XML_BASE) if facsimile is not None else None
    graphics = {}
    if facsimile is not None:
        for graphic in facsimile.findall("{*}graphic"):
            ident = graphic.get(XML_ID) or graphic.get("url")
            if ident:
                graphics[ident] = {
                    "url": graphic.get("url"),
                    "folio": graphic.get("n"),
                }

    current = None
    anchors = {}
    pages = []
    for element in root.iter():
        if local(element.tag) == "pb":
            facs = element.get("facs")
            graphic = graphics.get(facs.lstrip("#")) if facs else None
            current = {
                "xml_id": element.get(XML_ID),
                "n": element.get("n"),
                "facs": facs,
                "facsimile_url": urljoin(base, graphic["url"]) if base and graphic and graphic.get("url") else None,
                "graphic_folio": graphic.get("folio") if graphic else None,
            }
            pages.append(current)
        ident = element.get(XML_ID)
        if ident:
            anchors[ident] = current
    return pages, anchors


def anchor_record(ident, selection, element, page, passage, normalized, diplomatic):
    tags = Counter(local(e.tag) for e in element.iter() if local(e.tag) in REVISION_TAGS)
    page = page or {}
    expected = " ".join(render(element).split())
    if passage is None:
        generated_match = False
    else:
        generated_match = passage.get("latin") == expected

    result = {
        "id": f"{ident}.{element.get(XML_ID)}",
        "anchor": element.get(XML_ID),
        "xml_present": True,
        "generated_extract_match": generated_match,
        "page": page.get("n"),
        "page_xml_id": page.get("xml_id"),
        "page_facs": page.get("facs"),
        "page_folio": page.get("graphic_folio"),
        "facsimile_url": page.get("facsimile_url"),
        "revision_tags": dict(sorted(tags.items())),
        "revision_tag_total": sum(tags.values()),
        "normalized": {
            "present": normalized.get("present", False),
            "anchor_present": element.get(XML_ID) in normalized.get("anchors", {}),
        },
        "diplomatic": {
            "present": diplomatic.get("present", False),
            "anchor_present": element.get(XML_ID) in diplomatic.get("anchors", {}),
        },
    }
    for view, parsed in (("normalized", normalized), ("diplomatic", diplomatic)):
        if element.get(XML_ID) in parsed.get("anchors", {}):
            result[view].update(parsed["anchors"][element.get(XML_ID)])
        if parsed.get("parse_error"):
            result[view]["parse_error"] = parsed["parse_error"]
    return result


def collate_source(ident, selection):
    path = ROOT / selection["path"]
    tree = ET.parse(path)
    root = tree.getroot()
    elements = {e.get(XML_ID): e for e in root.iter() if e.get(XML_ID)}
    pages, page_by_anchor = pages_and_anchors(root)
    metadata = source_metadata(root)
    normalized_path = path.with_name(f"{ident}_normalized.html")
    diplomatic_path = path.with_name(f"{ident}_diplomatic.html")
    normalized = html_anchors(normalized_path)
    diplomatic = html_anchors(diplomatic_path)
    anchors = []
    for anchor in selection["anchors"]:
        assert anchor in elements, f"missing XML anchor {ident}.{anchor}"
        anchors.append(
            anchor_record(
                ident,
                selection,
                elements[anchor],
                page_by_anchor.get(anchor),
                PASSAGE_BY_ID.get(f"{ident}.{anchor}"),
                normalized,
                diplomatic,
            )
        )
    # Keep the source-level presentation details alongside the anchor rows.
    return {
        "id": ident,
        "stage": selection["stage"],
        "path": selection["path"],
        "title": title_of(root),
        "revision_layer": selection["revision_layer"],
        **metadata,
        "xml_sha256": sha256(path),
        "xml_source_url": f"https://www.newtonproject.ox.ac.uk/view/texts/xml/{ident}",
        "normalized_source_url": f"https://www.newtonproject.ox.ac.uk/view/texts/normalized/{ident}",
        "diplomatic_source_url": f"https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/{ident}",
        "page_count": len(pages),
        "pages": pages,
        "normalized_view": normalized,
        "diplomatic_view": diplomatic,
        "anchors": anchors,
    }


def supplementary_records(selected_ids):
    records = []
    for passage in PASSAGES:
        if passage["id"].split(".", 1)[0] in selected_ids:
            if passage["id"].split(".", 1)[1].startswith("par"):
                continue
        path = ROOT / passage["source_path"]
        records.append(
            {
                "id": passage["id"],
                "stage": passage.get("stage"),
                "source_path": passage["source_path"],
                "anchor": passage.get("anchor"),
                "source_url": passage.get("url"),
                "source_exists": path.is_file(),
                "source_sha256": sha256(path) if path.is_file() else None,
                "xml_checked": False,
                "collation_status": "supplementary_source_not_xml_anchored",
                "reason": "PDF or secondary locator; no selected TEI anchor is available for this record.",
            }
        )
    return records


def markdown(report):
    summary = report["summary"]
    text = "# Source collation\n\n"
    text += (
        "Generated 2026-09-21 by `scripts/collate_sources.py`. This report checks "
        "the local TEI/XML transcription against selected passage extracts and "
        "the presence of corresponding anchors in normalized and diplomatic HTML. "
        "It records page and facsimile metadata but does not inspect or download "
        "manuscript images, and it does not establish historical proof dependency.\n\n"
    )
    text += (
        f"Primary witnesses: {summary['primary_witnesses']}; selected XML anchors: "
        f"{summary['primary_anchors']}; exact generated-extract matches: "
        f"{summary['generated_extract_matches']}; revision-tagged anchors: "
        f"{summary['revision_tagged_anchors']}.\n\n"
    )
    text += "## Witness layers\n\n| Witness | Stage | Kind | Pages | Normalized anchors | Diplomatic anchors |\n|---|---|---:|---:|---:|---:|\n"
    for source in report["sources"]:
        total = len(source["anchors"])
        norm = sum(a["normalized"]["anchor_present"] for a in source["anchors"])
        dip = sum(a["diplomatic"]["anchor_present"] for a in source["anchors"])
        text += f"| {source['id']} | {source['stage']} | {source['source_kind']} | {source['page_count']} | {norm}/{total} | {dip}/{total} |\n"
    text += "\nA missing local HTML view is reported as absent; its official URL remains in the JSON record. XML is the machine-readable authority for exact revision markup.\n\n"
    for source in report["sources"]:
        text += f"## {source['id']} — {source['title']}\n\n"
        text += f"Source: {source['source_description']}\n"
        text += f"Date: {source['orig_date']}\n"
        text += f"Hand: {', '.join(source['hand_notes']) or 'not stated'}\n"
        text += f"XML: [{source['path']}](../{source['path']})\n"
        text += f"Library/facsimile record: {source['library_facsimile'] or 'none encoded'}\n\n"
        text += "| Anchor | Page | Facsimile target | Revision tags | Extract | Normalized | Diplomatic |\n|---|---:|---|---|---|---|---|\n"
        for anchor in source["anchors"]:
            facs = anchor["facsimile_url"] or "—"
            tags = ", ".join(f"{k}:{v}" for k, v in anchor["revision_tags"].items()) or "none"
            extract = "match" if anchor["generated_extract_match"] else "mismatch"
            norm = "present" if anchor["normalized"]["anchor_present"] else ("view missing" if not anchor["normalized"]["present"] else "anchor missing")
            dip = "present" if anchor["diplomatic"]["anchor_present"] else ("view missing" if not anchor["diplomatic"]["present"] else "anchor missing")
            text += f"| {anchor['anchor']} | {anchor['page'] or '—'} | {facs} | {tags} | {extract} | {norm} | {dip} |\n"
        text += "\n"
    if report["supplementary"]:
        text += "## Supplementary records\n\n"
        text += "These records are retained for source provenance but are not XML-anchor collation rows.\n\n| Record | Stage | Source | Status |\n|---|---|---|---|\n"
        for record in report["supplementary"]:
            text += f"| {record['id']} | {record['stage']} | {record['source_path']} | {record['collation_status']} |\n"
    return text


def main():
    sources = [collate_source(ident, selection) for ident, selection in SELECT.items()]
    supplementary = supplementary_records(set(SELECT))
    anchors = [a for source in sources for a in source["anchors"]]
    report = {
        "generated": "2026-09-21",
        "scope": {
            "method": "TEI/XML anchor, page-break, revision-tag, and local HTML-anchor collation",
            "xml_authority": True,
            "facsimile_images_downloaded": False,
            "historical_dependency_inferred": False,
            "unavailable_manuscript_image_access": "page and facsimile targets are recorded; no image reading is claimed",
        },
        "sources": sources,
        "supplementary": supplementary,
        "summary": {
            "primary_witnesses": len(sources),
            "primary_anchors": len(anchors),
            "generated_extract_matches": sum(a["generated_extract_match"] for a in anchors),
            "revision_tagged_anchors": sum(a["revision_tag_total"] > 0 for a in anchors),
            "normalized_anchor_matches": sum(a["normalized"]["anchor_present"] for a in anchors),
            "diplomatic_anchor_matches": sum(a["diplomatic"]["anchor_present"] for a in anchors),
            "supplementary_records": len(supplementary),
        },
    }
    (ROOT / "research" / "collation.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    (ROOT / "research" / "collation.md").write_text(markdown(report))
    print(
        f"Collated {len(sources)} witnesses, {len(anchors)} XML anchors, "
        f"{len(supplementary)} supplementary records"
    )


if __name__ == "__main__":
    main()
