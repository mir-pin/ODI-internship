import csv
import json
import sys
import re
from pathlib import Path

from rdflib import Graph, Namespace, Literal, RDF, RDFS
from rdflib.namespace import XSD

DATA_DIR = Path("./data")
MAPPING_FILE = Path("./mapping/mapping.json")
OUTPUT_FILE = Path("./taverna_data.ttl")

ODI = Namespace("https://purl.org/ebr/odi#")
BACODI = Namespace("https://purl.org/ebr/odi/data/")  
NS = {
    "odi": ODI, 
    "xsd": XSD
    }

# suffix -> class, used only odi:represents column
SUFFIX_TYPES = {
    "-persona": "odi:Person",
    "-luogo": "odi:Place",
}

ROMAN_NUMERALS = {
    "I": 1, "II": 2, "III": 3, "IIII": 4, "IV": 4, "V": 5, "VI": 6, "VII": 7,
    "VIII": 8, "VIIII": 9, "IX": 9, "X": 10, "XI": 11, "XII": 12, "XIII": 13,
    "XIIII": 14, "XIV": 14, "XV": 15, "XVI": 16, "XVII": 17, "XVIII": 18,
    "XIX": 19, "XX": 20, "XXI": 21,
}

RELATION_SOURCE_TYPE = "class"
RELATION_NAME_TYPE = "generic_relation_column"
RELATION_TARGET_TYPES = {"generic_relation_target", "object_property_target"}


def curie(s: str):
    """'odi:hasName' -> full URI. Unknown/missing prefix falls back to odi:."""
    prefix, _, local = s.partition(":")
    return NS.get(prefix, ODI)[local] if local else ODI[s]


def uri(individual_id: str):
    return BACODI[individual_id.strip().replace(" ", "_")]


def slugify(text: str) -> str:
    text = text.strip().lower()
    text = text.replace("'", "").replace("’", "")
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)  # drop remaining punctuation
    text = re.sub(r"[\s_]+", "-", text)                     # spaces/underscores -> hyphen
    return re.sub(r"-+", "-", text).strip("-")    


def strip_wrapping_quotes(text: str) -> str:
    """Remove one pair of literal straight quotes wrapping the whole value, if present.
    E.g. '"«ciao»"' -> '«ciao»'. A CSV export artifact, not part of the actual text."""
    if len(text) >= 2 and text[0] == '"' and text[-1] == '"':
        return text[1:-1].strip()
    return text


def warn(msg):
    print(f"[WARN] {msg}", file=sys.stderr)


def apply_rule(g, subj, row_id, col, value, rule):
    type = rule["type"]
    value = value.strip() if value else ""

    if type in (RELATION_NAME_TYPE, *RELATION_TARGET_TYPES):
        return  # handled once per row in process_file, not per column

    if type == RELATION_SOURCE_TYPE:
        cls = rule.get("rdf_type", col)
        g.add((subj, RDF.type, curie(cls)))
        return

    if col == "meaningLabel" or "nuova istanza" in type:
        if value:
            meaning_uri = uri(slugify(value))
            g.add((meaning_uri, RDF.type, ODI.Meaning))
            g.add((meaning_uri, RDFS.label, Literal(value, lang="it")))
            g.add((subj, ODI.hasMeaningOf, meaning_uri))
        return

    if type.startswith("object_property"):
            if not value:
                return
            if col == "odi:hasAuthor":
                value = strip_wrapping_quotes(value)
                for item in value.split(","):
                    part = item.strip()
                    if not part:
                        continue
                    target = uri(slugify(part))
                    g.add((subj, curie(col), target))
                    g.add((target, RDF.type, ODI.Person))
                    g.add((target, RDFS.label, Literal(part)))
                return
            
            target = uri(value)
            g.add((subj, curie(col), target))
            if col == "odi:represents":
                for suffix, cls in SUFFIX_TYPES.items():
                    if value.endswith(suffix):
                        g.add((target, RDF.type, curie(cls)))
                        break
                else:
                    warn(f"can't infer type of '{value}' from suffix (row {row_id})")
            return

    if type.startswith("data_property"):
        if not value:
            return
        value = strip_wrapping_quotes(value)
        datatype = curie(rule.get("datatype", "xsd:string"))
        if datatype == XSD.integer and not value.isdigit():
            roman = ROMAN_NUMERALS.get(value.upper())
            if roman is None:
                warn(f"cannot parse '{value}' as an integer for {col} (row {row_id})")
                return
            value = str(roman)
        g.add((subj, curie(col), Literal(value, datatype=datatype)))
        return

    if type == "rdf_type":
        if not value:
            return
        cls = rule.get("value_mapping", {}).get(value)
        if cls:
            g.add((subj, RDF.type, curie(cls)))
        else:
            warn(f"unknown rdf:type value '{value}' (row {row_id})")
        return

    warn(f"unrecognized rule type '{type}' for column '{col}' (row {row_id})")


def process_file(g, filename, colmap):
    path = DATA_DIR / filename
    if not path.exists():
        warn(f"file not found, skipping: {path}")
        return 0

    for col, rule in colmap.items():
        if "type" not in rule:
            raise ValueError(f"mapping.json: column '{col}' in '{filename}' is missing a \"type\"")

    id_col = next((c for c, r in colmap.items() if r["type"] == RELATION_SOURCE_TYPE), None)
    relation_name_col = next((c for c, r in colmap.items() if r["type"] == RELATION_NAME_TYPE), None)
    relation_target_col = next((c for c, r in colmap.items() if r["type"] in RELATION_TARGET_TYPES), None)
    has_rdf_type_col = any(r["type"] == "rdf_type" for r in colmap.values())

    n = 0
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            n += 1
            row_id = row.get(id_col, "").strip() if id_col else f"{filename}#{n}"
            if not row_id:
                continue
            subj = uri(row_id)

            for col, rule in colmap.items():
                if rule["type"] == RELATION_SOURCE_TYPE and has_rdf_type_col:
                    continue  # the specific subclass comes from the rdf_type column instead
                apply_rule(g, subj, row_id, col, row.get(col, ""), rule)

            if relation_name_col and relation_target_col:
                relation = row.get(relation_name_col, "").strip()
                target = row.get(relation_target_col, "").strip()
                if relation and target:
                    prop = ODI[relation.split(":")[-1]]
                    g.add((subj, prop, uri(target)))
    return n


def main():
    mapping = json.loads(MAPPING_FILE.read_text(encoding="utf-8"))
    g = Graph()
    g.bind("odi", ODI)
    g.bind("bacodi", BACODI)

    total = 0
    for filename, colmap in mapping.items():
        n = process_file(g, filename, colmap)
        print(f"{filename}: {n} rows")
        total += n

    g.serialize(destination=str(OUTPUT_FILE), format="turtle")
    print(f"\nDone: {total} rows -> {len(g)} triples -> {OUTPUT_FILE}")


if __name__ == "__main__":
    main()