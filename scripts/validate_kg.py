#!/usr/bin/env python3
"""
validate_kg.py - Validate an OWL/RDFS ontology, the RDF knowledge graph built on it,
and (optionally) the CSV->RDF mapping.json.

Usage
-----
    python validate_kg.py --ontology odiontology.ttl --kg taverna_data.ttl \
                          --mapping mapping/mapping.json [--json report.json]

    # ontology only
    python validate_kg.py --ontology odiontology.ttl

Options
-------
    --max-examples N   examples printed per finding (default 5, -1 = all)
    --strict           exit code 1 on warnings too (default: only on errors)
    --json FILE        also write the full report as JSON

Severity
--------
    ERROR    definitely broken (parse errors, unknown predicates/classes, type clashes ...)
    WARNING  very probably a modelling / data problem
    INFO     worth knowing (unused terms, missing inverses, statistics ...)

Finding codes
-------------
    L***  Turtle syntax lint (before parsing)      O***  Ontology
    M***  mapping.json vs ontology                 K***  Knowledge graph
    D***  Domain-specific consistency (cards, stories, decks ...)

Dependencies: rdflib >= 6   (pip install rdflib)
"""
import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from difflib import get_close_matches
from pathlib import Path
import unicodedata
from rdflib import BNode, Graph, Literal, URIRef
from rdflib.namespace import OWL, RDF, RDFS, XSD

# --------------------------------------------------------------------------- #
# Configuration - edit freely
# --------------------------------------------------------------------------- #
ODI = "https://purl.org/ebr/odi#"          # ontology namespace
DATA = "https://purl.org/ebr/odi/data/"    # individuals namespace

CONFIG = {
    # properties that should have at most ONE value per subject
    # (in addition to any property declared owl:FunctionalProperty)
    "functional": [
        "hasName", "hasTitle", "isNumber", "hasSuit", "hasTypology", "isContainedIn",
        "isACardOf", "specifies", "hasPositionInTheText", "hasCurrentNumberOfCards",
        "hasOriginalNumberOfCards", "hasTotalNumberOfCards", "hasDate",
        "hasPublicationDate", "hasCurrentLocation", "hasCondition",
    ],
    # class -> properties every instance is expected to have (at least one value)
    "required": {
        "Storycard": ["isACardOf", "specifies", "carriesRepresentation"],
        "DeckCard": ["hasName", "isContainedIn"],
        "TarotDeck": ["hasName"],
        "Story": ["hasTitle"],
        "Edition": ["hasTitle"],
        "Representation": ["hasMeaningOf"],
    },
    # classes that should never be the ONLY type of an individual
    "abstract_classes": ["Representation"],
}

STD_NS = {str(RDF): RDF, str(RDFS): RDFS, str(OWL): OWL, str(XSD): XSD}
PREFIXES = {
    ODI: "odi:", DATA: "bacodi:", str(RDF): "rdf:", str(RDFS): "rdfs:",
    str(OWL): "owl:", str(XSD): "xsd:",
}
ERROR, WARNING, INFO = "ERROR", "WARNING", "INFO"
SEV_ORDER = {ERROR: 0, WARNING: 1, INFO: 2}
INT_TYPES = {XSD.integer, XSD.int, XSD.long, XSD.short, XSD.byte, XSD.nonNegativeInteger,
             XSD.positiveInteger, XSD.negativeInteger, XSD.nonPositiveInteger,
             XSD.unsignedInt, XSD.unsignedLong, XSD.unsignedShort, XSD.unsignedByte}
PLACEHOLDERS = {"nan", "none", "null", "n/a", "na", "#n/a", "#n/d", "undefined", "-"}


# --------------------------------------------------------------------------- #
# Reporting
# --------------------------------------------------------------------------- #
class Report:
    def __init__(self):
        self.findings = {}  # (sev, code, title) -> list[str]

    def add(self, sev, code, title, detail=None):
        lst = self.findings.setdefault((sev, code, title), [])
        if detail is not None:
            lst.append(str(detail))
        return lst

    def count(self, sev):
        return sum(1 for (s, _, _) in self.findings if s == sev)

    def print(self, max_examples, min_level="INFO"):
        color = sys.stdout.isatty()
        col = {ERROR: "\033[31m", WARNING: "\033[33m", INFO: "\033[36m"}
        reset = "\033[0m" if color else ""

        max_sev_rank = SEV_ORDER.get(min_level.upper(), 2)

        for (sev, code, title), details in sorted(
                self.findings.items(), key=lambda kv: (SEV_ORDER[kv[0][0]], kv[0][1])):

            if SEV_ORDER[sev] > max_sev_rank:
                continue

            c = col[sev] if color else ""
            n = f" ({len(details)})" if details else ""
            print(f"{c}[{sev}] {code} {title}{n}{reset}")
            shown = details if max_examples < 0 else details[:max_examples]
            for d in shown:
                print(f"      - {d}")
            if len(shown) < len(details):
                print(f"      ... and {len(details) - len(shown)} more")
        print("\n" + "=" * 70)
        print(f"SUMMARY: {self.count(ERROR)} error type(s), "
              f"{self.count(WARNING)} warning type(s), {self.count(INFO)} info")

    def to_json(self):
        return [{"severity": s, "code": c, "title": t, "count": len(d), "details": d}
                for (s, c, t), d in sorted(self.findings.items(),
                                           key=lambda kv: (SEV_ORDER[kv[0][0]], kv[0][1]))]


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #
def qn(t):
    """Short printable form of an RDF term."""
    if isinstance(t, Literal):
        return repr(str(t))
    if isinstance(t, BNode):
        return f"_:{t}"
    s = str(t)
    for ns, p in PREFIXES.items():
        if s.startswith(ns):
            return p + s[len(ns):]
    return f"<{s}>"


def local_name(u):
    s = str(u)
    if s.startswith(ODI):
        return s[len(ODI):]
    return re.split(r"[#/]", s)[-1]


def is_std(u):
    return any(str(u).startswith(ns) for ns in STD_NS)


def std_term_defined(u):
    """True if u (in rdf/rdfs/owl/xsd namespace) is a real term of that vocabulary."""
    s = str(u)
    for ns, vocab in STD_NS.items():
        if s.startswith(ns):
            local = s[len(ns):]
            if not local:
                return True
            try:
                vocab[local]
                return True
            except (AttributeError, KeyError):
                return False
    return True


def suggest(name, candidates, n=3):
    """Close matches: case-insensitive exact first, then fuzzy."""
    low = {c.lower(): c for c in candidates}
    out = []
    if name.lower() in low and low[name.lower()] != name:
        out.append(low[name.lower()])
    for m in get_close_matches(name, list(candidates), n=n, cutoff=0.75):
        if m not in out:
            out.append(m)
    return out


def hint(name, candidates):
    s = suggest(name, candidates)
    return f"  -> did you mean: {', '.join(s)}?" if s else ""


def to_int(lit):
    try:
        return int(str(lit).strip())
    except (ValueError, TypeError):
        return None


def strip_accents(s):
    return "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))



# --------------------------------------------------------------------------- #
# Loading
# --------------------------------------------------------------------------- #

def load_graph(path, label, rpt):
    path = Path(path)
    if not path.exists():
        rpt.add(ERROR, "L000", f"{label} file not found", str(path))
        return None
    g = Graph()
    try:
        g.parse(str(path))
    except Exception as e:
        rpt.add(ERROR, "L004", f"{label} cannot be parsed - fix syntax errors first",
                f"{path.name}: {str(e).strip()[:400]}")
        return None
    return g


# --------------------------------------------------------------------------- #
# Ontology model
# --------------------------------------------------------------------------- #
class Onto:
    def __init__(self, g):
        self.g = g
        cls = set(g.subjects(RDF.type, OWL.Class)) | set(g.subjects(RDF.type, RDFS.Class))
        self.classes = {c for c in cls if isinstance(c, URIRef)}
        self.obj_props = set(g.subjects(RDF.type, OWL.ObjectProperty))
        self.data_props = set(g.subjects(RDF.type, OWL.DatatypeProperty))
        self.ann_props = set(g.subjects(RDF.type, OWL.AnnotationProperty))
        self.props = self.obj_props | self.data_props | self.ann_props | \
            set(g.subjects(RDF.type, RDF.Property))
        self.domains = {p: set(g.objects(p, RDFS.domain)) for p in self.props}
        self.ranges = {p: set(g.objects(p, RDFS.range)) for p in self.props}
        self.functional = set(g.subjects(RDF.type, OWL.FunctionalProperty))
        self.inverse = defaultdict(set)
        for a, b in g.subject_objects(OWL.inverseOf):
            self.inverse[a].add(b)
            self.inverse[b].add(a)
        self.disjoint = set()
        for a, b in g.subject_objects(OWL.disjointWith):
            self.disjoint |= {(a, b), (b, a)}
        self._anc = {}

    def ancestors(self, c):
        """Reflexive-transitive superclasses."""
        if c not in self._anc:
            self._anc[c] = set(self.g.transitive_objects(c, RDFS.subClassOf))
        return self._anc[c]

    def term(self, local):
        return URIRef(ODI + local)


def strict_reach(g, node, pred):
    seen, stack = set(), list(g.objects(node, pred))
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack.extend(g.objects(n, pred))
    return seen


# --------------------------------------------------------------------------- #
# Ontology checks
# --------------------------------------------------------------------------- #
def check_ontology(g, O, rpt):
    declared = O.classes | O.props
    declared_local = [local_name(t) for t in declared]

    if not any(g.subjects(RDF.type, OWL.Ontology)):
        rpt.add(WARNING, "O001", "No owl:Ontology declaration")

    # --- terms used but not declared / undefined std terms ---------------------
    terms = {x for tr in g for x in tr if isinstance(x, URIRef)}
    for t in sorted(terms):
        s = str(t)
        if s.startswith(ODI) and s != ODI and t not in declared:
            rpt.add(ERROR, "O002", "Term used in the ontology but never declared "
                                   "(no rdf:type owl:Class/Property)",
                    qn(t) + hint(local_name(t), declared_local))
        elif is_std(t) and not std_term_defined(t):
            rpt.add(ERROR, "O003", "Undefined term of a standard vocabulary", qn(t))

    # --- entity documentation -----------------------------------------------
    for e in sorted(declared, key=str):
        labels = [l for l in g.objects(e, RDFS.label) if isinstance(l, Literal)]
        comments = [c for c in g.objects(e, RDFS.comment) if isinstance(c, Literal)]
        if not labels:
            rpt.add(WARNING, "O010", "Entity without rdfs:label", qn(e))
        if not comments:
            rpt.add(WARNING, "O011", "Entity without rdfs:comment", qn(e))
        for lang in ("it", "en"):
            if labels and not any(l.language == lang for l in labels):
                rpt.add(WARNING, "O012", "Missing label in a language", f"{qn(e)} ({lang})")
            if comments and not any(c.language == lang for c in comments):
                rpt.add(WARNING, "O013", "Missing comment in a language", f"{qn(e)} ({lang})")
        for l in labels:
            if not l.language:
                rpt.add(WARNING, "O014", "rdfs:label without language tag", f"{qn(e)}: {l}")
        for c in comments:
            if not c.language:
                rpt.add(WARNING, "O015", "rdfs:comment without language tag",
                        f"{qn(e)}: {str(c)[:60]}")
            if str(c).strip().lower() in {str(l).strip().lower() for l in labels}:
                rpt.add(WARNING, "O016", "Comment identical to a label (placeholder?)",
                        f"{qn(e)}: {c}")
        # naming conventions
        ln = local_name(e)
        if e in O.classes and ln[:1].islower():
            rpt.add(WARNING, "O017", "Class name should start with an uppercase letter", qn(e))
        if e in O.props and ln[:1].isupper():
            rpt.add(WARNING, "O018", "Property name should start with a lowercase letter", qn(e))
        # english label vs local name
        en = [str(l) for l in labels if l.language == "en"]
        if en and re.sub(r"[^a-z0-9]", "", en[0].lower()) != ln.lower():
            rpt.add(INFO, "O019", "English label does not match the term's local name",
                    f"{qn(e)} vs '{en[0]}'")

    # --- duplicate labels -----------------------------------------------------
    by_label = defaultdict(set)
    for e in declared:
        for l in g.objects(e, RDFS.label):
            if isinstance(l, Literal):
                by_label[(l.language, str(l).strip().lower())].add(e)
    for (lang, lab), ents in by_label.items():
        if len(ents) > 1:
            rpt.add(WARNING, "O020", "Same label on different entities",
                    f"'{lab}'@{lang}: {', '.join(sorted(qn(x) for x in ents))}")

    # --- near-duplicate names --------------------------------------------------
    ds = sorted(declared, key=str)
    for i, a in enumerate(ds):
        for b in ds[i + 1:]:
            la, lb = local_name(a), local_name(b)
            if la.lower() == lb.lower():
                rpt.add(WARNING, "O021", "Names differing only by case", f"{qn(a)} / {qn(b)}")

    # --- kind consistency ------------------------------------------------------
    for p in sorted(O.obj_props & O.data_props, key=str):
        rpt.add(ERROR, "O030", "Property declared both Object and Datatype property", qn(p))
    for e in sorted(O.classes & O.props, key=str):
        rpt.add(ERROR, "O031", "Entity declared both as class and as property", qn(e))

    # --- domain / range ---------------------------------------------------------
    def class_ok(c):
        return c in O.classes or c == OWL.Thing or c == RDFS.Literal or \
            str(c).startswith(str(XSD)) or c == RDFS.Resource

    for p in sorted(O.props, key=str):
        if p in O.ann_props:
            continue
        D, R = O.domains[p], O.ranges[p]
        kind = "object" if p in O.obj_props else "datatype"
        if not D:
            rpt.add(WARNING, "O040", f"{kind.capitalize()} property without rdfs:domain", qn(p))
        if not R:
            rpt.add(WARNING, "O041", f"{kind.capitalize()} property without rdfs:range", qn(p))
        for c in D | R:
            if isinstance(c, URIRef) and not class_ok(c):
                rpt.add(ERROR, "O042", "Domain/range refers to an undeclared class",
                        f"{qn(p)} -> {qn(c)}" + hint(local_name(c), declared_local))
            if c == OWL.Thing:
                rpt.add(INFO, "O043", "Domain/range is owl:Thing (too generic?)", qn(p))
        if p in O.obj_props:
            for c in R:
                if str(c).startswith(str(XSD)) or c == RDFS.Literal:
                    rpt.add(ERROR, "O044", "Object property with a datatype as range",
                            f"{qn(p)} -> {qn(c)}")
        if p in O.data_props:
            for c in R:
                if c in O.classes:
                    rpt.add(ERROR, "O045", "Datatype property with a class as range",
                            f"{qn(p)} -> {qn(c)}")
        if len(D) > 1:
            rpt.add(WARNING, "O046", "Multiple rdfs:domain = INTERSECTION in RDFS/OWL "
                                     "(if you meant 'either', use owl:unionOf)",
                    f"{qn(p)}: {', '.join(sorted(qn(c) for c in D))}")
        if len(R) > 1:
            rpt.add(WARNING, "O047", "Multiple rdfs:range = INTERSECTION in RDFS/OWL "
                                     "(if you meant 'either', use owl:unionOf)",
                    f"{qn(p)}: {', '.join(sorted(qn(c) for c in R))}")
        # property linking a class with its own sub/superclass
        if p in O.obj_props:
            for d in D:
                for r in R:
                    if d != r and (r in O.ancestors(d) or d in O.ancestors(r)):
                        rpt.add(WARNING, "O048", "Object property links a class with its own "
                                                 "sub/superclass (suspicious hierarchy?)",
                                f"{qn(p)}: {qn(d)} -> {qn(r)}")
        if p in O.data_props and not any(g.objects(p, RDFS.subPropertyOf)):
            rpt.add(INFO, "O049", "Datatype property without rdfs:subPropertyOf", qn(p))

    # --- cycles -----------------------------------------------------------------
    top = {OWL.topObjectProperty, OWL.topDataProperty}
    for c in O.classes:
        if c in strict_reach(g, c, RDFS.subClassOf):
            rpt.add(ERROR, "O050", "Cycle in rdfs:subClassOf", qn(c))
    for p in O.props:
        if p in strict_reach(g, p, RDFS.subPropertyOf):
            rpt.add(ERROR, "O051", "Cycle in rdfs:subPropertyOf", qn(p))
    for t in top:
        if (t, RDFS.subPropertyOf, t) in g:
            rpt.add(INFO, "O052", "owl:top*Property is a subproperty of itself "
                                  "(harmless artefact of the OWL API)", qn(t))
    for c in O.classes:
        for sup in g.objects(c, RDFS.subClassOf):
            if isinstance(sup, URIRef) and sup != OWL.Thing and sup not in O.classes:
                rpt.add(ERROR, "O053", "subClassOf an undeclared class",
                        f"{qn(c)} -> {qn(sup)}")

    # --- inverses ----------------------------------------------------------------
    done = set()
    for a, bs in O.inverse.items():
        for b in bs:
            if (b, a) in done:
                continue
            done.add((a, b))
            if not ((a, OWL.inverseOf, b) in g and (b, OWL.inverseOf, a) in g):
                rpt.add(INFO, "O060", "owl:inverseOf declared in one direction only "
                                      "(fine for OWL, explicit for humans)", f"{qn(a)} <-> {qn(b)}")
            if O.domains.get(a) != O.ranges.get(b) or O.ranges.get(a) != O.domains.get(b):
                rpt.add(WARNING, "O061", "Inverse properties: domain/range are not swapped",
                        f"{qn(a)} <-> {qn(b)}")

    # --- classes -----------------------------------------------------------------
    for a, b in sorted(O.disjoint):
        if b in O.ancestors(a) or a in O.ancestors(b):
            rpt.add(ERROR, "O070", "Disjoint classes that are also in a subclass relation",
                    f"{qn(a)} / {qn(b)}")


# --------------------------------------------------------------------------- #
# mapping.json checks
# --------------------------------------------------------------------------- #
KNOWN_RULE_TYPES = ("class", "object_property", "data_property", "rdf_type",
                    "generic_relation_column", "generic_relation_target",
                    "object_property_target", "object_property_new_subject", 
                    "subject_only", "label_of_target")


def check_mapping(path, O, rpt):
    path = Path(path)
    try:
        mapping = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:  # noqa: BLE001
        rpt.add(ERROR, "M000", "mapping.json cannot be read", str(e))
        return
    cls_local = [local_name(c) for c in O.classes]
    prop_local = [local_name(p) for p in O.props]

    def resolve(cur):
        if not isinstance(cur, str) or ":" not in cur:
            return None
        pfx, loc = cur.split(":", 1)
        return URIRef(ODI + loc) if pfx == "odi" else None

    def check_class(cur, ctx, code="M010"):
        u = resolve(cur)
        if u is not None and u not in O.classes:
            rpt.add(ERROR, code, "Mapping refers to a class missing from the ontology",
                    f"{ctx}: {cur}" + hint(local_name(u), cls_local))

    for fname, cols in mapping.items():
        file_cls = None
        for key, rule in cols.items():
            if isinstance(rule, dict) and rule.get("type") == "class" and key.startswith("odi:"):
                file_cls = resolve(rule.get("rdf_type", key))
        for key, rule in cols.items():
            ctx = f"{fname} / {key}"
            if not isinstance(rule, dict) or "type" not in rule:
                rpt.add(ERROR, "M001", "Mapping rule without \"type\"", ctx)
                continue
            rtype = rule["type"]
            if not rtype.startswith(KNOWN_RULE_TYPES) and "nuova istanza" not in rtype:
                rpt.add(WARNING, "M002", "Rule type not handled by csv_to_rdf.py", f"{ctx}: {rtype}")
            if rtype in ("class", "subject_only"):
                if key.startswith("odi:"):
                    check_class(key, ctx)
                if "rdf_type" in rule:
                    check_class(rule["rdf_type"], ctx)
                continue
            if rtype == "rdf_type":
                for v, target in rule.get("value_mapping", {}).items():
                    check_class(target, f"{ctx}[{v}]")
                continue
            if rtype.startswith("generic_relation") or rtype == "object_property_target":
                note = rule.get("note", "")
                names = re.findall(r"odi:(\w+)", note)
                m = re.search(r"ontologia:\s*(.+)$", note)
                if m:
                    names += [x.strip() for x in m.group(1).split(",") if re.fullmatch(r"\w+", x.strip())]
                for nme in names:
                    if O.term(nme) not in O.obj_props:
                        rpt.add(ERROR, "M020", "Candidate relation in mapping note is not an "
                                               "object property of the ontology",
                                f"{ctx}: {nme}" + hint(nme, prop_local))
                if "range" in rule:
                    check_class(rule["range"], ctx)
                continue
            # ordinary properties
            if not key.startswith("odi:"):
                continue  # e.g. meaningLabel (handled specially by the script)
            p = resolve(key)
            if p not in O.props:
                rpt.add(ERROR, "M021", "Mapping refers to a property missing from the ontology",
                        ctx + hint(local_name(p), prop_local))
                continue
            if rtype.startswith("object_property") and p not in O.obj_props:
                rpt.add(ERROR, "M022", "Mapped as object property but the ontology says otherwise", ctx)
            if rtype.startswith("data_property") and p not in O.data_props:
                rpt.add(ERROR, "M023", "Mapped as data property but the ontology says otherwise", ctx)
            dom = rule.get("domain")
            if dom:
                check_class(dom, ctx, "M011")
                du = resolve(dom)
                if du in O.classes and O.domains[p] and du not in O.domains[p]:
                    rpt.add(WARNING, "M030", "Mapping domain differs from the ontology's domain",
                            f"{ctx}: mapping={dom}, ontology={sorted(qn(x) for x in O.domains[p])}")
            rng = rule.get("range")
            if rng:
                check_class(rng, ctx, "M012")
                for part in re.split(r"\s+o\s+|,", rng):
                    ru = resolve(part.strip())
                    if ru in O.classes and O.ranges[p] and ru not in O.ranges[p]:
                        rpt.add(WARNING, "M031", "Mapping range differs from the ontology's range",
                                f"{ctx}: mapping={part.strip()}, ontology={sorted(qn(x) for x in O.ranges[p])}")
            dt = rule.get("datatype")
            if dt and O.ranges[p]:
                if dt.startswith("xsd:") and XSD[dt[4:]] not in O.ranges[p]:
                    rpt.add(WARNING, "M032", "Mapping datatype differs from the ontology's range",
                            f"{ctx}: mapping={dt}, ontology={sorted(qn(x) for x in O.ranges[p])}")
            # is the property applicable to the class of the file's rows?
            if file_cls is not None and O.domains[p] and not (O.ancestors(file_cls) & O.domains[p]):
                rpt.add(WARNING, "M033", "Property's ontology domain does not cover the class "
                                         "of the rows of this file",
                        f"{ctx}: file class={qn(file_cls)}, domain={sorted(qn(x) for x in O.domains[p])}")


# --------------------------------------------------------------------------- #
# Knowledge graph checks
# --------------------------------------------------------------------------- #
def check_kg(kg, O, rpt, cfg):
    types = defaultdict(set)
    for s, o in kg.subject_objects(RDF.type):
        types[s].add(o)
    _cl = {}

    def closure(n):
        if n not in _cl:
            out = set()
            for t in types.get(n, ()):
                out |= O.ancestors(t)
            _cl[n] = out
        return _cl[n]

    def is_individual(n):
        s = str(n)
        return isinstance(n, URIRef) and not s.startswith(ODI) and not is_std(n)

    prop_local = [local_name(p) for p in O.props]
    cls_local = [local_name(c) for c in O.classes]
    functional = set(O.functional) | {O.term(x) for x in cfg["functional"]}

    unknown_pred, unknown_cls = defaultdict(list), defaultdict(list)
    used_props, used_classes = Counter(), Counter()
    subjects, edges, ref_from = set(), [], {}
    pv = defaultdict(set)                     # (s, p) -> {o}
    viol = defaultdict(list)                  # domain/range violations
    lit_issues = defaultdict(list)
    self_loops = []

    def lit_check(s, p, o):
        txt = str(o)
        if txt != txt.strip():
            lit_issues["Leading/trailing whitespace"].append(f"{qn(s)} {qn(p)} {txt!r}")
        if not txt.strip():
            lit_issues["Empty literal"].append(f"{qn(s)} {qn(p)}")
        elif txt.strip().lower() in PLACEHOLDERS:
            lit_issues["Placeholder value (nan/None/null/...)"].append(f"{qn(s)} {qn(p)} {txt!r}")
        if len(txt.strip()) >= 2 and txt.strip()[0] == '"' and txt.strip()[-1] == '"':
            lit_issues["Value wrapped in literal straight quotes (CSV artefact)"].append(
                f"{qn(s)} {qn(p)} {txt!r}")

    for s, p, o in kg:
        subjects.add(s)
        if isinstance(s, Literal):
            rpt.add(ERROR, "K000", "Literal as subject", qn(s))
            continue
        if isinstance(o, Literal):
            lit_check(s, p, o)
        if isinstance(s, BNode):
            rpt.add(INFO, "K004", "Blank node used as subject", qn(s))

        if p == RDF.type:
            if not isinstance(o, URIRef):
                rpt.add(ERROR, "K005", "rdf:type with a non-URI object", f"{qn(s)} -> {qn(o)}")
                continue
            used_classes[o] += 1
            if o not in O.classes and not (is_std(o) and std_term_defined(o)):
                unknown_cls[o].append(qn(s))
            continue

        if is_std(p):
            if not std_term_defined(p):
                unknown_pred[p].append(f"{qn(s)} {qn(p)} {qn(o)}")
            continue

        if p not in O.props:
            unknown_pred[p].append(f"{qn(s)} {qn(p)} {qn(o)}")
            continue
        used_props[p] += 1
        pv[(s, p)].add(o)

        if p in O.obj_props:
            if isinstance(o, Literal):
                rpt.add(ERROR, "K010", "Object property with a literal value",
                        f"{qn(s)} {qn(p)} {qn(o)}")
                continue
            edges.append((s, p, o))
            ref_from.setdefault(o, (s, p))
            if s == o:
                self_loops.append(f"{qn(s)} {qn(p)}")
            D, R = O.domains.get(p, set()), O.ranges.get(p, set())
            ts = closure(s)
            if D and ts and not (ts & D):
                viol[(qn(p), "domain", tuple(sorted(qn(t) for t in types[s])),
                      tuple(sorted(qn(d) for d in D)))].append(f"{qn(s)} -> {qn(o)}")
            to = closure(o)
            if R and to and not (to & R):
                viol[(qn(p), "range", tuple(sorted(qn(t) for t in types[o])),
                      tuple(sorted(qn(r) for r in R)))].append(f"{qn(s)} -> {qn(o)}")
        elif p in O.data_props:
            if not isinstance(o, Literal):
                rpt.add(ERROR, "K011", "Datatype property with a resource value",
                        f"{qn(s)} {qn(p)} {qn(o)}")
                continue
            D = O.domains.get(p, set())
            ts = closure(s)
            if D and ts and not (ts & D):
                viol[(qn(p), "domain", tuple(sorted(qn(t) for t in types[s])),
                      tuple(sorted(qn(d) for d in D)))].append(f"{qn(s)} {qn(o)}")
            for r in O.ranges.get(p, set()):
                dt = o.datatype
                ok = (dt == r) or (r == XSD.integer and dt in INT_TYPES) or \
                     (r == XSD.decimal and (dt in INT_TYPES or dt == XSD.decimal)) or \
                     (r == XSD.string and dt is None)
                if not ok:
                    what = "plain literal" if dt is None else qn(dt)
                    rpt.add(ERROR, "K012", "Literal datatype differs from the property's range",
                            f"{qn(s)} {qn(p)} {str(o)!r}: found {what}, expected {qn(r)}")
                    continue
                ill = getattr(o, "ill_typed", None)
                if ill is None:
                    ill = dt in INT_TYPES | {XSD.decimal, XSD.double, XSD.boolean, XSD.date,
                                             XSD.dateTime} and o.value is None
                if ill:
                    rpt.add(ERROR, "K013", "Ill-formed literal for its datatype",
                            f"{qn(s)} {qn(p)} {str(o)!r} ^^{qn(dt)}")
                if r == XSD.anyURI and re.search(r"\s", str(o)):
                    rpt.add(WARNING, "K014", "anyURI value contains whitespace",
                            f"{qn(s)} {qn(p)} {str(o)!r}")
        # annotation props: nothing more to check

    for pred, ex in unknown_pred.items():
        rpt.add(ERROR, "K001", "Unknown predicate (not declared in the ontology)",
                f"{qn(pred)} x{len(ex)}, e.g. {ex[0]}" + hint(local_name(pred), prop_local))
    for c, ex in unknown_cls.items():
        rpt.add(ERROR, "K002", "Unknown class in rdf:type (not declared in the ontology)",
                f"{qn(c)} x{len(ex)}, e.g. {ex[0]}" + hint(local_name(c), cls_local))
    for (p, kind, found, expected), ex in sorted(viol.items()):
        rpt.add(ERROR, "K020" if kind == "domain" else "K021",
                f"{kind.capitalize()} violation (asserted types + subclass closure)",
                f"{p}: {kind} should be one of {list(expected)}, found {list(found)} "
                f"x{len(ex)}, e.g. {ex[0]}")
    for issue, ex in lit_issues.items():
        for e in ex:
            rpt.add(WARNING, "K030", f"Literal hygiene: {issue}", e)
    for sl in self_loops:
        rpt.add(WARNING, "K031", "Self-loop on an object property", sl)

    # --- individuals: dangling / untyped / isolated ------------------------------
    nodes = {n for n in subjects if is_individual(n)} | {o for _, _, o in edges if is_individual(o)}
    for n in sorted(nodes, key=str):
        if n not in subjects:
            s, p = ref_from[n]
            rpt.add(ERROR, "K040", "Referenced but never defined (no triple has it as subject "
                                   "- missing CSV row / ID mismatch?)",
                    f"{qn(n)} <- {qn(s)} {qn(p)}")
    for n in sorted((n for n in nodes if n in subjects and n not in types), key=str):
        rpt.add(WARNING, "K041", "Individual without rdf:type", qn(n))

    deg = Counter()
    parent = {n: n for n in nodes}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    incoming = Counter()
    for s, p, o in edges:
        incoming[o] += 1
        if s in parent and o in parent:
            deg[s] += 1
            deg[o] += 1
            parent[find(s)] = find(o)
    for n in sorted(nodes, key=str):
        if deg[n] == 0:
            rpt.add(WARNING, "K042", "Isolated individual (no relations to other individuals)",
                    f"{qn(n)} types={sorted(qn(t) for t in types.get(n, []))}")
    comps = Counter(find(n) for n in nodes)
    sizes = Counter(comps.values())
    rpt.add(INFO, "K043", "Connected components (by size)",
            ", ".join(f"size {k}: {v}" for k, v in sorted(sizes.items(), reverse=True)[:10]))
    roots = defaultdict(int)
    for n in nodes:
        if n in subjects and incoming[n] == 0:
            for t in types.get(n, ["<untyped>"]):
                roots[qn(t)] += 1
    if roots:
        rpt.add(INFO, "K044", "Individuals never referenced by others (per class; fine for "
                              "roots such as Edition/TarotDeck)",
                ", ".join(f"{k}: {v}" for k, v in sorted(roots.items())))

    # --- typing consistency --------------------------------------------------------
    pair_ex = defaultdict(list)
    for n, ts in types.items():
        ts = [t for t in ts if t in O.classes]
        for i, a in enumerate(ts):
            for b in ts[i + 1:]:
                if a in O.ancestors(b) or b in O.ancestors(a):
                    continue
                key = tuple(sorted((qn(a), qn(b))))
                sev = ERROR if (a, b) in O.disjoint else WARNING
                pair_ex[(sev, key)].append(qn(n))
    for (sev, key), ex in pair_ex.items():
        rpt.add(sev, "K050", "Individual typed with unrelated classes"
                + (" (declared disjoint!)" if sev == ERROR else ""),
                f"{' + '.join(key)} x{len(ex)}, e.g. {ex[0]}")
    abstract = {O.term(x) for x in cfg["abstract_classes"]}
    for n, ts in sorted(types.items(), key=lambda kv: str(kv[0])):
        if ts and ts <= abstract:
            rpt.add(WARNING, "K051", "Individual typed only with an abstract/generic class "
                                     "(missing specific subclass)",
                    f"{qn(n)}: {sorted(qn(t) for t in ts)}")

    # --- cardinality / completeness --------------------------------------------------
    for (s, p), vals in sorted(pv.items(), key=lambda kv: (str(kv[0][0]), str(kv[0][1]))):
        if p in functional and len(vals) > 1:
            rpt.add(WARNING, "K060", "Property expected to be single-valued has several values",
                    f"{qn(s)} {qn(p)}: {sorted(qn(v) for v in vals)}")
    have = defaultdict(set)
    for (s, p) in pv:
        have[s].add(p)
    for cname, plist in cfg["required"].items():
        c = O.term(cname)
        if c not in O.classes:
            continue
        for n in sorted((n for n in types if c in closure(n)), key=str):
            for pn in plist:
                if O.term(pn) not in have[n]:
                    rpt.add(WARNING, "K061", "Missing expected property for class",
                            f"{qn(n)} ({cname}) lacks odi:{pn}")

    # --- inverses --------------------------------------------------------------------
    inv_missing = Counter()
    inv_ex = {}
    for s, p, o in edges:
        for q in O.inverse.get(p, ()):
            if (o, q, s) not in kg:
                inv_missing[(qn(p), qn(q))] += 1
                inv_ex.setdefault((qn(p), qn(q)), f"{qn(s)} {qn(p)} {qn(o)}")
    for (p, q), n in inv_missing.items():
        rpt.add(INFO, "K070", "Inverse triple not materialised (only matters without a reasoner)",
                f"{p} has no {q} counterpart x{n}, e.g. {inv_ex[(p, q)]}")

    # --- usage -------------------------------------------------------------------------
    for c in sorted(O.classes, key=str):
        if used_classes[c] == 0:
            rpt.add(INFO, "K080", "Ontology class never instantiated (directly)", qn(c))
    for p in sorted(O.props, key=str):
        if used_props[p] == 0 and p not in O.ann_props:
            rpt.add(INFO, "K081", "Ontology property never used in the KG", qn(p))

    # --- URI hygiene ---------------------------------------------------------------------
    norm = defaultdict(set)
    for n in nodes:
        s = str(n)
        if not s.startswith(DATA):
            rpt.add(WARNING, "K090", "Individual outside the expected data namespace", qn(n))
            continue
        loc = s[len(DATA):]
        if re.search(r"[^A-Za-z0-9_\-.~%]", loc):
            rpt.add(WARNING, "K091", "URI local part contains unusual characters", qn(n))
        norm[re.sub(r"[_\-\s]", "", strip_accents(loc).lower())].add(n)
    for k, group in norm.items():
        if len(group) > 1:
            rpt.add(WARNING, "K092", "URIs differing only by case/accents/separators "
                                     "(probable duplicate entity)",
                    ", ".join(sorted(qn(x) for x in group)))

    # --- duplicates by label ---------------------------------------------------------------
    by_label = defaultdict(set)
    for s, o in kg.subject_objects(RDFS.label):
        for t in types.get(s, {None}):
            by_label[(t, str(o).strip().lower())].add(s)
    for (t, lab), ss in by_label.items():
        if len(ss) > 1:
            rpt.add(WARNING, "K093", "Several individuals of the same class share a label "
                                     "(duplicates?)",
                    f"{qn(t) if t else '<untyped>'} '{lab}': {', '.join(sorted(qn(x) for x in ss))}")
    for m in kg.subjects(RDF.type, O.term("Meaning")):
        if not any(kg.objects(m, RDFS.label)):
            rpt.add(WARNING, "K094", "Meaning without rdfs:label", qn(m))

    # --- statistics ---------------------------------------------------------------------------
    rpt.add(INFO, "K100", "Statistics",
            f"{len(kg)} triples, {len(nodes)} individuals, {len(used_props)} properties used, "
            f"{len(used_classes)} classes used")
    for c, n in sorted(used_classes.items(), key=lambda kv: -kv[1]):
        rpt.add(INFO, "K101", "Instances per class", f"{qn(c)}: {n}")

    return types, closure


# --------------------------------------------------------------------------- #
# Domain-specific consistency (book / tarot model)
# --------------------------------------------------------------------------- #
def check_domain(kg, O, rpt, types, closure):
    T = O.term

    def inst(cname):
        c = T(cname)
        return sorted((n for n in types if c in closure(n)), key=str) if c in O.classes else []

    # Story: declared total vs actual cards; positions
    for story in inst("Story"):
        cards = set(kg.subjects(T("isACardOf"), story)) | set(kg.objects(story, T("hasCard")))
        for tot in kg.objects(story, T("hasTotalNumberOfCards")):
            n = to_int(tot)
            if n is not None and n != len(cards):
                rpt.add(WARNING, "D001", "Story: hasTotalNumberOfCards != number of linked "
                                         "Storycards", f"{qn(story)}: declared {n}, found {len(cards)}")
        pos = []
        for c in cards:
            pos += [to_int(x) for x in kg.objects(c, T("hasPositionInTheText"))]
        pos = [p for p in pos if p is not None]
        if pos:
            dup = [p for p, k in Counter(pos).items() if k > 1]
            if dup:
                rpt.add(WARNING, "D002", "Story: duplicate positions in the text",
                        f"{qn(story)}: {sorted(dup)}")
            missing = sorted(set(range(1, max(pos) + 1)) - set(pos))
            if missing:
                rpt.add(WARNING, "D003", "Story: gaps in card positions (1..max)",
                        f"{qn(story)}: missing {missing}")
    # Storycard belongs to exactly one story
    for sc in inst("Storycard"):
        if len(set(kg.objects(sc, T("isACardOf")))) > 1:
            rpt.add(WARNING, "D004", "Storycard belongs to several stories", qn(sc))
    # Deck counts
    for deck in inst("TarotDeck"):
        cards = set(kg.subjects(T("isContainedIn"), deck)) | set(kg.objects(deck, T("contains")))
        cur = [to_int(x) for x in kg.objects(deck, T("hasCurrentNumberOfCards"))]
        org = [to_int(x) for x in kg.objects(deck, T("hasOriginalNumberOfCards"))]
        if cur and cur[0] is not None and cur[0] != len(cards):
            rpt.add(WARNING, "D010", "Deck: hasCurrentNumberOfCards != DeckCards linked to it",
                    f"{qn(deck)}: declared {cur[0]}, found {len(cards)}")
        if cur and org and None not in (cur[0], org[0]) and cur[0] > org[0]:
            rpt.add(ERROR, "D011", "Deck: current number of cards > original number",
                    f"{qn(deck)}: current {cur[0]}, original {org[0]}")
    # Deck cards: 'isNumber' only makes sense for numeral cards (soft check)
    for dc in inst("DeckCard"):
        if not any(kg.objects(dc, T("isContainedIn"))):
            continue
    # Chapters / editions
    for ch in inst("Chapter"):
        if not any(kg.objects(ch, T("includes"))):
            rpt.add(WARNING, "D020", "Chapter that includes no Story", qn(ch))
    for ed in inst("Edition"):
        if not any(kg.objects(ed, T("hasChapter"))):
            rpt.add(WARNING, "D021", "Edition without chapters", qn(ed))
    chapters_used = set(kg.objects(None, T("hasChapter")))
    for ch in inst("Chapter"):
        if ch not in chapters_used:
            rpt.add(WARNING, "D022", "Chapter not attached to any Edition (hasChapter)", qn(ch))
    stories_used = set(kg.objects(None, T("includes")))
    for st in inst("Story"):
        if st not in stories_used:
            rpt.add(WARNING, "D023", "Story not included in any Chapter", qn(st))
    # Representations
    carried = set(kg.objects(None, T("carriesRepresentation")))
    for r in inst("Representation"):
        if r not in carried:
            rpt.add(WARNING, "D030", "Representation not carried by any Storycard", qn(r))
    # represents: Character -> Person, FinctionalPlace -> Place
    for s, o in kg.subject_objects(T("represents")):
        cs, co = closure(s), closure(o)
        if T("Character") in cs and co and T("Person") not in co:
            rpt.add(WARNING, "D031", "Character represents something that is not a Person",
                    f"{qn(s)} -> {qn(o)}")
        if T("FinctionalPlace") in cs and co and T("Place") not in co:
            rpt.add(WARNING, "D032", "Fictional place represents something that is not a Place",
                    f"{qn(s)} -> {qn(o)}")
    # Relations between Representations must stay in the same story (via cards)
    carrier = defaultdict(set)
    for sc, r in kg.subject_objects(T("carriesRepresentation")):
        carrier[r] |= set(kg.objects(sc, T("isACardOf")))
    rel_props = [p for p in O.obj_props if O.domains.get(p) and
                 any(T("Character") in O.ancestors(d) or d == T("Representation")
                     for d in O.domains[p])]
    for p in rel_props:
        for s, o in kg.subject_objects(p):
            if carrier.get(s) and carrier.get(o) and not (carrier[s] & carrier[o]):
                rpt.add(WARNING, "D040", "Relation between Representations of different stories",
                        f"{qn(s)} {qn(p)} {qn(o)}")


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description="Validate ontology, knowledge graph and mapping.")
    ap.add_argument("--ontology", default="./odiontology.ttl", help="ontology file")
    ap.add_argument("--kg", default="./taverna_data.ttl", help="knowledge graph file")
    ap.add_argument("--mapping", default="./mapping/mapping.json", help="mapping.json used by csv_to_rdf.py")
    ap.add_argument("--json", help="write the report as JSON")
    ap.add_argument("--max-examples", type=int, default=15)
    ap.add_argument("--strict", action="store_true", help="exit 1 also on warnings")
    ap.add_argument("--level", choices=["ERROR", "WARNING", "INFO"], default="INFO",
                help="Livello minimo da visualizzare (default: INFO)")
    args = ap.parse_args()

    rpt = Report()
    og = load_graph(args.ontology, "Ontology", rpt)
    O = Onto(og) if og is not None else None
    if O:
        check_ontology(og, O, rpt)
        rpt.add(INFO, "O100", "Ontology statistics",
                f"{len(og)} triples, {len(O.classes)} classes, {len(O.obj_props)} object "
                f"properties, {len(O.data_props)} datatype properties")
    if args.mapping:
        if O:
            check_mapping(args.mapping, O, rpt)
        else:
            rpt.add(WARNING, "M999", "Mapping check skipped (ontology not loaded)")
    if args.kg:
        kg = load_graph(args.kg, "Knowledge graph", rpt)
        if kg is not None and O:
            types, closure = check_kg(kg, O, rpt, CONFIG)
            check_domain(kg, O, rpt, types, closure)
        elif kg is not None:
            rpt.add(WARNING, "K999", "KG checks skipped (ontology not loaded)")

    rpt.print(args.max_examples, min_level=args.level)
    if args.json:
        Path(args.json).write_text(json.dumps(rpt.to_json(), indent=2, ensure_ascii=False),
                                   encoding="utf-8")
        print(f"JSON report written to {args.json}")
    sys.exit(1 if rpt.count(ERROR) or (args.strict and rpt.count(WARNING)) else 0)


if __name__ == "__main__":
    main()
