"""extract_unit.py <tla-ts>/packages/tla-ts/tests/unit <out-suite-dir>

Reads upstream's unit tests as text (never runs them) and writes each check({...}) call whose
source and config it can evaluate statically as a conformance-format test file:
<out>/tlc/unit/<file>/<n>.tla with a YAML header (outcome: any, config, args).
Parameters of an enclosing it.each/test.each table are bound row by row.
"""
import json
import os
import re
import sys

# ---- a small JS tokenizer and literal evaluator


class Unknown(Exception):
    pass


def skip_ws(s, i):
    while i < len(s):
        if s[i].isspace():
            i += 1
        elif s.startswith("//", i):
            j = s.find("\n", i)
            i = len(s) if j < 0 else j + 1
        elif s.startswith("/*", i):
            j = s.find("*/", i + 2)
            i = len(s) if j < 0 else j + 2
        else:
            break
    return i


ESC = {"n": "\n", "t": "\t", "r": "\r", "\\": "\\", "'": "'", '"': '"', "`": "`", "$": "$", "0": "\0", "b": "\b", "f": "\f", "v": "\v"}


def read_string(s, i):
    q = s[i]
    i += 1
    out = []
    while s[i] != q:
        if s[i] == "\\":
            c = s[i + 1]
            if c == "u":
                if s[i + 2] == "{":
                    j = s.index("}", i)
                    out.append(chr(int(s[i + 3:j], 16)))
                    i = j + 1
                else:
                    out.append(chr(int(s[i + 2:i + 6], 16)))
                    i += 6
                continue
            if c == "x":
                out.append(chr(int(s[i + 2:i + 4], 16)))
                i += 4
                continue
            if c == "\n":
                i += 2
                continue
            out.append(ESC.get(c, c))
            i += 2
        else:
            out.append(s[i])
            i += 1
    return "".join(out), i + 1


def read_template(s, i):
    """Returns ([str | expr-source], end)."""
    i += 1
    parts = []
    cur = []
    while s[i] != "`":
        if s[i] == "\\":
            c = s[i + 1]
            if c == "u":
                out, _ = read_string('"' + s[i:i + 6] + '"', 0)
                cur.append(out)
                i += 6
                continue
            cur.append(ESC.get(c, c))
            i += 2
        elif s.startswith("${", i):
            parts.append("".join(cur))
            cur = []
            j = match_brace(s, i + 1)
            parts.append(("expr", s[i + 2:j]))
            i = j + 1
        else:
            cur.append(s[i])
            i += 1
    parts.append("".join(cur))
    return parts, i + 1


def match_brace(s, i):
    """s[i] is an opening bracket; returns the index of its match."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = [pairs[s[i]]]
    i += 1
    while stack:
        i = skip_ws(s, i)
        c = s[i]
        if c in "\"'":
            _, i = read_string(s, i)
            continue
        if c == "`":
            _, i = read_template(s, i)
            continue
        if c in pairs:
            stack.append(pairs[c])
        elif c in ")]}":
            if c != stack.pop():
                raise Unknown("unbalanced")
            if not stack:
                return i
        elif c == "/" and is_regex_start(s, i):
            i = skip_regex(s, i)
            continue
        i += 1
    raise Unknown("eof")


def is_regex_start(s, i):
    j = i - 1
    while j >= 0 and s[j].isspace():
        j -= 1
    return j < 0 or s[j] in "(,=:[!&|?{};"


def skip_regex(s, i):
    i += 1
    in_class = False
    while True:
        c = s[i]
        if c == "\\":
            i += 2
            continue
        if c == "[":
            in_class = True
        elif c == "]":
            in_class = False
        elif c == "/" and not in_class:
            i += 1
            while i < len(s) and s[i].isalpha():
                i += 1
            return i
        elif c == "\n":
            return i
        i += 1


class Evaluator:
    def __init__(self, env):
        self.env = env

    def eval(self, text):
        self.s = text
        v, i = self.expr(0)
        i = skip_ws(text, i)
        if i != len(text):
            raise Unknown("trailing " + text[i:i + 30])
        return v

    def expr(self, i):
        v, i = self.term(i)
        while True:
            j = skip_ws(self.s, i)
            if j < len(self.s) and self.s[j] == "+" and not self.s.startswith("++", j):
                w, i = self.term(j + 1)
                if isinstance(v, str) or isinstance(w, str):
                    v = to_str(v) + to_str(w)
                else:
                    v = v + w
            elif self.s.startswith("??", j):
                w, i = self.term(j + 2)
                v = w if v is None else v
            else:
                return v, j

    def term(self, i):
        s = self.s
        i = skip_ws(s, i)
        c = s[i]
        if c in "\"'":
            v, i = read_string(s, i)
        elif c == "`":
            parts, i = read_template(s, i)
            v = "".join(p if isinstance(p, str) else to_str(Evaluator(self.env).eval(p[1])) for p in parts)
        elif c == "[":
            j = match_brace(s, i)
            v = [Evaluator(self.env).eval(x) for x in split_top(s[i + 1:j])]
            i = j + 1
        elif c == "{":
            j = match_brace(s, i)
            v = parse_object(s[i + 1:j], self.env, strict=True)
            i = j + 1
        elif c == "(":
            j = match_brace(s, i)
            v = Evaluator(self.env).eval(s[i + 1:j])
            i = j + 1
        elif c == "-" or c.isdigit():
            m = re.compile(r"-?\d[\d_]*(\.\d+)?n?").match(s, i)
            if not m:
                raise Unknown("number")
            t = m.group(0).replace("_", "")
            v = int(t.rstrip("n")) if "." not in t else float(t)
            i = m.end()
        else:
            m = re.compile(r"[A-Za-z_$][\w$]*").match(s, i)
            if not m:
                raise Unknown("token " + s[i:i + 20])
            name = m.group(0)
            i = m.end()
            if name == "true":
                v = True
            elif name == "false":
                v = False
            elif name in ("undefined", "null"):
                v = None
            elif name == "BigInt":
                j = skip_ws(s, i)
                k = match_brace(s, j)
                v = int(Evaluator(self.env).eval(s[j + 1:k]))
                i = k + 1
            elif name in self.env:
                v = self.env[name]
            else:
                raise Unknown("name " + name)
        # postfix: .join(x), .repeat(n), .trim(), [n], .length, .map not supported
        while True:
            j = skip_ws(s, i)
            if s.startswith(".join(", j):
                k = match_brace(s, j + 5)
                sep = Evaluator(self.env).eval(s[j + 6:k]) if s[j + 6:k].strip() else ","
                if not isinstance(v, list):
                    raise Unknown("join")
                v = sep.join(to_str(x) for x in v)
                i = k + 1
            elif s.startswith(".repeat(", j):
                k = match_brace(s, j + 7)
                v = v * int(Evaluator(self.env).eval(s[j + 8:k]))
                i = k + 1
            elif s.startswith(".trim()", j):
                v = v.strip()
                i = j + 7
            elif s.startswith(".trimEnd()", j):
                v = v.rstrip()
                i = j + 10
            elif s.startswith(".replace", j) or s.startswith("?.", j) or s.startswith(".", j) and not s.startswith("..", j):
                raise Unknown("method")
            elif j < len(s) and s[j] == "[" and isinstance(v, list):
                k = match_brace(s, j)
                v = v[int(Evaluator(self.env).eval(s[j + 1:k]))]
                i = k + 1
            elif j < len(s) and s[j] in "?*/%<>=&|!" and not s.startswith("??", j):
                raise Unknown("operator")
            else:
                return v, i


def to_str(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if v is None:
        raise Unknown("undefined in string")
    if isinstance(v, (list, dict)):
        raise Unknown("object in string")
    return str(v)


def split_top(text):
    parts, depth, i, start = [], 0, 0, 0
    pairs = "([{"
    while i < len(text):
        c = text[i]
        if c in "\"'":
            _, i = read_string(text, i)
            continue
        if c == "`":
            _, i = read_template(text, i)
            continue
        if text.startswith("//", i) or text.startswith("/*", i):
            i = skip_ws(text, i)
            continue
        if c in pairs:
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
        i += 1
    parts.append(text[start:])
    return [p for p in parts if p.strip()]


def parse_object(text, env, strict=False):
    out = {}
    for entry in split_top(text):
        e = skip_ws(entry, 0)
        entry = entry[e:]
        m = re.match(r'(?:"([^"]+)"|([A-Za-z_$][\w$]*))\s*(:)?', entry)
        if entry.startswith("..."):
            if strict:
                raise Unknown("spread")
            out["..."] = True
            continue
        if not m:
            raise Unknown("key")
        key = m.group(1) or m.group(2)
        if m.group(3):
            rest = entry[m.end():]
            if re.match(r"\s*(async\s*)?(\([^)]*\)|\w+)\s*=>", rest) or re.match(r"\s*(async\s+)?function", rest):
                out[key] = ("fn",)
                continue
            try:
                out[key] = Evaluator(env).eval(rest)
            except Unknown as error:
                if strict:
                    raise
                out[key] = ("unknown", str(error))
        else:
            if key in env:
                out[key] = env[key]
            else:
                out[key] = ("unknown", "shorthand " + key)
    return out


# ---- test structure


def params_of(text):
    """Parameter names of `async (a, b) =>` / `([a, b]) =>` / `({a, b}) =>`."""
    m = re.match(r"\s*(?:async\s*)?\(([\s\S]*?)\)\s*=>", text)
    if not m:
        return None
    inner = m.group(1).strip()
    if inner.startswith("[") or inner.startswith("{"):
        return ("destructure", [p.strip().split("=")[0].strip() for p in inner[1:-1].split(",") if p.strip()], inner[0])
    return ("list", [p.strip().split("=")[0].strip().split(":")[0].strip() for p in inner.split(",") if p.strip()], None)


def bind(params, row):
    kind, names, bracket = params
    if kind == "list":
        if isinstance(row, list) and len(names) > 1:
            return {n: (row[k] if k < len(row) else None) for k, n in enumerate(names)}
        if isinstance(row, list) and len(names) == 1:
            # it.each([[a, b]]) spreads the row; [a] row to a single name.
            return {names[0]: row[0] if len(row) == 1 else row}
        if isinstance(row, dict) and len(names) == 1:
            return {names[0]: row}
        return {names[0]: row} if names else {}
    if bracket == "[":
        if isinstance(row, list) and len(row) == 1 and isinstance(row[0], list):
            row = row[0]
        return {n: (row[k] if isinstance(row, list) and k < len(row) else None) for k, n in enumerate(names)}
    if isinstance(row, list) and len(row) == 1:
        row = row[0]
    return {n: row.get(n) if isinstance(row, dict) else None for n in names}


CONSTS = re.compile(r"\bconst\s+([A-Za-z_$][\w$]*)\s*=\s*")


def collect_consts(text, env):
    """Top-level-ish `const name = <literal>;` definitions that evaluate statically."""
    env = dict(env)
    for m in CONSTS.finditer(text):
        start = m.end()
        # value runs to the next ";\n" at depth 0
        depth, i = 0, start
        try:
            while i < len(text):
                c = text[i]
                if c in "\"'":
                    _, i = read_string(text, i)
                    continue
                if c == "`":
                    _, i = read_template(text, i)
                    continue
                if c in "([{":
                    depth += 1
                elif c in ")]}":
                    depth -= 1
                    if depth < 0:
                        break
                elif c == ";" and depth == 0:
                    break
                elif c == "\n" and depth == 0 and not text[i:].lstrip().startswith((".", "+", "?")):
                    break
                i += 1
            env[m.group(1)] = Evaluator(env).eval(text[start:i])
        except (Unknown, IndexError, ValueError, KeyError):
            pass
    return env


CALL = re.compile(r"\b(check|simulate|checkDepthFirst)\(\{")
EACH = re.compile(r"\b(?:it|test|describe)(?:\.concurrent)?\.each\(")


def cases_in(text):
    """Yields (call, options, title) for each check({...}) with its bindings."""
    file_env = collect_consts(text, {})
    # Map each it.each table to its callback span and rows.
    tables = []
    for m in EACH.finditer(text):
        try:
            open_ = m.end() - 1
            close = match_brace(text, open_)
            rows = Evaluator(file_env).eval(text[open_ + 1:close])
            if not isinstance(rows, list):
                continue
            j = skip_ws(text, close + 1)
            if text[j] != "(":
                continue
            call_close = match_brace(text, j)
            args = split_top(text[j + 1:call_close])
            if len(args) < 2:
                continue
            callback = args[1]
            params = params_of(callback)
            if not params:
                continue
            cb_start = j + 1 + text[j + 1:call_close].index(callback)
            tables.append((cb_start, cb_start + len(callback), rows, params))
        except (Unknown, IndexError, ValueError, KeyError, TypeError):
            continue
    for m in CALL.finditer(text):
        open_ = m.end() - 1
        try:
            close = match_brace(text, open_)
        except (Unknown, IndexError):
            continue
        body = text[open_ + 1:close]
        enclosing = [t for t in tables if t[0] <= m.start() < t[1]]
        if enclosing:
            start, end, rows, params = enclosing[-1]
            for row in rows:
                try:
                    env = dict(file_env)
                    env.update(bind(params, row))
                    env = collect_consts(text[start:m.start()], env)
                    yield m.group(1), parse_object(body, env)
                except (Unknown, IndexError, ValueError, KeyError, TypeError, AttributeError):
                    continue
        else:
            # Consts of the enclosing it(...) body: scan back to the previous "it(" or "test(".
            k = max(text.rfind("\n  it(", 0, m.start()), text.rfind("\n  test(", 0, m.start()), text.rfind("\n    it(", 0, m.start()), 0)
            try:
                env = collect_consts(text[k:m.start()], file_env)
                yield m.group(1), parse_object(body, env)
            except (Unknown, IndexError, ValueError, KeyError, TypeError, AttributeError):
                continue


FLAG_KEYS = {
    "seed": lambda v: ["-seed", str(v)],
    "workers": lambda v: ["-workers", str(v)],
    "livenessCheck": lambda v: [] if v == "default" else ["-lncheck", v],
    "fingerprintPolynomial": lambda v: ["-fp", str(v)],
    "isLazyValueExpanded": lambda v: [] if v else ["-terse"],
    "isViewPrinted": lambda v: ["-view"] if v else [],
    "maxSetSize": lambda v: ["-maxSetSize", str(v)],
    "isTool": lambda v: [],
    "isContinued": lambda v: ["-continue"] if v else [],
    "isWarningEnabled": lambda v: [] if v else ["-nowarning"],
    "coverage": lambda v: ["-coverage", str(v)],
}
IGNORED = {"onPrint", "onPause", "onProgress", "isFingerprintDistanceSkipped", "isSanyReported", "version"}


def to_case(call, options):
    source, config = options.get("source"), options.get("config")
    if not isinstance(source, str) or not isinstance(config, str):
        return None
    if "..." in options:
        return None
    args = []
    for key, value in options.items():
        if key in ("source", "config") or key in IGNORED:
            continue
        if isinstance(value, tuple) or key not in FLAG_KEYS:
            return None
        args += FLAG_KEYS[key](value)
    if call != "check":
        return None
    m = re.search(r"-{4,}\s*MODULE\s+(\w+)", source)
    if not m:
        return None
    return m.group(1), source, config, args


def main():
    unit, out = sys.argv[1], sys.argv[2]
    seen = set()
    count = 0
    stats = {}
    for name in sorted(os.listdir(unit)):
        if not name.endswith(".ts"):
            continue
        text = open(os.path.join(unit, name)).read()
        n = 0
        for call, options in cases_in(text):
            case = to_case(call, options)
            if not case:
                stats["skipped"] = stats.get("skipped", 0) + 1
                continue
            module, source, config, args = case
            key = (source, config, tuple(args))
            if key in seen:
                continue
            seen.add(key)
            n += 1
            directory = os.path.join(out, "tlc", "unit", name[:-3].replace(".", "_"), f"c{n:04d}")
            os.makedirs(directory, exist_ok=True)
            header = {"description": "upstream unit case", "outcome": "any", "config": config}
            if args:
                header["args"] = args
            # A conformance file: YAML header, then the module (the harness appends nothing for a model).
            body = "(*---\n" + json.dumps(header, ensure_ascii=False) + "\n---*)\n" + source.rstrip("\n") + "\n"
            open(os.path.join(directory, module + ".tla"), "w").write(body)
            count += 1
        stats[name] = n
    print(count, "cases;", {k: v for k, v in stats.items() if v})


if __name__ == "__main__":
    main()
