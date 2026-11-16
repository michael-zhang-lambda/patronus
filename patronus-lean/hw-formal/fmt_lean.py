"""Break long lines of generated patronus-lean models at parenthesis boundaries.

usage: python3 fmt_lean.py [--width N] FILE...   (rewrites files in place)

e.g. from patronus-lean/hw-formal:  python3 fmt_lean.py tests/*.lean
"""
import re
import sys

WIDTH = 100
# atoms that bind to the operand that follows them when a group is broken
OPS = {"if", "then", "else", "&&&", "|||", "^^^", "==", "||", "&&", "+", "-", "*"}


def parse(s, i=0):
    """Parse s[i:] into a list of units until a matching ')' (or end).

    A unit is (prefix, group) where group is None for a plain atom, or a list of
    units for a parenthesised group; `prefix` is text glued directly before it.
    Returns (units, index after the closing paren).
    """
    units, buf = [], ""
    while i < len(s):
        c = s[i]
        if c == "(":
            inner, i = parse(s, i + 1)
            units.append((buf, inner))
            buf = ""
            # text glued after a group (e.g. `.toNat`) becomes its own atom
            m = re.match(r"[^\s()]+", s[i:])
            if m:
                units.append((m.group(0), None))
                i += len(m.group(0))
            continue
        if c == ")":
            if buf:
                units.append((buf, None))
            return units, i + 1
        if c == " ":
            if buf:
                units.append((buf, None))
            buf = ""
        else:
            buf += c
        i += 1
    if buf:
        units.append((buf, None))
    return units, i


def flat(u):
    prefix, g = u
    if g is None:
        return prefix
    return prefix + "(" + " ".join(flat(x) for x in g) + ")"


def segments(units):
    """Group units into segments that stay on one line when a group is broken."""
    segs, i = [], 0
    # head: leading run of plain atoms (function name and simple arguments)
    head = []
    while i < len(units) and units[i][1] is None and not (i and units[i][0] in OPS):
        head.append(units[i])
        i += 1
    if head:
        segs.append(head)
    pending = []
    for u in units[i:]:
        pending.append(u)
        if not (u[1] is None and u[0] in OPS):
            segs.append(pending)
            pending = []
    if pending:
        segs.append(pending)
    # a head that is only an operator/keyword (e.g. `if`) merges with the next segment
    if len(segs) > 1 and all(u[1] is None and u[0] in OPS for u in segs[0]):
        segs[0:2] = [segs[0] + segs[1]]
    return segs


def render_seg(seg, col, tail=0):
    """Render a segment starting at column `col`; return list of lines (first unindented)."""
    out = ""
    for k, u in enumerate(seg):
        if k:
            out += " "
        if k < len(seg) - 1:
            out += flat(u)
        else:
            lines = render_unit(u, col + len(out), tail)
            return [out + lines[0]] + lines[1:]
    return [out]


def render_unit(u, col, tail=0):
    """`tail` is the number of characters (closing parens) that follow on the last line."""
    text = flat(u)
    prefix, g = u
    if g is None or col + len(text) + tail <= WIDTH:
        return [text]
    body = render_group(g, col + len(prefix) + 1, tail + 1)
    body[0] = prefix + "(" + body[0]
    body[-1] += ")"
    return body


def render_group(units, col, tail=0):
    """Render the contents of a group whose first character is at column `col`."""
    text = " ".join(flat(x) for x in units)
    if col + len(text) + tail <= WIDTH:
        return [text]
    segs = segments(units)
    lines = render_seg(segs[0], col, tail if len(segs) == 1 else 0)
    ind = col + 2
    for k, seg in enumerate(segs[1:], 2):
        sub = render_seg(seg, ind, tail if k == len(segs) else 0)
        lines.append(" " * ind + sub[0])
        lines.extend(sub[1:])
    return lines


def format_line(line):
    if len(line) <= WIDTH:
        return [line]
    m = re.match(r"(\s*(?:\S+ := )?)(.*)$", line)
    lead, expr = m.group(1), m.group(2)
    units, end = parse(expr)
    assert end == len(expr), f"unbalanced parentheses: {line}"
    assert " ".join(flat(x) for x in units) == expr, f"round-trip failed: {line}"
    body = render_group(units, len(lead))
    # continuation lines must be indented past the field name
    return [lead + body[0]] + body[1:]


def main():
    global WIDTH
    args = sys.argv[1:]
    if args[:1] == ["--width"]:
        WIDTH = int(args[1])
        args = args[2:]
    for path in args:
        src = open(path).read().split("\n")
        out = [l for line in src for l in format_line(line)]
        open(path, "w").write("\n".join(out))


if __name__ == "__main__":
    main()
