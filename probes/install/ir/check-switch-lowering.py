#!/usr/bin/env python3
"""Check that `opt -passes=lower-switch` preserves every switch's successor.

The production stage-2 module carries twenty `switch` instructions.  The
importer does not model `switch`, so the route's plan is to lower them and
trust the transform.  This script discharges that trust per switch: it reads
the committed module, lowers it with the recorded pass, and for each original
switch compares

  * the successor the original switch names (case value -> target, else
    default), with
  * the block the lowered control flow reaches for the same condition value,

over a domain that is exhaustive for the switch's type:

  * i8: all 256 bit patterns.  The lowered chain is interpreted concretely for
    each, including the range tests the pass emits for clustered cases
    (`%off = add i8 %cond, -base; icmp ule i8 %off, span`).
  * wider types: every integer constant the lowered decision tree compares
    against, each constant +/- 1, and the type's extremes.  This is exhaustive
    only when the tree branches on `icmp` of the condition *itself* against
    constants -- then each test's truth, hence the reached leaf, is constant on
    every interval between consecutive constants, so the representatives cover
    every equivalence class.  The script refuses a wider-type chain that
    derives a value from the condition first rather than sampling around it.

Exit status: 0 when every switch corresponds, 1 on any mismatch or on a
lowered form the checker cannot read, 3 on a setup fault.

Usage:
  python3 check-switch-lowering.py <module.ll> <lowered.ll> [out.tsv]
"""

import re
import sys

DEFINE = re.compile(r"^define\b")
FUNC_NAME = re.compile(r"@([A-Za-z0-9_.$]+)\(")
LABEL = re.compile(r"^([A-Za-z0-9_.$]+):")
SWITCH_HEAD = re.compile(r"^switch\s+(i\d+)\s+(%\S+?),\s*label\s+%(\S+?)\s*\[$")
SWITCH_ONE_LINE = re.compile(
    r"^switch\s+(i\d+)\s+(%\S+?),\s*label\s+%(\S+?)\s*\[(.*)\]$")
SWITCH_CASE = re.compile(r"^(i\d+)\s+(-?\d+),\s*label\s+%(\S+?)$")
BR_COND = re.compile(
    r"^br\s+i1\s+(%\S+?),\s*label\s+%(\S+?),\s*label\s+%(\S+?)$")
BR_UNCOND = re.compile(r"^br\s+label\s+%(\S+?)$")
ASSIGN = re.compile(r"^(%\S+?)\s*=\s*(.+)$")
INT_TYPE = re.compile(r"^i(\d+)$")
CONST = re.compile(r"^-?\d+$")

BINOPS = {"add", "sub", "and", "or", "xor", "shl", "lshr", "ashr"}
ICMP_PREDS = {"eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge"}


class SetupError(Exception):
    pass


class CheckError(Exception):
    pass


def parse_module(path):
    """Return {function: {'blocks': {label: [instruction lines]}}}.

    The unnamed entry block is keyed ''.  `;` comments and blanks are dropped;
    a block's instruction list keeps source order.
    """
    funcs = {}
    cur_fn = None
    cur_block = None
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            text = line.strip()
            if text == "" or text.startswith(";"):
                continue
            if DEFINE.match(text):
                m = FUNC_NAME.search(text)
                if not m:
                    raise SetupError("%s: define without a function name" % path)
                cur_fn = m.group(1)
                funcs[cur_fn] = {"blocks": {}}
                cur_block = ""
                funcs[cur_fn]["blocks"][""] = []
                continue
            if cur_fn is None:
                continue
            if text == "}":
                cur_fn = None
                cur_block = None
                continue
            m = LABEL.match(line)
            if m:
                cur_block = m.group(1)
                funcs[cur_fn]["blocks"].setdefault(cur_block, [])
                continue
            if cur_block is not None:
                funcs[cur_fn]["blocks"][cur_block].append(text)
    return funcs


def module_switch_count(funcs):
    count = 0
    for body in funcs.values():
        for instrs in body["blocks"].values():
            count += sum(1 for text in instrs if text.startswith("switch "))
    return count


def find_switches(funcs):
    """Yield (function, block, type, cond, default, [case lines])."""
    for fn, body in funcs.items():
        for block, instrs in body["blocks"].items():
            i = 0
            while i < len(instrs):
                text = instrs[i]
                one = SWITCH_ONE_LINE.match(text)
                if one:
                    ty, cond, default, rest = one.groups()
                    cases = [p.strip() for p in rest.split("]") if p.strip()]
                    yield fn, block, ty, cond, default, cases
                    i += 1
                    continue
                head = SWITCH_HEAD.match(text)
                if head:
                    ty, cond, default = head.groups()
                    cases = []
                    i += 1
                    closed = False
                    while i < len(instrs):
                        piece = instrs[i]
                        if piece == "]":
                            closed = True
                            i += 1
                            break
                        cases.append(piece)
                        i += 1
                    if not closed:
                        raise CheckError(
                            "unterminated switch in %s block %r" % (fn, block))
                    yield fn, block, ty, cond, default, cases
                    continue
                i += 1


def parse_cases(ty, case_lines):
    cases = []
    for text in case_lines:
        m = SWITCH_CASE.match(text)
        if not m:
            raise CheckError("cannot read switch case %r" % text)
        cty, value, target = m.groups()
        if cty != ty:
            raise CheckError("case type %s under switch type %s" % (cty, ty))
        cases.append((int(value), target))
    return cases


def block_term(instrs):
    if not instrs:
        raise CheckError("empty block")
    return instrs[-1]


def signed(width, bits):
    if bits & (1 << (width - 1)):
        return bits - (1 << width)
    return bits


def mask(width, value):
    return value & ((1 << width) - 1)


def truth(pred, width, left_bits, right_bits):
    if pred == "eq":
        return left_bits == right_bits
    if pred == "ne":
        return left_bits != right_bits
    if pred in ("slt", "sle", "sgt", "sge"):
        a, b = signed(width, left_bits), signed(width, right_bits)
    else:
        a, b = left_bits, right_bits
    return {"slt": a < b, "sle": a <= b, "sgt": a > b, "sge": a >= b,
            "ult": a < b, "ule": a <= b, "ugt": a > b, "uge": a >= b}[pred]


def parse_operand(text, env, width):
    """Resolve an operand to (bits, width) or raise CheckError."""
    if CONST.match(text):
        return mask(width, int(text)), width
    if text in env:
        return env[text]
    raise CheckError("operand %r is not the condition, a constant or a value "
                     "derived from them" % text)


def eval_assignment(text, env):
    """Evaluate one `%x = op ...` chain instruction; return nothing."""
    m = ASSIGN.match(text)
    if not m:
        raise CheckError("chain block carries a non-assignment %r" % text)
    name, rhs = m.groups()
    parts = rhs.split(None, 1)
    op = parts[0]
    rest = parts[1] if len(parts) > 1 else ""
    if op == "icmp":
        fields = rest.split(None, 1)
        if len(fields) != 2:
            raise CheckError("cannot read icmp %r" % text)
        pred, operands = fields
        if pred not in ICMP_PREDS:
            raise CheckError("unknown icmp predicate %r" % pred)
        ops = operands.split(",")
        if len(ops) != 2:
            raise CheckError("cannot read icmp operands %r" % text)
        ty_text, left = ops[0].split()
        right = ops[1].strip()
        mty = INT_TYPE.match(ty_text)
        if not mty:
            raise CheckError("icmp on non-integer type %s" % ty_text)
        iw = int(mty.group(1))
        lbits, _ = parse_operand(left, env, iw)
        rbits, _ = parse_operand(right, env, iw)
        env[name] = (truth(pred, iw, lbits, rbits), None)
        return
    if op in BINOPS:
        fields = rest.split(None, 1)
        if len(fields) != 2:
            raise CheckError("cannot read %s %r" % (op, text))
        ty_text, operands = fields
        ops = operands.split(",")
        if len(ops) != 2:
            raise CheckError("cannot read %s operands %r" % (op, text))
        mty = INT_TYPE.match(ty_text)
        if not mty:
            raise CheckError("arithmetic on non-integer type %s" % ty_text)
        bw = int(mty.group(1))
        lbits, _ = parse_operand(ops[0].strip(), env, bw)
        rbits, _ = parse_operand(ops[1].strip(), env, bw)
        if op == "add":
            out = mask(bw, lbits + rbits)
        elif op == "sub":
            out = mask(bw, lbits - rbits)
        elif op == "and":
            out = lbits & rbits
        elif op == "or":
            out = lbits | rbits
        elif op == "xor":
            out = lbits ^ rbits
        elif op == "shl":
            out = mask(bw, lbits << (rbits & (bw - 1)))
        elif op == "lshr":
            out = lbits >> (rbits & (bw - 1))
        else:  # ashr
            out = mask(bw, signed(bw, lbits) >> (rbits & (bw - 1)))
        env[name] = (out, bw)
        return
    if op in ("zext", "trunc"):
        # `%x = zext i8 %y to i32`: source type, operand, then destination.
        conv = re.match(r"^(i\d+)\s+(%\S+)\s+to\s+(i\d+)$", rest)
        if not conv:
            raise CheckError("cannot read %s %r" % (op, text))
        src_ty, operand, dst_ty = conv.groups()
        sw = int(INT_TYPE.match(src_ty).group(1))
        dw = int(INT_TYPE.match(dst_ty).group(1))
        val, _ = parse_operand(operand, env, sw)
        env[name] = (mask(dw, val), dw)
        return
    raise CheckError("unsupported chain instruction %r" % text)


class Lowered:
    def __init__(self, funcs):
        self.funcs = funcs

    def blocks(self, fn):
        return self.funcs[fn]["blocks"]

    def step(self, fn, block, cond, cond_bits, width, strict):
        """Take one step from `block`; return the next block.

        `strict` evaluates every instruction before the terminator.  The
        switch's own block is not strict: it holds the code that computed the
        condition and any pre-existing phis, and only the terminator the pass
        rewrote matters there.
        """
        blocks = self.blocks(fn)
        if block not in blocks:
            raise CheckError("lowered module has no block %r" % block)
        instrs = blocks[block]
        env = {cond: (cond_bits, width)}
        for text in instrs[:-1]:
            if strict:
                eval_assignment(text, env)
            else:
                try:
                    eval_assignment(text, env)
                except CheckError:
                    pass
        term = block_term(instrs)
        uncond = BR_UNCOND.match(term)
        if uncond:
            return uncond.group(1)
        condbr = BR_COND.match(term)
        if not condbr:
            raise CheckError(
                "chain block %r does not end in a branch: %r" % (block, term))
        branch, yes, no = condbr.groups()
        if branch not in env or env[branch][1] is not None:
            raise CheckError(
                "branch condition %s in block %r is not an integer comparison"
                % (branch, block))
        return yes if env[branch][0] else no


def chain_region(lowered, fn, start_block, successors):
    """Blocks reachable from the switch block before any original successor."""
    seen = set()
    pending = [start_block]
    while pending:
        block = pending.pop()
        if block in successors or block in seen:
            continue
        seen.add(block)
        term = block_term(lowered.blocks(fn)[block])
        uncond = BR_UNCOND.match(term)
        if uncond:
            pending.append(uncond.group(1))
            continue
        condbr = BR_COND.match(term)
        if not condbr:
            raise CheckError(
                "chain block %r does not end in a branch: %r" % (block, term))
        pending.extend([condbr.group(2), condbr.group(3)])
    return seen


def wide_chain_constants(lowered, region, fn, cond):
    """Constants tested by an `icmp <pred> <cond>, <const>` chain.

    Returns the constants, and raises when a tested value is derived from the
    condition, which would invalidate the interval argument the caller relies
    on for a wider-than-i8 sweep.
    """
    constants = set()
    for block in region:
        instrs = lowered.blocks(fn)[block]
        term = block_term(instrs)
        condbr = BR_COND.match(term)
        if not condbr:
            continue
        branch = condbr.group(1)
        found = None
        for text in instrs:
            m = ASSIGN.match(text)
            if not m or m.group(1) != branch:
                continue
            found = m.group(2)
            break
        if found is None:
            raise CheckError(
                "branch %s in block %r has no definition in that block"
                % (branch, block))
        fields = found.split(None, 1)
        if len(fields) != 2 or fields[0] != "icmp":
            raise CheckError(
                "wider-type chain branches on %r, not on an icmp of the "
                "condition" % found)
        operands = fields[1].split(None, 1)[1].split(",")
        if len(operands) != 2:
            raise CheckError("cannot read icmp operands %r" % found)
        left = operands[0].split()[1]
        right = operands[1].strip()
        if left == cond and CONST.match(right):
            constants.add(int(right))
        elif right == cond and CONST.match(left):
            constants.add(int(left))
        else:
            raise CheckError(
                "wider-type chain tests %r, which is not the condition %s "
                "against a constant; the interval sweep would not be "
                "exhaustive" % (found, cond))
    return constants


def reached(lowered, fn, start_block, successors, cond, value, width):
    block = start_block
    visited = set()
    while block not in successors:
        if block in visited:
            raise CheckError("cycle in lowered chain at block %r" % block)
        strict = block != start_block
        visited.add(block)
        block = lowered.step(fn, block, cond, value, width, strict)
    return block


def switch_target(cases, default, value, width):
    bits = mask(width, value)
    for case_value, target in cases:
        if mask(width, case_value) == bits:
            return target
    return default


def domain_for(width, cases, constants):
    if width == 8:
        return list(range(256)), "exhaustive i8 (all 256 bit patterns)"
    lo, hi = 0, (1 << width) - 1
    points = {mask(width, c) for c in constants} | {
        mask(width, v) for v, _ in cases}
    reps = {lo, hi, 0, 1, hi}
    for c in points:
        for delta in (-1, 0, 1):
            reps.add(mask(width, c + delta))
    # Signed extremes and their neighbours, so the unbounded intervals are hit
    # under either reading.
    s_lo = mask(width, -(1 << (width - 1)))
    s_hi = mask(width, (1 << (width - 1)) - 1)
    reps.update({s_lo, s_hi, mask(width, s_lo + 1), mask(width, s_hi - 1)})
    return sorted(reps), (
        "representative i%d: tested constants +/- 1 and type extremes" % width)


def check(module_path, lowered_path):
    original = parse_module(module_path)
    lowered_funcs = parse_module(lowered_path)
    if module_switch_count(lowered_funcs) != 0:
        raise CheckError("the lowered module still carries a switch")
    lowered = Lowered(lowered_funcs)
    rows = []
    total = 0
    failures = 0
    for fn, block, ty, cond, default, case_lines in find_switches(original):
        total += 1
        if fn not in lowered_funcs:
            raise CheckError("lowered module has no function %s" % fn)
        if block not in lowered.blocks(fn):
            raise CheckError("lowered module has no block %r" % block)
        mty = INT_TYPE.match(ty)
        if not mty:
            raise CheckError("switch on non-integer type %s" % ty)
        width = int(mty.group(1))
        cases = parse_cases(ty, case_lines)
        successors = {default} | {target for _, target in cases}
        if len(successors) < 2:
            # The row this check supports needs every switch to have at least
            # two distinct successors: with one, the lowering emits a bare
            # branch that never reads the condition, which is *defined* where a
            # switch on a poison condition is undefined.  The successor table
            # enumerates defined integers and cannot see that gap, so the check
            # refuses the shape instead of reporting a correspondence for it.
            raise CheckError(
                "switch at %s has a single successor (%s): the lowering emits a bare "
                "branch that does not read the condition, so this check's "
                "correspondence does not cover it" % (block, ", ".join(sorted(successors))))
        region = chain_region(lowered, fn, block, successors)
        if width == 8:
            values, domain = domain_for(width, cases, set())
        else:
            constants = wide_chain_constants(lowered, region, fn, cond)
            values, domain = domain_for(width, cases, constants)
        mismatches = 0
        first = ""
        for value in values:
            want = switch_target(cases, default, value, width)
            got = reached(lowered, fn, block, successors, cond, value, width)
            if got != want:
                mismatches += 1
                if not first:
                    first = "value %d: switch %%%s, lowered %%%s" % (
                        signed(width, value), want, got)
        reachable = set()
        for value in values:
            reachable.add(reached(lowered, fn, block, successors, cond,
                                  value, width))
        missing = sorted(successors - reachable)
        if missing:
            mismatches += 1
            if not first:
                first = "successors never reached: %s" % ",".join(missing)
        verdict = "ok" if mismatches == 0 else "MISMATCH"
        if mismatches:
            failures += 1
        rows.append({
            "index": total,
            "function": fn,
            "block": block,
            "type": ty,
            "condition": cond,
            "default": default,
            "cases": len(cases),
            "domain": domain,
            "tested": len(values),
            "chain_blocks": len(region),
            "mismatches": mismatches,
            "verdict": verdict,
            "detail": first,
        })
    return rows, total, failures


def emit(rows, total, failures, out):
    out.write("index\tfunction\tblock\ttype\tcondition\tdefault\tcases\t"
              "domain\ttested\tchain_blocks\tmismatches\tverdict\tdetail\n")
    for row in rows:
        out.write("%(index)d\t%(function)s\t%(block)s\t%(type)s\t"
                  "%(condition)s\t%(default)s\t%(cases)d\t%(domain)s\t"
                  "%(tested)d\t%(chain_blocks)d\t%(mismatches)d\t"
                  "%(verdict)s\t%(detail)s\n" % row)
    status = "ok" if failures == 0 and total > 0 else "FAIL"
    out.write("summary\t%s\tswitches=%d\tmismatched=%d\n"
              % (status, total, failures))


def main(argv):
    if len(argv) < 3:
        sys.stderr.write(
            "usage: %s <module.ll> <lowered.ll> [out.tsv]\n" % argv[0])
        return 3
    try:
        rows, total, failures = check(argv[1], argv[2])
    except SetupError as exc:
        sys.stderr.write("SETUP: %s\n" % exc)
        return 3
    except CheckError as exc:
        sys.stderr.write("CHECK: %s\n" % exc)
        return 1
    if len(argv) > 3:
        with open(argv[3], "w", encoding="utf-8") as fh:
            emit(rows, total, failures, fh)
    else:
        emit(rows, total, failures, sys.stdout)
    if failures or total == 0:
        sys.stderr.write("FAIL: %d of %d switches did not correspond\n"
                         % (failures, total))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
