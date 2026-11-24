# Copied from /tmp/hetero-corpus-large/gen.py, sha256 e0602885100e1190668fcd67d599925835959ed1913161d05a14576393602b53; the text below is that file unchanged.
#!/usr/bin/env python3
# Scratch-only larger heterogeneous JSON corpus: same deterministic record
# generator, 5 seeds per (style,size), plus deep/escape documents.
# Every document is <= 1 MiB (the route's default input bound).
import hashlib
import json
import os
import random

OUT = "/tmp/hetero-corpus-large"
BASE_SEED = 0x5EED2026F1ED
GOLDEN = 0x9E3779B97F4A7C15
MASK = (1 << 64) - 1
SEEDS = 5
SIZES = [512, 2048, 8192, 32768, 131072, 524288, 1048576]
STYLES = ["pretty", "tab", "compact", "spaced"]
SPECIAL_SIZES = [65536, 262144]
SPECIAL_SEEDS = 2
MAX_BYTES = 1048576

UNI = ["café", "naïve", "Ελλάδα", "日本語", "🙂", "e\u0301", "Ω", "Привет",
       "مرحبا", "한국어", "naïve café"]
KINDS = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta"]
TAGS = ["red", "green", "blue", "slow", "fast", "edge", "utf8", "num", "nested"]
EXPS = [1.5e-7, -3.25e12, 6.022e23, 2.5e-9, 1.0e300, -4.75e-100]
BIGS = [2**63 - 1, -(2**63), 10**18 + 7, 123456789012345678901234567890]
WS = ["", "\n", " \n\t", "\n\n", "\t \n"]


def nested_chain(r, depth, i):
    node = {"leaf": [i, r.choice(UNI), True, None]}
    for d in range(depth):
        node = {"level": d, "vals": [i, d, r.choice(["s", "t"]), r.choice([True, False])],
                "child": node}
    return node


def make_record(i, full, r):
    ratio = r.uniform(-1e6, 1e6)
    rec = {"id": i, "kind": r.choice(KINDS)}
    if not full:
        rec.update(
            name=f'row {i}: "quoted" \\ back\nline\ttab',
            ratio=round(ratio, 6),
            unicode=r.choice(UNI),
            tags=r.sample(TAGS, k=r.randint(1, 3)),
            nested={"a": [i, r.choice(UNI)], "b": {"c": [True, None]}},
        )
        if i % 2:
            rec["ok"] = r.choice([True, False])
        return rec
    rec.update(
        name=f'row {i}: "quoted" \\ back\nline\ttab',
        unicode=r.choice(UNI),
        esc="ctrl \u0001 \u001f end",
        ratio=round(ratio, 6),
        exp=r.choice(EXPS),
        count=r.randint(-10**12, 10**12),
        big=r.choice(BIGS),
        precise=0.1 + 0.2,
        negzero=-0.0,
        ok=r.choice([True, False]),
        none=None,
        tags=r.sample(TAGS, k=r.randint(1, 4)),
        mixed=[i, round(ratio, 3), r.choice(UNI), r.choice([True, False]), None],
        nested=nested_chain(r, r.randint(1, 4), i),
    )
    if i % 3 == 0:
        rec["variant"] = r.choice(["alpha", "beta", "gamma", "delta"])
    if i % 4 == 0:
        rec.pop("none")
    if i % 5 == 0:
        rec["extra"] = {"k": r.randint(0, 9), "v": r.choice(UNI)}
    return rec


def dumps(obj, style):
    if style == "pretty":
        return json.dumps(obj, ensure_ascii=False, indent=2, allow_nan=False)
    if style == "tab":
        return json.dumps(obj, ensure_ascii=False, indent="\t", allow_nan=False)
    if style == "compact":
        return json.dumps(obj, ensure_ascii=True, separators=(",", ":"), allow_nan=False)
    if style == "spaced":
        return json.dumps(obj, ensure_ascii=False, separators=(", ", " : "), allow_nan=False)
    raise ValueError(style)


def fit(make_text, target, max_n):
    """Largest n in [1,max_n] whose UTF-8 text is <= target; 1 if one exceeds."""
    lo, hi, best = 1, max_n, None
    while lo <= hi:
        mid = (lo + hi) // 2
        n, s = make_text(mid)
        if len(s.encode("utf-8")) <= target:
            best = (n, s)
            lo = mid + 1
        else:
            hi = mid - 1
    if best is None:
        n, s = make_text(1)
        best = (1, s)
    return best


def depth(o):
    if isinstance(o, dict):
        return 1 + max([depth(v) for v in o.values()] or [0])
    if isinstance(o, list):
        return 1 + max([depth(v) for v in o] or [0])
    return 1


def root_obj(records, style, root_kind, meta):
    if root_kind == "object":
        return {"corpus": "hetero-large", "style": style, "seed": meta["seed"],
                "target_bytes": meta["target"],
                "generator": {"name": "gen.py", "version": 2},
                "records": records}
    return records


def write_doc(name, text):
    path = os.path.join(OUT, name)
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    return path


def main():
    os.makedirs(OUT, exist_ok=True)
    rows = []
    doc = 0

    for style_i, style in enumerate(STYLES):
        for target in SIZES:
            for si in range(SEEDS):
                seed = (BASE_SEED + doc * GOLDEN) & MASK
                r = random.Random(seed)
                full = target >= 8192
                pool_n = 3000 if full else 500
                pool = [make_record(i, full, r) for i in range(pool_n)]
                prefix = r.choice(WS)
                suffix = r.choice(WS)
                root_kind = "object" if (style_i + si) % 2 == 0 else "array"
                meta = {"seed": seed, "target": target, "style": style,
                        "root": root_kind, "seed_index": si}

                def make_text(n, style=style, pool=pool, prefix=prefix,
                              suffix=suffix, root_kind=root_kind, meta=meta):
                    obj = root_obj(pool[:n], style, root_kind, meta)
                    return n, prefix + dumps(obj, style) + suffix

                n, text = fit(make_text, target, pool_n)
                obj = root_obj(pool[:n], style, root_kind, meta)
                name = f"hetero-{style}-{target:07d}-s{si}-{doc:03d}.json"
                path = write_doc(name, text)
                rows.append((name, style, target, n, len(text.encode("utf-8")),
                             root_kind, seed, depth(obj), si, path))
                doc += 1

    # Deep and escape specials at two sizes, two seeds each.
    for kind in ("deep", "escapes"):
        for target in SPECIAL_SIZES:
            for si in range(SPECIAL_SEEDS):
                seed = (BASE_SEED + doc * GOLDEN) & MASK
                r = random.Random(seed)
                prefix = "\n"
                suffix = "\n"
                if kind == "deep":
                    pool = [nested_chain(r, 60, i) for i in range(400)]

                    def make_text(n, pool=pool, prefix=prefix, suffix=suffix):
                        return n, prefix + json.dumps(
                            pool[:n], ensure_ascii=False,
                            separators=(",", ":"), allow_nan=False) + suffix
                else:
                    pieces = [{
                        "s": (f'esc {i}: quote=" back=\\ nl=\n tab=\t ctrl=\u0001\u001f '
                              f'unicode=\u00e9 \u65e5 \U0001F642 slash=/'),
                        "n": i,
                        "u": r.choice(UNI),
                    } for i in range(3000)]

                    def make_text(n, pieces=pieces):
                        return n, json.dumps(
                            pieces[:n], ensure_ascii=True,
                            separators=(",", ":"), allow_nan=False)

                max_n = len(pool) if kind == "deep" else len(pieces)
                n, text = fit(make_text, target, max_n)
                obj = pool[:n] if kind == "deep" else pieces[:n]
                name = f"hetero-{kind}-{target:07d}-s{si}-{doc:03d}.json"
                path = write_doc(name, text)
                rows.append((name, kind, target, n, len(text.encode("utf-8")),
                             "array", seed, depth(obj), si, path))
                doc += 1

    manifest = os.path.join(OUT, "manifest.tsv")
    with open(manifest, "w", encoding="utf-8") as f:
        f.write("file\tstyle\ttarget_bytes\trecords\tbytes\tsha256\troot\t"
                "seed\tmax_depth\tseed_index\n")
        for name, style, target, n, size, root, seed, md, si, path in rows:
            with open(path, "rb") as g:
                sha = hashlib.sha256(g.read()).hexdigest()
            assert size <= MAX_BYTES, (name, size)
            f.write(f"{name}\t{style}\t{target}\t{n}\t{size}\t{sha}\t{root}\t"
                    f"0x{seed:016X}\t{md}\t{si}\n")

    sizes = [r[4] for r in rows]
    style_counts = {}
    root_counts = {}
    size_counts = {}
    for _, style, target, _, _, root, _, _, _, _ in rows:
        style_counts[style] = style_counts.get(style, 0) + 1
        root_counts[root] = root_counts.get(root, 0) + 1
        size_counts[target] = size_counts.get(target, 0) + 1

    with open(os.path.join(OUT, "meta.txt"), "w", encoding="utf-8") as f:
        f.write(f"base_seed=0x{BASE_SEED:X}\n")
        f.write(f"golden={GOLDEN:#x}\n")
        f.write(f"generator={os.path.abspath(__file__)}\n")
        with open(os.path.abspath(__file__), "rb") as g:
            f.write(f"generator_sha256={hashlib.sha256(g.read()).hexdigest()}\n")
        f.write(f"documents={len(rows)}\n")
        f.write(f"bytes_total={sum(sizes)}\n")
        f.write(f"bytes_min={min(sizes)}\n")
        f.write(f"bytes_max={max(sizes)}\n")
        f.write(f"styles={json.dumps(style_counts, sort_keys=True)}\n")
        f.write(f"roots={json.dumps(root_counts, sort_keys=True)}\n")
        f.write(f"size_counts={json.dumps(size_counts, sort_keys=True)}\n")
        f.write(f"route_default_max_input={MAX_BYTES}\n")

    print(f"documents: {len(rows)}")
    print(f"bytes: min {min(sizes)} max {max(sizes)} total {sum(sizes)}")
    print(f"styles: {style_counts}")
    print(f"roots: {root_counts}")
    print(f"sizes: {size_counts}")
    print(f"manifest: {manifest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
