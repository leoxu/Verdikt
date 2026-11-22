#!/usr/bin/env python3
"""Generates test/corpus/*.core: small bad/good program pairs in the style of the Juliet CWE suite, written directly
in `core` (the C front-end is a separate track). Each file starts with
    // EXPECT: <ub kind>|none     // ENTRY: f     [// LIBC]
and is checked by corpus_tests (symbolic execution + replay on the interpreter)."""
import os, sys

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "test", "corpus")
files = {}

DECL = """core.declare @malloc(i64) -> ptr
core.declare @free(ptr) -> void
core.declare @calloc(i64, i64) -> ptr
core.declare @memcpy(ptr, ptr, i64) -> ptr
core.declare @memset(ptr, i32, i64) -> ptr
"""

def emit(cwe, name, expect, body, libc=False, entry="f"):
    kind = "bad" if expect != "none" else "good"
    fn = f"{cwe}_{name}_{kind}.core"
    hdr = f"// EXPECT: {expect}\n// ENTRY: {entry}\n" + ("// LIBC\n" if libc else "")
    files[fn] = hdr + (DECL if libc else "") + body

def func(name, params, ret, blocks):
    return f"core.func @{name}({', '.join(params)}) -> {ret} {{\n{blocks}}}\n"

# ---------------------------------------------------------------- CWE-121 stack buffer overflow (constant index)
for size in (4, 16, 64):
    for bad in (True, False):
        idx = size if bad else size - 1
        body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %buf = core.alloca {{size={size}}} : ptr
  %i = core.const {idx} : i64
  %q = core.ptr_add %buf, %i : ptr
  core.check.oob %q {{w=1, access="w"}}
  %b = core.trunc %x : i8
  core.store %b, %q
  core.return %x
""")
        emit("CWE121", f"const_idx{size}", "oob_write" if bad else "none", body)

# ---------------------------------------------------------------- CWE-121 symbolic index
for size in (8, 32):
    for bad in (True, False):
        guard = "" if bad else f"""  %lim = core.const {size} : i64
  %in = core.icmp ult %i, %lim : bool
  core.cond_br %in, ^go, ^out
^out:
  %m = core.const -1 : i32
  core.return %m
^go:
"""
        entry_br = "" if bad else ""
        body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %buf = core.alloca {{size={size}}} : ptr
  %i = core.zext %x : i64
{guard}  %q = core.ptr_add %buf, %i : ptr
  core.check.oob %q {{w=1, access="w"}}
  %b = core.const 1 : i8
  core.store %b, %q
  core.return %x
""")
        emit("CWE121", f"sym_idx{size}", "oob_write" if bad else "none", body)

# ---------------------------------------------------------------- CWE-122 heap overflow via memcpy
for n, m in ((8, 9), (16, 32), (4, 5)):
    for bad in (True, False):
        cnt = m if bad else n
        body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %n = core.const {n} : i64
  %c = core.const {cnt} : i64
  %dst = core.call @malloc(%n) : ptr
  %isn = core.is_null %dst : bool
  core.cond_br %isn, ^ret, ^go
^go:
  %src = core.alloca {{size=64}} : ptr
  %z = core.const 0 : i32
  %big = core.const 64 : i64
  %f0 = core.call @memset(%src, %z, %big) : ptr
  %r = core.call @memcpy(%dst, %src, %c) : ptr
  core.call @free(%dst)
  core.br ^ret
^ret:
  core.return %x
""")
        emit("CWE122", f"memcpy{n}_{cnt}", "oob_write" if bad else "none", body, libc=True)

# ---------------------------------------------------------------- CWE-122 symbolic heap length
for bad in (True, False):
    if bad:
        use = """  %off = core.add %n, %zero64 : i64
"""
    else:
        use = """  %one = core.const 1 : i64
  %off = core.sub %n, %one : i64
"""
    body = func("f", ["i32"], "i32", f"""^entry(%len: i32):
  %z = core.const 0 : i32
  %pos = core.icmp sgt %len, %z : bool
  core.assume %pos
  %zero64 = core.const 0 : i64
  %n = core.sext %len : i64
  %p = core.heap_alloc %n {{fail=never}} : ptr
{use}  %q = core.ptr_add %p, %off : ptr
  core.check.ptr_arith %p, %off
  core.check.null %q
  core.check.uaf %q
  core.check.oob %q {{w=1, access="w"}}
  %b = core.const 0 : i8
  core.store %b, %q
  core.free %q
  core.return %z
""")
    # free(q) of an interior pointer would be wrong for the good case; keep it simple: free the base
    body = body.replace("  core.free %q\n", "  core.check.free %p {expect=heap}\n  core.free %p\n")
    emit("CWE122", "sym_len", "oob_write" if bad else "none", body)

# ---------------------------------------------------------------- CWE-124 / CWE-127 under-write / under-read
for k in (1, 2, 8):
    for bad in (True, False):
        off = -k if bad else 0
        for cwe, access, store in (("CWE124", "w", True), ("CWE127", "r", False)):
            op = ("  %b = core.const 1 : i8\n  core.store %b, %q\n" if store
                  else "  core.check.uninit %q {w=1}\n  %v = core.load %q : i8\n")
            init = "" if store else "  %zero = core.const 0 : i8\n  %n = core.const 16 : i64\n  core.memset %buf, %zero, %n\n"
            body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %buf = core.alloca {{size=16}} : ptr
{init}  %i = core.const {off} : i64
  core.check.ptr_arith %buf, %i
  %q = core.ptr_add %buf, %i : ptr
  core.check.oob %q {{w=1, access="{access}"}}
{op}  core.return %x
""")
            emit(cwe, f"under{k}", "ptr_arith_oob" if bad else "none", body)

# ---------------------------------------------------------------- CWE-126 over-read
for size in (4, 16):
    for bad in (True, False):
        idx = size if bad else size - 1
        body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %buf = core.alloca {{size={size}}} : ptr
  %zero = core.const 0 : i8
  %n = core.const {size} : i64
  core.memset %buf, %zero, %n
  %i = core.const {idx} : i64
  %q = core.ptr_add %buf, %i : ptr
  core.check.oob %q {{w=1, access="r"}}
  %v = core.load %q : i8
  %r = core.zext %v : i32
  core.return %r
""")
        emit("CWE126", f"over{size}", "oob_read" if bad else "none", body)

# ---------------------------------------------------------------- CWE-415 double free
def df_direct(bad):
    second = "  core.call @free(%p)\n" if bad else ""
    return func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %n = core.const 8 : i64
  %p = core.call @malloc(%n) : ptr
  core.call @free(%p)
{second}  core.return %x
""")
emit("CWE415", "direct", "double_free", df_direct(True), libc=True)
emit("CWE415", "direct", "none", df_direct(False), libc=True)

def df_cond(bad):
    # bad: if (x) free(p); free(p);   good: if (x) free(p); else free(p);
    other = "^join" if bad else "^elsefree"
    extra = "" if bad else """^elsefree:
  core.call @free(%p)
  core.br ^end
"""
    join = """^join:
  core.call @free(%p)
  core.br ^end
""" if bad else ""
    return func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %n = core.const 8 : i64
  %p = core.call @malloc(%n) : ptr
  %z = core.const 0 : i32
  %c = core.icmp ne %x, %z : bool
  core.cond_br %c, ^first, {other}
^first:
  core.call @free(%p)
  core.br {"^join" if bad else "^end"}
{extra}{join}^end:
  core.return %x
""")
emit("CWE415", "cond", "double_free", df_cond(True), libc=True)
emit("CWE415", "cond", "none", df_cond(False), libc=True)

def df_null_reset(bad):
    reset = "" if bad else """  %z = core.const 0 : i64
  %np = core.int_to_ptr %z : ptr
  core.store %np, %slot
  %p2 = core.load %slot : ptr
"""
    sec = "%p" if bad else "%p2"
    return func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %n = core.const 8 : i64
  %p = core.call @malloc(%n) : ptr
  %slot = core.alloca {{size=8, align=8}} : ptr
  core.store %p, %slot
  core.call @free(%p)
{reset}  core.call @free({sec})
  core.return %x
""")
emit("CWE415", "null_reset", "double_free", df_null_reset(True), libc=True)
emit("CWE415", "null_reset", "none", df_null_reset(False), libc=True)

# ---------------------------------------------------------------- CWE-416 use after free
def uaf(kind, bad):
    pre = """  %n = core.const 8 : i64
  %p = core.heap_alloc %n {fail=never} : ptr
  %v0 = core.const 5 : i32
  core.store %v0, %p
"""
    chk = "  core.check.null %p\n  core.check.uaf %p\n"
    if kind == "read":
        use = chk + "  %v = core.load %p : i32\n"
        free = "  core.free %p\n"
        body = pre + (free + use if bad else use + free)
    elif kind == "write":
        use = chk + "  core.check.oob %p {w=4, access=\"w\"}\n  core.store %v0, %p\n"
        free = "  core.free %p\n"
        body = pre + (free + use if bad else use + free)
    elif kind == "slot":
        pre2 = pre + "  %slot = core.alloca {size=8, align=8} : ptr\n  core.store %p, %slot\n"
        use = "  %q = core.load %slot : ptr\n  core.check.null %q\n  core.check.uaf %q\n  %v = core.load %q : i32\n"
        free = "  core.free %p\n"
        body = pre2 + (free + use if bad else use + free)
    else:  # cond: if (x) free(p); then use p
        pre3 = pre + "  %z = core.const 0 : i32\n"
        if bad:
            body = pre3 + """  %c = core.icmp ne %x, %z : bool
  core.cond_br %c, ^fr, ^use
^fr:
  core.free %p
  core.br ^use
^use:
""" + chk + "  %v = core.load %p : i32\n"
        else:
            body = pre3 + """  %c = core.icmp ne %x, %z : bool
  core.cond_br %c, ^fr, ^use
^fr:
  core.br ^end
^use:
""" + chk + """  %v = core.load %p : i32
  core.free %p
  core.br ^end
^end:
  %v = core.const 0 : i32
"""
            # %v defined twice in the good variant: rename the tail
            body = body.replace("  core.br ^end\n^end:\n  %v = core.const 0 : i32\n", "  core.br ^end\n^end:\n")
    return func("f", ["i32"], "i32", "^entry(%x: i32):\n" + body + "  core.return %x\n")
for kind in ("read", "write", "slot", "cond"):
    emit("CWE416", kind, "use_after_free", uaf(kind, True))
    emit("CWE416", kind, "none", uaf(kind, False))

# ---------------------------------------------------------------- CWE-476 null dereference
for bad in (True, False):
    chk = "" if not bad else ""
    body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
  %n = core.const 4 : i64
  %p = core.call @malloc(%n) : ptr
""" + ("""  core.check.null %p
  core.store %x, %p
  core.call @free(%p)
  core.br ^ret
^ret:
  core.return %x
""" if bad else """  %isn = core.is_null %p : bool
  core.cond_br %isn, ^ret, ^ok
^ok:
  core.check.null %p
  core.store %x, %p
  core.call @free(%p)
  core.br ^ret
^ret:
  core.return %x
"""))
    emit("CWE476", "malloc", "null_deref" if bad else "none", body, libc=True)
for bad in (True, False):
    src = """  %z = core.const 0 : i64
  %p = core.int_to_ptr %z : ptr
""" if bad else "  %p = core.alloca {size=4, align=4} : ptr\n  core.store %x, %p\n"
    body = func("f", ["i32"], "i32", "^entry(%x: i32):\n" + src + """  core.check.null %p
  %v = core.load %p : i32
  core.return %v
""")
    emit("CWE476", "const_null", "null_deref" if bad else "none", body)

# ---------------------------------------------------------------- CWE-457 uninitialised variable
for kind in ("stack", "heap", "partial"):
    for bad in (True, False):
        if kind == "stack":
            setup = "  %p = core.alloca {size=4, align=4} : ptr\n" + ("" if bad else "  core.store %x, %p\n")
        elif kind == "heap":
            setup = ("  %n = core.const 4 : i64\n  %p = core.heap_alloc %n {fail=never} : ptr\n" if bad
                     else "  %n = core.const 4 : i64\n  %p = core.call @calloc(%n, %n) : ptr\n  %isn = core.is_null %p : bool\n  core.cond_br %isn, ^nomem, ^have\n^nomem:\n  core.return %x\n^have:\n")
        else:
            setup = "  %p = core.alloca {size=4, align=4} : ptr\n  %b = core.trunc %x : i8\n  core.store %b, %p\n" + ("" if bad else "  %z = core.const 0 : i32\n  core.store %z, %p\n")
        body = func("f", ["i32"], "i32", "^entry(%x: i32):\n" + setup + """  core.check.uninit %p {w=4}
  %v = core.load %p : i32
  core.return %v
""")
        emit("CWE457", kind, "uninit_read" if bad else "none", body, libc=(kind == "heap" and not bad))

# ---------------------------------------------------------------- CWE-369 divide by zero
for kind, opn in (("div", "sdiv"), ("rem", "srem")):
    for bad in (True, False):
        guard = "" if bad else """  %z = core.const 0 : i32
  %isz = core.icmp eq %d, %z : bool
  core.cond_br %isz, ^out, ^go
^out:
  core.return %z
^go:
"""
        body = func("f", ["i32"], "i32", f"""^entry(%d: i32):
{guard}  %hundred = core.const 100 : i32
  core.check.div %hundred, %d
  %r = core.{opn} %hundred, %d : i32
  core.return %r
""")
        emit("CWE369", kind, "div_by_zero" if bad else "none", body)

# ---------------------------------------------------------------- CWE-190 integer overflow
for kind, chk, opn in (("add", "sadd_ovf", "add"), ("mul", "smul_ovf", "mul")):
    for bad in (True, False):
        guard = "" if bad else """  %lim = core.const 1000 : i32
  %small = core.icmp slt %x, %lim : bool
  core.assume %small
  %nlim = core.const -1000 : i32
  %small2 = core.icmp sgt %x, %nlim : bool
  core.assume %small2
"""
        body = func("f", ["i32"], "i32", f"""^entry(%x: i32):
{guard}  %k = core.const 100000 : i32
  core.check.{chk} %x, %k
  %r = core.{opn} %x, %k {{sov}} : i32
  core.return %r
""")
        emit("CWE190", kind, "signed_overflow" if bad else "none", body)

# ---------------------------------------------------------------- CWE-562 return of stack address
for bad in (True, False):
    callee = func("make", [], "ptr", ("""^entry:
  %p = core.alloca {size=4, align=4} : ptr
  %c = core.const 7 : i32
  core.store %c, %p
  core.return %p
""" if bad else """^entry:
  %n = core.const 4 : i64
  %p = core.heap_alloc %n {fail=never} : ptr
  %c = core.const 7 : i32
  core.store %c, %p
  core.return %p
"""))
    body = callee + func("f", ["i32"], "i32", """^entry(%x: i32):
  %p = core.call @make() : ptr
  core.check.null %p
  core.check.uaf %p
  %v = core.load %p : i32
  core.return %v
""")
    emit("CWE562", "ret_addr", "use_after_scope" if bad else "none", body)

# ---------------------------------------------------------------- CWE-590 / CWE-761 free of non-heap / interior pointer
body = func("f", ["i32"], "i32", """^entry(%x: i32):
  %p = core.alloca {size=8} : ptr
  core.call @free(%p)
  core.return %x
""")
emit("CWE590", "stack", "invalid_free", body, libc=True)
body = func("f", ["i32"], "i32", """^entry(%x: i32):
  %n = core.const 8 : i64
  %p = core.call @malloc(%n) : ptr
  %isn = core.is_null %p : bool
  core.cond_br %isn, ^ret, ^go
^go:
  %four = core.const 4 : i64
  %q = core.ptr_add %p, %four : ptr
  core.call @free(%q)
  core.br ^ret
^ret:
  core.return %x
""")
emit("CWE761", "interior", "invalid_free", body, libc=True)
body = func("f", ["i32"], "i32", """^entry(%x: i32):
  %n = core.const 8 : i64
  %p = core.call @malloc(%n) : ptr
  core.call @free(%p)
  core.return %x
""")
emit("CWE590", "heap", "none", body, libc=True)

# ---------------------------------------------------------------- CWE-195 sign extension (DESIGN.md §19.9 example 1)
for bad in (True, False):
    neg = "" if bad else """  %zero = core.const 0 : i32
  %isneg = core.icmp slt %len, %zero : bool
  core.cond_br %isneg, ^rej, ^c2
^rej:
  %m1 = core.const -1 : i32
  core.return %m1
^c2:
"""
    body = func("f", ["i32"], "i32", f"""^entry(%len: i32):
  %max = core.const 256 : i32
  %big = core.icmp sgt %len, %max : bool
  core.cond_br %big, ^reject, ^go
^reject:
  %m2 = core.const -2 : i32
  core.return %m2
^go:
{neg}  %n = core.sext %len : i64
  %lim = core.const 256 : i64
  %ok = core.icmp ule %n, %lim : bool
  core.assert %ok {{msg="size exceeds buffer"}}
  core.return %len
""")
    emit("CWE195", "sext", "assert" if bad else "none", body)

os.makedirs(OUT, exist_ok=True)
for f in os.listdir(OUT):
    if f.endswith(".core"):
        os.remove(os.path.join(OUT, f))
for name, text in sorted(files.items()):
    open(os.path.join(OUT, name), "w").write(text)
print(f"wrote {len(files)} files to {os.path.normpath(OUT)}")
