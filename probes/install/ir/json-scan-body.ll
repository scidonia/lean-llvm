; The JSON window scanner as authored IR: the counter, the carry and the stop
; word live in memory, the per-lane rule is select-based, and the carry crosses
; the window's boundary in a 16-byte state slot.  A full window takes the vector
; path (one load of thirty-two bytes and the quote, backslash and b < 0x20 lane
; masks); a shorter window takes the same lane body with the byte's own
; predicates as its skip bits.
;
; Emitted from LeanLLVM.Vellum.JsonScanBody.scanWindowBody -- the AST in
; LeanLLVM/Vellum/JsonScanBody.lean that LeanLLVM/Vellum/JsonScanIR.lean parses
; this file back to -- with
;
;   nix develop -c bash -c 'lake exe leanllvm-json-scan-emit > probes/install/ir/json-scan-body.ll'
;
; through LeanLLVM.Function.render, the framework's own printer.
;
; The refinement statement about this text is not yet proved: LeanLLVM/Vellum/
; JsonScanIR.lean pins the text to the AST and proves the prefix facts the
; statement rests on, and its own header records what is outstanding.  Until
; that theorem exists, nothing here is certified, and the manifest must not
; name this fixture.
;
; This is not the output of Lean's native compiler and not the output of clang:
; no `lean -c` C emission and no clang lowering is involved, and nothing in the
; text below was removed or rewritten after rendering.  The AVX2 body in
; probes/install/json/scan-window.candidate.c, and the fixture its capture
; script writes, are the algorithm's source and its measured inventory; they are
; not this body and they are not certified.
define i32 @leanllvm_json_scan_window(ptr %in, ptr %out, ptr %state, i32 %valid) {
entry:
  %k = alloca i64, align 8
  %maskp = alloca i32, align 4
  %stopp = alloca i32, align 4
  %v64 = zext i32 %valid to i64
  store i64 0, ptr %k
  store i32 0, ptr %maskp
  store i32 0, ptr %stopp
  %qmp = alloca i32, align 4
  %smp = alloca i32, align 4
  %cmp = alloca i32, align 4
  store i32 0, ptr %qmp
  store i32 0, ptr %smp
  store i32 0, ptr %cmp
  %short = icmp ne i32 %valid, 32
  br i1 %short, label %cond, label %wide

wide:
  %vv = load <32 x i8>, ptr %in
  %qv = icmp eq <32 x i8> %vv, splat (i8 34)
  %qm = bitcast <32 x i1> %qv to i32
  %sv = icmp eq <32 x i8> %vv, splat (i8 92)
  %sm = bitcast <32 x i1> %sv to i32
  %cv = icmp ult <32 x i8> %vv, splat (i8 32)
  %cm = bitcast <32 x i1> %cv to i32
  store i32 %qm, ptr %qmp
  store i32 %sm, ptr %smp
  store i32 %cm, ptr %cmp
  br label %cond

cond:
  %kc = load i64, ptr %k
  %lt = icmp ult i64 %kc, %v64
  br i1 %lt, label %body, label %done

body:
  %ki = load i64, ptr %k
  %k32 = trunc i64 %ki to i32
  %one = shl i32 1, %k32
  %bp = getelementptr inbounds i8, ptr %in, i64 %ki
  %b = load i8, ptr %bp
  %q0 = load i32, ptr %qmp
  %q1 = lshr i32 %q0, %k32
  %q2 = and i32 %q1, 1
  %q3 = icmp ne i32 %q2, 0
  %q4 = icmp eq i8 %b, 34
  %qb = or i1 %q3, %q4
  %s0 = load i32, ptr %smp
  %s1 = lshr i32 %s0, %k32
  %s2 = and i32 %s1, 1
  %s3 = icmp ne i32 %s2, 0
  %s4 = icmp eq i8 %b, 92
  %sb = or i1 %s3, %s4
  %c0 = load i32, ptr %cmp
  %c1 = lshr i32 %c0, %k32
  %c2 = and i32 %c1, 1
  %c3 = icmp ne i32 %c2, 0
  %c4 = icmp ult i8 %b, 32
  %cb = or i1 %c3, %c4
  %b64 = zext i8 %b to i64
  %bt = and i64 %b64, 63
  %g64 = icmp ult i8 %b, 64
  %g128 = icmp ult i8 %b, 128
  %t0 = select i1 %g128, i64 2882303762456641536, i64 0
  %t1 = select i1 %g64, i64 288247989812602368, i64 %t0
  %sh = lshr i64 %t1, %bt
  %sb1 = and i64 %sh, 1
  %stb = icmp ne i64 %sb1, 0
  %m0 = load i32, ptr %maskp
  %m1 = or i32 %m0, %one
  %m2 = select i1 %stb, i32 %m1, i32 %m0
  store i32 %m2, ptr %maskp
  %f = load i32, ptr %state
  %sp4 = getelementptr inbounds i8, ptr %state, i32 4
  %nw = load i32, ptr %sp4
  %sp8 = getelementptr inbounds i8, ptr %state, i32 8
  %lo = load i32, ptr %sp8
  %sp12 = getelementptr inbounds i8, ptr %state, i32 12
  %hi = load i32, ptr %sp12
  %stp = load i32, ptr %stopp
  %live = icmp eq i32 %stp, 0
  %innb = and i32 %f, 1
  %inn = icmp ne i32 %innb, 0
  %oddb = and i32 %f, 2
  %odd = icmp ne i32 %oddb, 0
  %ninn = xor i1 %inn, 1
  %mre = icmp ne i32 %nw, 0
  %nmre = icmp eq i32 %nw, 0
  %lov = and i32 %lo, 255
  %hiv = and i32 %hi, 255
  %b32 = zext i8 %b to i32
  %ilo = icmp ule i32 %lov, %b32
  %ihi = icmp ule i32 %b32, %hiv
  %irg = and i1 %ilo, %ihi
  %nirg = xor i1 %irg, 1
  %uok = and i1 %mre, %irg
  %ubad = and i1 %mre, %nirg
  %nod = and i1 %nmre, %odd
  %nodd = xor i1 %odd, 1
  %npm = and i1 %nmre, %nodd
  %aq = and i1 %npm, %qb
  %aqo = and i1 %aq, %ninn
  %aqc = and i1 %aq, %inn
  %nq = xor i1 %qb, 1
  %npq = and i1 %npm, %nq
  %abs = and i1 %npq, %sb
  %absin = and i1 %abs, %inn
  %nbs = xor i1 %sb, 1
  %npb = and i1 %npq, %nbs
  %ib = and i1 %npb, %inn
  %ncb = xor i1 %cb, 1
  %actl = and i1 %ib, %cb
  %leadb = and i1 %ib, %ncb
  %asc = icmp ult i8 %b, 128
  %nasc = xor i1 %asc, 1
  %lead = and i1 %leadb, %nasc
  %lge = icmp uge i8 %b, 194
  %lle = icmp ule i8 %b, 244
  %lok = and i1 %lge, %lle
  %nlok = xor i1 %lok, 1
  %lbad = and i1 %lead, %nlok
  %lset = and i1 %lead, %lok
  %sk0 = and i1 %inn, %nodd
  %sk1 = and i1 %sk0, %nmre
  %sk2 = and i1 %sk1, %nq
  %sk3 = and i1 %sk2, %nbs
  %sk4 = and i1 %sk3, %ncb
  %skip = and i1 %sk4, %asc
  %b3 = icmp uge i8 %b, 240
  %b2 = icmp uge i8 %b, 224
  %n3v = select i1 %b3, i32 3, i32 2
  %nc = select i1 %b2, i32 %n3v, i32 1
  %e0 = icmp eq i8 %b, 224
  %f0 = icmp eq i8 %b, 240
  %lc0 = select i1 %f0, i32 144, i32 128
  %lc = select i1 %e0, i32 160, i32 %lc0
  %q1b = icmp eq i8 %b, 237
  %q2b = icmp eq i8 %b, 244
  %hc0 = select i1 %q2b, i32 143, i32 191
  %hc = select i1 %q1b, i32 159, i32 %hc0
  %lane1 = add i32 %k32, 1
  %wcl = add i32 %lane1, 64
  %wct = add i32 %lane1, 640
  %wbd = add i32 %lane1, 896
  %sw0 = select i1 %lbad, i32 %wbd, i32 %wct
  %sw1 = select i1 %actl, i32 %wct, i32 %sw0
  %sw2 = select i1 %aqc, i32 %wcl, i32 %sw1
  %ras = or i1 %ubad, %actl
  %ras2 = or i1 %ras, %lbad
  %raise = or i1 %ras2, %aqc
  %stp0 = and i1 %live, %raise
  %stpn = select i1 %stp0, i32 %sw2, i32 %stp
  store i32 %stpn, ptr %stopp
  %nact = xor i1 %skip, 1
  %act = and i1 %live, %nact
  %nw0 = sub i32 %nw, 1
  %fc0 = xor i32 %f, 2
  %f1 = select i1 %nod, i32 %fc0, i32 %f
  %fq1 = or i32 %f1, 1
  %f2 = select i1 %aqo, i32 %fq1, i32 %f1
  %fb1 = or i32 %f2, 2
  %f3 = select i1 %absin, i32 %fb1, i32 %f2
  %cw0 = select i1 %uok, i32 %nw0, i32 %nw
  %cw1 = select i1 %lset, i32 %nc, i32 %cw0
  %lw0 = select i1 %uok, i32 128, i32 %lov
  %lw1 = select i1 %lset, i32 %lc, i32 %lw0
  %hw0 = select i1 %uok, i32 191, i32 %hiv
  %hw1 = select i1 %lset, i32 %hc, i32 %hw0
  %fout = select i1 %act, i32 %f3, i32 %f
  %cout = select i1 %act, i32 %cw1, i32 %nw
  %lout = select i1 %act, i32 %lw1, i32 %lo
  %hout = select i1 %act, i32 %hw1, i32 %hi
  store i32 %fout, ptr %state
  store i32 %cout, ptr %sp4
  store i32 %lout, ptr %sp8
  store i32 %hout, ptr %sp12
  %kn = add i64 %ki, 1
  store i64 %kn, ptr %k
  br label %cond

done:
  %rm = load i32, ptr %maskp
  store i32 %rm, ptr %out
  %rs = load i32, ptr %stopp
  ret i32 %rs
}
