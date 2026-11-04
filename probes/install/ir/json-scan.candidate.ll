; The window scanner as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-json-scan.sh
;
; This is not the certified body.  The certified body is printed from
; LeanLLVM/Vellum/JsonScanBody.lean -- the AST that
; LeanLLVM/Vellum/JsonScanIR.lean parses probes/install/ir/json-scan-body.ll
; back to and proves the refinement statement about -- into
; probes/install/ir/json-scan-body.ll.  What follows is the same algorithm as
; the compiler builds it, and it is kept as the measured record of the shapes
; this fragment has to carry: no manifest arm names this fixture, the installed
; unit is the printed body, and nothing here certifies these bytes.
;
; It is captured from probes/install/json/scan-window.candidate.c, emitted with
;
;   clang -S -emit-llvm -O2 -mavx2 -fno-slp-vectorize probes/install/json/scan-window.candidate.c
;
; and demoted with
;
;   opt -passes='reg2mem,instnamer'
;
; then the verbatim `define` block of @leanllvm_json_scan_window, with the
; textual syntax listed in capture-json-scan.sh removed.  `instnamer` labels
; the entry block (the parser requires a label on every block) and names
; values; it changes no instruction.
;
; The optimiser form is clang 21.1.8 at -O2 -mavx2 for
; x86_64-unknown-linux-gnu with +avx2.  `reg2mem` is not a convenience: the
; fragment has no `phi`, and every loop-carried value clang promotes -- the
; lane counter, the loop-invariant masks, the values the byte rule's arms
; merge -- is demoted into an `alloca` with a store on each incoming
; path and a load at each use, which is the memory-carried loop the module
; proves.  `-fno-slp-vectorize` keeps the SLP vectoriser from rewriting the
; scalar structural-mask pass into `insertelement`/`shufflevector`.
;
; Removed before the parser sees the text, each because it does not change the
; value computed: `noundef`; `readonly`; `writeonly`; `captures(none)`;
; `local_unnamed_addr`; `#0` and the `attributes #0 = { ... }` group
; (including `memory(argmem: readwrite)` and the target-feature list);
; `, align N`; `, !tbaa !N`; every `!llvm.*` and `!N = ...` line;
; `target datalayout`; `target triple`; `source_filename`; the
; poison-promise flags `nuw`, `nsw`, `nneg`, `exact` and `disjoint`;
; `range(i32 64, 1)` on the `define`; and the dead
; `%"reg2mem alloca point" = bitcast i32 0 to i32` that `reg2mem` inserts as
; its alloca point.  The module configuration those lines carried is:
; x86_64-unknown-linux-gnu, little endian, 64-bit pointers, +avx2.
;
; `range(i32 64, 1)` is clang's inferred value range for the returned status
; word.  An LLVM `range` attribute is a `ConstantRange`, whose interval may
; wrap, so as written `[64, 1)` is the union of `{0}` and `[64, 2^32 - 1]`,
; not the empty set (which is spelled `[0, 0)`): the returned word is zero, or
; at least 64.  Every return of this body satisfies that -- a zero status is
; `0`, and a non-zero one carries a non-zero kind in bits 6-7, so it is at
; least 64 -- and dropping the attribute at capture therefore removes a
; caller-facing promise rather than a computation: it can only enlarge the set
; of permitted returns.  `Parser.lean` refuses a return attribute before the
; return type by name, and the fixture is the text that is compiled at the end
; of the route, so nothing semantic is crossed.
;
; The accesses carry no `align` because the parser's `load`/`store` have no
; alignment field; the contract's `scanAlignmentFree` records that none is
; required or assumed, and the theorem claims nothing about alignment.
;
; Measured inventory of the block below (counted on this text):
;   blocks 37, allocas 100
;   scalar memory: load i32 144, store i32 141, load i8 24,
;                  store i8 2, load i1 7, store i1 5,
;                  getelementptr 5
;   vector: load <32 x i8> 1, icmp eq <32 x i8> 2,
;           icmp ult <32 x i8> 1, bitcast mask 3
;   scalar arithmetic: lshr i64 1, shl 6, and 8, or 23,
;                      add 6, mul 2, sub 0
;   terminators: condbr 14, br 22, ret 1
;
; The body reads the first `valid` bytes once for the structural mask and once
; for the byte rule, writes the mask at `%out` and the carry in the sixteen
; bytes at `%state`, calls nothing, and contains no `phi`, no vector store,
; no vector `alloca`, no shuffle and no intrinsic.
define i32 @leanllvm_json_scan_window(ptr %arg, ptr %arg305, ptr %arg306, i32 %arg307) {
bb:
  %.reg2mem = alloca i64
  %.reg2mem12 = alloca i32
  %.reg2mem14 = alloca i32
  %.reg2mem16 = alloca i32
  %.reg2mem18 = alloca i32
  %.reg2mem20 = alloca i32
  %.reg2mem23 = alloca i32
  %.reg2mem26 = alloca i32
  %.reg2mem29 = alloca i32
  %.reg2mem32 = alloca i32
  %.reg2mem35 = alloca i32
  %.reg2mem37 = alloca i32
  %.reg2mem39 = alloca i32
  %.reg2mem41 = alloca i32
  %.reg2mem43 = alloca i32
  %.reg2mem47 = alloca i32
  %.reg2mem51 = alloca i32
  %.reg2mem55 = alloca i32
  %.reg2mem57 = alloca i32
  %.reg2mem59 = alloca i32
  %.reg2mem61 = alloca i32
  %.reg2mem63 = alloca i32
  %.reg2mem65 = alloca i32
  %.reg2mem67 = alloca i32
  %.reg2mem69 = alloca i32
  %.reg2mem71 = alloca i32
  %.reg2mem73 = alloca i32
  %.reg2mem75 = alloca i32
  %.reg2mem78 = alloca i32
  %.reg2mem82 = alloca i32
  %.reg2mem86 = alloca i32
  %.reg2mem90 = alloca i32
  %.reg2mem95 = alloca i32
  %.reg2mem97 = alloca i1
  %.reg2mem99 = alloca i1
  %.reg2mem101 = alloca i1
  %.reg2mem103 = alloca i32
  %.reg2mem107 = alloca i1
  %.reg2mem110 = alloca i32
  %.reg2mem118 = alloca i32
  %.reg2mem121 = alloca i8
  %.reg2mem138 = alloca i32
  %.reg2mem142 = alloca i32
  %.reg2mem148 = alloca i32
  %.reg2mem153 = alloca i32
  %.reg2mem158 = alloca i32
  %.reg2mem163 = alloca i64
  %.reg2mem171 = alloca i64
  %.reg2mem174 = alloca i32
  %.reg2mem177 = alloca i32
  %.reg2mem180 = alloca i32
  %.reg2mem183 = alloca i32
  %.reg2mem185 = alloca i32
  %.reg2mem187 = alloca i32
  %.reg2mem189 = alloca i32
  %.reg2mem192 = alloca i32
  %.reg2mem197 = alloca i8
  %.reg2mem204 = alloca i32
  %.reg2mem207 = alloca i32
  %.reg2mem210 = alloca i32
  %.reg2mem213 = alloca i64
  %.reg2mem217 = alloca i64
  %.reg2mem219 = alloca i32
  %.reg2mem221 = alloca i32
  %.reg2mem223 = alloca i32
  %.reg2mem225 = alloca i32
  %.reg2mem227 = alloca ptr
  %.reg2mem230 = alloca ptr
  %.reg2mem233 = alloca ptr
  %.reg2mem236 = alloca i64
  %.reg2mem238 = alloca i32
  %.reg2mem240 = alloca i32
  %.reg2mem242 = alloca i32
  %.reg2mem244 = alloca i32
  %.reg2mem246 = alloca i32
  %.reg2mem248 = alloca i32
  %.reg2mem250 = alloca i1
  %.reg2mem253 = alloca i32
  %.reg2mem255 = alloca i32
  %.reg2mem257 = alloca i32
  %.reg2mem259 = alloca i32
  %.reg2mem261 = alloca i32
  %.reg2mem263 = alloca i32
  %.reg2mem265 = alloca i32
  %.reg2mem267 = alloca i32
  %.reg2mem269 = alloca i32
  %.reg2mem271 = alloca i32
  %.reg2mem273 = alloca i32
  %.reg2mem275 = alloca i32
  %.reg2mem277 = alloca i32
  %.reg2mem279 = alloca i32
  %.reg2mem281 = alloca i64
  %.reg2mem283 = alloca i32
  %.reg2mem285 = alloca i32
  %.reg2mem287 = alloca i32
  %.reg2mem289 = alloca i32
  %.reg2mem291 = alloca i32
  %.reg2mem293 = alloca i32
  %.reg2mem295 = alloca i32
  %.reg2mem297 = alloca i64
  %.reg2mem299 = alloca i32
  %.reg2mem301 = alloca i32
  %.reg2mem303 = alloca i32
  %i = icmp eq i32 %arg307, 32
  store i1 %i, ptr %.reg2mem250
  %.reload252 = load i1, ptr %.reg2mem250
  br i1 %.reload252, label %bb308, label %bb316

bb308:                                            ; preds = %bb
  %i309 = load <32 x i8>, ptr %arg
  %i310 = icmp eq <32 x i8> %i309, splat (i8 34)
  %i311 = bitcast <32 x i1> %i310 to i32
  store i32 %i311, ptr %.reg2mem248
  %i312 = icmp eq <32 x i8> %i309, splat (i8 92)
  %i313 = bitcast <32 x i1> %i312 to i32
  store i32 %i313, ptr %.reg2mem246
  %i314 = icmp ult <32 x i8> %i309, splat (i8 32)
  %i315 = bitcast <32 x i1> %i314 to i32
  store i32 %i315, ptr %.reg2mem244
  %.reload245 = load i32, ptr %.reg2mem244
  %.reload247 = load i32, ptr %.reg2mem246
  %.reload249 = load i32, ptr %.reg2mem248
  store i32 %.reload245, ptr %.reg2mem299
  store i32 %.reload247, ptr %.reg2mem301
  store i32 %.reload249, ptr %.reg2mem303
  br label %bb319

bb316:                                            ; preds = %bb
  %i317 = icmp eq i32 %arg307, 0
  br i1 %i317, label %bb318, label %._crit_edge

._crit_edge:                                      ; preds = %bb316
  store i32 0, ptr %.reg2mem299
  store i32 0, ptr %.reg2mem301
  store i32 0, ptr %.reg2mem303
  br label %bb319

bb318:                                            ; preds = %bb316
  store i32 0, ptr %arg305
  store i32 0, ptr %.reg2mem253
  br label %bb505

bb319:                                            ; preds = %._crit_edge, %bb308
  %.reload304 = load i32, ptr %.reg2mem303
  %.reload302 = load i32, ptr %.reg2mem301
  %.reload300 = load i32, ptr %.reg2mem299
  store i32 %.reload304, ptr %.reg2mem242
  store i32 %.reload302, ptr %.reg2mem240
  store i32 %.reload300, ptr %.reg2mem238
  %i320 = zext i32 %arg307 to i64
  store i64 %i320, ptr %.reg2mem236
  %.reload239 = load i32, ptr %.reg2mem238
  %.reload241 = load i32, ptr %.reg2mem240
  %.reload243 = load i32, ptr %.reg2mem242
  store i32 %.reload239, ptr %.reg2mem289
  store i32 %.reload241, ptr %.reg2mem291
  store i32 %.reload243, ptr %.reg2mem293
  store i32 0, ptr %.reg2mem295
  store i64 0, ptr %.reg2mem297
  br label %bb330

bb321:                                            ; preds = %bb358
  %.reload190 = load i32, ptr %.reg2mem189
  store i32 %.reload190, ptr %arg305
  %i322 = getelementptr inbounds i8, ptr %arg306, i64 4
  store ptr %i322, ptr %.reg2mem233
  %i323 = getelementptr inbounds i8, ptr %arg306, i64 8
  store ptr %i323, ptr %.reg2mem230
  %i324 = getelementptr inbounds i8, ptr %arg306, i64 12
  store ptr %i324, ptr %.reg2mem227
  %i325 = load i32, ptr %arg306
  store i32 %i325, ptr %.reg2mem225
  %.reload235 = load ptr, ptr %.reg2mem233
  %i326 = load i32, ptr %.reload235
  store i32 %i326, ptr %.reg2mem223
  %.reload232 = load ptr, ptr %.reg2mem230
  %i327 = load i32, ptr %.reload232
  store i32 %i327, ptr %.reg2mem221
  %.reload229 = load ptr, ptr %.reg2mem227
  %i328 = load i32, ptr %.reload229
  store i32 %i328, ptr %.reg2mem219
  %i329 = zext i32 %arg307 to i64
  store i64 %i329, ptr %.reg2mem217
  %.reload220 = load i32, ptr %.reg2mem219
  %.reload222 = load i32, ptr %.reg2mem221
  %.reload224 = load i32, ptr %.reg2mem223
  %.reload226 = load i32, ptr %.reg2mem225
  store i32 %.reload226, ptr %.reg2mem273
  store i32 %.reload224, ptr %.reg2mem275
  store i32 %.reload222, ptr %.reg2mem277
  store i32 %.reload220, ptr %.reg2mem279
  store i64 0, ptr %.reg2mem281
  br label %bb361

bb330:                                            ; preds = %._crit_edge2, %bb319
  %.reload298 = load i64, ptr %.reg2mem297
  %.reload296 = load i32, ptr %.reg2mem295
  %.reload294 = load i32, ptr %.reg2mem293
  %.reload292 = load i32, ptr %.reg2mem291
  %.reload290 = load i32, ptr %.reg2mem289
  store i64 %.reload298, ptr %.reg2mem213
  store i32 %.reload294, ptr %.reg2mem210
  store i32 %.reload292, ptr %.reg2mem207
  store i32 %.reload290, ptr %.reg2mem204
  %.reload216 = load i64, ptr %.reg2mem213
  %i331 = getelementptr inbounds i8, ptr %arg, i64 %.reload216
  %i332 = load i8, ptr %i331
  store i8 %i332, ptr %.reg2mem197
  %.reload203 = load i8, ptr %.reg2mem197
  %i333 = icmp ult i8 %.reload203, 64
  %.reload202 = load i8, ptr %.reg2mem197
  %i334 = icmp sgt i8 %.reload202, -1
  %i335 = select i1 %i334, i64 2882303762456641536, i64 0
  %i336 = select i1 %i333, i64 288247989812602368, i64 %i335
  %.reload201 = load i8, ptr %.reg2mem197
  %i337 = and i8 %.reload201, 63
  %i338 = zext i8 %i337 to i64
  %i339 = lshr i64 %i336, %i338
  %i340 = trunc i64 %i339 to i32
  %i341 = and i32 %i340, 1
  %.reload215 = load i64, ptr %.reg2mem213
  %i342 = trunc i64 %.reload215 to i32
  store i32 %i342, ptr %.reg2mem192
  %.reload196 = load i32, ptr %.reg2mem192
  %i343 = shl i32 %i341, %.reload196
  %i344 = or i32 %i343, %.reload296
  store i32 %i344, ptr %.reg2mem189
  %.reload251 = load i1, ptr %.reg2mem250
  br i1 %.reload251, label %._crit_edge1, label %bb345

._crit_edge1:                                     ; preds = %bb330
  %.reload205 = load i32, ptr %.reg2mem204
  %.reload208 = load i32, ptr %.reg2mem207
  %.reload211 = load i32, ptr %.reg2mem210
  store i32 %.reload211, ptr %.reg2mem283
  store i32 %.reload208, ptr %.reg2mem285
  store i32 %.reload205, ptr %.reg2mem287
  br label %bb358

bb345:                                            ; preds = %bb330
  %.reload200 = load i8, ptr %.reg2mem197
  %i346 = icmp eq i8 %.reload200, 34
  %i347 = zext i1 %i346 to i32
  %.reload195 = load i32, ptr %.reg2mem192
  %i348 = shl i32 %i347, %.reload195
  %.reload212 = load i32, ptr %.reg2mem210
  %i349 = or i32 %i348, %.reload212
  store i32 %i349, ptr %.reg2mem187
  %.reload199 = load i8, ptr %.reg2mem197
  %i350 = icmp eq i8 %.reload199, 92
  %i351 = zext i1 %i350 to i32
  %.reload194 = load i32, ptr %.reg2mem192
  %i352 = shl i32 %i351, %.reload194
  %.reload209 = load i32, ptr %.reg2mem207
  %i353 = or i32 %i352, %.reload209
  store i32 %i353, ptr %.reg2mem185
  %.reload198 = load i8, ptr %.reg2mem197
  %i354 = icmp ult i8 %.reload198, 32
  %i355 = zext i1 %i354 to i32
  %.reload193 = load i32, ptr %.reg2mem192
  %i356 = shl i32 %i355, %.reload193
  %.reload206 = load i32, ptr %.reg2mem204
  %i357 = or i32 %i356, %.reload206
  store i32 %i357, ptr %.reg2mem183
  %.reload184 = load i32, ptr %.reg2mem183
  %.reload186 = load i32, ptr %.reg2mem185
  %.reload188 = load i32, ptr %.reg2mem187
  store i32 %.reload188, ptr %.reg2mem283
  store i32 %.reload186, ptr %.reg2mem285
  store i32 %.reload184, ptr %.reg2mem287
  br label %bb358

bb358:                                            ; preds = %._crit_edge1, %bb345
  %.reload288 = load i32, ptr %.reg2mem287
  %.reload286 = load i32, ptr %.reg2mem285
  %.reload284 = load i32, ptr %.reg2mem283
  store i32 %.reload288, ptr %.reg2mem180
  store i32 %.reload286, ptr %.reg2mem177
  store i32 %.reload284, ptr %.reg2mem174
  %.reload214 = load i64, ptr %.reg2mem213
  %i359 = add i64 %.reload214, 1
  store i64 %i359, ptr %.reg2mem171
  %.reload172 = load i64, ptr %.reg2mem171
  %.reload237 = load i64, ptr %.reg2mem236
  %i360 = icmp eq i64 %.reload172, %.reload237
  br i1 %i360, label %bb321, label %._crit_edge2

._crit_edge2:                                     ; preds = %bb358
  %.reload173 = load i64, ptr %.reg2mem171
  %.reload176 = load i32, ptr %.reg2mem174
  %.reload179 = load i32, ptr %.reg2mem177
  %.reload182 = load i32, ptr %.reg2mem180
  %.reload191 = load i32, ptr %.reg2mem189
  store i32 %.reload182, ptr %.reg2mem289
  store i32 %.reload179, ptr %.reg2mem291
  store i32 %.reload176, ptr %.reg2mem293
  store i32 %.reload191, ptr %.reg2mem295
  store i64 %.reload173, ptr %.reg2mem297
  br label %bb330

bb361:                                            ; preds = %._crit_edge10, %bb321
  %.reload282 = load i64, ptr %.reg2mem281
  %.reload280 = load i32, ptr %.reg2mem279
  %.reload278 = load i32, ptr %.reg2mem277
  %.reload276 = load i32, ptr %.reg2mem275
  %.reload274 = load i32, ptr %.reg2mem273
  store i64 %.reload282, ptr %.reg2mem163
  store i32 %.reload280, ptr %.reg2mem158
  store i32 %.reload278, ptr %.reg2mem153
  store i32 %.reload276, ptr %.reg2mem148
  store i32 %.reload274, ptr %.reg2mem142
  %.reload170 = load i64, ptr %.reg2mem163
  %i362 = trunc i64 %.reload170 to i32
  %i363 = shl i32 1, %i362
  store i32 %i363, ptr %.reg2mem138
  %.reload169 = load i64, ptr %.reg2mem163
  %i364 = getelementptr inbounds i8, ptr %arg, i64 %.reload169
  %i365 = load i8, ptr %i364
  store i8 %i365, ptr %.reg2mem121
  %.reload137 = load i8, ptr %.reg2mem121
  %i366 = zext i8 %.reload137 to i32
  store i32 %i366, ptr %.reg2mem118
  %.reload147 = load i32, ptr %.reg2mem142
  %i367 = and i32 %.reload147, 3
  store i32 %i367, ptr %.reg2mem110
  %.reload117 = load i32, ptr %.reg2mem110
  %i368 = icmp eq i32 %.reload117, 1
  %.reload152 = load i32, ptr %.reg2mem148
  %i369 = icmp eq i32 %.reload152, 0
  store i1 %i369, ptr %.reg2mem107
  %.reload109 = load i1, ptr %.reg2mem107
  %i370 = select i1 %i368, i1 %.reload109, i1 false
  %.reload141 = load i32, ptr %.reg2mem138
  %.reload175 = load i32, ptr %.reg2mem174
  %i371 = and i32 %.reload141, %.reload175
  %i372 = icmp eq i32 %i371, 0
  %i373 = select i1 %i370, i1 %i372, i1 false
  %.reload140 = load i32, ptr %.reg2mem138
  %.reload178 = load i32, ptr %.reg2mem177
  %i374 = and i32 %.reload140, %.reload178
  %i375 = icmp eq i32 %i374, 0
  %i376 = select i1 %i373, i1 %i375, i1 false
  br i1 %i376, label %bb377, label %._crit_edge3

._crit_edge3:                                     ; preds = %bb361
  br label %bb382

bb377:                                            ; preds = %bb361
  %.reload139 = load i32, ptr %.reg2mem138
  %.reload181 = load i32, ptr %.reg2mem180
  %i378 = and i32 %.reload139, %.reload181
  %i379 = icmp eq i32 %i378, 0
  %.reload136 = load i8, ptr %.reg2mem121
  %i380 = icmp sgt i8 %.reload136, -1
  %i381 = select i1 %i379, i1 %i380, i1 false
  br i1 %i381, label %._crit_edge4, label %._crit_edge5

._crit_edge5:                                     ; preds = %bb377
  br label %bb382

._crit_edge4:                                     ; preds = %bb377
  %.reload143 = load i32, ptr %.reg2mem142
  %.reload154 = load i32, ptr %.reg2mem153
  %.reload159 = load i32, ptr %.reg2mem158
  store i32 %.reload143, ptr %.reg2mem255
  store i32 0, ptr %.reg2mem257
  store i32 %.reload154, ptr %.reg2mem259
  store i32 %.reload159, ptr %.reg2mem261
  br label %bb502

bb382:                                            ; preds = %._crit_edge5, %._crit_edge3
  %.reload146 = load i32, ptr %.reg2mem142
  %i383 = and i32 %.reload146, 1
  store i32 %i383, ptr %.reg2mem103
  %.reload135 = load i8, ptr %.reg2mem121
  %i384 = icmp eq i8 %.reload135, 34
  store i1 %i384, ptr %.reg2mem101
  %.reload134 = load i8, ptr %.reg2mem121
  %i385 = icmp eq i8 %.reload134, 92
  store i1 %i385, ptr %.reg2mem99
  %.reload133 = load i8, ptr %.reg2mem121
  %i386 = icmp ugt i8 %.reload133, 31
  store i1 %i386, ptr %.reg2mem97
  %.reload132 = load i8, ptr %.reg2mem121
  %i387 = icmp sgt i8 %.reload132, 31
  %.reload145 = load i32, ptr %.reg2mem142
  %i388 = select i1 %i387, i32 %.reload145, i32 0
  store i32 %i388, ptr %.reg2mem95
  %.reload131 = load i8, ptr %.reg2mem121
  %i389 = add i8 %.reload131, 62
  %i390 = icmp ult i8 %i389, 30
  %i391 = zext i1 %i390 to i32
  %.reload130 = load i8, ptr %.reg2mem121
  %i392 = icmp eq i8 %.reload130, -32
  %.reload129 = load i8, ptr %.reg2mem121
  %i393 = icmp eq i8 %.reload129, -19
  %.reload128 = load i8, ptr %.reg2mem121
  %i394 = and i8 %.reload128, -2
  %i395 = icmp eq i8 %i394, -18
  %i396 = zext i1 %i395 to i32
  %.reload127 = load i8, ptr %.reg2mem121
  %i397 = icmp eq i8 %.reload127, -16
  %i398 = zext i1 %i397 to i32
  %.reload126 = load i8, ptr %.reg2mem121
  %i399 = add i8 %.reload126, 15
  %i400 = icmp ult i8 %i399, 3
  %i401 = zext i1 %i400 to i32
  %.reload125 = load i8, ptr %.reg2mem121
  %i402 = icmp eq i8 %.reload125, -12
  %i403 = zext i1 %i402 to i32
  %.reload124 = load i8, ptr %.reg2mem121
  %i404 = add i8 %.reload124, 31
  %i405 = icmp ult i8 %i404, 13
  %.reload123 = load i8, ptr %.reg2mem121
  %i406 = add i8 %.reload123, 32
  %i407 = icmp ult i8 %i406, 14
  %i408 = zext i1 %i407 to i32
  %i409 = or i32 %i408, %i398
  %i410 = or i32 %i409, %i403
  %i411 = or i32 %i410, %i391
  %i412 = or i32 %i411, %i396
  %i413 = or i32 %i412, %i401
  store i32 %i413, ptr %.reg2mem90
  %i414 = or i32 %i408, %i396
  %i415 = shl i32 %i414, 1
  %i416 = or i32 %i401, %i403
  %i417 = or i32 %i416, %i398
  %i418 = mul i32 %i417, 3
  %i419 = or i32 %i418, %i415
  %i420 = or i32 %i419, %i391
  store i32 %i420, ptr %.reg2mem86
  %i421 = select i1 %i390, i32 128, i32 0
  %i422 = select i1 %i392, i32 160, i32 0
  %i423 = select i1 %i397, i32 144, i32 0
  %i424 = or i32 %i423, %i422
  %i425 = or i32 %i424, %i421
  %.reload122 = load i8, ptr %.reg2mem121
  %i426 = add i8 %.reload122, 15
  %i427 = icmp ult i8 %i426, 4
  %i428 = or i1 %i405, %i427
  %i429 = or i1 %i428, %i395
  %i430 = select i1 %i429, i32 128, i32 0
  %i431 = or i32 %i430, %i425
  store i32 %i431, ptr %.reg2mem82
  %i432 = icmp ult i8 %i389, 43
  %i433 = select i1 %i393, i32 159, i32 0
  %i434 = select i1 %i432, i32 191, i32 %i433
  %i435 = select i1 %i395, i32 191, i32 0
  %i436 = or i32 %i434, %i435
  %i437 = select i1 %i397, i32 191, i32 %i436
  %i438 = select i1 %i402, i32 143, i32 0
  %i439 = select i1 %i400, i32 191, i32 %i438
  %i440 = or i32 %i439, %i437
  store i32 %i440, ptr %.reg2mem78
  %.reload108 = load i1, ptr %.reg2mem107
  br i1 %.reload108, label %bb441, label %bb445

bb441:                                            ; preds = %bb382
  %.reload144 = load i32, ptr %.reg2mem142
  %i442 = and i32 %.reload144, 2
  %i443 = icmp eq i32 %i442, 0
  br i1 %i443, label %bb444, label %bb455

bb444:                                            ; preds = %bb441
  %.reload102 = load i1, ptr %.reg2mem101
  br i1 %.reload102, label %bb461, label %bb471

bb445:                                            ; preds = %bb382
  %.reload120 = load i32, ptr %.reg2mem118
  %.reload157 = load i32, ptr %.reg2mem153
  %i446 = icmp ule i32 %.reload157, %.reload120
  %.reload119 = load i32, ptr %.reg2mem118
  %.reload162 = load i32, ptr %.reg2mem158
  %i447 = icmp uge i32 %.reload162, %.reload119
  %i448 = and i1 %i446, %i447
  %i449 = sext i1 %i448 to i32
  %.reload151 = load i32, ptr %.reg2mem148
  %i450 = add i32 %.reload151, %i449
  store i32 %i450, ptr %.reg2mem75
  br i1 %i448, label %bb492, label %bb451

bb451:                                            ; preds = %bb445
  %.reload168 = load i64, ptr %.reg2mem163
  %i452 = trunc i64 %.reload168 to i32
  %i453 = add i32 %i452, 1
  %i454 = or i32 %i453, 896
  store i32 %i454, ptr %.reg2mem73
  %.reload74 = load i32, ptr %.reg2mem73
  %.reload76 = load i32, ptr %.reg2mem75
  %.reload112 = load i32, ptr %.reg2mem110
  %.reload156 = load i32, ptr %.reg2mem153
  %.reload161 = load i32, ptr %.reg2mem158
  store i32 %.reload74, ptr %.reg2mem263
  store i32 %.reload156, ptr %.reg2mem265
  store i32 %.reload112, ptr %.reg2mem267
  store i32 %.reload76, ptr %.reg2mem269
  store i32 %.reload161, ptr %.reg2mem271
  br label %bb496

bb455:                                            ; preds = %bb441
  %.reload116 = load i32, ptr %.reg2mem110
  %i456 = add i32 %.reload116, -2
  store i32 %i456, ptr %.reg2mem71
  %.reload94 = load i32, ptr %.reg2mem90
  %i457 = icmp eq i32 %.reload94, 0
  %.reload89 = load i32, ptr %.reg2mem86
  %i458 = select i1 %i457, i32 0, i32 %.reload89
  store i32 %i458, ptr %.reg2mem69
  %.reload85 = load i32, ptr %.reg2mem82
  %i459 = select i1 %i457, i32 0, i32 %.reload85
  store i32 %i459, ptr %.reg2mem67
  %.reload81 = load i32, ptr %.reg2mem78
  %i460 = select i1 %i457, i32 0, i32 %.reload81
  store i32 %i460, ptr %.reg2mem65
  %.reload66 = load i32, ptr %.reg2mem65
  %.reload68 = load i32, ptr %.reg2mem67
  %.reload70 = load i32, ptr %.reg2mem69
  %.reload72 = load i32, ptr %.reg2mem71
  store i32 0, ptr %.reg2mem263
  store i32 %.reload68, ptr %.reg2mem265
  store i32 %.reload72, ptr %.reg2mem267
  store i32 %.reload70, ptr %.reg2mem269
  store i32 %.reload66, ptr %.reg2mem271
  br label %bb496

bb461:                                            ; preds = %bb444
  %.reload93 = load i32, ptr %.reg2mem90
  %i462 = icmp eq i32 %.reload93, 0
  %.reload88 = load i32, ptr %.reg2mem86
  %i463 = select i1 %i462, i32 0, i32 %.reload88
  store i32 %i463, ptr %.reg2mem63
  %.reload84 = load i32, ptr %.reg2mem82
  %i464 = select i1 %i462, i32 0, i32 %.reload84
  store i32 %i464, ptr %.reg2mem61
  %.reload80 = load i32, ptr %.reg2mem78
  %i465 = select i1 %i462, i32 0, i32 %.reload80
  store i32 %i465, ptr %.reg2mem59
  %.reload106 = load i32, ptr %.reg2mem103
  %i466 = icmp eq i32 %.reload106, 0
  %.reload167 = load i64, ptr %.reg2mem163
  %i467 = trunc i64 %.reload167 to i32
  %i468 = add i32 %i467, 1
  %i469 = or i32 %i468, 64
  %i470 = select i1 %i466, i32 0, i32 %i469
  store i32 %i470, ptr %.reg2mem57
  %.reload58 = load i32, ptr %.reg2mem57
  %.reload60 = load i32, ptr %.reg2mem59
  %.reload62 = load i32, ptr %.reg2mem61
  %.reload64 = load i32, ptr %.reg2mem63
  store i32 %.reload58, ptr %.reg2mem263
  store i32 %.reload62, ptr %.reg2mem265
  store i32 1, ptr %.reg2mem267
  store i32 %.reload64, ptr %.reg2mem269
  store i32 %.reload60, ptr %.reg2mem271
  br label %bb496

bb471:                                            ; preds = %bb444
  %.reload105 = load i32, ptr %.reg2mem103
  %i472 = mul i32 %.reload105, 3
  store i32 %i472, ptr %.reg2mem55
  %.reload92 = load i32, ptr %.reg2mem90
  %i473 = icmp eq i32 %.reload92, 0
  %.reload87 = load i32, ptr %.reg2mem86
  %i474 = select i1 %i473, i32 0, i32 %.reload87
  store i32 %i474, ptr %.reg2mem51
  %.reload83 = load i32, ptr %.reg2mem82
  %i475 = select i1 %i473, i32 0, i32 %.reload83
  store i32 %i475, ptr %.reg2mem47
  %.reload79 = load i32, ptr %.reg2mem78
  %i476 = select i1 %i473, i32 0, i32 %.reload79
  store i32 %i476, ptr %.reg2mem43
  %.reload100 = load i1, ptr %.reg2mem99
  br i1 %.reload100, label %._crit_edge6, label %bb477

._crit_edge6:                                     ; preds = %bb471
  %.reload44 = load i32, ptr %.reg2mem43
  %.reload48 = load i32, ptr %.reg2mem47
  %.reload52 = load i32, ptr %.reg2mem51
  %.reload56 = load i32, ptr %.reg2mem55
  store i32 0, ptr %.reg2mem263
  store i32 %.reload48, ptr %.reg2mem265
  store i32 %.reload56, ptr %.reg2mem267
  store i32 %.reload52, ptr %.reg2mem269
  store i32 %.reload44, ptr %.reg2mem271
  br label %bb496

bb477:                                            ; preds = %bb471
  %.reload104 = load i32, ptr %.reg2mem103
  %i478 = icmp eq i32 %.reload104, 0
  %.reload98 = load i1, ptr %.reg2mem97
  %i479 = or i1 %.reload98, %i478
  br i1 %i479, label %bb484, label %bb480

bb480:                                            ; preds = %bb477
  %.reload166 = load i64, ptr %.reg2mem163
  %i481 = trunc i64 %.reload166 to i32
  %i482 = add i32 %i481, 1
  %i483 = or i32 %i482, 640
  store i32 %i483, ptr %.reg2mem41
  %.reload42 = load i32, ptr %.reg2mem41
  %.reload45 = load i32, ptr %.reg2mem43
  %.reload49 = load i32, ptr %.reg2mem47
  %.reload53 = load i32, ptr %.reg2mem51
  %.reload113 = load i32, ptr %.reg2mem110
  store i32 %.reload42, ptr %.reg2mem263
  store i32 %.reload49, ptr %.reg2mem265
  store i32 %.reload113, ptr %.reg2mem267
  store i32 %.reload53, ptr %.reg2mem269
  store i32 %.reload45, ptr %.reg2mem271
  br label %bb496

bb484:                                            ; preds = %bb477
  %.reload91 = load i32, ptr %.reg2mem90
  %i485 = xor i32 %.reload91, 1
  %.reload96 = load i32, ptr %.reg2mem95
  %i486 = and i32 %i485, %.reload96
  %i487 = icmp eq i32 %i486, 0
  %.reload165 = load i64, ptr %.reg2mem163
  %i488 = trunc i64 %.reload165 to i32
  %i489 = add i32 %i488, 1
  %i490 = or i32 %i489, 896
  %i491 = select i1 %i487, i32 0, i32 %i490
  store i32 %i491, ptr %.reg2mem39
  %.reload40 = load i32, ptr %.reg2mem39
  %.reload46 = load i32, ptr %.reg2mem43
  %.reload50 = load i32, ptr %.reg2mem47
  %.reload54 = load i32, ptr %.reg2mem51
  %.reload115 = load i32, ptr %.reg2mem110
  store i32 %.reload40, ptr %.reg2mem263
  store i32 %.reload50, ptr %.reg2mem265
  store i32 %.reload115, ptr %.reg2mem267
  store i32 %.reload54, ptr %.reg2mem269
  store i32 %.reload46, ptr %.reg2mem271
  br label %bb496

bb492:                                            ; preds = %bb445
  %.reload150 = load i32, ptr %.reg2mem148
  %i493 = icmp eq i32 %.reload150, 1
  %i494 = select i1 %i493, i32 0, i32 128
  store i32 %i494, ptr %.reg2mem37
  %i495 = select i1 %i493, i32 0, i32 191
  store i32 %i495, ptr %.reg2mem35
  %.reload36 = load i32, ptr %.reg2mem35
  %.reload38 = load i32, ptr %.reg2mem37
  %.reload77 = load i32, ptr %.reg2mem75
  %.reload114 = load i32, ptr %.reg2mem110
  store i32 0, ptr %.reg2mem263
  store i32 %.reload38, ptr %.reg2mem265
  store i32 %.reload114, ptr %.reg2mem267
  store i32 %.reload77, ptr %.reg2mem269
  store i32 %.reload36, ptr %.reg2mem271
  br label %bb496

bb496:                                            ; preds = %._crit_edge6, %bb492, %bb484, %bb480, %bb461, %bb455, %bb451
  %.reload272 = load i32, ptr %.reg2mem271
  %.reload270 = load i32, ptr %.reg2mem269
  %.reload268 = load i32, ptr %.reg2mem267
  %.reload266 = load i32, ptr %.reg2mem265
  %.reload264 = load i32, ptr %.reg2mem263
  store i32 %.reload272, ptr %.reg2mem32
  store i32 %.reload270, ptr %.reg2mem29
  store i32 %.reload268, ptr %.reg2mem26
  store i32 %.reload266, ptr %.reg2mem23
  store i32 %.reload264, ptr %.reg2mem20
  %.reload22 = load i32, ptr %.reg2mem20
  %i497 = icmp eq i32 %.reload22, 0
  %.reload28 = load i32, ptr %.reg2mem26
  %.reload111 = load i32, ptr %.reg2mem110
  %i498 = select i1 %i497, i32 %.reload28, i32 %.reload111
  store i32 %i498, ptr %arg306
  %.reload31 = load i32, ptr %.reg2mem29
  %.reload149 = load i32, ptr %.reg2mem148
  %i499 = select i1 %i497, i32 %.reload31, i32 %.reload149
  %.reload234 = load ptr, ptr %.reg2mem233
  store i32 %i499, ptr %.reload234
  %.reload25 = load i32, ptr %.reg2mem23
  %.reload155 = load i32, ptr %.reg2mem153
  %i500 = select i1 %i497, i32 %.reload25, i32 %.reload155
  %.reload231 = load ptr, ptr %.reg2mem230
  store i32 %i500, ptr %.reload231
  %.reload34 = load i32, ptr %.reg2mem32
  %.reload160 = load i32, ptr %.reg2mem158
  %i501 = select i1 %i497, i32 %.reload34, i32 %.reload160
  %.reload228 = load ptr, ptr %.reg2mem227
  store i32 %i501, ptr %.reload228
  br i1 %i497, label %._crit_edge7, label %._crit_edge8

._crit_edge8:                                     ; preds = %bb496
  %.reload21 = load i32, ptr %.reg2mem20
  store i32 %.reload21, ptr %.reg2mem253
  br label %bb505

._crit_edge7:                                     ; preds = %bb496
  %.reload24 = load i32, ptr %.reg2mem23
  %.reload27 = load i32, ptr %.reg2mem26
  %.reload30 = load i32, ptr %.reg2mem29
  %.reload33 = load i32, ptr %.reg2mem32
  store i32 %.reload27, ptr %.reg2mem255
  store i32 %.reload30, ptr %.reg2mem257
  store i32 %.reload24, ptr %.reg2mem259
  store i32 %.reload33, ptr %.reg2mem261
  br label %bb502

bb502:                                            ; preds = %._crit_edge7, %._crit_edge4
  %.reload262 = load i32, ptr %.reg2mem261
  %.reload260 = load i32, ptr %.reg2mem259
  %.reload258 = load i32, ptr %.reg2mem257
  %.reload256 = load i32, ptr %.reg2mem255
  store i32 %.reload262, ptr %.reg2mem18
  store i32 %.reload260, ptr %.reg2mem16
  store i32 %.reload258, ptr %.reg2mem14
  store i32 %.reload256, ptr %.reg2mem12
  %.reload164 = load i64, ptr %.reg2mem163
  %i503 = add i64 %.reload164, 1
  store i64 %i503, ptr %.reg2mem
  %.reload = load i64, ptr %.reg2mem
  %.reload218 = load i64, ptr %.reg2mem217
  %i504 = icmp eq i64 %.reload, %.reload218
  br i1 %i504, label %._crit_edge9, label %._crit_edge10

._crit_edge10:                                    ; preds = %bb502
  %.reload11 = load i64, ptr %.reg2mem
  %.reload13 = load i32, ptr %.reg2mem12
  %.reload15 = load i32, ptr %.reg2mem14
  %.reload17 = load i32, ptr %.reg2mem16
  %.reload19 = load i32, ptr %.reg2mem18
  store i32 %.reload13, ptr %.reg2mem273
  store i32 %.reload15, ptr %.reg2mem275
  store i32 %.reload17, ptr %.reg2mem277
  store i32 %.reload19, ptr %.reg2mem279
  store i64 %.reload11, ptr %.reg2mem281
  br label %bb361

._crit_edge9:                                     ; preds = %bb502
  store i32 0, ptr %.reg2mem253
  br label %bb505

bb505:                                            ; preds = %._crit_edge9, %._crit_edge8, %bb318
  %.reload254 = load i32, ptr %.reg2mem253
  ret i32 %.reload254
}
