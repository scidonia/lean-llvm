; The selected-body marker for the baseline unit.
;
; `Caller.lean` reads this symbol so the probe can show which body was linked
; without relying on output equivalence.  It carries no semantics of the seam
; and is bound by hash like every other installation input.
define i64 @leanllvm_impl_id(i64 %dummy) {
entry:
  ret i64 1
}
