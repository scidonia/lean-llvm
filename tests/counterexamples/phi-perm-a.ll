; One half of the permutation pair.  The three leading `phi`s are independent:
; none of their back-edge operands names another member's destination, so the
; order the run installs them in is unobservable.  The loop body runs three
; times and `main` returns `%a + %b` at the last visit, `5 + 8 = 13`.
;
; `phi-perm-b.ll` holds the same function with the `phi` lines reordered; a
; model whose answer changes with that order is reading a snapshot that depends
; on the run's textual order rather than on the edge's values.
define i32 @main() {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %a = phi i32 [ 3, %entry ], [ %a.next, %loop ]
  %b = phi i32 [ 4, %entry ], [ %b.next, %loop ]
  %a.next = add i32 %a, 1
  %b.next = add i32 %b, 2
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 3
  br i1 %again, label %loop, label %done
done:
  %r = add i32 %a, %b
  ret i32 %r
}
