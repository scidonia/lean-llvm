; The permutation pair's other half: `phi-perm-a.ll` with its three leading
; `phi`s reordered.  The `phi`s are independent, so only the edge's values
; matter and both texts return `13`.  See `phi-perm-a.ll` for the walk.
define i32 @main() {
entry:
  br label %loop
loop:
  %a = phi i32 [ 3, %entry ], [ %a.next, %loop ]
  %b = phi i32 [ 4, %entry ], [ %b.next, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %a.next = add i32 %a, 1
  %b.next = add i32 %b, 2
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 3
  br i1 %again, label %loop, label %done
done:
  %r = add i32 %a, %b
  ret i32 %r
}
