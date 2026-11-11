; A `phi` whose back-edge incoming operand is its own destination: `%x` carries
; its value across the edge.  The run reads the incoming environment, where `%x`
; is the value the previous visit installed, so the carry is stable at `7` for
; every iteration and `main` returns `7`.
;
; The case is the complement of the swap and the cycle: nothing here depends on
; which snapshot a member reads, and a model that read its own new binding
; instead would still have to leave `%x` at `7`.  It fails if the run reads an
; unbound name, if a carried binding is installed before its operand is read
; from the wrong environment, or if the loop's back edge is not the edge the
; `%x` incoming is keyed to.
define i32 @main() {
entry:
  br label %loop
loop:
  %x = phi i32 [ 7, %entry ], [ %x, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 3
  br i1 %again, label %loop, label %done
done:
  ret i32 %x
}
