; A three-register `phi` cycle on the loop's back edge: `%a` takes `%c`, `%b`
; takes `%a` and `%c` takes `%b`.  Every incoming operand is the destination of
; another member of the same run, so a model that installs one member's binding
; before reading the next member's operand rotates through its own new values
; instead of the values the edge delivered.
;
; The loop body runs twice.  At the second visit the edge carries
; `(%a, %b, %c) = (1, 2, 3)`, so one snapshot gives `(%a, %b, %c) = (3, 1, 2)`
; and `main` returns `2`.  Installing each binding before the next operand is
; read gives `(3, 3, 3)` and returns `3`.
define i32 @main() {
entry:
  br label %loop
loop:
  %a = phi i32 [ 1, %entry ], [ %c, %loop ]
  %b = phi i32 [ 2, %entry ], [ %a, %loop ]
  %c = phi i32 [ 3, %entry ], [ %b, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 2
  br i1 %again, label %loop, label %done
done:
  ret i32 %c
}
