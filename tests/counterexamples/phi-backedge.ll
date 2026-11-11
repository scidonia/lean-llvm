; A `phi` with three incoming entries, reached from two different predecessor
; blocks.  `%loop` is entered from `%entry`, then from `%else`, then from `%then`,
; then from `%else` again; each edge selects the entry keyed to the block the
; edge actually came from, not the first entry listed and not the block the run
; started in.
;
; Walk: `(%i, %a) = (0, 1)` from `%entry`; `%i` is even, so `%else` adds `100`
; and sets `%a.e = 101`; the next visit takes `%i = 1`, `%a = 101` from `%else`,
; and `%then` adds `10` and sets `%a.t = 111`; the last visit takes `%i = 2`,
; `%a = 111` from `%then`, and `%else` adds `100` and sets `%a.e = 211`, but
; `%i = 3` leaves the loop, so `%a.e` is never installed and `%a` is still `111`.
; `main` returns `111`.
define i32 @main() {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %it, %then ], [ %ie, %else ]
  %a = phi i32 [ 1, %entry ], [ %a.t, %then ], [ %a.e, %else ]
  %odd = and i32 %i, 1
  %isodd = icmp eq i32 %odd, 1
  br i1 %isodd, label %then, label %else
then:
  %a.t = add i32 %a, 10
  %it = add i32 %i, 1
  %cont.t = icmp ult i32 %it, 3
  br i1 %cont.t, label %loop, label %done
else:
  %a.e = add i32 %a, 100
  %ie = add i32 %i, 1
  %cont.e = icmp ult i32 %ie, 3
  br i1 %cont.e, label %loop, label %done
done:
  ret i32 %a
}
