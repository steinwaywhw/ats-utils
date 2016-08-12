#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "show.sats"

implement {a} show_any (x) = gprint_val<a> x

implement {a} show_addr (x) = $extfcall (void, "printf", "%p", $UNSAFE.cast{ptr} x)

implement {}  show_sep () = show_any<string> ":"
implement {}  show_begin () = ()
implement {}  show_end () = ()

