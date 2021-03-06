#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "show.sats"


typedef nat = intGte 0

implement {a} show_any (x) = gprint_val<a> x

implement show_any<nat> (x) = gprint_int ($UNSAFE.cast{int} x)
implement (n:int) show_any<string1 n> (x) = gprint_val<string> (g0ofg1 x)
implement (a:t@ype,b:t@ype) show_any<@(a,b)> (x) = (show_any<a> x.0; show_sep<> (); show_any<b> x.1)
implement (a:t@ype,b:t@ype) show_any<$tup(a,b)> (x) = (show_any<a> x.0; show_sep<> (); show_any<b> x.1)


implement {a} show_addr (x) = $extfcall (void, "printf", "%p", $UNSAFE.cast{ptr} x)

implement {}  show_sep () = show_any<string> ":"
implement {}  show_begin () = ()
implement {}  show_end () = ()

