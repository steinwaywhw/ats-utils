#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "./maybe.sats"

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (a) order_compare<maybe a> (x, y) = 
	case+ (x, y) of 
	| (Nothing _, Nothing _) => 0
	| (Just x, Just y) => order_compare<a> (x, y)
	| (Nothing _, _) => ~1
	| (_, Nothing _) => 1

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (a) show_any<maybe a> (m) = 
	case+ m of 
	| Just x 	 => ignoret (show_any<string> "Just ("; show_any<a> x; show_any<string> ")")
	| Nothing () => ignoret (show_any<string> "Nothing")

(******************************)

implement {a,b} maybe_bind (m, f) = 
	case+ m of 
	| Nothing _ => Nothing ()
	| Just (x)  => Just (f x)

(******************************)

