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
	| Nothing _ => show_any<string> "Nothing"
	| Just x 	=> (show_any<string> "Just ("; show_any<a> x; show_any<string> ")")

(******************************)

implement {a,b} maybe_bind (m, f) = 
	case+ m of 
	| Nothing _ => Nothing ()
	| Just (x)  => Just (f x)

(******************************)

////

implement maybe_selftest () = () where {

//	overload show with show<maybe int>
	val p = show_any<maybe string>

//	val x = Nothing{int} ()
//	val _ = show x

	val _ = show ()

//	val _ = show "sss"
	val x = Just("hahaha")
	val _ = p x

//	val _ = show ()

//	val x = Just (123)
//	val _ = show x

//	val _ = show () 

//	val _ = show "aaa"

//	val x = maybe_bind (x, lam x => "after bind")
//	val _ = show x


//	val _ = assertloc (Nothing{int} () \eq<maybe int> Nothing{int} ())
//	val _ = assertloc (Just 3 \eq<maybe int> Just 3)
//	val _ = assertloc (Just "aaa" \eq<maybe string> Just "aaa")

}