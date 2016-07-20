#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "./symintr.sats"
staload "./maybe.sats"

implement {a,b} maybe_bind (m, f) = 
	case+ m of 
	| Nothing _ => Nothing ()
	| Just (x)  => Just (f x)

implement {a} maybe_show$elm (x) = 
	gprint_val<a> x

implement {a} maybe_show (m) = 
	case+ m of 
	| Nothing _ => show "Nothing"
	| Just x 	=> (show "Just ("; maybe_show$elm<a> x; show ")")

implement {a} maybe_eq$eq (x, y) = 
	gcompare_val_val<a> (x, y) = 0

implement {a} maybe_eq (x, y) = 
	case+ (x, y) of 
	| (Just x, Just y) => maybe_eq$eq<a> (x, y)
	| (Nothing _, Nothing _) => true
	| (_, _) => false


local 
	(* such specific template definition has to be AFTER a generic one *)
	typedef nat = [n:nat] int n 
in 
	implement maybe_show$elm<nat> (x) = let 
		extern castfn to_int {a:t@ype} (a): int 
	in 
		maybe_show$elm<int> (to_int{nat} x)
	end
end


implement maybe_selftest () = () where {
	val x = Nothing ()
	val _ = show<char> x

	val _ = show ()

	val x = Just("hahaha")
	val _ = show<string> x

	val _ = show ()

	val x = Just (123)
	val _ = show<int> x

	val _ = show () 

	val x = maybe_bind (x, lam x => "after bind")
	val _ = show<string> x


	val _ = assertloc (Nothing{int} () = Nothing{int} ())
	val _ = assertloc (Just 3 \maybe_eq<int> Just 3)
	val _ = assertloc (Just "aaa" \maybe_eq<string> Just "aaa")

}