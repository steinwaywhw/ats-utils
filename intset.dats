#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"
staload "./intset.sats"
//staload SET = "libats/ML/SATS/funset.sats"
//staload _ = "libats/ML/DATS/funset.dats"

datatype _set (set) = 
| Empty (empty_set ()) of ()
| {s:set} {n:int} Elem (set_add (s, n)) of (int n, set s)

assume set (s:set) = _set s
//assume set (s:set) = SET.set (int)

#define :: Elem

implement empty_set () = Empty ()

implement set_add {s} {n} (s, n) = 
	if set_member (n, s)
	then s 
	else n :: s

implement set_del {s} {n} (s, n) =
	case+ s of 
	| Empty () => s 
	| x :: s => if x = n then s else x :: set_del (s, n)

implement set_union {s,r} (s, r) =
	case+ s of 
	| Empty () => r 
	| x :: s => set_union (s, set_add (r, x))

implement set_intersect {s,r} (s, r) =
	case+ s of 
	| Empty () => Empty ()
	| x :: s => 
		if set_member (x, r) 
		then x :: set_intersect (s, r)
		else set_intersect (s, r)

implement set_difference {s,r} (s, r) =
	case+ s of 
	| Empty () => Empty ()
	| x :: s => 
		if set_member (x, r)
		then set_difference (s, r)
		else x :: set_difference (s, r)

implement set_member {n} {s} (n, s) =
	case+ s of 
	| Empty _ => false 
	| x :: s => if x = n then true else set_member (n, s)

implement set_subset {s,r} (s, r) = 
	case+ s of 
	| Empty () => true 
	| x :: s => set_member (x, r) * set_subset (s, r)

implement set_eq {s,r} (s, r) = 
	set_subset (s, r) * set_subset (r, s)

implement set_is_empty {s} (s) = 
	case+ s of 
	| Empty () => true 
	| Elem _ => false


local 

fun test (): void = () where {
	val s = empty_set ()
	val _ = assertloc (set_is_empty s)
	val _ = assertloc (s = empty_set ())

}

in 

implement main0 () = test ()

end
