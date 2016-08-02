#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"
staload "./intset.sats"
//staload SET = "libats/ML/SATS/funset.sats"
//staload _ = "libats/ML/DATS/funset.dats"

datatype _set (set) = 
| Empty (empty_set ()) of ()
| {s:set} {n:int | ~mem(n, s)} Elem (set_add (s, n)) of (int n, set s)

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
	| x :: s => if n = x then s else x :: set_del (s, n)

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
	| x :: s => if set_member (x, r) then set_subset (s, r) else false

implement set_eq {s,r} (s, r) = 
	if set_subset (s, r) then set_subset (r, s) else false

implement set_neq {s,r} (s, r) = ~(s \set_eq r)

implement set_is_empty {s} (s) = 
	case+ s of 
	| Empty () => true 
	| Elem _ => false

implement set_range {x,y} (x, y) = let 
//	val _ = $solver_assert (set_range_base)
//	val _ = $solver_assert (set_range_ind)
//	val _ = $solver_assert (set_range_lemma1)
//	val _ = $solver_assert (set_range_lemma2)
in 
	if x = y 
	then 
		let 
			prval pf = set_range_base {x} ()
		in 
			x :: Empty ()
		end
	else if x > y
	then 
		let 
			prval pf = set_range_ind {x,y} ()
			prval pf = set_range_lemma2 {x-1,y,x} ()
		in 
			x :: set_range (x-1, y)
		end
	else 
		let 
			prval pf = set_range_lemma1 {x,y} ()
		in 
			set_range (y, x)
		end

end

//implement set_reduce {s} {a} (s, base, f) = 
//	case+ s of 
//	| Empty () => base 
//	| Elem (n, s) => f (n, set_reduce (s, base, f))


//local 

//staload  "libats/ML/SATS/basis.sats"
//staload  "libats/ML/SATS/list0.sats"
//staload _(*anon*) = "libats/ML/DATS/list0.dats"

//fun test (): void = () where {
//	val _ = $solver_assert (set_range_base)
//	val _ = $solver_assert (set_range_ind)
//	val _ = $solver_assert (set_range_lemma1)
//	val _ = $solver_assert (set_range_lemma2)


//	val s = empty_set ()
//	val _ = assertloc (set_is_empty s)
//	val _ = assertloc (s \set_eq empty_set ())

//	val _ = assertloc (set_range (1, 3) \set_eq 3 :: set_range (2, 1))
//	val _ = assertloc (set_range (1, 3) \set_neq set_range (1, 2))


////	val list = set_reduce{s}{list(int)} (set_range(0, 9), list0_nil(), lam (x, xs) => list0_cons (x, xs))
////	val _ = println! list
////	val _ = assertloc (set_range (3) = set_union(set_range (2), 3 :: Empty()))
//}

//in 

////implement main0 () = test ()
////
////end

//end


