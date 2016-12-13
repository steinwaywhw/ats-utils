#define ATS_DYNLOADFLAG 0

//#include "share/atspre_staload.hats"
staload "./mset.sats"




local

prval () = $solver_assert lemma_elt_eq 
prval () = $solver_assert lemma_elt_fun
prval () = $solver_assert lemma_elt_unique
prval () = $solver_assert lemma_car_nat

#define :: add

datatype _imset (bag) = 
| nil (nil) of ()
| {g:bag} {i:int} cons (mk(i)::g) of (int i, _imset g)

assume imset (g:bag) = _imset g

in 

implement imset_empty () = nil ()

implement imset_add {g} {i} (s, i) = 
	case+ s of 
	| nil () => cons (i, nil ())
	| cons (x, s) => 
		if x < i 
		then cons (x, imset_add (s, i))
		else cons (i, cons (x, s))

implement imset_del {g} {i} (s, i) = 
	case+ s of 
	| nil () => nil ()
	| cons (x, s) => 
		if x = i 
		then s 
		else cons (x, imset_del (s, i))



implement imset_union {g1,g2} (s1, s2) = 
	case+ s2 of 
	| nil () => s1 
	| cons (x, s2) => imset_union (cons (x, s1), s2)


//implement imset_intersect {g1,g2} (s1, s2) = 
//	case+ (s1, s2) of 
//	| (nil (), nil ()) => nil ()
//	| (cons (x1, s1), cons (x2, s2)) => 

//implement imset_diff {g1,g2} (s1, s2) = 
//implement imset_join {g1,g2} (s1, s2) = 

implement imset_member {g} {i} (s, i) = 
	case+ s of 
	| nil () => false 
	| cons (x, s) => if x = i then true else imset_member (s, i)

//implement imset_subset {g1,g2} (s1, s2) = 

//implement imset_eq {g1,g2} (s1, s2) = 

//implement imset_neq {g1,g2} (s1, s2) = 

implement imset_cardinality {g} {i} (s, i) = 
	case+ s of 
	| nil () => 0
	| cons (x, s) => if x = i then 1 + imset_cardinality (s, i) else imset_cardinality (s, i)



end 



////
local

#define :: add 

abstype bag (bag)

extern fun test1 (): bag (mk(2) :: nil)
extern fun test2 (): bag (mk(2) :: mk(2) :: mk(3) :: nil)
extern fun test3 (): bag (mk(2) :: mk(3) :: nil)
extern fun require1 {g:bag|mem(g,mk(2))} (bag g): void
extern fun require2 {g1,g2:bag|g1==g2} (bag g1, bag g2): void
extern fun require3 {g1,g2,g3:bag|g1 - g2 == g3} (bag g1, bag g2, bag g3): void
extern fun require4 {i:int} {g:bag|((mk(i)::g ) \del mk(i)) == g} (bag g, int i): void
//extern fun require {g1,g2:set|mem(mk(1),g1) * mem(mk(1),g2)} (set g1, set g2): void 

in 

prval () = $solver_assert (lemma_elt_eq)
prval () = $solver_assert (lemma_elt_fun)
prval () = $solver_assert (lemma_elt_unique)


val a = test1()
val b = test2()
val c = test3()
//prval _ = lemma_eq_seq_id {nil} ()
//prval _ = lemma_length_base ()
//prval _ = lemma_length_ind {2} {nil} ()
//prval _ = lemma_length_ind {1} {2::nil} ()
val _ = require1 (a)
val _ = require2 (b, b)
val _ = require3 (b, a, c)
val _ = require4 (a, 2)

end




////
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



local 


fun test (): void = () where {


	val s = empty_set ()
	val _ = assertloc (set_is_empty s)
	val _ = assertloc (s = empty_set ())

//	val _ = assertloc (set_range (1, 3) = 3 :: set_range (2, 1))
//	val _ = assertloc (set_range (1, 3) != set_range (1, 2))


//	val list = set_reduce{s}{list(int)} (set_range(0, 9), list0_nil(), lam (x, xs) => list0_cons (x, xs))
//	val _ = println! list
//	val _ = assertloc (set_range (3) = set_union(set_range (2), 3 :: Empty()))
}

in 

//implement main0 () = test ()
//
//end

end


