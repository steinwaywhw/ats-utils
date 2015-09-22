staload "./intervalset.sats"
staload "./list.sats"
staload _ = "./list.dats"

#define ATS_DYNLOADFLAG 0
#define :: Cons 

typedef interval (pt: t@ype) = @(pt, pt)

(* assume it is sorted in the list, and all intervals are disjoint *)
assume interval_set (pt: t@ype) = list (interval pt)

(* CHAR (ASCII) Interval Set *)

implement intdom_compare<char> (a, b) = a - b
implement intdom_succ<char> (c) = if c = '\177' then c else c + 1
implement intdom_pred<char> (c) = if c = '\000' then c else c - 1
implement intdom_lowerbound<char> () = '\000'
implement intdom_upperbound<char> () = '\177'

(* general interval domain function *)
implement {pt} intdom_is_succ (a, b) = if intdom_compare (intdom_pred b, a) = 0 && intdom_compare (intdom_succ a, b) = 0 then true else false
implement {pt} intdom_min (a, b) = if intdom_compare (a, b) < 0 then a else b 
implement {pt} intdom_max (a, b) = if intdom_compare (a, b) > 0 then a else b 

(* local utility function on interval domain *)		
fun {pt:t@ype} intdom_member (from: pt, to: pt, item: pt) = 
	if intdom_compare (from, to) <= 0 
	then intdom_compare (item, from) >= 0 && intdom_compare (item, to) <= 0
	else intdom_member (to, from, item)

fun {pt:t@ype} intdom_is_subset (a: interval pt, b: interval pt): bool = let 
	val @(a1, a2) = a 
	val @(b1, b2) = b 
in 
	if intdom_compare (a1, b1) >= 0 && intdom_compare (a2, b2) <= 0
	then true
	else false
end 

fun {pt:t@ype} intdom_mkinterval (a: pt, b: pt): interval pt = 
	if intdom_compare (a, b) > 0 
	then intdom_mkinterval (b, a)
	else @(a, b)

(* interval set functions, based on interval domain *)
implement {pt} intset_empty () = Nil ()
implement {pt} intset_universe () = @(intdom_lowerbound (), intdom_upperbound ()) :: Nil ()

implement {pt} intset_singleton (p) = @(p, p) :: Nil ()
implement {pt} intset_interval (a, b) = intdom_mkinterval (a, b) :: Nil ()

implement {pt} intset_is_empty (set) = 
	case+ set of 
	| Nil () => true
	| _      => false

implement {pt} intset_is_universe (set) = 
	case+ set of 
	| @(a, b) :: Nil () => intdom_compare (a, intdom_lowerbound ()) = 0 && intdom_compare (b, intdom_upperbound ()) = 0
	| _ => false 

implement {pt} intset_member (set, p) = 
	list_any (set, lam x => let val @(a, b) = x in intdom_member (a, b, p) end)

implement {pt} intset_items (set) = let 
	fun interval_items (a: pt, b: pt): list pt =
		if intdom_compare (a, b) > 0 then Nil ()
		else a :: interval_items (intdom_succ a, b)
in 
	case+ set of 
	| Nil () => Nil ()
	| @(a, b) :: xs => list_concat (interval_items (a, b), intset_items xs)
end 

implement {pt} intset_intervals (set) = set 


implement {pt} intset_add (set, p) = let 
	fun merge (a: interval pt, p: pt, set: interval_set pt): interval_set pt = let 
		val @(x, y) = a 
	in 
		case+ set of 
		| Nil () => @(x, p) :: Nil ()
		| @(c, d) :: set => 
			if intdom_compare (intdom_pred (c), p) = 0
			then @(x, d) :: set 
			else @(x, p) :: @(c, d) :: set 
	end 
in 
	case+ set of 
	| Nil () => Cons (@(p, p), Nil ())
	| @(a, b) :: set => 
		if intdom_is_succ (p, a)          then @(p, b) :: set
		else if intdom_compare (p, a) < 0 then @(p, p) :: @(a, b) :: set
		else if intdom_member (a, b, p)   then @(a, b) :: set
		else if intdom_is_succ (b, p)     then merge (@(a, b), p, set)
		else (* b < p *) 					   @(a, b) :: intset_add (set, p)
end 

implement {pt} intset_add_interval (set, from, to) = let 
	fun merge (a: interval pt, from: pt, to: pt, set: interval_set pt): interval_set pt = let 
		val @(x, y) = a 
	in 
		case+ set of 
		| Nil () => @(intdom_min (x, from), to) :: set 
		| @(c, d) :: set => 
			if intdom_is_succ (to, c)
			then @(intdom_min (x, from), d) :: set 
			else @(intdom_min (x, from), to) :: @(c, d) :: set
	end


in 
	if intdom_compare (from, to) > 0 
	then intset_add_interval (set, to, from)
	else 
		case+ set of 
		| Nil () =>  @(from, to) :: Nil ()
		| @(a, b) :: set => 
			if intdom_is_succ (to, a)            then @(from, b) :: set
			else if intdom_compare (to, a) < 0   then @(from, to) :: @(a, b) :: set
			else if intdom_member (a, b, to)     then @(intdom_min (from, a), b) :: set
			else if intdom_compare (b, from) < 0 then @(a, b) :: intset_add_interval (set, from, to)
			else (* a <= from <= b+1 <= to *) merge (@(a, b), from, to, set)
end 

implement {pt} intset_complement (set) = let 
	fun aux (a: interval pt, set: interval_set pt): interval_set pt = let 
		val @(a, b) = a
	in 
		case+ set of 
		| Nil () => if intdom_compare (b, intdom_upperbound ()) = 0 then Nil () else @(intdom_succ b, intdom_upperbound ()) :: Nil ()
		| @(x, y) :: set => @(intdom_succ b, intdom_pred x) :: aux (@(x, y), set)
	end 	
in 
	case+ set of 
	| Nil () => intset_universe ()
	| @(a, b) :: set => 
		if intdom_compare (a, intdom_lowerbound ()) = 0 
		then aux (@(a, b), set)
		else @(intdom_lowerbound (), intdom_pred a) :: aux (@(a, b), set)
end

implement {pt} intset_union (a, b) = 
	case+ a of 
	| Nil () => b 
	| @(x, y) :: set => intset_union (set, intset_add_interval (b, x, y))

implement {pt} intset_intersect (a, b) = 
	intset_difference (
		intset_union (a, b),
		intset_union (intset_difference (a, b), intset_difference (b, a)))

implement {pt} intset_difference (a, b) = let 
	fun minus (set: interval_set pt, i: interval pt): interval_set pt = let 
		val @(x, y) = i 
	in 
		case+ set of 
		| Nil () => Nil ()
		| @(a, b) :: set => 
			if intdom_compare (y, a) < 0                                     then @(a, b) :: set
			else if intdom_compare (b, x) <  0                               then @(a, b) :: minus (set, i)
			else if intdom_compare (x, a) <= 0 && intdom_compare (b, y) <= 0 then minus (set, i)
			else if intdom_compare (a, x) <  0 && intdom_compare (y, b) < 0  then @(a, intdom_pred x) :: @(intdom_succ y, b) :: set
			else if intdom_compare (x, a) <= 0                               then @(intdom_succ y, b) :: set
			else if intdom_compare (x, a) >  0                               then @(a, intdom_pred x) :: set
			else Nil () (* should not happen *)
	end 
in 
	case+ b of 
	| Nil () => a 
	| interval :: set => intset_difference (minus (a, interval), set)
end

implement {pt} intset_compare (a, b) =
	case+ (a, b) of 
	| (Nil _, Nil _) => 0
	| (Nil _, _) =>> ~1 
	| (_, Nil _) =>> 1
	| (@(a1, a2) :: a, @(b1, b2) :: b) => 
		if intdom_compare (a1, b1) != 0 then intdom_compare (a1, b1)
		else if intdom_compare (a2, b2) != 0 then intdom_compare (a2, b2)
		else intset_compare (a, b)

implement {pt} intset_is_subset (a, b) = let 
	fun subset (set: interval_set pt, i: interval pt): bool = 
		list_any (set, lam x => let 
				val @(a, b) = x
				val @(m, n) = i 
			in 
				intdom_compare (a, m) <= 0 && intdom_compare (n, b) <= 0
			end)
in 
	list_all (a, lam x => subset (b, x))
end 





