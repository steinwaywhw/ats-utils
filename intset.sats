
datasort set = (** *)

stacst empty_set: () -> set
stacst full_set: () -> set 
stacst set_add: (set, int) -> set
stacst set_del: (set, int) -> set
stacst set_union: (set, set) -> set 
stacst set_intersect: (set, set) -> set
stacst set_difference: (set, set) -> set
stacst set_complement: (set) -> set
stacst set_member: (int, set) -> bool
stacst set_subset: (set, set) -> bool
stacst set_eq: (set, set) -> bool
//stacst set_size: (set) -> int

stadef add = set_add 
stadef del = set_del 
stadef cup = set_union
stadef cap = set_intersect
stadef dif = set_difference
stadef com = set_complement
stadef mem = set_member
stadef sub = set_subset
//stadef size = set_size

stadef == = set_eq


abstype set (set)


fun empty_set (): set (empty_set())
fun set_add {s:set} {n:int} (set s, int n): set (add(s,n))
fun set_del {s:set} {n:int} (set s, int n): set (del(s,n))
fun set_union {s,r:set} (set s, set r): set (cup(s,r)) 
fun set_intersect {s,r:set} (set s, set r): set (cap(s,r))
fun set_difference {s,r:set} (set s, set r): set (dif(s,r))
//fun set_complement {s,r:set} (set): set
fun set_member {n:int} {s:set} (int n, set s): bool (mem(n,s))
fun set_subset {s,r:set} (set s, set r): bool (sub(s,r))
fun set_eq {s,r:set} (set s, set r): bool (s==r)
fun set_is_empty {s:set} (set s): bool (s==empty_set())

overload = with set_eq 

//extern fun set_add {s:set} {x:int} (set s, int x): set (add (s, x))

//extern praxi set_eq {a,b:set|sub(a,b) && sub(b,a)} (): [a==b] unit_p
//extern fun set_union {a,b:set} (set a, set b): set (cup(a,b))
//extern fun set_eq {a,b:set} (set a, set b): bool (a==b)
//extern
//praxi
//empty_set_is_empty(): [set_count(empty_set()) == 0] unit_p

//abstype MySet(s:set)

//extern
//fun
//make_empty(): MySet(empty_set())

//extern
//fun
//require_empty {xs: set | set_count(xs) == 0} (MySet(xs)): void

//local
////  prval _ = $solver_assert(set_eq)
//in
//  val s = 1 :: 2 :: 3 :: Empty()
//  val r = 4 :: 2 :: Empty()
//  val true = set_eq (set_union (s, r), set_union (r, s))
//end