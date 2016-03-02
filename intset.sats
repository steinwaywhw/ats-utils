
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
stacst set_neq: (set, set) -> bool
stacst set_range: (int, int) -> set 

//stacst set_size: (set) -> int

stadef add = set_add 
stadef del = set_del 
stadef cup = set_union
stadef cap = set_intersect
stadef dif = set_difference
stadef com = set_complement
stadef mem = set_member
stadef sub = set_subset
stadef range = set_range

//stadef size = set_size
infixl 30 :: 

stadef != = set_neq
stadef == = set_eq
stadef :: = set_add 

praxi set_range_base {x:int} (): [range(x,x)==add(empty_set(),x)] unit_p
praxi set_range_ind {x,y:int|x>y} (): [range(x,y)==add(range(x-1,y),x)] unit_p
praxi set_range_lemma1 {x,y:int} (): [range(x,y)==range(y,x)] unit_p
praxi set_range_lemma2 {x,y,z:int|x>=y && (y>z || z>x)} (): [~mem(z,range(x,y))] unit_p
//praxi set_range_ind2 {x,y:int|x<y} (): [range(x,y)==add(range(x+1,y),x)]
//praxi set_range_lemma {x,y,z:int|}

//praxi set_range_base (): [range(0)==add(empty_set(),0)] unit_p
//prfun set_range_ind1 {x:nat|x>0} (): [range(x)==add(range(x-1),x)] unit_p
//prfun set_range_ind2 {x,y:nat|y>x} (): [~mem(y,range(x))] unit_p
//praxi set_range_ind2 {x,y:int|x > y} (): [range(x,y)==cup(add(empty_set(),x),range(x-1,y))] unit_p

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
fun set_neq {s,r:set} (set s, set r): bool (s != r)
fun set_is_empty {s:set} (set s): bool (s==empty_set())
fun set_range {x,y:int} (int x, int y): set (range(x,y))

overload = with set_eq 
overload != with set_neq


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