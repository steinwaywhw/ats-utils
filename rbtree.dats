local (* local-in-end *)

staload "./rbtree.sats"
staload "./util.sats"
staload "./list.sats"
staload _ = "./list.dats"

#define :: Cons

(* it has to be in such an order, because we make use of this order *)
#define R  0
#define B  1
#define BB 2

(* color definition *)
sortdef color = {i:nat | i <= 2} 
stadef darken (c:int): int = c + 1
stadef lighten (c:int): int = c - 1

stadef incr (h:int, c:int): int    = h + c
stadef blacken (h:int, c:int): int = h + (B - c)
stadef redden (h:int, c:int): int  = h - (c - R)

(* static constraint *)
stadef either (c:int, c1:int, c2:int): bool = (c==c1) + (c==c2)
stadef either1 (cl:int, cr:int, c:int): bool = (cl==c) + (cr==c)
stadef either2 (cl:int, cr:int, c1:int, c2:int): bool = (cl==c1) * (cr==c2) + (cl==c2) * (cr==c1)
stadef both (cl:int, cr:int, c:int): bool = (cl==c) * (cr==c)

stadef valid (c:int, cl:int, cr:int): bool = (c==R) * both (cl,cr,B) + (c==B) * either (cl,R,B) * either (cr,R,B)
stadef violation_rr (c:int, cl:int, cr:int): bool = (c==R) * either2 (cl,cr,B,R)
stadef violation_bb (c:int, cl:int, cr:int): bool = (c==BB) * either2 (cl,cr,B,R)
stadef unbalanced_bb (c:int, cl:int, cr:int): bool = (c==B) * either2 (cl,cr,R,BB) + either (c,B,R) * either2 (cl,cr,B,BB)

(* datatype *)
datatype _rbtree (a:t@ype, (*color*) int, (*black height*) int) =
	| Empty (a, B, 0) 
	| {c,cl,cr:color | valid (c,cl,cr)} {h:nat} Node (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))

#define E Empty

datatype __rbtree (a:t@ype, (*color*) int, (*black height*) int) = 
	| BEmpty (a, B, 0)
	| BBEmpty (a, BB, 1)
	| {c,cl,cr:color|valid (c,cl,cr)}        {h:nat} RBNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))
	| {c,cl,cr:color|violation_rr (c,cl,cr)} {h:nat} RRNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))
	| {c,cl,cr:color|violation_bb (c,cl,cr)} {h:nat} BBNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))

assume rbtree (a:t@ype) = [h:nat] _rbtree (a, B, h)

(* utility *)
fun darken {c:color|c < BB} (color: int c): int (c+1) = color+1
fun lighten {c:color|c > R} (color: int c): int (c-1) = color-1

symintr blacken 
symintr redden

fun {a:t@ype} __blacken {c:color} {h:nat|(h >= 1) * (c == BB) + (c != BB)} (tree: __rbtree (a, c, h)): _rbtree (a, B, blacken (h, c)) = 
	case+ tree of 
	| BEmpty _ => Empty ()
	| BBEmpty _ => Empty () 
	| RBNode (_, a, x, b) => Node (B, a, x, b)
	| BBNode (_, a, x, b) => Node (B, a, x, b)
	| RRNode (_, a, x, b) => Node (B, a, x, b)

fun {a:t@ype} _blacken {c:color} {h:nat} (tree: _rbtree (a, c, h)): _rbtree (a, B, blacken (h, c)) = 
	case+ tree of 
	| Empty _ => Empty ()
	| Node (_, a, x, b) => Node (B, a, x, b)

fun {a:t@ype} __redden {c:color|c==B} {h:nat} (tree: __rbtree (a, c, h)): _rbtree (a, R, redden (h, c)) = 
	case- tree of 
	| RBNode (_, a as Node (B, _, _, _), x, b as Node (B, _, _, _)) => Node (R, a, x, b)

fun {a:t@ype} _redden {c:color|c==B} {h:nat} (tree: _rbtree (a, c, h)): _rbtree (a, R, redden (h, c)) = 
	case- tree of 
	| Node (_, a as Node (B, _, _, _), x, b as Node (B, _, _, _)) => Node (R, a, x, b)

overload blacken with _blacken 
overload blacken with __blacken
overload redden with _redden
overload redden with __redden 

fun {a:t@ype} normalize {c:color|either (c,B,R)} {h:nat} (tree: __rbtree (a, c, h)): _rbtree (a, c, h) = 
	case- tree of 
	| BEmpty _ => Empty ()
	| RBNode (color, a, x, b) => Node (color, a, x, b)

fun {a:t@ype} balance_right_rr {c,cl,cr:color|valid (c,cl,cr) + violation_rr (c,cl,cr) * (cr==R)} {h:nat} (color: int c, left: _rbtree (a, cl, h), element: a, right: __rbtree (a, cr, h)): [cc:color|either (cc,R,B)] __rbtree (a, cc, incr (h, c)) = 
	case- (color, left, right) of 
	(* valid RB node with bubbled red root *)
	| (R, _, RBNode (R, _, _, _)) => RRNode (color, left, element, normalize right)
	(* valid RB node *)
	| (_, _, RBNode _) =>> RBNode (color, left, element, normalize right)
	| (_, _, BEmpty _) =>> RBNode (color, left, element, normalize right)
	(* RR with recoloring *)
	| (_, Node (R, _, _, _), RRNode (R, Node (R, _, _, _), _, _)) => RBNode (lighten color, blacken left, element, blacken right)
	| (_, Node (R, _, _, _), RRNode (R, _, _, Node (R, _, _, _))) => RBNode (lighten color, blacken left, element, blacken right)
	(* RR with rebalancing *)
	| (_, _, RRNode (R, Node (R, b, y, c), z, d)) =>> RBNode (B, Node (lighten color, left, element, b), y, Node (lighten color, c, z, d)) 
	| (_, _, RRNode (R, b, y, Node (R, c, z, d))) =>> RBNode (B, Node (lighten color, left, element, b), y, Node (lighten color, c, z, d)) 

fun {a:t@ype} balance_right_bb {c,cl,cr:color|valid (c,cl,cr) + unbalanced_bb (c,cl,cr) * (cr==BB)} {h:nat} (color: int c, left: _rbtree (a, cl, h), element: a, right: __rbtree (a, cr, h)): [cc:color|either (cc,c,darken c)] __rbtree (a, cc, incr (h, c)) = 
	case- (color, left, right) of 
	(* normal cases *)
	| (_, _, RBNode _) => RBNode (color, left, element, normalize right)
	| (_, _, BEmpty _) => RBNode (color, left, element, normalize right)
	(* BB with black sibling and at least one red nephew *)
	| (_, Node (B, a, x, Node (R, b, y, c)), BBNode _)  => RBNode (color, Node (B, a, x, b), y, Node (B, c, element, blacken right)) 
	| (_, Node (B, Node (R, a, x, b), y, c), BBNode _)  => RBNode (color, Node (B, a, x, b), y, Node (B, c, element, blacken right))
	| (_, Node (B, a, x, Node (R, b, y, c)), BBEmpty _) => RBNode (color, Node (B, a, x, b), y, Node (B, c, element, blacken right))
	| (_, Node (B, Node (R, a, x, b), y, c), BBEmpty _) => RBNode (color, Node (B, a, x, b), y, Node (B, c, element, blacken right))
	(* BB with black sibling and no red nephew *)
	| (B, Node (B, _, _, _), BBNode _)  =>> BBNode (darken color, redden left, element, blacken right)
	| (R, Node (B, _, _, _), BBNode _)  =>> RBNode (darken color, redden left, element, blacken right)
	| (B, Node (B, _, _, _), BBEmpty _) =>> BBNode (darken color, redden left, element, blacken right)
	| (R, Node (B, _, _, _), BBEmpty _) =>> RBNode (darken color, redden left, element, blacken right)
	(* BB with red sibling and two black nephew *)
	| (_, Node (R, a, x, b), BBNode _)  =>> balance_right_bb (B, a, x, balance_right_bb (R, b, element, right))
	| (_, Node (R, a, x, b), BBEmpty _) =>> balance_right_bb (B, a, x, balance_right_bb (R, b, element, right))
	(* should not happen *)
//	| (_, _, _) =>> RBNode (color, left, element, normalize right) where {val _ = assertloc false}


fun {a:t@ype} balance_left_rr {c,cl,cr:color|valid (c,cl,cr) + violation_rr (c,cl,cr) * (cl==R)} {h:nat} (color: int c, left: __rbtree (a, cl, h), element: a, right: _rbtree (a, cr, h)): [cc:color|either (cc,R,B)] __rbtree (a, cc, incr (h, c)) = 
	case- (color, left, right) of 
	(* valid RB node with bubbled red root *)
	| (R, RBNode (R, _, _, _), _) => RRNode (color, normalize left, element, right)
	(* valid RB node *)
	| (_, RBNode _, _) =>> RBNode (color, normalize left, element, right)
	| (_, BEmpty _, _) =>> RBNode (color, normalize left, element, right)
	(* RR with recoloring *)
	| (_, RRNode (R, Node (R, _, _, _), _, _), Node (R, _, _, _)) => RBNode (lighten color, blacken left, element, blacken right)
	| (_, RRNode (R, _, _, Node (R, _, _, _)), Node (R, _, _, _)) => RBNode (lighten color, blacken left, element, blacken right)
	(* RR with rebalancing *)
	| (_, RRNode (R, Node (R, a, x, b), y, c), _) =>> RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))
	| (_, RRNode (R, a, x, Node (R, b, y, c)), _) =>> RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))

fun {a:t@ype} balance_left_bb {c,cl,cr:color|valid (c,cl,cr) + unbalanced_bb (c,cl,cr) * (cl==BB)} {h:nat} (color: int c, left: __rbtree (a, cl, h), element: a, right: _rbtree (a, cr, h)): [cc:color|either (cc,c,darken c)] __rbtree (a, cc, incr (h, c)) = 
	case- (color, left, right) of 
	(* normal cases *)
	| (_, RBNode _, _) => RBNode (color, normalize left, element, right) 
	| (_, BEmpty _, _) => RBNode (color, normalize left, element, right) 
	(* BB with black sibling and at least one red nephew *)
	| (_, BBNode _,  Node (B, Node (R, b, y, c), z, d)) => RBNode (color, Node (B, blacken left, element, b), y, Node (B, c, z, d))
	| (_, BBNode _,  Node (B, b, y, Node (R, c, z, d))) => RBNode (color, Node (B, blacken left, element, b), y, Node (B, c, z, d))
	| (_, BBEmpty _, Node (B, Node (R, b, y, c), z, d)) => RBNode (color, Node (B, blacken left, element, b), y, Node (B, c, z, d))
	| (_, BBEmpty _, Node (B, b, y, Node (R, c, z, d))) => RBNode (color, Node (B, blacken left, element, b), y, Node (B, c, z, d))
	(* BB with black sibling and no red nephew *)
	| (_, BBNode _,  Node (B, _, _, _)) when color = B => BBNode (darken color, blacken left, element, redden right)
	| (_, BBNode _,  Node (B, _, _, _)) when color = R => RBNode (darken color, blacken left, element, redden right)
	| (_, BBEmpty _, Node (B, _, _, _)) when color = B => BBNode (darken color, blacken left, element, redden right)
	| (_, BBEmpty _, Node (B, _, _, _)) when color = R => RBNode (darken color, blacken left, element, redden right)
	(* BB with red sibling and two black nephew *)
	| (_, BBNode _,  Node (R, b, y, c)) => balance_left_bb (B, balance_left_bb (R, left, element, b), y, c)
	| (_, BBEmpty _, Node (R, b, y, c)) => balance_left_bb (B, balance_left_bb (R, left, element, b), y, c)
	(* should not happen *)
//	| (_, _, _) =>> RBNode (color, normalize left, element, right) where {val _ = assertloc false}

//(* http://cs.wellesley.edu/~cs231/fall01/red-black.pdf *)

(* http://matt.might.net/articles/red-black-delete/ *)
(* http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/32/slides/red-black-pearl.pdf *)


in (* local-in-end *)




//implement {a} empty () = Empty ()

implement {a} member (tree, element, cmp) = let 
	fun search {c:color} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> bool = 
		case+ tree of 
		| Empty _ => false 
		| Node (_, l, e, r) =>
			if cmp (element, e) = 0 then true 
			else if cmp (element, e) < 0 then search l 
			else search r
in 
	search tree
end

implement {a} elements (tree) = let 
	fun flatten {c:color} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> list a =
		case+ tree of 
		| Empty _ => Nil ()
		| Node (_, l, e, r) => concat (flatten l, (e :: (flatten r)))
in 
	flatten tree
end

implement {a} insert (tree, element, cmp) = let 

	fun ins {c:color} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> [cc:color|either (cc,B,R)] __rbtree (a, cc, h) = 
		case+ tree of 
		| E () => RBNode (R, E (), element, E ())
		| Node (color, a, x, b) => 
			if      cmp (element, x) < 0 then balance_left_rr (color, ins a, x, b)
			else if cmp (element, x) > 0 then balance_right_rr (color, a, x, ins b)
			else    RBNode (color, a, x, b)
in 
	blacken (ins tree)
end

implement {a} delete (tree, element, cmp) = let 
	
	fun del {c:color|either(c,B,R)} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> [cc:color|either (cc,c,darken c)] __rbtree (a, cc, h) = 
		case+ tree of 
		| Empty _ => BEmpty ()
		| Node (color, a, x, b) =>
			if      cmp (element, x) < 0 then balance_left_bb (color, del a, x, b)
		    else if cmp (element, x) > 0 then balance_right_bb (color, a, x, del b)
			else    delroot tree

	and delroot {c:color} {h:nat} {(c==B)*(h>=1)+(c==R)} (tree: _rbtree (a, c, h)):<cloref1> [cc:color|either (cc,c,darken c)] __rbtree (a, cc, h) = 
		case- tree of 
		| Node (R, E (), _, E ()) => BEmpty ()
		| Node (B, E (), _, E ()) => BBEmpty ()
		| Node (B, Node (R, _, x, _), _, E ()) => RBNode (B, E (), x, E ())
		| Node (B, E (), _, Node (R, _, y, _)) => RBNode (B, E (), y, E ())
		| Node (color, a, x, b) =>> balance_left_bb (color, delmax a, findmax a, b)

	and delmax {c:color|either(c,B,R)} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> [cc:color|either (cc,c,darken c)] __rbtree (a, cc, h) = 
		case- tree of 
		| Node (_, _, x, E ()) => delroot tree 
		| Node (color, a, x, b) =>> balance_right_bb (color, a, x, delmax b)

	and findmax {c:color} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> a =
		case- tree of 
		| Node (_, _, x, E ()) => x 
		| Node (_, _, _, b) =>> findmax b  

in 
	case+ del tree of 
	| BBNode (_, a, x, b) => Node (B, a, x, b)
	| BBEmpty _ => Empty ()
	| x as RBNode _ => normalize x
	| x as BEmpty _ => normalize x 
end 

end (* local-in-end *)