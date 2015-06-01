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
stadef darken (c:color): color = c+1
stadef lighten (c:color): color = c-1

stadef incr (h:nat, c:color): nat = h + c 
//	scase (h, c) of 
//	| (h, R)    => h
//	| (h, B)    => h+1
//	| (h, BB)   => h+2

stadef blacken (h:nat, c:color): nat = h + (B - c)
//	scase c of 
//	| R => h+1
//	| B => h 
//	| BB => h-1

(* static constraint *)
stadef valid (c:color, cl:color, cr:color): bool = ((c==R) * (cl==B) * (cr==B)) + (c==B)
stadef violation_rr (c:color, cl:color, cr:color): bool = (c==R) * (((cl==R) * (cr==B)) + ((cl==B) * (cr==R)))
stadef violation_bb (c:color, cl:color, cr:color): bool = (c==BB) * ((cl==R) + (cr==R))

(* datatype *)
datatype _rbtree (a:t@ype, c:color, h:nat) =
	| Empty (a, B, 0) of ()
	| {c,cl,cr:color | valid (c,cl,cr)} {h:nat} Node (a, c, incr (h, c)) of (int c, _rbtree (a, h, cl), a, _rbtree (a, h, cr))

datatype __rbtree (a:t@ype, c:color, h:nat) = 
	| BEmpty (a, B, 0)
	| BBEmpty (a, BB, 1)
	| {c,cl,cr:color|valid (c,cl,cr)} {h:nat} RBNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))
	| {c,cl,cr:color|violation_rr (c,cl,cr)} {h:nat} RRNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))
	| {c,cl,cr:color|violation_bb (c,cl,cr)} {h:nat} BBNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))

assume rbtree (a:t@ype) = [h:nat] _rbtree (a, B, h)


(* utility *)
symintr darken
symintr lighten

fun darken_c {c:color|c < BB} (color: int c): int (c+1) = color+1
fun lighten_c {c:color|c > R} (color: int c): int (c-1) = color-1

overload darken with darken_c
overload lighten with lighten_c

fun {a:t@ype} darken_rb {c:color|c < BB} {h:nat} (tree: __rbtree (a, c, h)): __rbtree (a, darken c, h) = 
	case+ tree of 
	| RBNode (color, a, x, b) when color = R => RBNode (darken color, a, x, b)
	| RBNode (color, a, x, b) when color = B => BBNode (darken color, a, x, b)
	| RRNode (color, a, x, b) => RBNode (darken color, a, x, b)
	| BEmpty () => BBEmpty ()
	| _ =>> assertloc false

fun {a:t@ype} lighten_rb {c:color|c > R} {h:nat} (tree: __rbtree (a, c, h)): __rbtree (a, lighten c, h) = 
	case+ tree of 
	| RBNode (color, a, x, b) => RBNode (lighten color, a, x, b)
	| BBNode (color, a, x, b) => RBNode (lighten color, a, x, b)
	| BBEmpty () => BEmpty ()
	| _ =>> assertloc (false)

overload darken with darken_rb 
overload lighten with lighten_rb

fun {a:t@ype} blacken {c:color} {h:nat} (tree: __rbtree (a, c, h)): _rbtree (a, B, blacken (h, c)) = 
	case+ tree of 
	| BEmpty _ => Empty ()
	| BBEmpty _ => Empty () 
	| RBNode (_, a, x, b) => Node (B, a, x, b)
	| BBNode (_, a, x, b) => Node (B, a, x, b)
	| RRNode (_, a, x, b) => Node (B, a, x, b)



//stadef validleaf (c:color, h:nat): bool = (c==B) * (h==0)
//stadef bbleaf (c:color, h:nat): bool = (c==BB) * (h==1)

//stadef violation_bb (c:color): bool = c==BB 
//stadef violation_nb (c:color): bool = c==NB

//stadef rb (c:color): bool = (c == B) + (c == R)




//datatype _rbtree (a:t@ype, c:color, h:nat, bad:bool) = 
//	| {c,cl,cr:color} {h:nat} {bad:bool} {(~bad * valid (c,cl,cr)) + bad} Node (a, c, incr (h, c), bad) of (int c, _rbtree (a, h, cl, bad), a, _rbtree (a, h, cr, bad))
//	| {c:color} {h:nat} {bad:bool} {(~bad * validleaf (c, h) + (bad * bbleaf (c, h)))} Empty (a, c, h, bad) of ()



//datatype i__rbtree (a:t@ype, c:color, h:nat) = 
//	| {c,cl,cr:color|valid (c,cl,cr) + violation_rr (c,cl,cr)} INode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))

//datatype d__rbtree (a:t@ype, c:color, h:nat) = 
//	| DBEmpty (a, B, 0) of () 
//	| DBBEmpty (a, BB, 1) of ()
//	| {c,cl,cr:color|valid (c,cl,cr) + violation_rr (c,cl,cr) + violation_bb (c,cl,cr)} {h:nat} DNode (a, c, incr (h, c)) of (int c, _rbtree (a, cl, h), a, _rbtree (a, cr, h))



(* local function *)

//fun {a:t@ype} balance_left {c,cl,cr:color} {h:nat} (color: int c, left: __rbtree (a, cl, h), element: a, right: _rbtree (a, cr, h)): __rbtree (a, cr, h) = 
//	case+ (left, right) of 
//	(* valid RB node *)
//	| (RBNode (_, _, _, _), _) => RBNode (color, left, element, right)
//	(* RR (or RR with BB) with recoloring *)
//	| (RRNode (R, Node (R, _, _, _), _, _), Node (R, _, _, _)) => RBNode (lighten color, darken left, element, darken right)
//	| (RRNode (R, _, _, Node (R, _, _, _)), Node (R, _, _, _)) => RBNode (lighten color, darken left, element, darken right)
//	(* RR (or RR with BB) with rebalancing *)
//	| (RRNode (R, Node (R, a, x, b), y, c), _) => RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))
//	| (RRNode (R, a, x, Node (R, b, y, c)), _) => RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))
//	 BB case 1 and case 2, when sibling is black 
//	| (BBNode (BB, _, _, _), Node (B, c, z, d)) => (
//		case+ c of 
//		| Node (B, _, _, _) when color = R => RBNode (darken color, Node (R, lighten left, element, c), z, d)
//		| Node (B, _, _, _) when color = B => BBNode (darken color, Node (R, lighten left, element, c), z, d)
//		| Node (R, _, _, _) => balance_left (darken color, RRNode (R, lighten left, element, c), z, d)
//		)
//	(* BB case 3, when sibling is red (with two black children) *)
//	| (BBNode (BB, _, _, _), Node (R, Node (B, c, y, d), z, e)) => (
//		case+ c of 
//		| Node (B, _, _, _) => RBNode (B, Node (B, Node (R, lighten left, element, c), y, d), z, e)
//		| Node (R, _, _, _) => balance_left (B, balance_left (B, RRNode (R, lighten left, element, c), y, d), z, e)
//		)
//	(* should not happen *)
//	| (_, _) =>> RBNode (color, left, element, right) where {val _ = assertloc false}


fun {a:t@ype} balance_right {c,cl,cr:color} {h:nat} (color: int c, left: _rbtree (a, cl, h), element: a, right: __rbtree (a, cr, h)): [cc:color] __rbtree (a, cc, h) = 
	case+ (left, right) of 
	(* valid RB node *)
	| (_, RBNode _) => RBNode (color, left, element, right)
	(* RR (or RR with BB) with recoloring *)
	| (Node (R, _, _, _), RRNode (R, Node (R, _, _, _), _, _)) => RBNode (lighten color, darken left, element, darken right)
	| (Node (R, _, _, _), RRNode (R, _, _, Node (R, _, _, _))) => RBNode (lighten color, darken left, element, darken right)
	(* RR (or RR with BB) with rebalancing *)
	| (_, RRNode (R, Node (R, a, x, b), y, c)) => RBNode (B, Node (lighten color, left, element, a), x, Node (lighten color, b, y, c))
	| (_, RRNode (R, a, x, Node (R, b, y, c))) => RBNode (B, Node (lighten color, left, element, a), x, Node (lighten color, b, y, c))
	(* BB with black sibling and at least one red nephew *)
	| (Node (B, b, y, Node (R, c, z, d)), BBNode _)  => RBNode (color, Node (B, b, y, c), z, Node (B, d, element, lighten right))
	| (Node (B, Node (R, b, y, c), z, d), BBNode _)  => RBNode (color, Node (B, b, y, c), z, Node (B, d, element, lighten right))
	| (Node (B, b, y, Node (R, c, z, d)), BBEmpty _) => RBNode (color, Node (B, b, y, c), z, Node (B, d, element, lighten right))
	| (Node (B, Node (R, b, y, c), z, d), BBEmpty _) => RBNode (color, Node (B, b, y, c), z, Node (B, d, element, lighten right))
	(* BB with black sibling and no red nephew *)
	| (Node (B, _, _, _), BBNode _)  when color = B => BBNode (darken color, lighten left, element, lighten right)
	| (Node (B, _, _, _), BBNode _)  when color = R => RBNode (darken color, lighten left, element, lighten right)
	| (Node (B, _, _, _), BBEmpty _) when color = B => BBNode (darken color, lighten left, element, lighten right)
	| (Node (B, _, _, _), BBEmpty _) when color = R => RBNode (darken color, lighten left, element, lighten right)
	(* BB with red sibling and two black nephew *)
	| (Node (R, b, y, c), BBNode _)  => balance_right(B, b, y, balance_right(R, c, element, right))
	| (Node (R, b, y, c), BBEmpty _) => balance_right(B, b, y, balance_right(R, c, element, right))
	(* should not happen *)
	| (_, _) =>> RBNode (color, left, element, right) where {val _ = assertloc false}


fun {a:t@ype} balance_left {c,cl,cr:color} {h:nat} (color: int c, left: __rbtree (a, cl, h), element: a, right: _rbtree (a, cr, h)): [cc:color] __rbtree (a, cc, h) = 
	case+ (left, right) of 
	(* valid RB node *)
	| (RBNode _, _) => RBNode (color, left, element, right)
	(* RR (or RR with BB) with recoloring *)
	| (RRNode (R, Node (R, _, _, _), _, _), Node (R, _, _, _)) => RBNode (lighten color, darken left, element, darken right)
	| (RRNode (R, _, _, Node (R, _, _, _)), Node (R, _, _, _)) => RBNode (lighten color, darken left, element, darken right)
	(* RR (or RR with BB) with rebalancing *)
	| (RRNode (R, Node (R, a, x, b), y, c), _) => RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))
	| (RRNode (R, a, x, Node (R, b, y, c)), _) => RBNode (B, Node (lighten color, a, x, b), y, Node (lighten color, c, element, right))
	(* BB with black sibling and at least one red nephew *)
	| (BBNode _, Node (B, Node (R, b, y, c), z, d))  => RBNode (color, Node (B, lighten left, element, b), y, Node (B, c, z, d))
	| (BBNode _, Node (B, b, y, Node (R, c, z, d)))  => RBNode (color, Node (B, lighten left, element, b), y, Node (B, c, z, d))
	| (BBEmpty _, Node (B, Node (R, b, y, c), z, d)) => RBNode (color, Node (B, lighten left, element, b), y, Node (B, c, z, d))
	| (BBEmpty _, Node (B, b, y, Node (R, c, z, d))) => RBNode (color, Node (B, lighten left, element, b), y, Node (B, c, z, d))
	(* BB with black sibling and no red nephew *)
	| (BBNode _, Node (B, _, _, _))  when color = B => BBNode (darken color, lighten left, element, lighten right)
	| (BBNode _, Node (B, _, _, _))  when color = R => RBNode (darken color, lighten left, element, lighten right)
	| (BBEmpty _, Node (B, _, _, _)) when color = B => BBNode (darken color, lighten left, element, lighten right)
	| (BBEmpty _, Node (B, _, _, _)) when color = R => RBNode (darken color, lighten left, element, lighten right)
	(* BB with red sibling and two black nephew *)
	| (BBNode _, Node (R, b, y, c))  => balance_left (B, balance_left (R, left, element, b), y, c)
	| (BBEmpty _, Node (R, b, y, c)) => balance_left (B, balance_left (R, left, element, b), y, c)
	(* should not happen *)
	| (_, _) =>> RBNode (color, left, element, right) where {val _ = assertloc false}


//	(* BB case 1 and case 2, when sibling is black *)
//	| (BBNode (BB, _, _, _), Node (B, c, z, d)) => (
//		case+ c of 
//		| Node (B, _, _, _) when color = R => RBNode (darken color, Node (R, lighten left, element, c), z, d)
//		| Node (B, _, _, _) when color = B => BBNode (darken color, Node (R, lighten left, element, c), z, d)
//		| Node (R, _, _, _) => balance_left (darken color, RRNode (R, lighten left, element, c), z, d)
//		)
//	(* BB case 3, when sibling is red (with two black children) *)
//	| (BBNode (BB, _, _, _), Node (R, Node (B, c, y, d), z, e)) => (
//		case+ c of 
//		| Node (B, _, _, _) => RBNode (B, Node (B, Node (R, lighten left, element, c), y, d), z, e)
//		| Node (R, _, _, _) => balance_left (B, balance_left (B, RRNode (R, lighten left, element, c), y, d), z, e)
//		)


//	(* RR with BB *)
//	| (RRNode (R, Node (R, a, x, b), y, c), _) when color = BB => RBNode (B, Node (B, a, x, b), y, Node (B, c, element, right))
//	| (RRNode (R, a, x, Node (R, b, y, c)), _) when color = BB => RBNode (B, Node (B, a, x, b), y, Node (B, c, element, right))
//  (* RR with rebalancing *)
//  | (RRNode (R, Node (R, a, x, b), y, c), Node (B, _, _, _)) when color = B  => RBNode (B, Node (R, a, x, b), y, Node (R, c, element, right))
//  | (RRNode (R, a, x, Node (R, b, y, c)), Node (B, _, _, _)) when color = B  => RBNode (B, Node (R, a, x, b), y, Node (R, c, element, right))




//(* http://cs.wellesley.edu/~cs231/fall01/red-black.pdf *)
//fun {a} balance {c,cl,cr:color|c==B} {b1,b2:bool|(b1*b2)==false;(b1+b2)==true} (color: int c, left: _rbtree (a, cl, h, b1), element: a, right: _rbtree (a, cr, h, b2)): _rbtree (a, c, h, false) = 
//	case+ (left, c, right) of 
//	(* 4 cases where only recoloring is needed *)
//	| (Node (R, Node (R, x, a, y), b, z), B, Node (R, m, c, n)) => Node (R, Node (B, Node (R, x, a, y), b, z), element, Node (B, m, c, n))
//	| (Node (R, x, a, Node (R, y, b, z)), B, Node (R, m, c, n)) => Node (R, Node (B, x, a, Node (R, y, b, z)), element, Node (B, m, c, n))
//	| (Node (R, m, c, n), B, Node (R, x, a, Node (R, y, b, z))) => Node (R, Node (B, m, c, n), element, Node (B, x, a, Node (R, y, b, z)))
//	| (Node (R, m, c, n), B, Node (R, Node (R, x, a, y), b, z)) => Node (R, Node (B, m, c, n), element, Node (B, Node (R, x, a, y), b, z))
//	(* 4 cases where rebalancing is also needed *)
//	| (Node (R, Node (R, x, a, y), b, z), B, Node (B, _, _, _)) => Node (B, Node (R, x, a, y), b, Node (R, z, element, right))
//	| (Node (R, x, a, Node (R, y, b, z)), B, Node (B, _, _, _)) => Node (B, Node (R, x, a, y), b, Node (R, z, element, right))
//	| (Node (B, _, _, _), B, Node (R, Node (R, x, a, y), b, z)) => Node (B, Node (R, left, element, x), a, Node (R, y, b, z))
//	| (Node (B, _, _, _), B, Node (R, x, a, Node (R, y, b, z))) => Node (B, Node (R, left, element, x), a, Node (R, y, b, z))
//	(* otherwise *)
//	| (_, _, _) =>> Node (color, left, element, right)


(* balance_insert should generate _rbtree (or valid i__rbtree), but its difficult to write insert then *)

//(* http://cs.wellesley.edu/~cs231/fall01/red-black.pdf *)
//fun {a:t@ype} balance_insert_left {c,cl,cr:color|c==B} {h:nat} (color: int c, left: i__rbtree (a, cl, h), element: a, right: _rbtree (a, cr, h)): i__rbtree (a, c, h) = 
//	case+ (left, right) of 
//	(* recoloring *)
//	| (INode (R, Node (R, x, a, y), b, z), Node (R, m, c, n)) => INode (R, Node (B, Node (R, x, a, y), b, z), element, Node (B, m, c, n)) 
//	| (INode (R, x, a, Node (R, y, b, z)), Node (R, m, c, n)) => INode (R, Node (B, x, a, Node (R, y, b, z)), element, Node (B, m, c, n))
//	(* rebalancing *)
//	| (INode (R, Node (R, x, a, y), b, z), Node (B, _, _, _)) => INode (B, Node (R, x, a, y), b, Node (R, z, element, right))
//	| (INode (R, x, a, Node (R, y, b, z)), Node (B, _, _, _)) => INode (B, Node (R, x, a, y), b, Node (R, z, element, right))
//	(* otherwise *)
//	| (_, _) =>> INode (color, left, element, right)

//(* http://cs.wellesley.edu/~cs231/fall01/red-black.pdf *)
//fun {a:t@ype} balance_insert_right {c,cl,cr:color|c==B} {h:nat} (color: int c, left: _rbtree (a, cl, h), element: a, right: i__rbtree (a, cr, h)): i__rbtree (a, c, h) = 
//	case+ (left, right) of 
//	(* recoloring *)
//	| (Node (R, m, c, n), INode (R, Node (R, x, a, y), b, z)) => INode (R, Node (B, m, c, n), element, Node (B, Node (R, x, a, y), b, z)) 
//	| (Node (R, m, c, n), INode (R, x, a, Node (R, y, b, z))) => INode (R, Node (B, m, c, n), element, Node (B, x, a, Node (R, y, b, z)))
//	(* rebalancing *)
//	| (Node (B, _, _, _), INode (R, Node (R, x, a, y), b, z)) => INode (B, Node (R, left, element, x), a, Node (R, y, b, z))
//	| (Node (B, _, _, _), INode (R, x, a, Node (R, y, b, z))) => INode (B, Node (R, left, element, x), a, Node (R, y, b, z))
//	(* otherwise *)
//	| (_, _) =>> INode (color, left, element, right)

//stadef balance_delete_case1 (c:color, cl:color, cr:color): bool = (c==R) * (((cl==BB)*(cr==B)) + ((cl==B)*(cr==BB)))
//stadef balance_delete_case2 (c:color, cl:color, cr:color): bool = (c==B) * (((cl==BB)*(cr==B)) + ((cl==B)*(cr==BB)))
//stadef balance_delete_case3 (c:color, cl:color, cr:color): bool = (c==B) * (((cl==BB)*(cr==R)) + ((cl==R)*(cr==BB)))
//stadef balance_delete (c:color, cl:color, cr:color): bool = balance_delete_case1 (c, cl, cr) + balance_delete_case2 (c, cl, cr) + balance_delete_case3 (c, cl, cr)



//fun {a:t@ype} balance_delete_rr {c,cl,cr:color|c==B} {h:nat}


//fun {a:t@ype} balance_delete_left {c:cl,cr:color|balance_delete (c,cl,cr) * (cl==BB)} {h:nat|h==2} (color: int c, left: d__rbtree (a, cl, h), y: a, right: _rbtree (a, cr, h)): d__rbtree (a, c, h) = 
//	case+ (left, right) of 
//	| (DNode (BB, a, x, b), Node (B, c, z, d)) => balance_delete_left ()
//	| (DNode (BB, a, x, b), Node (B, c, z, d)) => Node (B, Node (R, Node (B, a, x, b), y, c), z, d) 


//	(* normal case: RR violation with recoloring: not possible *)
//	(* normal case: RR violation with rebalancing *)
//	| DNode (R, Node (R, a, x, b), y, c) where color = B => DNode (B, Node (R, a, x, b), y, Node (R, c, element, right))
//	| DNode (R, a, x, Node (R, b, y, c)) where color = B => DNode (B, Node (R, a, x, b), y, Node (R, c, element, right))
//	(* new case: RR violation with BB parent *)
//	| DNode (R, Node (R, a, x, b), y, c) where color = BB => DNode (B, Node (B, a, x, b), y, Node (B, c, element, right))
//	| DNode (R, a, x, Node (R, b, y, c)) where color = BB => DNode (B, Node (B, a, x, b), y, Node (B, c, element, right))
//	(* new case: WB violation with BB parent *)
//	| DNode (NB, Node (B, a, x, b), y, Node (B, c, z, d)) => 
//		(* DNode (B, Node (B, Node (R, a, x, b), y, c), z, Node (B, d, element, right)) *)
//		case+ balance_delete_left (B, DNode (R, a, x, b), y, c) of 
//		| DNode ()                   

//	| (_, _) =>> INode (color, left, element, right)


(*
 *  bubble: to remove double black leaf. it either completely eliminate double black, or push it up as a double black non-leaf node
 *)


(* http://matt.might.net/articles/red-black-delete/ *)
(* http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/32/slides/red-black-pearl.pdf *)

//stadef bubble_case1 (c:color, cl:color, cr:color): bool = (c==R)*(((cl==EE)*(cr==B)) + ((cl==B)*(cr==EE)))
//stadef bubble_case2 (c:color, cl:color, cr:color): bool = (c==B)*(((cl==EE)*(cr==B)) + ((cl==B)*(cr==EE)))
//stadef bubble_case3 (c:color, cl:color, cr:color): bool = (c==B)*(((cl==EE)*(cr==R)) + ((cl==R)*(cr==EE)))
//stadef bubble (c:color, cl:color, cr:color): bool = bubble_case1 (c, cl, cr) + bubble_case2 (c, cl, cr) + bubble_case3 (c, cl, cr)

//fun {a:t@ype} bubble_left {c,cl,cr:color|bubble (c,cl,cr) * (cl==BB)} {h:nat|h==1} (color: int c, left: d__rbtree (a, cl, h), x: a, right: _rbtree (a, cr, h)): d__rbtree (a, darken c, incr (h, c)) = 
//	case+ (left, right) of 
//	| (DBBEmpty (), Node (R, Node (B, E, y, E), z, Node (B, E, w, E))) => DNode (B, Node (B, E, x, Node (R, E, y, E)), z, Node (B, E, w, E))
//	| (_, _) => DNode (darken color, lighten left, x, lighten right)

//fun {a:t@ype} bubble_right {c,cl,cr:color|bubble (c,cl,cr) * (cr==BB)} {h:nat|h==1} (color: int c, left: _rbtree (a, cl, h), w: a, right: d__rbtree (a, cr, h)): d__rbtree (a, darken c, incr (h, c)) = 
//	case+ (left, right) of 
//	| (Node (R, Node (B, E, x, E), y, Node (B, E, z, E)), DBBEmpty ()) => DNode (B, Node (B, E, x, E), y, Node (B, Node (R, E, z, E), w, E))
//	| (_, _) => DNode (darken color, lighten left, w, lighten right)



in (* local-in-end *)




implement {a} empty () = Empty ()

implement {a} member (tree, element, cmp) = 
	case+ tree of 
	| Empty _ => false 
	| Node (_, l, e, r) => 
		if cmp (element, e) < 0 then member (l, element, cmp)
		else if cmp (element, e) > 0 then member (r, element, cmp)
		else true 

implement {a} elements (tree) = 
	case+ tree of 
	| Empty _ => Nil ()
	| Node (_, l, e, r) => concat (elements l, (e :: (elements r)))

implement {a} insert (tree, element, cmp) = let 

	#define E Empty 
//	fun ins {c:color|(c==R)+(c==B)} {h:nat} (tree: _rbtree (a, c, h, false), element: a, cmp: (a, a) -> int): [cc:color;bad:bool|((~bad)*(cc==B))+(cc==R)] _rbtree (a, cc, h, bad) =
//		case+ tree of 
//		| Empty _ => Node (R, Empty{..}{B}{..}{false} (), element, Empty{..}{B}{..}{..} ())
//		| Node (_, _, e, _) where cmp (element, e) = 0 => tree
//		| Node (color, left, e, right) where cmp (element, e) < 0 => if color = B then balance (color, ins (left, element, cmp), e, right) else Node (color, ins (left, element, cmp), e, right)
//		| Node (color, left, e, right) where cmp (element, e) > 0 => if color = B then balance (color, left, e, ins (right, element, cmp)) else Node (color, left, e, ins (right, element, cmp))

//	fun blacken {c:color} {h:nat} (tree: i__rbtree (a, c, h)): _rbtree (a, B, incr (h, c)) = 
//		case+ tree of 
//		| INode (_, left, e, right) => Node (B, left, e, right)

//	fun ins {c:color} {h:nat} (tree: _rbtree (a, c, h)):<cloref1> [cc:color] i__rbtree (a, cc, h) = 
//		case+ tree of 
//		| Empty _                                                 => INode (R, Empty (), element, Empty ())
//		| Node (color, left, e, right) where cmp (element, e) < 0 => if color = B then balance_insert_left (color, ins left, e, right) else INode (color, ins left, e, right)
//		| Node (color, left, e, right) where cmp (element, e) > 0 => if color = B then balance_insert_right (color, left, e, ins right) else INode (color, left, e, ins right)
//		| Node (color, left, e, right) where cmp (element, e) = 0 => INode (color, left, e, right)

	fun ins {c:color} {h:nat} (tree: _rbtree (a, c, h), element: a):<cloref1> [cc:color] __rbtree (a, cc, h) = 
		case+ tree of 
		| Empty _                                          => RBNode (R, E, element, E)
		| Node (color, a, x, b) when cmp (element, x) < 0 => balance_left (color, ins (a, element), x, b)
		| Node (color, a, x, b) when cmp (element, x) > 0 => balance_right (color, a, x, ins (b, element))
		| Node (color, a, x, b) when cmp (element, x) = 0 => RBNode (color, a, x, b)
in 
	blacken (ins (tree, element))
end


implement {a} delete (tree, element, cmp) = let 
	
	#define E Empty 

	fun del {c:color} {h:nat} (tree: _rbtree (a, c, h), element: a):<cloref1> [cc:color] __rbtree (a, cc, h) = 
		case+ tree of 
		| Empty _ => BEmpty ()
		| Node (color, a, x, b) when cmp (element, x) = 0 => delroot tree
		| Node (color, a, x, b) when cmp (element, x) < 0 => balance_left (color, del (a, element), x, b)
		| Node (color, a, x, b) when cmp (element, x) > 0 => balance_right (color, a, x, del (b, element))

	and delroot {c:color} {h:nat|h>0} (tree: _rbtree (a, c, h)):<cloref1> [cc:color] __rbtree (a, cc, h) = 
		case+ tree of 
		| Node (R, E, _, E) => BEmpty ()
		| Node (B, E, _, E) => BBEmpty ()
		| Node (B, Node (R, _, x, _), _, E) => RBNode (B, E, x, E)
		| Node (B, E, _, Node (R, _, y, _)) => RBNode (B, E, y, E)
		| Node (B, a, x, b) => balance_left (B, delmax a, findmax a, b)

	and delmax {c:color} {h:nat|h>0} (tree: _rbtree (a, c, h)):<cloref1> [cc:color] __rbtree (a, cc, h) = 
		case+ tree of 
		| Node (_, _, x, E) => delroot tree 
		| Node (color, a, x, b) => balance_right (color, a, x, delmax b)

	and findmax {c:color} {h:nat|h>0} (tree: _rbtree (a, c, h)):<cloref1> a =
		case+ tree of 
		| Node (_, _, x, E) => x 
		| Node (_, _, _, b) => findmax b  

in 
	blacken (del (tree, element))
end 

end (* local-in-end *)