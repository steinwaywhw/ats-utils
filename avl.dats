#include "share/atspre_staload.hats" (* for int/nat/max *)
#define ATS_DYNLOADFLAG 0

//staload "libats/ML/SATS/string.sats"
//staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./avl.sats"
staload "./list.sats"
staload _ = "./list.dats"
staload "./maybe.sats"
staload _ = "./maybe.dats"


(* internal datatype *)

datatype avltree_t (a:t@ype, int) = 
| AVLNil (a, 0) of ()| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1} AVLNode (a, 1 + max (hl, hr)) of (a, avltree_t (a, hl), avltree_t (a, hr))
typedef avltree_t (a:t@ype) = [n:nat] avltree_t (a, n)

#define nil  AVLNil 
#define cons AVLNode

local (* LOCAL *)

assume avltree a = avltree_t a

(* internal functions/exceptions, not intended for outside use *)

exception AVLTreeException of string


fun {a:t@ype} _height {h:nat} (tree: avltree_t (a, h)): int h =
	case+ tree of 
	| AVLNil () => 0 
	| AVLNode (_, left, right) => 1 + max (_height left, _height right)

fun {a:t@ype} _rotate_right {hl,hr:nat|hl-hr==2} (k: a, left: avltree_t (a, hl), right: avltree_t (a, hr)): [h:nat|hl <= h; h <= hl+1] avltree_t (a, h) =
	let 
		val+ AVLNode (lk, ll, lr) = left 
	in 
		if _height ll >= _height lr 
		then AVLNode (lk, ll, AVLNode (k, lr, right))
		else let val+ AVLNode (lrk, lrl, lrr) = lr in AVLNode (lrk, AVLNode (lk, ll, lrl), AVLNode (k, lrr, right)) end
	end 

fun {a:t@ype} _rotate_left {hl,hr:nat|hr-hl==2} (k: a, left: avltree_t (a, hl), right: avltree_t (a, hr)): [h:nat|hr <= h; h <= hr+1] avltree_t (a, h) =
	let 
		val+ AVLNode (rk, rl, rr) = right
	in 
		if _height rl <= _height rr 
		then AVLNode (rk, AVLNode (k, left, rl), rr)
		else let val+ AVLNode (rlk, rll, rlr) = rl in AVLNode (rlk, AVLNode (k, left, rll), AVLNode (rk, rlr, rr)) end
	end

in (* LOCAL *)

(* implementations *)

implement {a} avltree_cmp$elm (a, b) = gcompare_val_val<a> (a, b)

//implement {a} avltree_cmp (a, b) = 
//	case+ (a, b) of 
//	| (nil _, nil _) => 0 
//	| (cons (k1,l1,r1), cons (k2,l2,r2)) => 
//		if avltree_cmp$elm (k1, k2) = 0 then 0
//		else if avltree_cmp (l1, l2) = 0 then avltree_cmp (r1, r2)
//		else if avltree_cmp (r1, r2) = 0
//	| (_, _) => (avltree_size a) - (avltree_size b)


implement {a} avltree_eq (a, b) = 
	case+ (a, b) of 
	| (nil _, nil _) => true 
	| (cons (k1, l1, r1), cons (k2, l2, r2)) => avltree_cmp$elm (k1, k2) = 0 andalso l1 = l2 andalso r1 = r2
	| (_, _) => false

implement {a} avltree_make () = AVLNil ()

implement {a} avltree_height (tree) = _height tree

implement {a} avltree_empty (tree) = 
	case+ tree of 
	| AVLNil () => true
	| _         => false

implement {a} avltree_size (tree) = 
	case+ tree of 
	| AVLNil ()                => 0
	| AVLNode (_, left, right) => 1 + avltree_size (left) + avltree_size (right)



implement {a} avltree_insert (tree, k) = let 

	val cmp = avltree_cmp$elm<a>

	fun _insert {h:nat} (t: avltree_t (a, h)): [hh:nat|h <= hh; hh <= h+1] avltree_t (a, hh) = 
		case+ t of 
		| AVLNil () => AVLNode (k, AVLNil (), AVLNil ())
		| AVLNode (current_k, left, right) => 
			if cmp (k, current_k) < 0 then
				let 
					val t = _insert left
				in 
					if _height t - _height right > 1 
					then _rotate_right (current_k, t, right)
					else AVLNode (current_k, t, right)
				end 
			else if cmp (k, current_k) > 0 then 
				let 
					val t = _insert right
				in 
					if _height t - _height left > 1 
					then _rotate_left (current_k, left, t)
					else AVLNode (current_k, left, t)
				end 
			else 
				$raise AVLTreeException ("Key already exists.") 
in 
	_insert tree
end 


implement {a} avltree_delete (tree, k) = let 
	val cmp = avltree_cmp$elm<a>

	fun find_min (tree: avltree a): a = 
		case+ tree of 
		| AVLNode (k, AVLNil (), _) => k
		| AVLNode (_, left, _)      => find_min left
		| AVLNil  ()                   => $raise AVLTreeException ("Key does not exist.") (* this should not happen *)

	fun _delete {h:nat} (tree: avltree_t (a, h), k: a): [hh:nat|h-1 <= hh; hh <= h] avltree_t (a, hh) = 
		case+ tree of 
		| AVLNil () => $raise AVLTreeException ("Key does not exist.")
		| AVLNode (current, AVLNil (), AVLNil ()) => 
			if cmp (current, k) = 0
			then AVLNil ()
			else $raise AVLTreeException ("Key does not exist.") 
		|  AVLNode (current, left, right) => 
			if cmp (k, current) < 0 then 
				let 
					val newleft = _delete (left, k)
				in 
					if _height right - _height newleft > 1
					then _rotate_left (current, newleft, right)
					else AVLNode (current, newleft, right)
				end 
			else if cmp (k, current) > 0 then 
				let 
					val newright = _delete (right, k)
				in 
					if _height left - _height newright > 1
					then _rotate_right (current, left, newright)
					else AVLNode (current, left, newright)
				end
			else 
				case+ (left, right) of 
				| (AVLNil (), _) => right 
				| (_, AVLNil ()) => left 
				| (_, _) => 
					let 
						val mink = find_min right 
						val newright = _delete (right, mink)
					in 
						if _height left - _height newright > 1
						then _rotate_right (mink, left, newright)
						else AVLNode (mink, left, newright)
					end
in 
	_delete (tree, k)
end 

implement {a} avltree_member (tree, k) = let 
	val cmp = avltree_cmp$elm<a>
in 
	case+ tree of 
	| AVLNil () => false 
	| AVLNode (current, left, right) => 
		if cmp (current, k) = 0 then true 
		else if cmp (current, k) > 0 then avltree_member (left, k)
		else avltree_member (right, k)
end 


implement {a} avltree_find (tree, k) = let 
	val cmp = avltree_cmp$elm<a>

	fun _find (tree: avltree a): maybe a = 
		case+ tree of 
		| AVLNil () => Nothing ()
		| AVLNode (current, left, right) => 
			if cmp (k, current) < 0 then _find left
			else if cmp (k, current) > 0 then _find right
			else Just k
in 
	_find tree
end 

implement {a} avltree_size (tree) = let 
	typedef nat = [n:nat] int n
in 
	avltree_foldr<a,nat> (tree, 0, lam (k, sum) => 1 + list_foldr<nat,nat> (sum, 0, lam (x, sum) => x + sum))
end

implement {a} avltree_height (tree) = let 
	typedef nat = [n:nat] int n 
in 
	avltree_foldr<a,nat> (tree, 0, lam (k, hs) => 1 + list_foldr<nat,nat> (hs, 0, lam (x, hs) => if x > hs then x else hs))
end

implement {a,b} avltree_foldr (tree, base, f) = let 
	#define :: ListCons
in 
	case+ tree of 
	| nil _ => base 
	| cons (k, l, r) => f (k, avltree_foldr (l, base, f) :: avltree_foldr (r, base, f) :: ListNil ())
end 


implement {a} avltree_foreach (tree, f) = 
	case+ tree of 
	| nil _ => () 
	| cons (k, l, r) => (avltree_foreach (l, f); f k; avltree_foreach (r, f)) 

//implement {a} avltree_iforeach (tree, f) = let 
//	typedef nat = [n:nat] int n

//	var index = 0: nat
//	fun loop (tree: avltree a, i: &nat):<cloref1> void = 
//		case+ tree of 
//		| nil _ => ()
//		| cons (k, l, r) => (loop (l, i); f (k, i); i := i + 1; loop (r, i))
//in 
//	loop (tree, index)
//end 

implement {a} avltree_filter (tree, f) = 
	list_foldr (list_filter (avltree_flatten (tree), f), nil (), lam (x, tree) => avltree_insert (tree, x))

implement {a,b} avltree_map (tree, f) = 
	list_foldr (avltree_flatten tree, nil (), lam (x, tree) => avltree_insert (tree, f x))


implement {a} avltree_flatten (tree) = let 
	#define :: ListCons 
in 
	case+ tree of 
	| nil _ => ListNil ()
	| cons (k, l, r) => list_concat (avltree_flatten l, k :: avltree_flatten r)
end

implement {a} avltree_any (tree, f) = 
	case+ tree of 
	| nil _ => false 
	| cons (k, l, r) => f k orelse avltree_any (l, f) orelse avltree_any (r, f)

implement {a} avltree_all (tree, f) = 
	case+ tree of 
	| nil _ => true 
	| cons (k, l, r) => f k andalso avltree_all (l, f) andalso avltree_all (r, f)


implement {a} avltree_show$elm (x) = gprint_val<a> x 


implement {a} avltree_show (tree) = let 

	val show_k = avltree_show$elm<a>

	fun pad (level: int): void = 
		if level > 0
		then let val _ = show "    " in pad (level - 1) end 

	fun show_with_pad (tree: avltree a, level: int): void = 
		case+ tree of 
		| AVLNil () => ()
		| AVLNode (k, AVLNil (), AVLNil ()) => 
			let 
				val _ = pad level
				val _ = show "("
				val _ = show_k k 
				val _ = show ")\n"
			in 
			end 
		| AVLNode (k, left, right) =>
			let 
				val _ = show_with_pad (right, level + 1)
				val _ = pad level 
				val _ = show "("
				val _ = show_k k 
				val _ = show ")\n"
				val _ = show_with_pad (left, level + 1)
			in 
			end 
in 
	show_with_pad (tree, 0)
end


end (* LOCAL *)


(* test *)

implement avltree_selftest (): void = () where {
//	implement avltree_cmp$elm = lam (x:int, y:int):int => x - y

	val t = avltree_make<int> () 
	val t = avltree_insert (t, 20)
	val t = avltree_insert (t, 4)
	val t = avltree_insert (t, 26)
	val t = avltree_insert (t, 3)
	val t = avltree_insert (t, 9)
	val t = avltree_insert (t, 21)
	val t = avltree_insert (t, 30)
	val t = avltree_insert (t, 2)
	val t = avltree_insert (t, 7)
	val t = avltree_insert (t, 11)
	val t1 = avltree_insert (t, 15)
	val t2 = avltree_insert (t, 8)

	val _ = avltree_show t1
	val _ = show "\n"
	val _ = avltree_show t2
	val _ = show "\n"

	val t = avltree_make<int> ()
	val t = avltree_insert (t, 5)
	val t = avltree_insert (t, 2)
	val t = avltree_insert (t, 8)
	val t = avltree_insert (t, 1)
	val t = avltree_insert (t, 3)
	val t = avltree_insert (t, 7)
	val t = avltree_insert (t, 10)
	val t = avltree_insert (t, 4)
	val t = avltree_insert (t, 6)
	val t = avltree_insert (t, 9)
	val t = avltree_insert (t, 11)
	val t = avltree_insert (t, 12)

	val t = avltree_delete (t, 1)
	val _ = avltree_show t
}




