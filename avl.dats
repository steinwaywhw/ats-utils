#include "share/atspre_staload.hats" 
#define ATS_DYNLOADFLAG 0

staload "./avl.sats"
staload "./list.sats"
staload "./maybe.sats"

staload _ = "./list.dats"
staload _ = "./maybe.dats"

(* internal datatype *)

datatype avltree_t (a:t@ype, int) = 
| AVLNil (a, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1} 
  AVLNode (a, 1 + max (hl, hr)) of (a, avltree_t (a, hl), avltree_t (a, hr))
typedef avltree_t (a:t@ype) = [n:nat] avltree_t (a, n)

#define nil  AVLNil 
#define cons AVLNode

exception AVLTreeException of string

local (* LOCAL *)

assume avltree a = avltree_t a

fun {a:t@ype} _height {h:nat} (tree: avltree_t (a, h)): int h =
	case+ tree of 
	| nil ()                => 0 
	| cons (_, left, right) => 1 + max (_height left, _height right)

fun {a:t@ype} _rotate_right {hl,hr:nat|hl-hr==2} (k: a, left: avltree_t (a, hl), right: avltree_t (a, hr)): [h:nat|hl <= h; h <= hl+1] avltree_t (a, h) =
	let 
		val+ cons (lk, ll, lr) = left 
	in 
		if _height ll >= _height lr 
		then cons (lk, ll, cons (k, lr, right))
		else let val+ cons (lrk, lrl, lrr) = lr in cons (lrk, cons (lk, ll, lrl), cons (k, lrr, right)) end
	end 

fun {a:t@ype} _rotate_left {hl,hr:nat|hr-hl==2} (k: a, left: avltree_t (a, hl), right: avltree_t (a, hr)): [h:nat|hr <= h; h <= hr+1] avltree_t (a, h) =
	let 
		val+ cons (rk, rl, rr) = right
	in 
		if _height rl <= _height rr 
		then cons (rk, cons (k, left, rl), rr)
		else let val+ cons (rlk, rll, rlr) = rl in cons (rlk, cons (k, left, rll), cons (rk, rlr, rr)) end
	end

in (* LOCAL *)

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (a) order_compare<avltree a> (xs, ys) = 
	case+ (xs, ys) of 
	| (nil _, nil _) => 0
	| (nil _, _)     => ~1
	| (_, nil _)     => 1
	| (cons (x, xl, xr), cons (y, yl, yr)) =>
		let 
			val cmp = order_compare<a> (x, y)
		in  
			if cmp = 0 
			then
				let val cmp = order_compare<avltree a> (xl, yl)
				in if cmp = 0 then order_compare<avltree a> (xr, yr) else cmp end
			else 
				cmp
		end

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (a) show_any<avltree a> (xs) = let 
	implement {} show_begin () = show_any<string> "("
	implement {} show_end   () = show_any<string> ")"
	implement {} show_sep   () = show_any<string> " "
in 
	case+ xs of 
	| cons (x, l, r) => 
		(show_begin<> (); 
		 show_any<a> x;
		 show_sep<> (); 
		 show_any<avltree a> l;
		 show_sep<> ();
		 show_any<avltree a> r;
		 show_end<> ())

	| nil () => 
		(show_begin<> (); 
		 show_end<> ())
end

(******************************)

implement {a} avltree_make () = nil ()

implement {a} avltree_height (tree) = _height tree

implement {a} avltree_empty (tree) = 
	case+ tree of 
	| nil () => true
	| _         => false

implement {a} avltree_size (tree) = 
	case+ tree of 
	| nil ()                => 0
	| cons (_, left, right) => 1 + avltree_size (left) + avltree_size (right)

(******************************)

implement {a} avltree_insert (tree, k) = let 

	val cmp = order_compare<a>

	fun _insert {h:nat} (t: avltree_t (a, h)): [hh:nat|h <= hh; hh <= h+1] avltree_t (a, hh) = 
		case+ t of 
		| nil () => cons (k, nil (), nil ())
		| cons (current_k, left, right) => 
			if cmp (k, current_k) < 0 then
				let 
					val t = _insert left
				in 
					if _height t - _height right > 1 
					then _rotate_right (current_k, t, right)
					else cons (current_k, t, right)
				end 
			else if cmp (k, current_k) > 0 then 
				let 
					val t = _insert right
				in 
					if _height t - _height left > 1 
					then _rotate_left (current_k, left, t)
					else cons (current_k, left, t)
				end 
			else 
				$raise AVLTreeException ("Key already exists.") 
in 
	_insert tree
end 


implement {a} avltree_delete (tree, k) = let 

	val cmp = order_compare<a>

	fun find_min (tree: avltree a): a = 
		case+ tree of 
		| cons (k, nil (), _) => k
		| cons (_, left, _)   => find_min left
		| nil  ()             => $raise AVLTreeException ("Key does not exist.") (* this should not happen *)

	fun _delete {h:nat} (tree: avltree_t (a, h), k: a): [hh:nat|h-1 <= hh; hh <= h] avltree_t (a, hh) = 
		case+ tree of 
		| nil () => $raise AVLTreeException ("Key does not exist.")
		| cons (current, nil (), nil ()) => 
			if cmp (current, k) = 0
			then nil ()
			else $raise AVLTreeException ("Key does not exist.") 
		| cons (current, left, right) => 
			if cmp (k, current) < 0 then 
				let 
					val newleft = _delete (left, k)
				in 
					if _height right - _height newleft > 1
					then _rotate_left (current, newleft, right)
					else cons (current, newleft, right)
				end 
			else if cmp (k, current) > 0 then 
				let 
					val newright = _delete (right, k)
				in 
					if _height left - _height newright > 1
					then _rotate_right (current, left, newright)
					else cons (current, left, newright)
				end
			else 
				case+ (left, right) of 
				| (nil (), _) => right 
				| (_, nil ()) => left 
				| (_, _) => 
					let 
						val mink = find_min right 
						val newright = _delete (right, mink)
					in 
						if _height left - _height newright > 1
						then _rotate_right (mink, left, newright)
						else cons (mink, left, newright)
					end
in 
	_delete (tree, k)
end 

implement {a} avltree_find (tree, k) = let 
	val cmp = order_compare<a>

	fun _find (tree: avltree a): maybe a = 
		case+ tree of 
		| nil () => Nothing ()
		| cons (current, left, right) => 
			if cmp (k, current) < 0 then _find left
			else if cmp (k, current) > 0 then _find right
			else Just k
in 
	_find tree
end 

implement {a} avltree_size (tree) = 
	avltree_foldr<a,nat> (tree, 0, lam (k, sum) => 
		1 + list_foldr<nat,nat> (sum, 0, lam (x, sum) => x + sum))


implement {a} avltree_height (tree) = 
	avltree_foldr<a,nat> (tree, 0, lam (k, hs) => 
		1 + list_foldr<nat,nat> (hs, 0, lam (x, hs) => if x > hs then x else hs))

(******************************)

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
(******************************)

implement {a} avltree_member (tree, k) = let 
	val cmp = order_compare<a>
in 
	case+ tree of 
	| nil () => false 
	| cons (current, left, right) => 
		if cmp (current, k) = 0 then true 
		else if cmp (current, k) > 0 then avltree_member (left, k)
		else avltree_member (right, k)
end 

implement {a} avltree_any (tree, f) = 
	case+ tree of 
	| nil _ => false 
	| cons (k, l, r) => f k orelse avltree_any (l, f) orelse avltree_any (r, f)

implement {a} avltree_all (tree, f) = 
	case+ tree of 
	| nil _ => true 
	| cons (k, l, r) => f k andalso avltree_all (l, f) andalso avltree_all (r, f)


//implement {a} avltree_show$elm (x) = gprint_val<a> x 


//implement {a} avltree_show (tree) = let 

//	val show_k = avltree_show$elm<a>

//	fun pad (level: int): void = 
//		if level > 0
//		then let val _ = show "    " in pad (level - 1) end 

//	fun show_with_pad (tree: avltree a, level: int): void = 
//		case+ tree of 
//		| nil () => ()
//		| cons (k, nil (), nil ()) => 
//			let 
//				val _ = pad level
//				val _ = show "("
//				val _ = show_k k 
//				val _ = show ")\n"
//			in 
//			end 
//		| cons (k, left, right) =>
//			let 
//				val _ = show_with_pad (right, level + 1)
//				val _ = pad level 
//				val _ = show "("
//				val _ = show_k k 
//				val _ = show ")\n"
//				val _ = show_with_pad (left, level + 1)
//			in 
//			end 
//in 
//	show_with_pad (tree, 0)
//end


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

	val _ = show<avltree int> t1
	val _ = show<string> "\n"
	val _ = show<avltree int> t2
	val _ = show<string> "\n"

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
	val _ = show<avltree int> t
}




