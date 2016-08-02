#include "share/atspre_staload.hats" (* for int/nat/max *)
#define ATS_DYNLOADFLAG 0

//staload "libats/ML/SATS/string.sats"
//staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./avl.sats"
staload "./maybe.sats"
staload _ = "./maybe.dats"


(* internal datatype *)

datatype avltree_t (k:t@ype, v:t@ype, int) = 
| AVLNil (k, v, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1} AVLNode (k, v, 1 + max (hl, hr)) of (k, v, avltree_t (k, v, hl), avltree_t (k, v, hr))
typedef avltree_t (k:t@ype, v:t@ype) = [n:nat] avltree_t (k, v, n)

#define nil  AVLNil 
#define cons AVLNode

local (* LOCAL *)

assume avltree (k, v) = avltree_t (k, v)

(* internal functions/exceptions, not intended for outside use *)

exception AVLTreeException of string


fun {k,v:t@ype} _height {h:nat} (tree: avltree_t (k, v, h)): int h =
	case+ tree of 
	| AVLNil () => 0 
	| AVLNode (_, _, left, right) => 1 + max (_height left, _height right)

fun {k,v:t@ype} _rotate_right {hl,hr:nat|hl-hr==2} (k: k, v: v, left: avltree_t (k, v, hl), right: avltree_t (k, v, hr)): [h:nat|hl <= h; h <= hl+1] avltree_t (k, v, h) =
	let 
		val+ AVLNode (lk, lv, ll, lr) = left 
	in 
		if _height ll >= _height lr 
		then AVLNode (lk, lv, ll, AVLNode (k, v, lr, right))
		else let val+ AVLNode (lrk, lrv, lrl, lrr) = lr in AVLNode (lrk, lrv, AVLNode (lk, lv, ll, lrl), AVLNode (k, v, lrr, right)) end
	end 

fun {k,v:t@ype} _rotate_left {hl,hr:nat|hr-hl==2} (k: k, v: v, left: avltree_t (k, v, hl), right: avltree_t (k, v, hr)): [h:nat|hr <= h; h <= hr+1] avltree_t (k, v, h) =
	let 
		val+ AVLNode (rk, rv, rl, rr) = right
	in 
		if _height rl <= _height rr 
		then AVLNode (rk, rv, AVLNode (k, v, left, rl), rr)
		else let val+ AVLNode (rlk, rlv, rll, rlr) = rl in AVLNode (rlk, rlv, AVLNode (k, v, left, rll), AVLNode (rk, rv, rlr, rr)) end
	end

in (* LOCAL *)

(* implementations *)

implement {a} avltree_cmp$elm (a, b) = gcompare_val_val<a> (a, b)

implement {k,v} avltree_cmp (a, b) = 
	case+ (a, b) of 
	| (nil _, nil _) => 0 
	| (cons (k1,v1,l1,r1), cons (k2,v2,l2,r2)) => 
		let val cmp = avltree_cmp$elm (k1, k2)
		in if cmp != 0 then cmp else 
			let val cmp = avltree_cmp$elm (v1, v2)
			in if cmp != 0 then cmp else 
				let val cmp = avltree_cmp (l1, l2)
				in if cmp != 0 then cmp else avltree_cmp (r1, r2) end 
			end 
		end
	| (_, _) => (avltree_size a) - (avltree_size b)


implement {k,v} avltree_eq (a, b) = avltree_cmp (a, b) = 0

implement {k,v} avltree_make () = AVLNil ()

implement {k,v} avltree_height (tree) = _height tree

implement {k,v} avltree_empty (tree) = 
	case+ tree of 
	| AVLNil () => true
	| _ => false

implement {k,v} avltree_size (tree) = 
	case+ tree of 
	| AVLNil () => 0
	| AVLNode (_, _, left, right) => 1 + avltree_size (left) + avltree_size (right)



implement {k,v} avltree_insert (tree, k, v) = let 

	val cmp = avltree_cmp$elm<k>

	fun _insert {h:nat} (t: avltree_t (k, v, h)): [hh:nat|h <= hh; hh <= h+1] avltree_t (k, v, hh) = 
		case+ t of 
		| AVLNil () => AVLNode (k, v, AVLNil (), AVLNil ())
		| AVLNode (current_k, current_v, left, right) => 
			if cmp (k, current_k) < 0 then
				let 
					val t = _insert left
				in 
					if _height t - _height right > 1 
					then _rotate_right (current_k, current_v, t, right)
					else AVLNode (current_k, current_v, t, right)
				end 
			else if cmp (k, current_k) > 0 then 
				let 
					val t = _insert right
				in 
					if _height t - _height left > 1 
					then _rotate_left (current_k, current_v, left, t)
					else AVLNode (current_k, current_v, left, t)
				end 
			else 
				$raise AVLTreeException ("Element already exists.") 
in 
	_insert tree
end 

implement {k,v} avltree_replace (tree, k, v) = let 
	val cmp = avltree_cmp$elm<k>
in 
	case+ tree of 
	| AVLNil () => $raise AVLTreeException ("Element does not exist.") 
	| AVLNode (current, _, left, right) => 
		if cmp (k, current) > 0 then avltree_replace (right, k, v)
		else if cmp (k, current) < 0 then avltree_replace (left, k, v)
		else AVLNode (current, v, left, right)
end


implement {k,v} avltree_insert_or_replace (tree, k, v) =
	if avltree_member (tree, k) 
	then avltree_replace (tree, k, v)
	else avltree_insert (tree, k, v)

implement {k,v} avltree_delete (tree, k) = let 
	val cmp = avltree_cmp$elm<k>

	fun find_min (tree: avltree (k, v)): (k, v) = 
		case+ tree of 
		| AVLNode (k, v, AVLNil (), _) => (k, v)
		| AVLNode (_, _, left, _)      => find_min left
		| AVLNil  ()                   => $raise AVLTreeException ("Element does not exist.") (* this should not happen *)

	fun _delete {h:nat} (tree: avltree_t (k, v, h), k: k): [hh:nat|h-1 <= hh; hh <= h] avltree_t (k, v, hh) = 
		case+ tree of 
		| AVLNil () => $raise AVLTreeException ("Element does not exist.")
		| AVLNode (current, _, AVLNil (), AVLNil ()) => 
			if cmp (current, k) = 0
			then AVLNil ()
			else $raise AVLTreeException ("Element does not exist.") 
		|  AVLNode (current, v, left, right) => 
			if cmp (k, current) < 0 then 
				let 
					val newleft = _delete (left, k)
				in 
					if _height right - _height newleft > 1
					then _rotate_left (current, v, newleft, right)
					else AVLNode (current, v, newleft, right)
				end 
			else if cmp (k, current) > 0 then 
				let 
					val newright = _delete (right, k)
				in 
					if _height left - _height newright > 1
					then _rotate_right (current, v, left, newright)
					else AVLNode (current, v, left, newright)
				end
			else 
				case+ (left, right) of 
				| (AVLNil (), _) => right 
				| (_, AVLNil ()) => left 
				| (_, _) => 
					let 
						val (mink, minv) = find_min right 
						val newright = _delete (right, mink)
					in 
						if _height left - _height newright > 1
						then _rotate_right (mink, minv, left, newright)
						else AVLNode (mink, minv, left, newright)
					end
in 
	_delete (tree, k)
end 

implement {k,v} avltree_member (tree, k) = let 
	val cmp = avltree_cmp$elm<k>
in 
	case+ tree of 
	| AVLNil () => false 
	| AVLNode (current, _, left, right) => 
		if cmp (current, k) = 0 then true 
		else if cmp (current, k) > 0 then avltree_member (left, k)
		else avltree_member (right, k)
end 


implement {k,v} avltree_find (tree, k) = let 
	val cmp = avltree_cmp$elm<k>

	fun _find (tree: avltree (k, v)): maybe v = 
		case+ tree of 
		| AVLNil () => Nothing ()
		| AVLNode (current, v, left, right) => 
			if cmp (k, current) < 0 then _find left
			else if cmp (k, current) > 0 then _find right
			else Just v 
in 
	_find tree
end 


implement {k,v} avltree_any (tree, f) = 
	case+ tree of 
	| nil _ => false 
	| cons (k, v, l, r) => f k orelse avltree_any (l, f) orelse avltree_any (r, f)

implement {k,v} avltree_all (tree, f) = 
	case+ tree of 
	| nil _ => true 
	| cons (k, v, l, r) => f k andalso avltree_all (l, f) andalso avltree_all (r, f)


implement {a} avltree_show$elm (x) = gprint_val<a> x 


implement {k,v} avltree_show (tree) = let 

	val show_k = avltree_show$elm<k>
	val show_v = avltree_show$elm<v>

	fun pad (level: int): void = 
		if level > 0
		then let val _ = show "    " in pad (level - 1) end 

	fun show_with_pad (tree: avltree (k, v), level: int): void = 
		case+ tree of 
		| AVLNil () => ()
		| AVLNode (k, v, AVLNil (), AVLNil ()) => 
			let 
				val _ = pad level
				val _ = show "("
				val _ = show_k k 
				val _ = show ":"
				val _ = show_v v 
				val _ = show ")\n"
			in 
			end 
		| AVLNode (k, v, left, right) =>
			let 
				val _ = show_with_pad (right, level + 1)
				val _ = pad level 
				val _ = show "("
				val _ = show_k k 
				val _ = show ":"
				val _ = show_v v 
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

	val t = avltree_make<int,int> () 
	val t = avltree_insert (t, 20, 20)
	val t = avltree_insert (t, 4, 4)
	val t = avltree_insert (t, 26, 26)
	val t = avltree_insert (t, 3, 3)
	val t = avltree_insert (t, 9, 9)
	val t = avltree_insert (t, 21, 21)
	val t = avltree_insert (t, 30, 30)
	val t = avltree_insert (t, 2, 2)
	val t = avltree_insert (t, 7, 7)
	val t = avltree_insert (t, 11, 11)
	val t1 = avltree_insert (t, 15, 15)
	val t2 = avltree_insert (t, 8, 8)

	val _ = avltree_show t1
	val _ = show "\n"
	val _ = avltree_show t2
	val _ = show "\n"

	val t = avltree_make<int,int> ()
	val t = avltree_insert (t, 5, 5)
	val t = avltree_insert (t, 2, 2)
	val t = avltree_insert (t, 8, 8)
	val t = avltree_insert (t, 1, 1)
	val t = avltree_insert (t, 3, 3)
	val t = avltree_insert (t, 7, 7)
	val t = avltree_insert (t, 10, 10)
	val t = avltree_insert (t, 4, 4)
	val t = avltree_insert (t, 6, 6)
	val t = avltree_insert (t, 9, 9)
	val t = avltree_insert (t, 11, 11)
	val t = avltree_insert (t, 12, 12)

	val t = avltree_delete (t, 1)
	val _ = avltree_show t
}




