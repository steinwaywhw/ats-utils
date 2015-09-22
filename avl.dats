#include "share/atspre_staload.hats" (* for int/nat/max *)
#define ATS_DYNLOADFLAG 0

staload "./avl.sats"
staload "./maybe.sats"
staload "./util.sats"

staload _ = "./maybe.dats"



(* internal datatype *)

datatype avltree_t (key:t@ype, value:t@ype+, int) = 
	| AVLNil (key, value, 0) of ()
	| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1} AVLNode (key, value, 1 + max (hl, hr)) of (key, value, avltree_t (key, value, hl), avltree_t (key, value, hr))
typedef avltree_t (key:t@ype, value:t@ype) = [n:nat] avltree_t (key, value, n)


(* interface *)

assume avltree (key, value) = avltree_t (key, value)


(* internal functions/exceptions, not intended for outside use *)

exception ElementAlreadyExists of ()
exception ElementDoesntExist of ()

fun {key:t@ype} {value:t@ype} height {h:nat} (tree: avltree_t (key, value, h)): int h =
	case+ tree of 
	| AVLNil () => 0 
	| AVLNode (_, _, left, right) => 1 + max (height left, height right)

fun {key:t@ype} {value:t@ype} rotate_right {hl,hr:nat|hl-hr==2} (k: key, v: value, left: avltree_t (key, value, hl), right: avltree_t (key, value, hr)): [h:nat|hl <= h; h <= hl+1] avltree_t (key, value, h) =
	let 
		val+ AVLNode (lk, lv, ll, lr) = left 
	in 
		if height ll >= height lr 
		then AVLNode (lk, lv, ll, AVLNode (k, v, lr, right))
		else let val+ AVLNode (lrk, lrv, lrl, lrr) = lr in AVLNode (lrk, lrv, AVLNode (lk, lv, ll, lrl), AVLNode (k, v, lrr, right)) end
	end 

fun {key:t@ype} {value:t@ype} rotate_left {hl,hr:nat|hr-hl==2} (k: key, v: value, left: avltree_t (key, value, hl), right: avltree_t (key, value, hr)): [h:nat|hr <= h; h <= hr+1] avltree_t (key, value, h) =
	let 
		val+ AVLNode (rk, rv, rl, rr) = right
	in 
		if height rl <= height rr 
		then AVLNode (rk, rv, AVLNode (k, v, left, rl), rr)
		else let val+ AVLNode (rlk, rlv, rll, rlr) = rl in AVLNode (rlk, rlv, AVLNode (k, v, left, rll), AVLNode (rk, rv, rlr, rr)) end
	end


(* implementations *)

implement avltree_height {key} {value} (tree) = height tree

implement {key} {value} avltree_insert (tree, k, v, cmp) = let 

	fun insert {h:nat} (t: avltree_t (key, value, h)): [hh:nat|h <= hh; hh <= h+1] avltree_t (key, value, hh) = 
		case+ t of 
		| AVLNil () => AVLNode (k, v, AVLNil (), AVLNil ())
		| AVLNode (current_key, current_value, left, right) => 
			if cmp (k, current_key) < 0 then
				let 
					val t = insert left
				in 
					if height t - height right > 1 
					then rotate_right (current_key, current_value, t, right)
					else AVLNode (current_key, current_value, t, right)
				end 
			else if cmp (k, current_key) > 0 then 
				let 
					val t = insert right
				in 
					if height t - height left > 1 
					then rotate_left (current_key, current_value, left, t)
					else AVLNode (current_key, current_value, left, t)
				end 
			else 
				$raise ElementAlreadyExists () 
in 
	insert tree
end 

implement {key} {value} avltree_replace (tree, k, v, cmp) = 
	case+ tree of 
	| AVLNil () => $raise ElementDoesntExist () 
	| AVLNode (current, _, left, right) => 
		if cmp (k, current) > 0 then avltree_replace (right, k, v, cmp)
		else if cmp (k, current) < 0 then avltree_replace (left, k, v, cmp)
		else AVLNode (current, v, left, right)

implement {key} {value} avltree_insert_or_replace (tree, k, v, cmp) = 
	if avltree_member (tree, k, cmp) 
	then avltree_replace (tree, k, v, cmp)
	else avltree_insert (tree, k, v, cmp)

implement {key} {value} avltree_delete (tree, k, cmp) = let 

	fun find_min (tree: avltree (key, value)): (key, value) = 
		case+ tree of 
		| AVLNode (k, v, AVLNil (), _) => (k, v)
		| AVLNode (_, _, left, _)      => find_min left
		| AVLNil  ()                   => $raise ElementDoesntExist () (* this should not happen *)

	fun delete {h:nat} (tree: avltree_t (key, value, h), k: key): [hh:nat|h-1 <= hh; hh <= h] avltree_t (key, value, hh) = 
		case+ tree of 
		| AVLNil () => $raise ElementDoesntExist ()
		| AVLNode (current, _, AVLNil (), AVLNil ()) => 
			if cmp (current, k) = 0
			then AVLNil ()
			else $raise ElementDoesntExist () 
		|  AVLNode (current, v, left, right) => 
			if cmp (k, current) < 0 then 
				let 
					val newleft = delete (left, k)
				in 
					if height right - height newleft > 1
					then rotate_left (current, v, newleft, right)
					else AVLNode (current, v, newleft, right)
				end 
			else if cmp (k, current) > 0 then 
				let 
					val newright = delete (right, k)
				in 
					if height left - height newright > 1
					then rotate_right (current, v, left, newright)
					else AVLNode (current, v, left, newright)
				end
			else 
				case+ (left, right) of 
				| (AVLNil (), _) => right 
				| (_, AVLNil ()) => left 
				| (_, _) => 
					let 
						val (mink, minv) = find_min right 
						val newright = delete (right, mink)
					in 
						if height left - height newright > 1
						then rotate_right (mink, minv, left, newright)
						else AVLNode (mink, minv, left, newright)
					end
in 
	delete (tree, k)
end 

implement {key} {value} avltree_member (tree, k, cmp) = 
	case+ tree of 
	| AVLNil () => false 
	| AVLNode (current, _, left, right) => 
		if cmp (current, k) = 0 then true 
		else if cmp (current, k) > 0 then avltree_member (left, k, cmp)
		else avltree_member (right, k, cmp)



implement {key} {value} avltree_lookup (tree, k, cmp) = let 
	fun lookup (tree: avltree (key, value)): maybe value = 
		case+ tree of 
		| AVLNil () => Nothing ()
		| AVLNode (current, v, left, right) => 
			if cmp (k, current) < 0 then lookup left
			else if cmp (k, current) > 0 then lookup right
			else Just v 
in 
	lookup tree
end 

implement avltree_empty {key} {value} (tree) = 
	case+ tree of 
	| AVLNil () => true
	| _ => false

implement avltree_size {key} {value} (tree) = 
	case+ tree of 
	| AVLNil () => i2sz 0
	| AVLNode (_, _, left, right) => i2sz 1 + avltree_size (left) + avltree_size (right)

implement {key} {value} avltree_show (tree, show_key, show_value) = let 

	fun pad (level: int): void = 
		if level > 0
		then let val _ = show "    " in pad (level - 1) end 

	fun show_with_pad (tree: avltree (key, value), level: int): void = 
		case+ tree of 
		| AVLNil () => ()
		| AVLNode (k, v, AVLNil (), AVLNil ()) => 
			let 
				val _ = pad level
				val _ = show "("
				val _ = show_key k 
				val _ = show ":"
				val _ = show_value v 
				val _ = show ")\n"
			in 
			end 
		| AVLNode (k, v, left, right) =>
			let 
				val _ = show_with_pad (right, level + 1)
				val _ = pad level 
				val _ = show "("
				val _ = show_key k 
				val _ = show ":"
				val _ = show_value v 
				val _ = show ")\n"
				val _ = show_with_pad (left, level + 1)
			in 
			end 
in 
	show_with_pad (tree, 0)
end


(* test *)

fun avltree_test (): void = () where {
	val cmp = lam (x:int, y:int):int => x - y

	val t = AVLNil () 
	val t = avltree_insert (t, 20, 20, cmp)
	val t = avltree_insert (t, 4, 4, cmp)
	val t = avltree_insert (t, 26, 26, cmp)
	val t = avltree_insert (t, 3, 3, cmp)
	val t = avltree_insert (t, 9, 9, cmp)
	val t = avltree_insert (t, 21, 21, cmp)
	val t = avltree_insert (t, 30, 30, cmp)
	val t = avltree_insert (t, 2, 2, cmp)
	val t = avltree_insert (t, 7, 7, cmp)
	val t = avltree_insert (t, 11, 11, cmp)
	val t1 = avltree_insert (t, 15, 15, cmp)
	val t2 = avltree_insert (t, 8, 8, cmp)

	val _ = avltree_show (t1, lam x => print_int x, lam x => print_int x) 
	val _ = show "\n"
	val _ = avltree_show (t2, lam x => print_int x, lam x => print_int x) 
	val _ = show "\n"

	val t = AVLNil ()
	val t = avltree_insert (t, 5, 5, cmp)
	val t = avltree_insert (t, 2, 2, cmp)
	val t = avltree_insert (t, 8, 8, cmp)
	val t = avltree_insert (t, 1, 1, cmp)
	val t = avltree_insert (t, 3, 3, cmp)
	val t = avltree_insert (t, 7, 7, cmp)
	val t = avltree_insert (t, 10, 10, cmp)
	val t = avltree_insert (t, 4, 4, cmp)
	val t = avltree_insert (t, 6, 6, cmp)
	val t = avltree_insert (t, 9, 9, cmp)
	val t = avltree_insert (t, 11, 11, cmp)
	val t = avltree_insert (t, 12, 12, cmp)

	val t = avltree_delete (t, 1, cmp)
	val _ = avltree_show (t, lam x => print_int x, lam x => print_int x)
}

implement main0 () = avltree_test ()



