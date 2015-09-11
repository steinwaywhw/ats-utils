#include "share/atspre_staload.hats"

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

fun height {key:t@ype} {value:t@ype} {h:nat} (tree: avltree_t (key, value, h)): int h =
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

	fun insert {h:nat} (t: avltree_t (key, value, h)):<cloref1> [hh:nat|h <= hh; hh <= h+1] avltree_t (key, value, hh) = 
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

implement {key} {value} avltree_lookup (tree, k, cmp) = let 
	fun lookup (tree: avltree (key, value)):<cloref1> maybe value = 
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

implement {key} {value} avltree_show (tree, show_key, show_value) = 
	case+ tree of 
	| AVLNil () => ()
	| AVLNode (k, v, AVLNil (), AVLNil ()) => 
		let 
			val _ = show "("
			val _ = show_key k 
			val _ = show ":"
			val _ = show_value v 
			val _ = show ")\n"
		in 
		end 
	| AVLNode (k, v, left, right) =>
		let 
			val _ = avltree_show (left, show_key, show_value)
			val _ = show "("
			val _ = show_key k 
			val _ = show ":"
			val _ = show_value v 
			val _ = show ")\n"
			val _ = avltree_show (right, show_key, show_value)
		in 
		end 


(* test *)

fun avltree_test (): void = () where {
	val cmp = lam (x:int, y:int):int => x - y

	val t = AVLNil () 
	val t = avltree_insert (t, 10, "hello", cmp)
	val t = avltree_insert (t, 11, "world", cmp)
	val t = avltree_insert (t, 12, "aaaa", cmp)
	val _ = avltree_show (t, lam x => print_int x, lam x => print_string x) 
	val t = avltree_insert (t, 10, "aaaaaa", cmp)
}

implement main0 () = avltree_test ()



