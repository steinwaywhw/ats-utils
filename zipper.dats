#include "share/atspre_staload.hats"
staload "./zipper.sats"
staload "list.sats"
staload _ = "./list.dats"

#define :: Cons

exception NoElem of ()

implement {a} make_zipper (tree) = Zipper (tree, Nil())

implement {a} peek (z, k) = 
	case+ z of 
	| Zipper (Empty (), _) => k ()
	| Zipper (Node (a, _, _), _) => a

implement {a} move_left (z) = 
	case+ z of 
	| Zipper (Empty (), moves) => z 
	| Zipper (Node (root, left, right), moves) =>> Zipper (left, Left (root, right) :: moves) 

implement {a} move_right (z) = 
	case+ z of 
	| Zipper (Empty (), moves) => z 
	| Zipper (Node (root, left, right), moves) =>> Zipper (right, Right (root, left) :: moves) 

implement {a} move_up (z) =
	case+ z of 
	| Zipper (_, Nil ()) => z 
	| Zipper (subroot, move :: moves) =>> 
		case+ move of 
		| Left (root, sibling) => Zipper (Node (root, subroot, sibling), moves)
		| Right (root, sibling) => Zipper (Node (root, sibling, subroot), moves)

implement {a} move_to_top (z) =
	case+ z of 
	| Zipper (_, Nil ()) => z 
	| Zipper (_, _) =>> move_to_top (move_up z)

implement {a} update (z, e) = 
	case+ z of 
	| Zipper (Empty (), moves) => Zipper (Node (e, Empty (), Empty ()), moves)
	| Zipper (Node (_, left, right), moves) =>> Zipper (Node (e, left, right), moves)

implement {a} test_zipper () = () where {

	fun show (z: zipper int): void = () where {
		val elem = peek (z, lam () => ~999)
		val _ = if elem = ~999 then println! "nil" else println! elem 
	}

	val tree = Node (5, 
					Node (3, 
						Node (1, Empty(), Empty()), 
						Node (2, Empty(), Empty())),
					Node (4, Empty(), Empty()))

	val z = make_zipper tree 
	val _ = show z 

	val z = move_left z 
	val _ = show z 

	val z = move_right z 
	val _ = show z 

	val z = move_right z 
	val _ = show z 

	val z = update (z, 10)
	val _ = show z

	val z = move_up z 
	val _ = show z 

	val z = move_to_top z 
	val _ = show z 

	val z = update (z, 55)
	val _ = show z

	val z = move_right z 
	val _ = show z 
}

implement main0 () = test_zipper ()
