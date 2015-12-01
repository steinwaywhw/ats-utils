staload "./list.sats"

datatype tree (a:t@ype) = 
| Empty (a) of ()
| Node (a) of (a, tree a, tree a)

datatype move (a:t@ype) = 
| Left (a) of (a, tree a)
| Right (a) of (a, tree a)

datatype zipper (a:t@ype) = 
| Zipper (a) of (tree a, list (move a))

fun {a:t@ype} make_zipper (tree a): zipper a
fun {a:t@ype} peek (zipper a, () -> a): a
fun {a:t@ype} move_left (zipper a): zipper a
fun {a:t@ype} move_right (zipper a): zipper a
fun {a:t@ype} move_up (zipper a): zipper a
fun {a:t@ype} move_to_top (zipper a): zipper a
fun {a:t@ype} update (zipper a, a): zipper a
fun {a:t@ype} test_zipper (): void