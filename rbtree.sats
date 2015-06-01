staload "./list.sats"



abstype rbtree (a:t@ype) = ptr

//fun {a:t@ype} empty (): rbtree a
fun {a:t@ype} member (rbtree a, a, (a, a) -> int): bool
fun {a:t@ype} elements (rbtree a): list a
fun {a:t@ype} insert (rbtree a, a, (a, a) -> int): rbtree a
fun {a:t@ype} delete (rbtree a, a, (a, a) -> int): rbtree a