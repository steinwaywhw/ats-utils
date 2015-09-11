staload "./maybe.sats"



abstype avltree (key:t@ype, value:t@ype) = ptr 

fun {key:t@ype} {value:t@ype} avltree_insert  (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)
fun {key:t@ype} {value:t@ype} avltree_replace (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)
fun {key:t@ype} {value:t@ype} avltree_delete  (avltree (key, value), key, cmp: (key, key) -> int): avltree (key, value)
fun {key:t@ype} {value:t@ype} avltree_lookup  (avltree (key, value), key, cmp: (key, key) -> int): maybe value
fun {key:t@ype} {value:t@ype} avltree_insert_or_replace (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)
fun {key:t@ype} {value:t@ype} avltree_member  (avltree (key, value), key, cmp: (key, key) -> int): bool

fun avltree_empty  {key:t@ype} {value:t@ype} (avltree (key, value)): bool
fun avltree_size   {key:t@ype} {value:t@ype} (avltree (key, value)): size_t
fun avltree_height {key:t@ype} {value:t@ype} (avltree (key, value)): int

fun {key:t@ype} {value:t@ype} avltree_show (avltree (key, value), show_key: key -> void, show_value: value -> void): void 


