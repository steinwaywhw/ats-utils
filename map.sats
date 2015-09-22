staload "./maybe.sats"
#define ATS_DYNLOADFLAG 0
	
abstype map (k:t@ype, v:t@ype) = ptr

fun {k:t@ype} {v:t@ype} map_insert (map (k, v), k, v, (k, k) -> int) : map (k, v)
fun {k:t@ype} {v:t@ype} map_member (map (k, v), k, (k, k) -> int)    : bool
fun {k:t@ype} {v:t@ype} map_lookup (map (k, v), k, (k, k) -> int)    : maybe (v)
fun {k:t@ype} {v:t@ype} map_update (map (k, v), k, v, (k, k) -> int) : map (k, v)
fun {k:t@ype} {v:t@ype} map_delete (map (k, v), k, (k, k) -> int)    : map (k, v)
fun map_empty {k:t@ype} {v:t@ype} (map (k, v)): bool
fun map_size  {k:t@ype} {v:t@ype} (map (k, v)): size_t