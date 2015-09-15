#define ATS_DYNLOADFLAG 0
		
staload "./map.sats"
staload "./avl.sats"
staload "./maybe.sats"

staload _ = "./avl.dats"
staload _ = "./maybe.dats"

assume map (k, v) = avltree (k, v)

implement {k} {v} map_insert (map, key, value, cmp) = avltree_insert (map, key, value, cmp)
implement {k} {v} map_member (map, key, cmp)        = avltree_member (map, key, cmp)
implement {k} {v} map_lookup (map, key, cmp)        = avltree_lookup (map, key, cmp)
implement {k} {v} map_update (map, key, value, cmp) = avltree_replace (map, key, value, cmp)
implement {k} {v} map_delete (map, key, cmp)        = avltree_delete (map, key, cmp)
implement map_empty {k} {v} (map): bool             = avltree_empty map
implement map_size  {k} {v} (map): size_t           = avltree_size map