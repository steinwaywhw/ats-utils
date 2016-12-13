
datasort BagElt = (* *)
sortdef elt = BagElt

stacst mk_elt: int -> elt 
stadef mk = mk_elt

stacst eq_elt_elt: (elt, elt) -> bool
stadef == = eq_elt_elt
stadef neq_elt_elt (a:elt, b:elt) = ~(a==b)
stadef != = neq_elt_elt

praxi lemma_elt_eq {e:elt} (): [e == e] unit_p
praxi lemma_elt_fun {i,j:int|i == j} (): [mk(i) == mk(j)] unit_p
praxi lemma_elt_unique {i,j:int|i != j} (): [mk(i) != mk(j)] unit_p

datasort Bag = (* *)
sortdef bag = Bag 

stacst bag_emp: () -> bag
stacst bag_add: (bag, elt) -> bag
stacst bag_del: (bag, elt) -> bag
stacst bag_cap: (bag, bag) -> bag 
stacst bag_cup: (bag, bag) -> bag
stacst bag_dif: (bag, bag) -> bag
stacst bag_jon: (bag, bag) -> bag
stacst bag_mem: (bag, elt) -> bool
stacst bag_sub: (bag, bag) -> bool
stacst bag_eq: (bag, bag) -> bool
stacst bag_car: (bag, elt) -> int

stadef nil = bag_emp
stadef add (e:elt, s:bag) = bag_add (s, e)
stadef del = bag_del 
stadef + = bag_cup
stadef - = bag_dif
stadef * = bag_cap
stadef join = bag_jon
stadef mem = bag_mem
stadef sub = bag_sub
stadef == = bag_eq
stadef neq (a:bag, b:bag) = ~(a==b)
stadef != = neq
stadef car = bag_car

praxi lemma_car_nat {g:bag} {i:elt} (): [car (g, i) >= 0] unit_p

abstype imset (bag) = ptr 

//stacst mk_elt_a: t@ype -> elt 
//stadef mk = mk_elt_a

fun imset_empty (): imset (nil)
fun imset_add {g:bag} {i:int} (imset g, int i): imset (bag_add(g, mk i))
fun imset_del {g:bag} {i:int} (imset g, int i): imset (bag_del(g, mk i))
fun imset_union {g1,g2:bag} (imset g1, imset g2): imset (g1 + g2)
fun imset_intersect {g1,g2:bag} (imset g1, imset g2): imset (g1 * g2)
fun imset_diff {g1,g2:bag} (imset g1, imset g2): imset (g1 - g2)
fun imset_join {g1,g2:bag} (imset g1, imset g2): imset (g1 \join g2)
fun imset_member {g:bag} {i:int} (imset g, int i): bool (mem(g, mk i))
fun imset_subset {g1,g2:bag} (imset g1, imset g2): bool (sub(g1, g2))
fun imset_eq {g1,g2:bag} (imset g1, imset g2): bool (g1 == g2)
fun imset_neq {g1,g2:bag} (imset g1, imset g2): bool (g1 != g2)
fun imset_cardinality {g:bag} {i:int} (imset g, int i): int (car(g, mk i))
