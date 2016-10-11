#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "symintr.sats"
staload "order.sats"

implement {a} order_compare (x, y) = gcompare_val_val<a> (x, y)

typedef nat = intGte 0
implement order_compare<nat> (x, y) = g0ofg1 x - g0ofg1 y

implement {a} order_compare_addr (x, y) = ($UNSAFE.cast{int} x) - ($UNSAFE.cast{int} y) 

implement (a:t@ype,b:t@ype) order_compare<@(a,b)> (x, y) = 
	if cmp<a> (x.0, y.0) != 0
	then cmp<a> (x.0, y.0)
	else cmp<b> (x.1, y.1)

implement (a:t@ype,b:t@ype,c:t@ype) order_compare<@(a,b,c)> (x, y) = 
	if cmp<a> (x.0, y.0) != 0
	then cmp<a> (x.0, y.0)
	else if cmp<b> (x.1, y.1) != 0
	then cmp<b> (x.1, y.1)
	else cmp<c> (x.2, y.2)

implement {a} order_eq (x, y) = order_compare<a> (x, y) = 0           
implement {a} order_neq (x, y) = order_compare<a> (x, y) != 0           
implement {a} order_gt (x, y) = order_compare<a> (x, y) > 0          
implement {a} order_lt (x, y) = order_compare<a> (x, y) < 0           
implement {a} order_gte (x, y) = order_compare<a> (x, y) >= 0           
implement {a} order_lte (x, y) = order_compare<a> (x, y) <= 0          

implement {a} order_min (x, y) = if x \order_lte<a> y then x else y 
implement {a} order_max (x, y) = if x \order_gte<a> y then x else y