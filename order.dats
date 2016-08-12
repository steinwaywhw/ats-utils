#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "symintr.sats"
staload "order.sats"

implement {a} order_compare (x, y) = gcompare_val_val<a> (x, y)

implement {a} order_eq (x, y) = order_compare<a> (x, y) = 0           
implement {a} order_neq (x, y) = order_compare<a> (x, y) != 0           
implement {a} order_gt (x, y) = order_compare<a> (x, y) > 0          
implement {a} order_lt (x, y) = order_compare<a> (x, y) < 0           
implement {a} order_gte (x, y) = order_compare<a> (x, y) >= 0           
implement {a} order_lte (x, y) = order_compare<a> (x, y) <= 0          

implement {a} order_min (x, y) = if x \order_lte<a> y then x else y 
implement {a} order_max (x, y) = if x \order_gte<a> y then x else y