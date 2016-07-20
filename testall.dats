#include "share/atspre_staload.hats"

staload "./symintr.sats"

staload "./maybe.sats"
staload _ = "./maybe.dats"

staload "./list.sats"
staload _ = "./list.dats"

staload "./stream.sats"
staload _ = "./stream.dats"


implement main0 () = () where {
//	val _ = maybe_selftest ()
//	val _ = list_selftest ()
	val _ = stream_selftest ()
}