#define ATS_DYNLOADFLAG 0
staload "unit.sats"

staload "./show.sats"
staload _ = "./show.dats"

implement show_any<unit> (xs) = gprint_val<string> "unit"