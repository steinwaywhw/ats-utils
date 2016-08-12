staload "unit.sats"

staload "./show.sats"
staload _ = "./show.dats"

implement show_any<unit> (xs) = show_any<string> "unit"