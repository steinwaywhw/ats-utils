staload "./util.sats"
staload "./list.sats"
staload "./stream.sats"
staload "./string.sats"



fun string_to_stream (string): lazy (stream char)
fun {a:t@ype} stream_to_list (lazy (stream a)): list a
