let stream_mapi f stream =
  let next i =
    try Some (f i (Stream.next stream))
    with Stream.Failure -> None in
  Stream.from next

exception PredictionsEnd
exception DepthEnd
