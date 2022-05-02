open Digital_list.Dep

let time l =
  let t = Sys.time() in
  Lazy.force l;
  let r = Sys.time() -. t in
  r

let measure r =
  time
    (lazy (
      let cdl = concrete_digital_list_empty r |> ref in
      for _ = 0 to 1000000 do
        cdl := !cdl |> concrete_digital_list_push r 0
      done;
      for i = 0 to (!cdl |> concrete_digital_list_length r) - 1 do
        cdl := !cdl |> concrete_digital_list_update r i (i mod 123) |> Option.get
      done;
      let a = Array.make (!cdl |> concrete_digital_list_length r) 0 in
      for i = 0 to (!cdl |> concrete_digital_list_length r) - 1 do
        a.(i) <- !cdl |> concrete_digital_list_nth r i |> Option.get
      done
    ))

let main =
  for r = 2 to 32 do
    measure r |> ignore
  done;
  for r = 2 to 256 do
    Printf.printf "%d, %f\n" r (measure r);
    flush stdout
  done
