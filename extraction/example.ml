open Digital_list

let main =
  let cdl = concrete_digital_list_empty 32 |> ref in
  for i = 0 to 10000000 do
    cdl := !cdl |> concrete_digital_list_push 32 i
  done;
  for i = 0 to 10000000 do
    cdl := !cdl |> concrete_digital_list_update 32 i 0 |> Option.get
  done;
  for i = 0 to 10000000 do
    ignore (!cdl |> concrete_digital_list_nth 32 i)
  done
