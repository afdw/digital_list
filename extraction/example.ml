let time l =
  let t = Sys.time() in
  let v = Lazy.force l in
  Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
  flush stdout;
  v

module Example = functor (Dl : Digital_list.DIGITAL_LIST) -> struct
  open Dl

  let main =
    time (lazy (
      let cdl = concrete_digital_list_empty 32 |> ref in
      for _ = 0 to 10000000 do
        cdl := !cdl |> concrete_digital_list_push 32 0
      done;
      for i = 0 to 10000000 do
        cdl := !cdl |> concrete_digital_list_update 32 i (i mod 123) |> Option.get
      done;
      let a = Array.make (!cdl |> concrete_digital_list_length 32) 0 in
      for i = 0 to 10000000 do
        a.(i) <- !cdl |> concrete_digital_list_nth 32 i |> Option.get
      done;
      Printf.printf "Raw data size (after serialization): %f MiB\n" ((Marshal.to_bytes a [] |> Bytes.length |> float_of_int) /. 1024.0 /. 1024.0);
      Printf.printf "Data structure size (after serialization): %f MiB\n" ((Marshal.to_bytes !cdl [] |> Bytes.length |> float_of_int) /. 1024.0 /. 1024.0)
    ))
end

module Example_dep = Example(Digital_list.Dep)

module Example_non_dep = Example(Digital_list.Non_dep)
