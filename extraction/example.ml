let time l =
  let t = Sys.time() in
  let v = Lazy.force l in
  Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
  flush stdout;
  v

let measure_size x = (Marshal.to_bytes x [] |> Bytes.length |> float_of_int) /. 1024.0 /. 1024.0

module Example = functor (Dl : Digital_list.DIGITAL_LIST) -> struct
  open Dl

  let main =
    time (lazy (
      let r = 32 in
      let cdl = concrete_digital_list_empty r |> ref in
      for _ = 0 to 10000000 do
        cdl := !cdl |> concrete_digital_list_push r 0
      done;
      for i = 0 to (!cdl |> concrete_digital_list_length r) - 1 do
        cdl := !cdl |> concrete_digital_list_update r i (i mod 123) |> Option.get
      done;
      let a = Array.make (!cdl |> concrete_digital_list_length r) 0 in
      for i = 0 to (!cdl |> concrete_digital_list_length r) - 1 do
        a.(i) <- !cdl |> concrete_digital_list_nth r i |> Option.get
      done;
      Printf.printf "Raw data size (after serialization): %f MiB\n" (a |> measure_size);
      Printf.printf "Data structure size (after serialization): %f MiB\n" (cdl |> measure_size)
    ))
end

let _ = Printf.printf "Dependent version:\n"

module Example_dep = Example(Digital_list.Dep)

let _ = Printf.printf "Non-dependent version:\n"

module Example_non_dep = Example(Digital_list.Non_dep)
