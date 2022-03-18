Load DigitalList.

Section Example.

Definition sample :=
  let n := 3 in
    let cdl0 := (
      concrete_digital_list_push n 5
      (concrete_digital_list_empty n)
    ) in
    (
      concrete_digital_list_nth n 0 cdl0,
      option_map
        (fun '(cdl1, x) => (concrete_digital_list_length n cdl1, concrete_digital_list_to_list n cdl1, x))
        (
          option_flat_map
            (concrete_digital_list_pop n)
            (concrete_digital_list_update n 0 7 cdl0)
        )
    ).

Compute sample.

End Example.

Extract Inductive unit => "unit" [ "()" ].

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive option => "option" [ "Some" "None" ].
Extract Inlined Constant option_map => "Option.map".

Extract Inductive prod => "(*)" [ "(,)" ].

Extract Inductive sigT => "(*)" [ "(,)" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant app => "List.append".

Extract Inductive nat => "int" [ "0" "succ" ] "(fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))".
Extract Inlined Constant pred => "pred".
Extract Inlined Constant plus => "(+)".
Extract Inlined Constant mult => "( * )".
Extract Inlined Constant Nat.div => "(/)".
Extract Inlined Constant Nat.modulo => "(mod)".
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Compare_dec.le_lt_eq_dec => "(<)".
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Inlined Constant Compare_dec.zerop => "(=) 0".

Extract Inductive array => "array" [ "(assert false)" ] "(assert false)".
Extract Constant array_length => "Array.length".
Extract Constant array_to_list => "Array.to_list".
Extract Inlined Constant array_empty => "[||]".
Extract Constant array_single => "fun x -> [|x|]".
Extract Constant array_nth => "
  fun i a ->
    try Some a.(i)
    with Invalid_argument _ -> None
".
Extract Constant array_update => "
  fun i x a ->
    let a0 = Array.copy a in
    try
      a0.(i) <- x;
      Some a0
    with Invalid_argument _ -> None
".
Extract Constant array_push => "
  fun x a ->
    let n = Array.length a in
    let a0 = Array.make (n + 1) x in
    Array.blit a 0 a0 0 n;
    a0
".
Extract Constant array_pop => "
  fun a ->
    let n = Array.length a in
    if n = 0
    then None
    else Some (Array.sub a 0 (n - 1), a.(n - 1))
".

Set Extraction File Comment "Extraction start".

Recursive Extraction sample.
