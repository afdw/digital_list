Load "Dep/DigitalList".

Section Example.

Definition sample :=
  let n := 3 in
    let cdl0 := (
      concrete_digital_list_push 5
      (concrete_digital_list_empty : concrete_digital_list nat n)
    ) in
    (
      concrete_digital_list_nth 0 cdl0,
      option_map
        (fun '(cdl1, x) => (concrete_digital_list_length cdl1, concrete_digital_list_to_list cdl1, x))
        (
          option_flat_map
            concrete_digital_list_pop
            (concrete_digital_list_update 0 7 cdl0)
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
Extract Constant array_to_list => "fun _ a -> Array.to_list a".
Extract Inlined Constant array_empty => "[||]".
Extract Constant array_single => "fun x -> [|x|]".
Extract Constant array_nth => "
  fun _ i a ->
    try Some a.(i)
    with Invalid_argument _ -> None
".
Extract Constant array_update => "
  fun _ i x a ->
    let a0 = Array.copy a in
    try
      a0.(i) <- x;
      Some a0
    with Invalid_argument _ -> None
".
Extract Constant array_push => "
  fun n x a ->
    let a0 = Array.make (n + 1) x in
    Array.blit a 0 a0 0 n;
    a0
".
Extract Constant array_pop => "fun n a -> (Array.sub a 0 n, a.(n))".

Set Extraction File Comment "Extraction start".

Recursive Extraction sample.
