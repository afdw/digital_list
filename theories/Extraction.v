Load DigitalList.

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

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive sigT => "(*)"  [ "(,)" ].
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

Extract Inductive sized_list =>
  "array"
  [
    "[||]"
    "(
      fun (n, x, sl) ->
        let sl0 = Array.make (n + 1) x in
        Array.blit sl 0 sl0 1 n;
        sl0
    )"
  ]
  "(
    fun f_SizedListNil f_SizedListCons sl ->
      try
        let sl' = Array.sub sl 1 (Array.length sl - 1) in
        f_SizedListCons (Array.length sl - 1) sl.(0) sl'
      with Invalid_argument _ -> f_SizedListNil ()
  )".
Extraction Implicit sized_list_to_list [ n ].
Extract Inlined Constant sized_list_to_list => "Array.to_list".
Extract Constant sized_list_of_list => "
  fun n default l ->
    let sl = Array.make n default in
    Array.blit (Array.of_list l) 0 sl 0 (min n (List.length l));
    sl
".
Extract Constant sized_list_rev => "fun n l -> Array.init n (fun i -> l.(n - i - 1))".
Extract Constant sized_list_push => "
  fun n x sl ->
    let sl0 = Array.make (n + 1) x in
    Array.blit sl 0 sl0 0 n;
    sl0
".
Extract Constant sized_list_pop => "fun n sl -> (Array.sub sl 0 n, sl.(n))".
Extraction Implicit sized_list_nth [ n ].
Extract Constant sized_list_nth => "
  fun i sl ->
    try Some sl.(i)
    with Invalid_argument _ -> None
".
Extraction Implicit sized_list_update [ n ].
Extract Constant sized_list_update => "
  fun i x sl ->
    let sl0 = Array.copy sl in
    try
      sl0.(i) <- x;
      Some sl0
    with Invalid_argument _ -> None
".

Set Extraction File Comment "Extraction start".

Recursive Extraction sample.
