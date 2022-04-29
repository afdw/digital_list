Load "NonDep/Indexes".

Inductive binary_leaf_tree {A} :=
  | BinaryLeafTreeLeaf : A -> binary_leaf_tree
  | BinaryLeafTreeInternalNode : binary_leaf_tree -> binary_leaf_tree -> binary_leaf_tree.

Arguments binary_leaf_tree : clear implicits.

Fixpoint binary_leaf_tree_to_list {A} (blt : binary_leaf_tree A) :=
  match blt with
  | BinaryLeafTreeLeaf x => [x]
  | BinaryLeafTreeInternalNode blt'1 blt'2 => binary_leaf_tree_to_list blt'1 ++ binary_leaf_tree_to_list blt'2
  end.

Inductive digital_list {A} :=
  | DigitalListNil : digital_list
  | DigitalListCons : option (binary_leaf_tree A) -> digital_list -> digital_list.

Arguments digital_list : clear implicits.

Inductive concrete_digital_list {A} :=
  | ConcreteDigitalList : forall (d : nat), digital_list A -> concrete_digital_list.

Arguments concrete_digital_list : clear implicits.

Fixpoint digital_list_to_list {A} d (dl : digital_list A) :=
  match dl with
  | DigitalListNil => []
  | DigitalListCons o dl' =>
    match o with
    | None => []
    | Some blt => binary_leaf_tree_to_list blt
    end ++ digital_list_to_list (pred d) dl'
  end.

Definition concrete_digital_list_to_list {A} (cdl : concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_to_list d dl.

Fixpoint digital_list_length {A} d (dl : digital_list A) :=
  match dl with
  | DigitalListNil => 0
  | DigitalListCons o dl' => (if o then Nat.pow 2 (pred d) else 0) + digital_list_length (pred d) dl'
  end.

Definition concrete_digital_list_length {A} (cdl : concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_length d dl.

Fixpoint complete_binary_leaf_tree_nth {A} d il (blt : binary_leaf_tree A) : option A :=
  match il, blt with
  | [], BinaryLeafTreeLeaf x => Some x
  | 0 :: il', BinaryLeafTreeInternalNode blt'1 _ => complete_binary_leaf_tree_nth (pred d) il' blt'1
  | 1 :: il', BinaryLeafTreeInternalNode _ blt'2 => complete_binary_leaf_tree_nth (pred d) il' blt'2
  | _, _ => None
  end.

Section Example.

Compute
  complete_binary_leaf_tree_nth
    3
    [1; 1; 0]
    (
      BinaryLeafTreeInternalNode
        (BinaryLeafTreeInternalNode
          (BinaryLeafTreeInternalNode
            (BinaryLeafTreeLeaf 0)
            (BinaryLeafTreeLeaf 1))
          (BinaryLeafTreeInternalNode
            (BinaryLeafTreeLeaf 2)
            (BinaryLeafTreeLeaf 3)))
        (BinaryLeafTreeInternalNode
          (BinaryLeafTreeInternalNode
            (BinaryLeafTreeLeaf 4)
            (BinaryLeafTreeLeaf 5))
          (BinaryLeafTreeInternalNode
            (BinaryLeafTreeLeaf 6)
            (BinaryLeafTreeLeaf 7)))
    ).

End Example.

Fixpoint complete_binary_leaf_tree_update {A} d il x (blt : binary_leaf_tree A) : option (binary_leaf_tree A) :=
  match il, blt with
  | [], _ => Some (BinaryLeafTreeLeaf x)
  | 0 :: il', BinaryLeafTreeInternalNode blt'1 blt'2 =>
    option_map
      (fun blt'1_0 => BinaryLeafTreeInternalNode blt'1_0 blt'2)
      (complete_binary_leaf_tree_update (pred d) il' x blt'1)
  | 1 :: il', BinaryLeafTreeInternalNode blt'1 blt'2 =>
    option_map
      (fun blt'2_0 => BinaryLeafTreeInternalNode blt'1 blt'2_0)
      (complete_binary_leaf_tree_update (pred d) il' x blt'2)
  | _, _ => None
  end.

Fixpoint complete_binary_leaf_tree_pop {A} d (blt : binary_leaf_tree A) : digital_list A * A :=
  match blt with
  | BinaryLeafTreeLeaf x => (DigitalListNil, x)
  | BinaryLeafTreeInternalNode blt'1 blt'2 =>
    let '(dl', x) := complete_binary_leaf_tree_pop (pred d) blt'2 in
      (DigitalListCons (Some blt'1) dl', x)
  end.

Definition digital_list_empty {A} : digital_list A := DigitalListNil.

Definition concrete_digital_list_empty {A} : concrete_digital_list A :=
  ConcreteDigitalList 0 digital_list_empty.

Fixpoint digital_list_nth_inner {A} d il (dl : digital_list A) : option A :=
  match il, dl with
  | 0 :: il', DigitalListCons None dl'
  | 1 :: il', DigitalListCons (Some _) dl' => digital_list_nth_inner (pred d) il' dl'
  | 0 :: il', DigitalListCons (Some blt) dl' => complete_binary_leaf_tree_nth (pred d) il' blt
  | _, _ => None
  end.

Definition digital_list_nth {A} d i (dl : digital_list A) : option A :=
  if Nat.ltb i (digital_list_length d dl)
  then digital_list_nth_inner d (indexes_list_of_index 2 d i) dl
  else None.

Definition concrete_digital_list_nth {A} i (cdl : concrete_digital_list A) : option A :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_nth d i dl.

Fixpoint digital_list_update_inner {A} d il x (dl : digital_list A) :
  option (digital_list A) :=
  match il, dl with
  | 0 :: il', DigitalListCons (None as o) dl'
  | 1 :: il', DigitalListCons (Some _ as o) dl' =>
    option_map
      (DigitalListCons o)
      (digital_list_update_inner (pred d) il' x dl')
  | 0 :: il', DigitalListCons (Some blt) dl' =>
    Some (DigitalListCons (complete_binary_leaf_tree_update (pred d) il' x blt) dl')
  | _, _ => None
  end.

Definition digital_list_update {A} d i x (dl : digital_list A) : option (digital_list A) :=
  if Nat.ltb i (digital_list_length d dl)
  then digital_list_update_inner d (indexes_list_of_index 2 d i) x dl
  else None.

Definition concrete_digital_list_update {A} i x (cdl : concrete_digital_list A) :
  option (concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map (ConcreteDigitalList d) (digital_list_update d i x dl).

Fixpoint digital_list_push {A} d x (dl : digital_list A) : option (binary_leaf_tree A) * (digital_list A) :=
  match dl with
  | DigitalListNil => (Some (BinaryLeafTreeLeaf x), DigitalListNil)
  | DigitalListCons o dl' =>
    match digital_list_push (pred d) x dl' with
    | (None, dl'0) => (None, DigitalListCons o dl'0)
    | (Some blt0, dl'0) =>
      match o with
      | None => (None, DigitalListCons (Some blt0) dl'0)
      | Some blt => (Some (BinaryLeafTreeInternalNode blt blt0), DigitalListCons None dl'0)
      end
    end
  end.

Definition concrete_digital_list_push {A} x (cdl : concrete_digital_list A) : concrete_digital_list A :=
  let '(ConcreteDigitalList d dl) := cdl in
    match digital_list_push d x dl with
    | (None, dl0) => ConcreteDigitalList d dl0
    | (Some blt0, dl0) => ConcreteDigitalList (S d) (DigitalListCons (Some blt0) dl0)
    end.

Fixpoint digital_list_pop {A} d (dl : digital_list A) : option (digital_list A * A) :=
  match dl with
  | DigitalListNil => None
  | DigitalListCons o dl' =>
    match digital_list_pop (pred d) dl' with
    | None =>
      option_map
        (fun blt =>
          let '(dl'0, x) := complete_binary_leaf_tree_pop (pred d) blt in
            (DigitalListCons None dl'0, x)
        )
        o
    | Some (dl'0, x) => Some (DigitalListCons o dl'0, x)
    end
  end.

Definition concrete_digital_list_pop {A} (cdl : concrete_digital_list A) :
  option (concrete_digital_list A * A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map
      (fun '(dl0, x) => (ConcreteDigitalList d dl0, x))
      (digital_list_pop d dl).
