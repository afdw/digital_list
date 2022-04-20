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

Inductive concrete_digital_list {A} : Type :=
  | ConcreteDigitalList : forall (d : nat), digital_list A -> concrete_digital_list.

Arguments concrete_digital_list : clear implicits.

Fixpoint digital_list_to_list {A} (d : nat) (dl : digital_list A) :=
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
  match d with
  | 0 =>
    match blt with
    | BinaryLeafTreeLeaf x => Some x
    | BinaryLeafTreeInternalNode _ _ => None
    end
  | S d' =>
    match il with
    | [] => None
    | i :: il' =>
      match blt with
      | BinaryLeafTreeLeaf _ => None
      | BinaryLeafTreeInternalNode blt'1 blt'2 =>
        match i with
        | 0 => complete_binary_leaf_tree_nth d' il' blt'1
        | 1 => complete_binary_leaf_tree_nth d' il' blt'2
        | _ => None
        end
      end
    end
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
  match d with
  | 0 =>
    Some (BinaryLeafTreeLeaf x)
  | S d' =>
    match il with
    | [] => None
    | i :: il' =>
      match blt with
      | BinaryLeafTreeLeaf _ => None
      | BinaryLeafTreeInternalNode blt'1 blt'2 =>
        match i with
        | 0 =>
          option_map
            (fun blt'1_0 => BinaryLeafTreeInternalNode blt'1_0 blt'2)
            (complete_binary_leaf_tree_update d' il' x blt'1)
        | 1 =>
          option_map
            (fun blt'2_0 => BinaryLeafTreeInternalNode blt'1 blt'2_0)
            (complete_binary_leaf_tree_update d' il' x blt'2)
        | _ => None
        end
      end
    end
  end.

Fixpoint complete_binary_leaf_tree_pop {A} d (blt : binary_leaf_tree A) : option (digital_list A * A) :=
  match d with
  | 0 =>
    match blt with
    | BinaryLeafTreeLeaf x => Some (DigitalListNil, x)
    | BinaryLeafTreeInternalNode _ _ => None
    end
  | S d' =>
    match blt with
    | BinaryLeafTreeLeaf _ => None
    | BinaryLeafTreeInternalNode blt'1 blt'2 =>
      option_map
        (fun '(dl', x) => (DigitalListCons (Some blt'1) dl', x))
        (complete_binary_leaf_tree_pop d' blt'2)
    end
  end.

Definition digital_list_empty {A} : digital_list A := DigitalListNil.

Definition concrete_digital_list_empty {A} : concrete_digital_list A :=
  ConcreteDigitalList 0 digital_list_empty.

Fixpoint digital_list_nth_inner {A} d il (dl : digital_list A) {struct dl} : option A :=
  match dl with
  | DigitalListNil =>
    None
  | DigitalListCons o dl' =>
    match il with
    | [] => None
    | i :: il' =>
      match o with
      | None => digital_list_nth_inner (pred d) il' dl'
      | Some blt =>
        match i with
        | 0 => complete_binary_leaf_tree_nth (pred d) il' blt
        | 1 => digital_list_nth_inner (pred d) il' dl'
        | _ => None
        end
      end
    end
  end.

Definition digital_list_nth {A} d i (dl : digital_list A) : option A :=
  if Nat.ltb i (digital_list_length d dl)
  then digital_list_nth_inner d (indexes_list_of_index 2 d i) dl
  else None.

Definition concrete_digital_list_nth {A} i (cdl : concrete_digital_list A) : option A :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_nth d i dl.

Fixpoint digital_list_update_inner {A} d il x (dl : digital_list A) {struct dl} : option (digital_list A) :=
  match dl with
  | DigitalListNil =>
    None
  | DigitalListCons o dl' =>
    match il with
    | [] => None
    | i :: il' =>
      match o with
      | None =>
        option_map
          (DigitalListCons o)
          (digital_list_update_inner (pred d) il' x dl')
      | Some blt =>
        match i with
        | 0 =>
          Some (DigitalListCons (complete_binary_leaf_tree_update (pred d) il' x blt) dl')
        | 1 =>
          option_map
            (DigitalListCons o)
            (digital_list_update_inner (pred d) il' x dl')
        | _ => None
        end
      end
    end
  end.

Definition digital_list_update {A} d i x (dl : digital_list A) : option (digital_list A) :=
  if Nat.ltb i (digital_list_length d dl)
  then digital_list_update_inner d (indexes_list_of_index 2 d i) x dl
  else None.

Definition concrete_digital_list_update {A} i x (cdl : concrete_digital_list A) :
  option (concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map (ConcreteDigitalList d) (digital_list_update d i x dl).

Fixpoint digital_list_push {A} d (x : A) (dl : digital_list A) : option (binary_leaf_tree A) * (digital_list A) :=
  match dl with
  | DigitalListNil =>
    (Some (BinaryLeafTreeLeaf x), DigitalListNil)
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
      option_flat_map
        (fun blt =>
          option_map
            (fun '(dl'0, x) => (DigitalListCons None dl'0, x))
            (complete_binary_leaf_tree_pop (pred d) blt)
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
