Inductive list A :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} x l.

Definition tl {A} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons _ l' => l'
  end.

Fixpoint app {A} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x l1' => cons x (app l1' l2)
  end.

Inductive nat :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n1 n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S n1' => S (plus n1' n2)
  end.

Fixpoint length {A} (l : list A) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

Fixpoint repeat {A} (x : A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' => cons x (repeat x n')
  end.
