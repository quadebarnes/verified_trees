Require Import PeanoNat.
Require Import List.
Import ListNotations.

Inductive tree : Type :=
  node (label : nat) (branches : list tree).

Fixpoint rm (t : tree) (target : nat) : option tree :=
  match t with
  | node label branches => if label =? target 
                             then None 
                             else Some (node label ((fix rm_list (l : list tree) (val : nat) : list tree :=
                                                    match l with
                                                    | nil => nil
                                                    | h::t => match rm h target with
                                                              | None => rm_list t val
                                                              | Some tree => tree::(rm_list t val)
                                                               end
                                                        end) branches target))
  end.

Example test_rm1: rm (node 1 [(node 3 nil);(node 7 nil);(node 9 nil)]) 3 
  = Some (node 1 [(node 7 nil);(node 9 nil)]).
Proof. reflexivity. Qed.

Fixpoint find (t : tree) (target : nat) : option tree := 
  match t with
  | node label branches => if label =? target 
                             then Some t 
                             else (fix find_list (l : list tree) (val : nat) : option tree :=
                                     match l with
                                     | nil => None
                                     | h::t => match find h val with 
                                               | None => find_list t val
                                               | tree => tree
                                               end 
                                      end) branches target
  end.

Example test_find1: find (node 1 [(node 3 [(node 14 nil)]);(node 7 nil);(node 9 nil)]) 3 
  = Some (node 3 [(node 14 nil)]).
Proof. reflexivity. Qed.

Fixpoint insert (t : tree) (newTree : tree) : tree :=
  match t with
  | node label branches => match branches with
                           | nil => node label [newTree]
                           | h::t => node label ((insert h newTree)::t)
                           end
  end.

Example test_insert1: insert (node 1 [(node 3 [(node 14 nil)]);(node 7 nil);(node 9 nil)]) (node 27 nil) 
  = (node 1 [(node 3 [(node 14 [(node 27 nil)])]);(node 7 nil);(node 9 nil)]).
Proof. reflexivity. Qed.

Fixpoint map_tree (t : tree) (f : nat -> nat) : tree :=
  match t with
  | node label branches => node (f label) ((fix map_list (l : list tree) (func : nat -> nat) : list tree :=
                                            match l with
                                            | nil => nil
                                            | h::t => (map_tree h func)::(map_list t func)
                                            end) branches f)
  end.

Definition double (n : nat) : nat := 
  n + n.

Example test_map_tree: map_tree (node 1 [(node 3 [(node 14 nil)]);(node 7 nil);(node 9 nil)]) double 
  = (node 2 [(node 6 [(node 28 nil)]);(node 14 nil);(node 18 nil)]).
Proof. reflexivity. Qed.