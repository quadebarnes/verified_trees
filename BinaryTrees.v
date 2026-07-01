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