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