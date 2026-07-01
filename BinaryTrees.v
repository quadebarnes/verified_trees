Require Import PeanoNat.
Require Import List.

Scheme All for list.

Inductive tree : Type :=
  node (label : nat) (branches : list tree).



Fixpoint rm (t : tree) (target : nat) : option tree :=
  match t with
  | node label branches => if label =? target 
                             then None 
                             else Some (node label (rm_list branches target))
  end
with rm_list (l : list tree) (target : nat) : list tree :=
  match l with
  | nil => nil
  | h::t => match rm h target with
            | None => rm_list t target
            | Some tree => tree::(rm_list t target)
            end
  end.