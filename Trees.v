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

Fixpoint fold (t : tree) (f : nat -> nat -> nat) (seed : nat) :=
  match t with 
  | node label branches => f label ((fix fold_list (l : list tree) (func : nat -> nat -> nat) (sd : nat) :=
                                           match l with
                                           | nil => sd
                                           | h::t => f (fold h f sd) (fold_list t f sd)
                                           end) branches f seed)
  end.

Example test_fold1: fold (node 1 [(node 3 [(node 14 nil)]);(node 7 nil);(node 9 nil)]) (fun a b => a + b) 0 
  = 34.
Proof. reflexivity. Qed.

Fixpoint size (t : tree) : nat :=
  match t with
  | node _ branches => S ((fix size_list (l : list tree) :=
                             match l with
                             | nil => O
                             | h::t => (size h) + (size_list t)
                             end) branches)
  end.

Example test_size: size (node 1 [(node 3 [(node 14 nil)]);(node 7 nil);(node 9 nil)])
  = 5.
Proof. reflexivity. Qed.

Fixpoint tree_ind' (P : tree -> Prop)
  (H : forall l br, Forall P br -> P (node l br))
  (t : tree) : P t := 
  match t with
  | node l br => H l br ((fix children (bs : list tree) : Forall P bs := 
                    match bs with
                    | [] => Forall_nil P
                    | h::t => Forall_cons h (tree_ind' P H h) (children t)
                    end) br)
  end.

Lemma double_plus_one: forall (n : nat), 
  double (S n) = S (S (double n)).
Proof. 
  intros n. induction n as [| n' IHn'].
  + unfold double. simpl. reflexivity.
  + rewrite IHn'. unfold double. 
    rewrite Nat.add_succ_r. rewrite Nat.add_succ_r. 
    rewrite Nat.add_succ_l. rewrite Nat.add_succ_l. 
    reflexivity.
Qed. 

Lemma double_distr: forall (n m : nat), double (n + m) 
  = double n + double m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - intros m. rewrite double_plus_one. simpl. rewrite <- IHn'.
    rewrite double_plus_one. 
    reflexivity.
Qed.

Theorem double_sum: forall (t : tree), 
  double (fold t plus 0) = fold (map_tree t double) plus 0.
Proof. 
  intros t. induction t using tree_ind'. induction H as [| head rest Hhead Htail Ih].
  - simpl. rewrite Nat.add_0_r. rewrite Nat.add_0_r. reflexivity.
  - simpl in *. rewrite Nat.add_shuffle3. 
    rewrite double_distr. rewrite double_distr.
    rewrite double_distr in Ih. rewrite Ih. rewrite Nat.add_shuffle3. 
    rewrite Hhead.
    reflexivity.
Qed.

Theorem map_double: forall (t : tree), 
  size (map_tree t double) = size t.
Proof.
  intros t. induction t using tree_ind'. induction H as [| head rest Hhead Htail Ih].
  - simpl. reflexivity.
  - simpl in *. rewrite <- Nat.add_succ_l. rewrite Nat.add_succ_comm.
    rewrite Ih. rewrite Hhead.
    rewrite Nat.add_succ_r. 
    reflexivity. 
Qed.

Theorem map_size: forall (t : tree) (f : nat -> nat), 
  size (map_tree t f) = size t.
Proof. 
  intros t f. induction t using tree_ind'. induction H as [| head rest Hhead Htail Ih].
  - simpl. reflexivity.
  - simpl in *. rewrite <- Nat.add_succ_l. rewrite Nat.add_succ_comm.
    rewrite Ih. rewrite Hhead.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed. 