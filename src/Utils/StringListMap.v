Require Import NArith Tries.Canonical Lists.List Sorting.Permutation.
Require Ascii.
Import ListNotations.

From coqutil Require Import Map.Interface.

From Utils Require Import Utils Monad ExtraMaps TrieMap.
From Utils Require PosListMap.
Import Monad.StateMonad.

From Pyrosome.Tools Require Import PosRenaming.

Import Ascii.
Import Strings.String.

Fixpoint blist_succ (l : list bool) : list bool :=
  match l with
  | [] => [true]
  | x::l' =>
      if x then false::(blist_succ l')
      else true::l'
  end.

Definition ascii_of_bit_list l :=
  match l with
  | [x; x0; x1; x2; x3; x4; x5; x6] =>
      Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6
  | _ => Ascii.zero
  end.

(* None denotes a carry *)
Definition ascii_succ a : Ascii.ascii :=
  Eval vm_compute in
    match a with
    | Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6 =>
        (*Note: will roll over at 255*)
        ascii_of_bit_list (blist_succ [x; x0; x1; x2; x3; x4; x5; x6])
    end.

Require Import Ascii.

Goal ascii_succ "0"%char = "1"%char.
Proof. compute. reflexivity. Abort.

Fixpoint string_num_succ s : string :=
  match s with
  | "" => "0"
  | String a s' =>
      if andb (Ascii.ltb a "9"%char) (Ascii.ltb "/"%char a)
      then String (ascii_succ a) s'
      else String "0"%char (string_num_succ s')
  end.

Definition string_succ s : string :=
  match index 0 "#" s with
  | None => s ++"#"
  | Some n =>
      let pre := substring 0 n s in
      let post := substring (S n) (length s) s in
      pre++"#" ++(string_num_succ post)
  end.

Goal string_num_succ "8" = "9".
Proof. compute. reflexivity. Abort.


Goal string_succ "v#8" = "v#9".
Proof. compute. reflexivity. Abort.


Goal string_succ "vZ#" = "vZ#0".
Proof. compute. reflexivity. Abort.

Goal string_succ "v/" = "v/#".
Proof. compute. reflexivity. Abort.

Goal string_succ "v#9" = "v#00".
Proof. compute. reflexivity. Abort.

Goal string_succ "v#90" = "v#01".
Proof. compute. reflexivity. Abort.


Definition sort_of := "@sort_of".

Fixpoint stp s : positive :=
  match s with
  | "" => xH
  | String a s' =>
      let p' := Zpower.shift_nat 8 (stp s') in
      match Ascii.N_of_ascii a with
      | N0 => p'
      | Npos p => p + p'
      end
  end.

Fixpoint positive_to_bit_list p :=
  match p with
  | xH => []
  | xO p' => false::(positive_to_bit_list p')
  | xI p' => true::(positive_to_bit_list p')
  end.

Fixpoint bit_list_to_string bl : string :=
  match bl with
  | [] => ""
  | x:: x0:: x1:: x2:: x3:: x4:: x5:: x6:: bl' =>
      String (Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6) (bit_list_to_string bl')
  (*TODO: wrong, but won't come up *)
  | _ => "VERY_WRONG"
  end.

Definition pts p : string :=
  bit_list_to_string (positive_to_bit_list p).

Goal pts (stp "Foo123#") = "Foo123#".
Proof. reflexivity. Abort.

(*could be able to be much faster, this is just the quick version*)
Definition string_trie_map value :=
  {|
    map.rep := PTree.t value;
    map.get m k := PTree.get (stp k) m;
    map.empty := PTree.empty value;
    map.put m k v := PTree.set (stp k) v m;
    map.remove m k := PTree.remove (stp k) m;
    map.fold A f a m :=
      let f' a p v := f a (pts p) v in
      @trie_fold value A f' a m;
  |}.


(*TODO: temporary? *)
#[export] Instance string_list_trie_map A : map.map (list string) A :=
  {
    rep := PosListMap.pos_trie;
    get m k := PosListMap.pt_get m (map stp k);
    empty := None;
    put m k v:= PosListMap.pt_put m (map stp k) v;
    remove m k := PosListMap.pt_remove m (map stp k);
    fold _ f acc pt :=
      let f' a p v := f a (map pts p) v in
      PosListMap.pt_fold f' acc pt;
  }.

#[export] Instance string_ptree_map_plus : map_plus string_trie_map :=
  {|
    map_intersect A B C f (m1 : string_trie_map A) m2 :=
      @TrieMap.intersect A B C f m1 m2;
    ExtraMaps.map_fold_values := @map_fold_values;
    map_map :=
      fun (A B : Type) (f : A -> B) =>
        PTree.map_filter (fun x : A => Some (f x))
  |}.

Definition string_max (s1 s2 : string) :=
  match String.compare s1 s2 with
  | Gt => s1
  | _ => s2
  end.
