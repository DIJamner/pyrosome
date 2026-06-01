(* ============================================================================
   A LAWFUL positive-list-keyed map: the "fattened" pos_trie.

   The existing [pos_trie] (PosListMap.v) is NOT a lawful map: its [map.ok] is
   provably false because a [pos_trie_leaf] cannot also carry children, so
   inserting a longer key onto a leaf discards it.  That trie is fine for the
   e-graph QUERY tries (which are uniform-depth and feed pt_spaced_intersect),
   but the e-graph DB tables need a genuine [map.ok].

   This file defines a separate, fully-lawful map over [list positive] keys by
   adding a third constructor [fpt_both] that carries BOTH a value (for the
   key that ends here) AND a child PTree.  get/put/remove/fold then become total
   and the full coqutil [map.ok] holds UNCONDITIONALLY (no depth restriction).

   pt_spaced_intersect is NOT defined here and is not needed: the DB tables are
   never intersected.  So the scary intersection-correctness proof stays on the
   original pos_trie.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Tries Require Import Canonical.
From Utils Require Import TrieMap.

Set Implicit Arguments.

Section __.
  Context {A : Type}.

  Inductive fpt' :=
  | fpt_leaf (a : A)                              (* the empty suffix ends here *)
  | fpt_node (m : PTree.tree' fpt')               (* only longer keys, no value here *)
  | fpt_both (a : A) (m : PTree.tree' fpt').       (* value here AND longer keys *)

  (* None is the empty map *)
  Definition fpt := option fpt'.

  (* --- get ----------------------------------------------------------------- *)
  Fixpoint fpt_get' (pt : fpt') (k : list positive) {struct k} : option A :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf a => Some a
        | fpt_both a _ => Some a
        | fpt_node _ => None
        end
    | p :: k' =>
        match pt with
        | fpt_leaf _ => None
        | fpt_node m
        | fpt_both _ m =>
            match PTree.get' p m with
            | Some pt' => fpt_get' pt' k'
            | None => None
            end
        end
    end.

  Definition fpt_get (pt : fpt) (k : list positive) : option A :=
    match pt with
    | None => None
    | Some pt' => fpt_get' pt' k
    end.

  (* --- singleton ----------------------------------------------------------- *)
  Fixpoint fpt_singleton (k : list positive) (v : A) : fpt' :=
    match k with
    | [] => fpt_leaf v
    | p :: k' => fpt_node (PTree.set0 p (fpt_singleton k' v))
    end.

  (* --- put ----------------------------------------------------------------- *)
  (* helper: update child at p of a PTree m with the put of (k',v) *)
  Definition fpt_child_put (m : PTree.tree' fpt') (p : positive)
                           (k' : list positive) (v : A)
                           (rec : fpt' -> fpt') : PTree.tree' fpt' :=
    match PTree.get' p m with
    | Some c => PTree.set' p (rec c) m
    | None => PTree.set' p (fpt_singleton k' v) m
    end.

  Fixpoint fpt_put' (pt : fpt') (k : list positive) (v : A) {struct k} : fpt' :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf _ => fpt_leaf v
        | fpt_node m => fpt_both v m
        | fpt_both _ m => fpt_both v m
        end
    | p :: k' =>
        match pt with
        | fpt_leaf a =>
            (* leaf gains a child branch; keeps its own value *)
            fpt_both a (PTree.set0 p (fpt_singleton k' v))
        | fpt_node m =>
            fpt_node (fpt_child_put m p k' v (fun c => fpt_put' c k' v))
        | fpt_both a m =>
            fpt_both a (fpt_child_put m p k' v (fun c => fpt_put' c k' v))
        end
    end.

  Definition fpt_put (pt : fpt) (k : list positive) (v : A) : fpt :=
    match pt with
    | None => Some (fpt_singleton k v)
    | Some pt' => Some (fpt_put' pt' k v)
    end.

  (* --- remove -------------------------------------------------------------- *)
  (* collapse a PTree result of a child-removal back into an fpt' carrier:
     - when a [node] loses its last child, the whole subtrie is empty -> None
     - when a [both a] loses its last child, it collapses to [leaf a] *)
  Fixpoint fpt_remove' (pt : fpt') (k : list positive) {struct k} : option fpt' :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf _ => None                 (* removed the only (empty-key) value *)
        | fpt_node m => Some (fpt_node m)    (* no value here; unchanged *)
        | fpt_both _ m => Some (fpt_node m)  (* drop the value, keep children *)
        end
    | p :: k' =>
        match pt with
        | fpt_leaf a => Some (fpt_leaf a)    (* key absent; unchanged *)
        | fpt_node m =>
            match PTree.get' p m with
            | Some c =>
                match fpt_remove' c k' with
                | Some c' => Some (fpt_node (PTree.set' p c' m))
                | None =>
                    match PTree.remove' p m with
                    | PTree.Empty => None              (* node lost all children *)
                    | PTree.Nodes m' => Some (fpt_node m')
                    end
                end
            | None => Some (fpt_node m)
            end
        | fpt_both a m =>
            match PTree.get' p m with
            | Some c =>
                match fpt_remove' c k' with
                | Some c' => Some (fpt_both a (PTree.set' p c' m))
                | None =>
                    match PTree.remove' p m with
                    | PTree.Empty => Some (fpt_leaf a) (* both lost children -> leaf *)
                    | PTree.Nodes m' => Some (fpt_both a m')
                    end
                end
            | None => Some (fpt_both a m)
            end
        end
    end.

  Definition fpt_remove (pt : fpt) (k : list positive) : fpt :=
    match pt with
    | None => None
    | Some pt' => fpt_remove' pt' k
    end.

  (* --- fold ---------------------------------------------------------------- *)
  Fixpoint fpt_fold' {R} (f : R -> list positive -> A -> R) (acc : R)
                     (pt : fpt') (stack : list positive) {struct pt} : R :=
    match pt with
    | fpt_leaf a => f acc (rev stack) a
    | fpt_node m =>
        TrieMap.trie_fold' (fun acc p c => fpt_fold' f acc c (p :: stack)) acc m 1
    | fpt_both a m =>
        let acc' := f acc (rev stack) a in
        TrieMap.trie_fold' (fun acc p c => fpt_fold' f acc c (p :: stack)) acc' m 1
    end.

  Definition fpt_fold {R} (f : R -> list positive -> A -> R) (acc : R) (pt : fpt) : R :=
    match pt with
    | None => acc
    | Some pt' => fpt_fold' f acc pt' []
    end.

  #[export] Instance full_pos_trie_map : map.map (list positive) A :=
    {
      rep := fpt;
      get := fpt_get;
      empty := None;
      put := fpt_put;
      remove := fpt_remove;
      fold _ := fpt_fold;
    }.

End __.

Arguments fpt' : clear implicits.
Arguments fpt : clear implicits.
