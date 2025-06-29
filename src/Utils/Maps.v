Require Import Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface Map.Properties.

From Utils Require Import Base Lists NamedList Eqb.

(* TODO: move has_key here from Sep *)
Section __.
  Context (A B : Type)
    (mp : map.map A B)
    (m_ok : map.ok mp)
    (A_Eqb : Eqb A)
    (A_Eqb_ok : Eqb_ok A_Eqb).

  Lemma map_keys_in (m : mp) k
    : In k (map.keys m) -> exists v, map.get m k = Some v.
  Proof.
    unfold map.keys.
    rewrite Properties.map.fold_to_tuples_fold.
    rewrite fold_right_map_fst.
    intro.
    
    apply pair_fst_in_exists in H.
    break.
    exists x.
    eapply map.tuples_spec.
    auto.
  Qed.
  
  Lemma map_keys_in' (m : mp) k
    : In k (map.keys m) <-> if map.get m k then True else False.
  Proof.
    case_match; intuition eauto.
    {
      eapply Properties.map.in_keys; eauto.
    }
    {
      eapply map_keys_in in H;
        basic_goal_prep.
      congruence.
    }
  Qed.
  
  Lemma map_split_incl2 (a x x0 : mp)
    : map.split a x x0 ->
      incl (map.keys a) (map.keys x ++ map.keys x0).
  Proof.
    intros Hsplit i Hin.
    autorewrite with utils.
    rewrite !map_keys_in' in *.
    eapply Properties.map.get_split with (k:=i) in Hsplit; eauto.
    intuition subst.
    {
      rewrite H1, <- H0.
      case_match; eauto.
    }
    {
      rewrite H1, <- H0.
      case_match; eauto.
    }
  Qed.

  
  Lemma map_keys_empty : map.keys (map:=mp) map.empty = [].
  Proof.
    unfold map.keys.
    basic_utils_crush.
    apply map.fold_empty.
  Qed.
  Hint Rewrite map_keys_empty : utils.

End __.


Arguments map_keys_in {A B}%type_scope {mp m_ok A_Eqb A_Eqb_ok} m k _.
Arguments map_keys_in' {A B}%type_scope {mp m_ok A_Eqb A_Eqb_ok} m k.


#[export] Hint Rewrite map_keys_empty : utils.
