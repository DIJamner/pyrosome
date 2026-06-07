(* z22: RedTy_fund — VALIDATED scripts for the leaves + esc_ty@Pi + esc_tm@Pi.
   reflect@Pi is BLOCKED on the domain-argument typing question (see
   WIP/NEXT_SESSION z22 QUESTION).  esc_ty@Pi and esc_tm@Pi were validated
   interactively against the committed file (cong family at dbf4e6c).

   Paste this after `mapp_code_cong` once reflect@Pi is resolved.  The first
   three bullets (leaves) + the Pi case's esc_ty (first `+`) and esc_tm (second
   `+`) are CLOSED end-to-end; the third `+` (reflect) is the open obligation. *)

Theorem RedTy_fund : forall G A B (r : RedTy ott G A B), Pmot G A B r.
Proof.
  apply RedTy_rect.
  - intros G A B ra rb. apply leaf_nat.
  - intros G A B ra rb. apply leaf_empty.
  - intros G A B na nb rN lN ra rb h. apply leaf_ne.
  - intros G A B rF lF lG F C F' C' hA hB DomRed CodRed IHDom IHCod.
    unfold Pmot, esc_ty, esc_tm, reflect_at.
    rewrite !(elt_sort_pi G A B rF lF lG F C F' C' hA hB DomRed CodRed).
    split;[split|].
    (* ===================== esc_ty@Pi (CLOSED) ===================== *)
    + intros S HA HB.
      pose proof ott_wf as Hwf.
      pose proof (@reds_wf string _ _ ott ott_wf ott_pa "hd" _ _ _ HA hA) as HPiAwf.
      pose proof (@reds_wf string _ _ ott ott_wf ott_pa "hd" _ _ _ HB hB) as HPiBwf.
      pose proof (Pi_rel_inv rF lF lG F C G _ HPiAwf) as (HG & HrF & HlF & HlG & HF & HC & _).
      pose proof (Pi_rel_inv rF lF lG F' C' G _ HPiBwf) as (_ & _ & _ & _ & HF' & HC' & _).
      assert (HidG : osub ott G G (oid G)).
      { unfold osub, oid. change (scon "sub" [G; G]) with (s_sub G G). unfold s_sub. ott_build. }
      destruct (IHDom G (oid G) HidG) as [[IHDom_ty _] _].
      pose proof (act_code_id_eq rF lF G F HG HrF HlF HF) as HactF.
      pose proof (act_code_id_eq rF lF G F' HG HrF HlF HF') as HactF'.
      pose proof (act_code_wf rF lF (oid G) G G F HG HG HrF HlF HidG HF) as HactFwf.
      pose proof (act_code_wf rF lF (oid G) G G F' HG HG HrF HlF HidG HF') as HactF'wf.
      pose proof (eq_term_trans (eq_term_sym HactF) (eq_term_trans (IHDom_ty _ HactFwf HactF'wf) HactF')) as HFF'.
      pose proof (osub_wknF rF lF G F HG HrF HlF HF) as HoswF.
      set (extGF := oext (oEl rF lF G F) (term_info rF lF) G) in *.
      set (wknF := owkn (oEl rF lF G F) (term_info rF lF) G) in *.
      set (hdF := ohd (oEl rF lF G F) (term_info rF lF) G) in *.
      destruct (IHDom extGF wknF HoswF) as [[IHDomW_ty _] IHDomW_rfl].
      pose proof (bound_var_typed rF lF G F F' HG HrF HlF HF DomRed HoswF) as Hhdty.
      cbn zeta in Hhdty.
      change (owkn (oEl rF lF G F) (term_info rF lF) G) with wknF in Hhdty.
      change (oext (oEl rF lF G F) (term_info rF lF) G) with extGF in Hhdty.
      change (ohd (oEl rF lF G F) (term_info rF lF) G) with hdF in Hhdty.
      assert (Hhdne : neutral ott_pa "hd" hdF) by (unfold hdF, ohd; apply neutral_hd).
      assert (HextGFwf : wf_term ott [] extGF s_env) by (unfold extGF, oext, dom_info; ott_build).
      pose proof (act_code_wf rF lF wknF G extGF F' HG HextGFwf HrF HlF HoswF HF') as HactWF'.
      change (scon "exp" [oU rF lF extGF; code_info lF; extGF])
        with (s_exp extGF (code_info lF) (oU rF lF extGF)) in HactWF'.
      pose proof (IHDomW_rfl _ HactWF' hdF hdF Hhdne Hhdne Hhdty Hhdty (eq_term_refl Hhdty)) as Hraa'.
      change (RedTy_R ott (DomRed extGF wknF HoswF) hdF hdF) with (RedTm ott (DomRed extGF wknF HoswF) hdF hdF) in Hraa'.
      destruct (IHCod extGF wknF HoswF hdF hdF Hraa') as [[IHCodW_ty _] _].
      pose proof (act_code_wf rF lF wknF G extGF F HG HextGFwf HrF HlF HoswF HF) as HactWFcode.
      change (scon "exp" [oU rF lF extGF; code_info lF; extGF])
        with (s_exp extGF (code_info lF) (oU rF lF extGF)) in HactWFcode.
      pose proof (elt_sort_eq_El_gen extGF (act_code rF lF wknF G extGF F) (act_code rF lF wknF G extGF F')
                    (DomRed extGF wknF HoswF) rF lF HextGFwf HrF HlF HactWFcode) as HbridgeF.
      pose proof (wf_term_conv Hhdty HbridgeF) as HhdAtF.
      pose proof (cod_at_wf rF lF lG wknF G extGF F C hdF HG HextGFwf HrF HlF HlG HoswF HF HC HhdAtF) as HcodatF.
      pose proof (IHDomW_ty _ HactWFcode HactWF') as HactWcodeEq.
      pose proof (El_cong rF lF extGF (act_code rF lF wknF G extGF F) (act_code rF lF wknF G extGF F')
                    HextGFwf HrF HlF HactWcodeEq) as HElhdcong.
      assert (Hsb_hd : eq_sort ott []
         (s_exp extGF (term_info rF lF) (oEl rF lF extGF (act_code rF lF wknF G extGF F)))
         (s_exp extGF (term_info rF lF) (oEl rF lF extGF (act_code rF lF wknF G extGF F')))).
      { unfold s_exp. sort_cong; cbn [Model.eq_term core_model];
          try solve [ eapply eq_term_refl; ott_build ]. exact HElhdcong. }
      pose proof (wf_term_conv HhdAtF Hsb_hd) as HhdAtF'.
      pose proof (cod_at_wf rF lF lG wknF G extGF F' C' hdF HG HextGFwf HrF HlF HlG HoswF HF' HC' HhdAtF') as HcodatF'.
      pose proof (IHCodW_ty _ HcodatF HcodatF') as HCodEsc.
      pose proof (cod_collapse_both rF lF lG G F C F' C' HG HrF HlF HlG HF HF' HFF' HC HC') as Hcc.
      cbv zeta in Hcc.
      change (owkn (oEl rF lF G F) (term_info rF lF) G) with wknF in HCodEsc.
      change (oext (oEl rF lF G F) (term_info rF lF) G) with extGF in HCodEsc.
      change (ohd (oEl rF lF G F) (term_info rF lF) G) with hdF in HCodEsc.
      pose proof (Hcc HCodEsc) as HCC'.
      exact (RedTy_Pi_sound rF lF lG G F C F' C' A B S HG HrF HlF HlG HF HF' HC HC' HFF' HCC' hA hB HA HB).
    (* ===================== esc_tm@Pi (CLOSED) ===================== *)
    + intros Sb HBwf a b Hm Ha Hb.
      pose proof ott_wf as Hwf.
      pose proof (El_Pi_member_inv rF lF lG F C G _ a Ha) as (HG & HrF & HlF & HlG & HF & HC).
      pose proof (@reds_wf string _ _ ott ott_wf ott_pa "hd" _ _ _ HBwf hB) as HPiBwf.
      pose proof (Pi_rel_inv rF lF lG F' C' G _ HPiBwf) as (_ & _ & _ & _ & HF' & HC' & _).
      (* --- shared HFF' / bound-var world / HCC' block (same as esc_ty) --- *)
      assert (HidG : osub ott G G (oid G)).
      { unfold osub, oid. change (scon "sub" [G; G]) with (s_sub G G). unfold s_sub. ott_build. }
      destruct (IHDom G (oid G) HidG) as [[IHDom_ty _] _].
      pose proof (act_code_id_eq rF lF G F HG HrF HlF HF) as HactF.
      pose proof (act_code_id_eq rF lF G F' HG HrF HlF HF') as HactF'.
      pose proof (act_code_wf rF lF (oid G) G G F HG HG HrF HlF HidG HF) as HactFwf.
      pose proof (act_code_wf rF lF (oid G) G G F' HG HG HrF HlF HidG HF') as HactF'wf.
      pose proof (eq_term_trans (eq_term_sym HactF) (eq_term_trans (IHDom_ty _ HactFwf HactF'wf) HactF')) as HFF'.
      pose proof (osub_wknF rF lF G F HG HrF HlF HF) as HoswF.
      set (extGF := oext (oEl rF lF G F) (term_info rF lF) G) in *.
      set (wknF := owkn (oEl rF lF G F) (term_info rF lF) G) in *.
      set (hdF := ohd (oEl rF lF G F) (term_info rF lF) G) in *.
      destruct (IHDom extGF wknF HoswF) as [[IHDomW_ty _] IHDomW_rfl].
      pose proof (bound_var_typed rF lF G F F' HG HrF HlF HF DomRed HoswF) as Hhdty.
      cbn zeta in Hhdty.
      change (owkn (oEl rF lF G F) (term_info rF lF) G) with wknF in Hhdty.
      change (oext (oEl rF lF G F) (term_info rF lF) G) with extGF in Hhdty.
      change (ohd (oEl rF lF G F) (term_info rF lF) G) with hdF in Hhdty.
      assert (Hhdne : neutral ott_pa "hd" hdF) by (unfold hdF, ohd; apply neutral_hd).
      assert (HextGFwf : wf_term ott [] extGF s_env) by (unfold extGF, oext, dom_info; ott_build).
      pose proof (act_code_wf rF lF wknF G extGF F' HG HextGFwf HrF HlF HoswF HF') as HactWF'.
      change (scon "exp" [oU rF lF extGF; code_info lF; extGF])
        with (s_exp extGF (code_info lF) (oU rF lF extGF)) in HactWF'.
      pose proof (IHDomW_rfl _ HactWF' hdF hdF Hhdne Hhdne Hhdty Hhdty (eq_term_refl Hhdty)) as Hraa'.
      change (RedTy_R ott (DomRed extGF wknF HoswF) hdF hdF) with (RedTm ott (DomRed extGF wknF HoswF) hdF hdF) in Hraa'.
      destruct (IHCod extGF wknF HoswF hdF hdF Hraa') as [[IHCodW_ty IHCodW_tm] _].
      pose proof (act_code_wf rF lF wknF G extGF F HG HextGFwf HrF HlF HoswF HF) as HactWFcode.
      change (scon "exp" [oU rF lF extGF; code_info lF; extGF])
        with (s_exp extGF (code_info lF) (oU rF lF extGF)) in HactWFcode.
      pose proof (elt_sort_eq_El_gen extGF (act_code rF lF wknF G extGF F) (act_code rF lF wknF G extGF F')
                    (DomRed extGF wknF HoswF) rF lF HextGFwf HrF HlF HactWFcode) as HbridgeF.
      pose proof (wf_term_conv Hhdty HbridgeF) as HhdAtF.
      pose proof (cod_at_wf rF lF lG wknF G extGF F C hdF HG HextGFwf HrF HlF HlG HoswF HF HC HhdAtF) as HcodatF.
      pose proof (IHDomW_ty _ HactWFcode HactWF') as HactWcodeEq.
      pose proof (El_cong rF lF extGF (act_code rF lF wknF G extGF F) (act_code rF lF wknF G extGF F')
                    HextGFwf HrF HlF HactWcodeEq) as HElhdcong.
      assert (Hsb_hd : eq_sort ott []
         (s_exp extGF (term_info rF lF) (oEl rF lF extGF (act_code rF lF wknF G extGF F)))
         (s_exp extGF (term_info rF lF) (oEl rF lF extGF (act_code rF lF wknF G extGF F')))).
      { unfold s_exp. sort_cong; cbn [Model.eq_term core_model];
          try solve [ eapply eq_term_refl; ott_build ]. exact HElhdcong. }
      pose proof (wf_term_conv HhdAtF Hsb_hd) as HhdAtF'.
      pose proof (cod_at_wf rF lF lG wknF G extGF F' C' hdF HG HextGFwf HrF HlF HlG HoswF HF' HC' HhdAtF') as HcodatF'.
      pose proof (IHCodW_ty _ HcodatF HcodatF') as HCodEsc.
      pose proof (cod_collapse_both rF lF lG G F C F' C' HG HrF HlF HlG HF HF' HFF' HC HC') as Hcc.
      cbv zeta in Hcc.
      change (owkn (oEl rF lF G F) (term_info rF lF) G) with wknF in HCodEsc.
      change (oext (oEl rF lF G F) (term_info rF lF) G) with extGF in HCodEsc.
      change (ohd (oEl rF lF G F) (term_info rF lF) G) with hdF in HCodEsc.
      pose proof (Hcc HCodEsc) as HCC'.
      (* --- the member work --- *)
      unfold RedTy_R, RedTy_pi, projT1 in Hm. cbn [projT1] in Hm.
      destruct Hm as [Happ].
      pose proof (Happ extGF wknF HoswF hdF hdF Hraa') as Hbodymem.
      cbn beta in Hbodymem.
      pose proof (mapp_wf rF lF lG wknF G extGF F C a hdF HG HextGFwf HrF HlF HlG HoswF HF HC Ha HhdAtF) as HmappA.
      assert (Horel : wf_term ott [] orel (scon "relevance" [])).
      { unfold orel. eapply Elab.wf_term_by';
          [ apply named_list_lookup_err_in; compute; reflexivity
          | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
      pose proof (oPi_rel_code_cong rF lF lG G F C F' C' HG HrF HlF HlG HF HF' HFF' HCC') as HPiCong.
      pose proof (El_cong orel lG G (oPi_rel rF lF lG F C G) (oPi_rel rF lF lG F' C' G) HG Horel HlG HPiCong) as HElPiCong.
      assert (HABeq : eq_sort ott []
         (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G)))
         (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F' C' G)))).
      { unfold s_exp. sort_cong; cbn [Model.eq_term core_model];
          try solve [ eapply eq_term_refl; ott_build ]. exact HElPiCong. }
      pose proof (wf_term_conv Hb HABeq) as Hb_BPi.
      pose proof (mapp_wf rF lF lG wknF G extGF F' C' b hdF HG HextGFwf HrF HlF HlG HoswF HF' HC' Hb_BPi HhdAtF') as HmappB.
      pose proof (elt_sort_eq_El_gen extGF (cod_at rF lF lG wknF G extGF F C hdF)
                    (cod_at rF lF lG wknF G extGF F' C' hdF)
                    (CodRed extGF wknF HoswF hdF hdF Hraa') orel lG HextGFwf Horel HlG HcodatF) as HbridgeCod.
      pose proof (wf_term_conv HmappA (eq_sort_sym HbridgeCod)) as HmappA_elt.
      pose proof (El_cong orel lG extGF (cod_at rF lF lG wknF G extGF F C hdF)
                    (cod_at rF lF lG wknF G extGF F' C' hdF) HextGFwf Horel HlG HCodEsc) as HElCodEsc.
      assert (HsbCod : eq_sort ott []
         (s_exp extGF (term_info orel lG) (oEl orel lG extGF (cod_at rF lF lG wknF G extGF F C hdF)))
         (s_exp extGF (term_info orel lG) (oEl orel lG extGF (cod_at rF lF lG wknF G extGF F' C' hdF)))).
      { unfold s_exp. sort_cong; cbn [Model.eq_term core_model];
          try solve [ eapply eq_term_refl; ott_build ]. exact HElCodEsc. }
      pose proof (wf_term_conv HmappB (eq_sort_sym (eq_sort_trans HbridgeCod HsbCod))) as HmappB_elt.
      pose proof (IHCodW_tm _ HcodatF' _ _ Hbodymem HmappA_elt HmappB_elt) as Hbody_elt.
      pose proof (eq_term_conv Hbody_elt HbridgeCod) as Hbody_ElCod.
      pose proof (mapp_code_cong rF lF lG wknF G extGF F C F' C' b hdF HG HextGFwf HrF HlF HlG HoswF HF HF' HFF' HC HC' HCC' Hb HhdAtF) as HmappCong.
      pose proof (eq_term_trans Hbody_ElCod (eq_term_sym HmappCong)) as Hbody_AC.
      eapply (RedTm_Pi_eta_sound rF lF lG G F C a b HG HrF HlF HlG HF HC Ha Hb).
      change (owkn (oEl rF lF G F) (term_info rF lF) G) with wknF.
      change (oext (oEl rF lF G F) (term_info rF lF) G) with extGF.
      change (ohd (oEl rF lF G F) (term_info rF lF) G) with hdF.
      exact Hbody_AC.
    (* ===================== reflect@Pi (OPEN — see QUESTION) ===================== *)
    + admit.
Admitted.
