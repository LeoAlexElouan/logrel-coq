From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaRed.

Context `{GenericTypingProperties}.

Lemma redΣdom {Γ F F' G G' l} : [Γ ||-S<l> tSig F G ≅ tSig F' G'] -> [Γ ||-S<l> F ≅ F'].
Proof.
  intros RΣ0; unshelve eapply (SinstKripke _ (normRedΣ RΣ0).(PolyRed.shpRed)).
  escape; gtyping.
Qed.

Lemma redΣcod {Γ} {wfΓ :[|-Γ]} {F} {wfF : [Γ |- F]} {F' G G' l} : [Γ ||-S<l> tSig F G ≅ tSig F' G'] -> [wfc_cons wfΓ wfF ||-<l> G ≅ G'].
Proof.
  intros RΣ0. unshelve eapply (instKripkeFam wfΓ wfF (normRedΣ RΣ0).(PolyRed.posRed)).
Qed.

Lemma redΣcodfst {Γ} {wfΓ :[|-Γ]} {F F' G G' l} (RΣ: [Γ ||-S<l> tSig F G ≅ tSig F' G']) [RA : [Γ ||-S<l> F ≅ F']] [a a'] :
  [_ ||-S<l> a ≅ a' : _ | RA] -> [wfΓ ||-<l> G[a..] ≅ G'[a'..]].
Proof.
  intros Ra.
  unshelve now eapply (instKripkeSubst wfΓ (normRedΣ RΣ).(PolyRed.posRed)); eapply SirrLR.
  apply (redΣdom (LRSig' (normRedΣ RΣ))).
Qed.


Import SigRedTmEq.

Lemma isLRPair_isWfPair {Γ A A' B B' l p} (ΣA : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣ := (normRedΣ ΣA))
  (Rp : isLRPair' RΣ p) :
    isWfPair Γ A B p.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rp as [???? wtdom convtydom wtcod convtycod rfst rsnd|].
  2: now econstructor.
  pose proof (Ra := SinstKripkeTm wfΓ rfst).
  pose proof (instKripkeSubst wfΓ RΣ.(PolyRed.posRed) _ Ra).
  epose proof (hb := rsnd _ wk_id wfΓ).
  eapply (irrLREq _ X) in hb.
  2: symmetry; etransitivity; [symmetry; eapply wk_id_ren_on|eapply subst_ren_subst_mixed].
  rewrite !(wk_id_ren_on _ b) in hb.
  escape.
  econstructor; tea.
Qed.

Section Helpers.
Context {Γ l A A'} (RA : [Γ ||-Σ<l> A ≅ A'])
  {t u} (Rt : SigRedTm' RA t) (Ru : SigRedTm' RA u).

Lemma build_sigRedTmEq
  (eqnf : [Γ |- Rt.(SigRedTmEq'.nf) ≅ Ru.(SigRedTmEq'.nf) : ParamRedTy.outTyL RA])
  (wfΓ : [|- Γ])
  (Rfst : [ SinstKripke wfΓ RA.(PolyRed.shpRed) | _ ||- tFst Rt.(SigRedTmEq'.nf) ≅ tFst Ru.(SigRedTmEq'.nf) : _ ])
  (Rsnd : [ instKripkeSubst wfΓ RA.(PolyRed.posRed) _ Rfst | _ ||- tSnd Rt.(SigRedTmEq'.nf) ≅ tSnd Ru.(SigRedTmEq'.nf) : _ ]) :
  [LRSig' RA | _ ||- t ≅ u : _].
Proof.
  eapply SigRedTmEq_to.
  unshelve eexists Rt Ru _; tea.
  - intros; now unshelve now eapply SirrLR; rewrite 2!wk_fst; eapply SwkLR.
  - intros; eapply irrLREq.
    2: rewrite 2!wk_snd; now eapply wkLR.
    now bsimpl.
Qed.

Lemma redtmwf_fst {F G f f'} :
  [ Γ |- f :⤳*: f' : tSig F G ] ->
  [ Γ |- tFst f :⤳*: tFst f' : F ].
Proof.
  intros [] ; constructor; [| now eapply redtm_fst].
  timeout 1 gen_typing.
Qed.

Lemma redtmwf_snd {F G f f'} :
  [ Γ |- f :⤳*: f' : tSig F G ] ->
  [ Γ |- G[(tFst f)..] ≅ G[(tFst f')..]] ->
  [ Γ |- tSnd f :⤳*: tSnd f' : G[(tFst f)..] ].
Proof.
  intros [] ? ; constructor; [| now eapply redtm_snd].
  eapply ty_conv; [| now symmetry]; timeout 1 gen_typing.
Qed.
End Helpers.



Lemma build_sigRedTmEq' {Γ} {wfΓ :[|-Γ]} {l F F' G G'}
  (RΣ0 : [Γ ||-S<l> tSig F G ≅ tSig F' G'])
  (RΣ := normRedΣ RΣ0)
  {t u} (Rt : SigRedTm' RΣ t) (Ru : SigRedTm' RΣ u)
  (Rdom := redΣdom RΣ0)
  (Rfst : [ Rdom | _ ||- tFst Rt.(SigRedTmEq'.nf) ≅ tFst Ru.(SigRedTmEq'.nf) : _ ])
  (Rcod := instKripkeSubst wfΓ RΣ.(PolyRed.posRed) _ Rfst)
  (Rsnd : [ Rcod | _ ||- tSnd Rt.(SigRedTmEq'.nf) ≅ tSnd Ru.(SigRedTmEq'.nf) : _ ]) :
  [LRSig' RΣ | _ ||- t ≅ u : _].
Proof.
  unshelve eapply (build_sigRedTmEq _ Rt Ru).
  1: eapply wfΓ.
  1: eapply SirrLREq; tea; reflexivity.
  2: eapply irrLREq; tea; reflexivity.
  epose proof (redΣcod RΣ0); escape.
  eapply convtm_eta_sig; cbn -[Wpack] in *; tea; destruct Rt, Ru; cbn -[Wpack] in *.
  2: eapply isLRPair_isWfPair.
  all: first [now eapply isLRPair_isWfPair| gtyping].
  Unshelve.
  eapply wfΓ.
  now eapply escape.
Qed.

Lemma fstRed {l Γ} {wfΓ : [|-Γ]} {F F' G G' p p'}
  (RΣ : [Γ ||-S<l> tSig F G ≅ tSig F' G'])
  (RF : [wfΓ ||-<l> F ≅ F'])
  (Rp : [Γ ||-S<l> p ≅ p' : _ | RΣ]) :
  [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eapply (SirrLR (LRSig' (normRedΣ RΣ))) in Rp.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_fst, tmr_wf_red. exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_fst, tmr_wf_red.
    eapply redtmwf_conv.
    1:exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + eapply Split_return; intros ??? oRF.
    now unshelve eapply SirrLR, (SigRedTmEq.eqFst Rp).
Qed.

(* Lemma fstRed {l Γ} {wfΓ : [|-Γ]} {F F' G G' p p'}
  (RΣ : [wfΓ ||-<l> tSig F G ≅ tSig F' G'])
  (RF : [wfΓ ||-<l> F ≅ F'])
  (Rp : [wfΓ ||-<l> p ≅ p' : _ | RΣ]) :
  [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eapply (dSplit_bind Rp).
  intros ??? oRΣ oRp.
  eapply Wpackrefold.
  rewrite <- 2!wk_fst.
  now unshelve eapply SfstRed, Rp.
Qed. *)


Lemma sndRed {l Γ} {wfΓ :[|-Γ]} {F F' G G'} {p p'}
  (RΣ : [Γ ||-S<l> tSig F G ≅ tSig F' G'])
  (Rp : [Γ ||-S<l> p ≅ p' : _ | RΣ])
  (RGfstp : [wfΓ ||-<l> G[(tFst p)..] ≅ G'[(tFst p')..]]) :
  [wfΓ ||-<l> tSnd p ≅ tSnd p' : _ | RGfstp].
Proof.
  set (RΣ' := (LRSig' (normRedΣ RΣ))).
  eapply (SirrLR RΣ') in Rp.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_snd, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_snd, tmr_wf_red, redtmwf_conv.
    1: exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + erewrite <-wk_id_ren_on, <-(wk_id_ren_on _ (tSnd (nf (redL _)))).
    eapply irrLRConv, (SigRedTmEq.eqSnd Rp wk_id wfΓ).
    erewrite wk_fst, <- eq_subst_scons.
    eassert (RF : [wfΓ ||-< l> F ≅ F'])
      by (eapply Split_return; intros;
      now eapply (normRedΣ RΣ).(PolyRed.shpRed)).
    epose proof (redTmFwd' Rp) as [Rp' _ _ _ _].
    epose proof (fstRed := fstRed RΣ' RF Rp').
    eapply (dSplit_bind fstRed).
    intros ??? oRF ofstRed.
    eapply WAdrefold.
    rewrite 2!subst_ren_subst_mixed.
    eapply kripkeLRlrefl.
    - clear dependent Δ. intros ????? RAA'.
      now eapply (normRedΣ RΣ).(PolyRed.posRed).
    - symmetry; now unshelve eapply SirrLR, fstRed.
    Unshelve. easy.
Qed.

(* Lemma fstRed {l Δ} {wfΔ :[|-Δ]} {F F' G G' p p'}
  (RΣ : [Δ ||-S<l> tSig F G ≅ tSig F' G'])
  (RF : [wfΔ ||-<l> F ≅ F'])
  (Rp : [Δ ||-S<l> p ≅ p' : _ | LRSig' (normRedΣ RΣ)]) :
  [wfΔ ||-<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_fst, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_fst, tmr_wf_red.
    eapply redtmwf_conv.
    1:exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + eapply Split_return; intros.
    now unshelve eapply SirrLR, (SigRedTmEq.eqFst Rp).
Qed.

Lemma sndRed {l Δ} {wfΔ :[|-Δ]} {F F' G G'} {p p'}
  (RΣ : [Δ ||-S<l> tSig F G ≅ tSig F' G'])
  (RΣn := LRSig' (normRedΣ RΣ))
  (Rp : [Δ ||-S<l> p ≅ p' : _ | RΣn])
  (RGfstp : [wfΔ ||-<l> G[(tFst p)..] ≅ G'[(tFst p')..]]) :
  [wfΔ ||-<l> tSnd p ≅ tSnd p' : _ | RGfstp].
Proof.
  eapply redSubstTmEq; cycle 1.
  + eapply redtm_snd, tmr_wf_red; exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_snd, tmr_wf_red, redtmwf_conv.
    1: exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + erewrite <-wk_id_ren_on, <-(wk_id_ren_on _ (tSnd (nf (redL _)))).
    eapply irrLRConv, (SigRedTmEq.eqSnd Rp wk_id wfΔ).
    eassert (RF : [wfΔ ||-< l> F ≅ F'])
      by (eapply Split_return; intros;
      now eapply (normRedΣ RΣ).(PolyRed.shpRed)).
    erewrite wk_fst, <- eq_subst_scons.
    epose proof (redTmFwd' Rp) as [Rp' _ _ _ _].
    epose proof (fstRed := fstRed RΣ RF Rp').
    symmetry.
    eapply (dSplit_bind fstRed).
    intros Ξ wfΞ ρΞ oRF ofstRed.
    eapply WAdrefold.
    rewrite 2!subst_ren_subst_mixed.
    eapply kripkeLRlrefl.
    - clear dependent Ξ; intros Ξ a b ρΞ wfΞ RAA'.
      now eapply (normRedΣ RΣ).(PolyRed.posRed).
    - now unshelve eapply SirrLR, fstRed.
    Unshelve. easy.
Qed. *)

Lemma pairFstRed {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [wfΓ ||-<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [wfΓ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA].
Proof.
  escape.
  eapply redSubstTmEq; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairFstRed' {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [wfΓ ||-<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [wfΓ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA]
  × [wfΓ ||-<l> tFst (tPair A B a b) ≅ a : _ | lrefl RA]
  × [wfΓ ||-<l> tFst (tPair A' B' a' b') ≅ a' : _ | urefl RA ].
Proof.
  escape.
  eapply redSubstTmEq'; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairSndRed {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (RBfst : [wfΓ ||-<l> B[(tFst (tPair A B a b))..] ≅ B'[(tFst (tPair A' B' a' b'))..]])
  (RBfsta : [wfΓ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..]])
  (Ra : [wfΓ ||-<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [wfΓ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst ].
Proof.
  escape.
  eapply redSubstTmEq; tea.
  1: now eapply irrLRConv.
  1,2: eapply redtm_snd_beta; tea; now eapply ty_conv.
Qed.

Lemma canonSig {Γ A A' B B' l p p'}
  {RΣ : [Γ ||-S< l > tSig A B ≅ tSig A' B']} :
  [ Γ ||-S< l > p ≅ p' : tSig A B | RΣ] ->
  [ Γ ||-S< l > p ≅ p' : tSig A B | LRSig' (normRedΣ RΣ)].
Proof.
  intro. now eapply SirrLR.
Qed.

Lemma sigEtaRed' {Γ} {wfΓ : [|-Γ]} {A A' B B' l p p'}
  (RΣ : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣ' : [wfΓ ||-<l> tSig A B ≅ tSig A' B'])
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RBfst : [wfΓ ||-<l> B[(tFst p)..] ≅ B'[(tFst p')..]])
  (Rp : [Γ ||-S<l> p : _ | RΣ])
  (Rp' : [Γ ||-S<l> p' : _ | RΣ])
  (Rfstpp' : [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RA])
  (Rsndpp' : [wfΓ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
  [wfΓ ||-<l> p ≅ p' : _ | RΣ'].
Proof.
  eapply canonSig in Rp, Rp'.
  eapply SigRedTmEq_from in Rp, Rp'.
  pose proof (redTmFwd' Rp) as [Rpnf _ _ _ _]; pose proof (Rpnf1 := fstRed _ RA Rpnf).
  pose proof (redTmFwd' Rp) as [Rpnf' _ _ _ _]; pose proof (Rpnf1' := fstRed _ RA Rpnf').
  unshelve eapply (build_sigRedTmEq' _ Rp.(SigRedTmEq'.redL _  _ _) Rp'.(redL)).
  

Lemma sigEtaRed {Γ} {wfΓ : [|-Γ]} {A A' B B' l p p'}
  (RΣ : [wfΓ ||-<l> tSig A B ≅ tSig A' B'])
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RBfst : [wfΓ ||-<l> B[(tFst p)..] ≅ B'[(tFst p')..]])
  (Rp : [wfΓ ||-<l> p : _ | RΣ])
  (Rp' : [wfΓ ||-<l> p' : _ | RΣ])
  (Rfstpp' : [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RA])
  (Rsndpp' : [wfΓ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
  [wfΓ ||-<l> p ≅ p' : _ | RΣ].
Proof.
  eapply (dSplit_bind Rp).
  intros ??? _ oRp.
  eapply Wpackrefold.
  eapply (dSplit_wk_bind Rp' ρ).
  intros ?? ρΞ oRΣ oRp'.
  eapply Wpackrefold.
  pose proof (Rp0 := cover Rp Ξ wfΞ (ρΞ∘w ρ) (overtree_PSh Rp oRp) oRΣ); cbn in Rp0.
  pose proof (Rp'0 := cover Rp' Ξ wfΞ (ρΞ∘w ρ) oRp' oRΣ); cbn in Rp'0.
  set (RΣ0 := cover RΣ Ξ wfΞ (ρΞ ∘w ρ) oRΣ) in *; clearbody RΣ0. cbn in RΣ0.
  pose proof (RA' := WwkRed (wkLR _ _ _ _ RA) (ρΞ∘w ρ) wfΞ).
  pose proof (redTmFwd' (canonSig Rp0)) as [Rpnf _ _ _ _]; pose proof (Rpnf1 := fstRed _ RA' Rpnf).
  pose proof (redTmFwd' (canonSig Rp'0)) as [Rpnf' _ _ _ _]; pose proof (Rpnf1' := fstRed _ RA' Rpnf').
  eapply (irrLREq (A:= tSig A⟨ρΞ∘w ρ⟩ B ⟨wk_up A (ρΞ∘w ρ)⟩)).
  1: symmetry; eapply wk_comp_ren_on.
  rewrite 2!wk_comp_ren_on.
  eapply Wpack_return.
  unshelve eapply (build_sigRedTmEq' _ (canonSig Rp0).(redL) (canonSig Rp'0).(redL)).
  easy.
  + 

Lemma sigEtaRed {Γ} {wfΓ :[|-Γ]} {A A' B B' l p p'}
  (RΣ0 : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣn := normRedΣ RΣ0)
  (RΣ := (LRSig' RΣn))
  (RA : [wfΓ ||-<l> A ≅ A'])
  (RBfst : [wfΓ ||-<l> B[(tFst p)..] ≅ B'[(tFst p')..]])
  (Rp : [Γ ||-<l> p : _ | RΣ])
  (Rp' : [Γ ||-<l> p' : _ | RΣ])
  (Rfstpp' : [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RA])
  (Rsndpp' : [wfΓ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
  [wfΓ ||-<l> p ≅ p' : _ | WAd_return (wfΓ := wfΓ) RΣ].
Proof.
  pose proof (redTmFwd' Rp) as [Rpnf _ _ _ _]; pose proof (Rpnf1 := fstRed _ RA Rpnf).
  pose proof (redTmFwd' Rp') as [Rpnf' _ _ _ _]; pose proof (Rpnf1' := fstRed _ RA Rpnf').
  eapply (dSplit_bind Rpnf1).
  intros ??? oRA oRpnf1.
  unshelve eapply Wpackrefold.
  1: now eapply WAd_return, SwkLR.
  eapply (dSplit_wk_bind_return Rpnf1' ρ).
  intros ?? ρΞ oRA' oRpnf1' oirr.
  unshelve eapply SirrLREq; clear oirr.
  4: symmetry; eapply wk_comp_ren_on.
  2: now eapply SwkLR.
  eapply SirrLR.
  eapply (build_sigRedTmEq'); fold ren_term.
  change (tSig A B)⟨ρ' ∘w ρ⟩ with (tSig A⟨ρ' ∘w ρ⟩ B⟨ρ' ∘w ρ⟩)
  rewrite 
  unshelve eapply Wpack_return, SwkLR, (build_sigRedTmEq' _ Rp.(redL) Rp'.(redL)); tea.
  - transitivity (tFst p); [symmetry|transitivity (tFst p')]; eapply SirrLR.
    eapply Rpnf1.
  - pose proof (RBB' := instKripkeSubst RΣn.(PolyRed.posRed)).
    pose proof (RB := instKripkeSubst (kripkeLRlrefl RΣn.(PolyRed.posRed))).
    pose proof (RB' := instKripkeSubst (kripkeLRurefl RΣn.(PolyRed.posRed))).
    pose proof (RBpnf1 := RBB' _ _ _ Rpnf1); pose proof (sndRed _ Rpnf RBpnf1).
    pose proof (RBpnf1' := RBB' _ _ _ Rpnf1'); pose proof (sndRed _ Rpnf' RBpnf1').
    cbn in *; eapply irrLR.
    eapply ((transLR _ _).(transRedTm) _ (tSnd p)).
    1: symmetry; eapply irrLRConv; tea; exact (RB _ _ _ Rpnf1).
    eapply ((transLR _ _).(transRedTm) _ (tSnd p')); tea.
    eapply irrLRConv; [|tea].
    eapply RBB', urefl; tea.
    Unshelve.
    3: eapply RB', urefl; tea.
    eapply RB; now symmetry.
Qed.


Lemma mkPair_isLRPair {Γ A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ := normRedΣ RΣ0)
  (RA1 : [Γ ||-<l> A ≅ A1])
  (RB1 : [Γ ||-<l> B[a1..] ≅ B1[a1..]])
  (Ra1 : [Γ ||-<l> a1 : _ | RA1])
  (Rb1 : [Γ ||-<l> b1 : _ | RB1])
: isLRPair RΣ (tPair A1 B1 a1 b1).
Proof.
  escape.
  unshelve eapply PairLRPair; tea; intros.
  - now unshelve now eapply irrLR, wkLR.
  - now unshelve now eapply irrLREq, wkLR; tea; rewrite subst_ren_subst_mixed.
Qed.

Definition pairSigRedTm {Γ A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ1 : [Γ ||-<l> tSig A B ≅ tSig A1 B1])
  (RΣ := normRedΣ RΣ0)
  (Ra1 : [Γ ||-<l> a1 : _ | redΣdom RΣ0])
  (Rb1 : [Γ ||-<l> b1 : _ | redΣcodfst RΣ0 Ra1])
: SigRedTm RΣ (tPair A1 B1 a1 b1).
Proof.
  exists (tPair A1 B1 a1 b1); pose proof (RA := redΣdom RΣ1);
    pose proof (RB := redΣcodfst RΣ1 (fst (irrLR _ RA _ _) Ra1)).
  + eapply redtmwf_refl; cbn.
    assert (wfΓ : [|- Γ]) by (escape ; gtyping).
    assert [_ ||-<l> a1 : _ | urefl RA ] by now eapply irrLRConv.
    pose proof (instKripkeFamConv wfΓ (normRedΣ RΣ1).(PolyRed.posRed)).
    assert [_ ||-<l> b1 : _ | urefl RB ] by now eapply irrLRConv.
    escape.
    eapply ty_conv; [ eapply ty_pair; tea| now symmetry].
  + now unshelve now eapply mkPair_isLRPair; eapply irrLR.
Defined.

Lemma pairCongRed {Γ A A' B B' a a' b b' l}
  (RΣ0 : [Γ ||-<l> tSig A B ≅ tSig A' B'])
  (RΣ := normRedΣ RΣ0)
  (RΣ' := LRSig' RΣ)
  (RA : [Γ ||-<l> A ≅ A'])
  (RBa : [Γ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-<l> a ≅ a' : A | RA])
  (Rb : [Γ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-<l> tPair A B a b ≅ tPair A' B' a' b' : _ | RΣ'].
Proof.
  assert (wfΓ : [|-Γ]) by (escape; gtyping).
  pose proof (convtyB := redΣcod RΣ').
  pose proof (wtB' := escape (symmetry (instKripkeFamConv wfΓ RΣ.(PolyRed.posRed)))).
  unshelve epose proof (pairFstRed' RA convtyB wtB' RBa Ra Rb) as (ff'&fa&fa').
  pose proof (RBconv := instKripkeSubst (kripkeLRlrefl RΣ.(PolyRed.posRed)) RA (fst (irrLR _ _ _ _) fa)).

  unshelve eapply build_sigRedTmEq'.
  + unshelve eapply pairSigRedTm; eapply lrefl; tea; now eapply irrLR.
  + unshelve eapply pairSigRedTm; tea; eapply urefl. now eapply irrLR.
    eapply irrLRConv; tea; eapply (instKripkeSubst (kripkeLRlrefl RΣ.(PolyRed.posRed)) RA Ra).
  + cbn; eapply irrLR, pairFstRed; tea.
  + unshelve now cbn; eapply irrLR; eapply pairSndRed; tea; symmetry.
    now eapply (instKripkeSubst RΣ.(PolyRed.posRed)).
Qed.

End SigmaRed.





