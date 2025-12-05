From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaRed.

Context `{GenericTypingProperties}.

Lemma SredΣdom {Γ F F' G G' l} : [Γ ||-S<l> tSig F G ≅ tSig F' G'] -> [Γ ||-S<l> F ≅ F'].
Proof.
  intros RΣ0; unshelve eapply (SinstKripke _ (normRedΣ RΣ0).(PolyRed.shpRed)).
  escape; gtyping.
Qed.


Lemma redΣdom {Γ} {wfΓ :[|-Γ]} {F F' G G' l} : [wfΓ ||-<l> tSig F G ≅ tSig F' G'] -> [wfΓ ||-<l> F ≅ F'].
Proof.
  intros RΣ.
  eapply (Split_bind_return RΣ).
  intros ??? oRΣ.
  eapply SredΣdom.
  now eapply RΣ.
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
  apply (SredΣdom (LRSig' (normRedΣ RΣ))).
Qed.


Import SigRedTmEq.

Lemma isLRPair_isWfPair {Γ A A' B B' l p} (ΣA : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣ := (normRedΣ ΣA))
  (Rp : isLRPair RΣ p) :
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
  {t u} (Rt : SigRedTm RA t) (Ru : SigRedTm RA u).

Lemma build_sigRedTmEq
  (eqnf : [Γ |- Rt.(SigRedTmEq.nf) ≅ Ru.(SigRedTmEq.nf) : ParamRedTy.outTyL RA])
  (wfΓ : [|- Γ])
  (Rfst : [ SinstKripke wfΓ RA.(PolyRed.shpRed) | _ ||- tFst Rt.(nf) ≅ tFst Ru.(nf) : _ ])
  (Rsnd : [ instKripkeSubst wfΓ RA.(PolyRed.posRed) _ Rfst | _ ||- tSnd Rt.(nf) ≅ tSnd Ru.(nf) : _ ]) :
  [LRSig' RA | _ ||- t ≅ u : _].
Proof.
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
  {t u} (Rt : SigRedTm RΣ t) (Ru : SigRedTm RΣ u)
  (Rdom := SredΣdom RΣ0)
  (Rfst : [ Rdom | _ ||- tFst Rt.(nf) ≅ tFst Ru.(nf) : _ ])
  (Rcod := instKripkeSubst wfΓ RΣ.(PolyRed.posRed) _ Rfst)
  (Rsnd : [ Rcod | _ ||- tSnd Rt.(nf) ≅ tSnd Ru.(nf) : _ ]) :
  [LRSig' RΣ | _ ||- t ≅ u : _].
Proof.
  unshelve eapply (build_sigRedTmEq _ Rt Ru).
  1: eapply wfΓ.
  1: eapply SirrLREq; tea; reflexivity.
  2: eapply irrLREq; tea; reflexivity.
  epose proof (redΣcod RΣ0); escape.
  eapply convtm_eta_sig; cbn -[Wpack] in *; tea; destruct Rt, Ru; cbn -[Wpack] in *.
  all: first [now eapply isLRPair_isWfPair| gtyping].
  Unshelve.
  eapply wfΓ.
  now eapply escape.
Qed.

Lemma canonSig {Γ A A' B B' l p p'}
  {RΣ : [Γ ||-S< l > tSig A B ≅ tSig A' B']} :
  [ Γ ||-S< l > p ≅ p' : tSig A B | RΣ] ->
  [ Γ ||-S< l > p ≅ p' : tSig A B | LRSig' (normRedΣ RΣ)].
Proof.
  intro. now eapply SirrLR.
Qed.

Lemma canonSig_inv {Γ A A' B B' l p p'}
  {RΣ : [Γ ||-S< l > tSig A B ≅ tSig A' B']} :
  [ Γ ||-S< l > p ≅ p' : tSig A B | LRSig' (normRedΣ RΣ)] ->
  [ Γ ||-S< l > p ≅ p' : tSig A B | RΣ].
Proof.
  intro. now eapply SirrLR.
Qed.

Lemma SfstRed {l Γ F F' G G' p p'}
  (RΣ : [Γ ||-S<l> tSig F G ≅ tSig F' G'])
  (RF : [Γ ||-S<l> F ≅ F'])
  (Rp : [Γ ||-S<l> p ≅ p' : _ | RΣ]) :
  [Γ ||-S<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eassert (wfΓ:[|-Γ]) by (escape; gtyping).
  eapply (SirrLR (LRSig' (normRedΣ RΣ))) in Rp.
  eapply SredSubstTmEq; cycle 1.
  + eapply redtm_fst, tmr_wf_red. exact (SigRedTmEq.red (SigRedTmEq.redL Rp)).
  + eapply redtm_fst, tmr_wf_red.
    eapply redtmwf_conv.
    1:exact (SigRedTmEq.red (SigRedTmEq.redR Rp)).
    now escape.
  + epose proof (SigRedTmEq.eqFst Rp wk_id wfΓ) as Rp'.
    erewrite 2!wk_id_ren_on in Rp'.
    eapply SirrLREq with (1:= wk_id_ren_on _ _), Rp'.
Qed.

Lemma fstRed {l Γ} {wfΓ : [|-Γ]} {F F' G G' p p'}
  (RΣ : [Γ ||-S<l> tSig F G ≅ tSig F' G'])
  (RF : [wfΓ ||-<l> F ≅ F'])
  (Rp : [Γ ||-S<l> p ≅ p' : _ | RΣ]) :
  [wfΓ ||-<l> tFst p ≅ tFst p' : _ | RF].
Proof.
  eapply Split_return.
  intros ??? oRF.
  erewrite <-2!wk_fst.
  unshelve eapply SirrLR, SfstRed, (SwkLR _ _ _ RΣ), Rp.
  now unshelve eapply RF.
  all: easy.
Qed.


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


Lemma pairFstRed {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [Γ ||-S<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-S<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-S<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA].
Proof.
  escape.
  eapply SredSubstTmEq; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairFstRed' {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [Γ ||-S<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-S<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-S<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA]
  × [Γ ||-S<l> tFst (tPair A B a b) ≅ a : _ | lrefl RA]
  × [Γ ||-S<l> tFst (tPair A' B' a' b') ≅ a' : _ | urefl RA ].
Proof.
  escape.
  eapply SredSubstTmEq'; tea.
  1,2: eapply redtm_fst_beta; tea; now eapply ty_conv.
Qed.

Lemma pairSndRed {Γ} {wfΓ :[|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' a a' b b' l}
  (RA : [Γ ||-S<l> A ≅ A'])
  (RB : [wfc_cons wfΓ wfA ||-<l> B ≅ B'])
  (WtB' : [Γ ,, A' |- B'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (RBfst : [wfΓ ||-<l> B[(tFst (tPair A B a b))..] ≅ B'[(tFst (tPair A' B' a' b'))..]])
  (RBfsta : [wfΓ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..]])
  (Ra : [Γ ||-S<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [wfΓ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst ].
Proof.
  escape.
  eapply redSubstTmEq; tea.
  1: now eapply irrLRConv.
  1,2: eapply redtm_snd_beta; tea; now eapply ty_conv.
Qed.

Lemma sigEtaRed {Γ} {wfΓ : [|-Γ]} {A A' B B' l p p'}
  (RΣ : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RA : [Γ ||-S<l> A ≅ A'])
  (RBfst : [wfΓ ||-<l> B[(tFst p)..] ≅ B'[(tFst p')..]])
  (Rp : [Γ ||-S<l> p : _ | RΣ])
  (Rp' : [Γ ||-S<l> p' : _ | RΣ])
  (Rfstpp' : [Γ ||-S<l> tFst p ≅ tFst p' : _ | RA])
  (Rsndpp' : [wfΓ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
  [Γ ||-S<l> p ≅ p' : _ | RΣ].
Proof.
  eapply canonSig in Rp, Rp'.
  eapply SirrLR.
  pose proof (redTmFwd' Rp) as [Rpnf _ _ _ _]; pose proof (Rpnf1 := SfstRed _ RA Rpnf).
  pose proof (redTmFwd' Rp') as [Rpnf' _ _ _ _]; pose proof (Rpnf1' := SfstRed _ RA Rpnf').
  unshelve eapply (build_sigRedTmEq' _ Rp.(redL) Rp'.(redL)); tea.
  - transitivity (tFst p); [symmetry|transitivity (tFst p')]; now eapply SirrLR.
  - set (RΣn := normRedΣ RΣ).
    pose proof (RBB' := instKripkeSubst wfΓ RΣn.(PolyRed.posRed)).
    pose proof (RB := instKripkeSubst wfΓ (kripkeLRlrefl (wfΓ :=wfΓ) RΣn.(PolyRed.posRed))).
    pose proof (RBpnf1 := RBB' _ _ _ Rpnf1); pose proof (sndRed _ Rpnf RBpnf1).
    pose proof (RBpnf1' := RBB' _ _ _ Rpnf1'); pose proof (sndRed _ Rpnf' RBpnf1').
    cbn -[Wpack] in *; eapply irrLR.
    transitivity (tSnd p).
    1: symmetry; eapply irrLRConv; tea; exact (RB _ _ _ Rpnf1).
    transitivity (tSnd p').
    1: eapply irrLRConv; tea; exact (RB _ _ _ Rpnf1).
    eapply irrLRConv; [|tea].
    eapply RB.
    transitivity (tFst p); tea.
    1:symmetry; tea.
    Unshelve.
    2: eapply RB; symmetry; tea.
Qed.


Lemma mkPair_isLRPair {Γ} {wfΓ : [|-Γ]} {A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣ := normRedΣ RΣ0)
  (RA1 : [Γ ||-S<l> A ≅ A1])
  (RB1 : [wfΓ ||-<l> B[a1..] ≅ B1[a1..]])
  (Ra1 : [Γ ||-S<l> a1 : _ | RA1])
  (Rb1 : [wfΓ ||-<l> b1 : _ | RB1])
: isLRPair RΣ (tPair A1 B1 a1 b1).
Proof.
  escape.
  unshelve eapply PairLRPair; tea; intros.
  - now unshelve now eapply SirrLR, SwkLR.
  - now unshelve now eapply irrLREq, wkLR; tea; rewrite subst_ren_subst_mixed.
Qed.

Definition pairSigRedTm {Γ} {wfΓ : [|-Γ]} {A A' A1 B B' B1 a1 b1 l}
  (RΣ0 : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
  (RΣ1 : [Γ ||-S<l> tSig A B ≅ tSig A1 B1])
  (RΣ := normRedΣ RΣ0)
  (Ra1 : [Γ ||-S<l> a1 : _ | SredΣdom RΣ0])
  (Rb1 : [wfΓ ||-<l> b1 : _ | redΣcodfst (wfΓ:=wfΓ) RΣ0 Ra1])
: SigRedTm RΣ (tPair A1 B1 a1 b1).
Proof.
  exists (tPair A1 B1 a1 b1); pose proof (RA := SredΣdom RΣ1);
    pose proof (RB := redΣcodfst (wfΓ:=wfΓ) RΣ1 (fst (SirrLR _ RA _ _) Ra1)).
  + eapply redtmwf_refl; cbn.
    eassert (wfA1 : [Γ|-A1]) by (escape; gtyping).
    assert [_ ||-S<l> a1 : _ | urefl RA ] by now eapply SirrLRConv.
    pose proof (instKripkeFamConv wfΓ wfA1 (normRedΣ RΣ1).(PolyRed.posRed)).
    assert [_ ||-<l> b1 : _ | urefl RB ] by now eapply irrLRConv.
    escape.
    eapply ty_conv; [ eapply ty_pair; tea| now symmetry].
  + now unshelve now eapply mkPair_isLRPair; [eapply SirrLR | eapply irrLR].
Defined.

Lemma pairCongRed {Γ} {wfΓ : [|-Γ]} {A A' B B' a a' b b' l}
  (RΣ : [Γ ||-S<l> tSig A B ≅ tSig A' B'])
(*   (RΣ := normRedΣ RΣ0)
  (RΣ' := LRSig' RΣ) *)
  (RA : [Γ ||-S<l> A ≅ A'])
  (RBa : [wfΓ ||-<l> B[a..] ≅ B'[a'..] ])
  (Ra : [Γ ||-S<l> a ≅ a' : A | RA])
  (Rb : [wfΓ ||-<l> b ≅ b' : _ | RBa ]) :
  [Γ ||-S<l> tPair A B a b ≅ tPair A' B' a' b' : _ | RΣ].
Proof.
  assert (wfA : [Γ|-A]) by (escape; gtyping).
  assert (wfA' : [Γ|-A']) by (escape; gtyping).
(*   eapply canonSig. *)
  pose proof (convtyB := redΣcod (wfΓ:=wfΓ) (wfF:=wfA) RΣ).
  pose proof (wtB' := fst (escapeSplitTy (symmetry (instKripkeFamConv wfΓ wfA' (normRedΣ RΣ).(PolyRed.posRed))))).
  unshelve epose proof (pairFstRed' RA convtyB wtB' RBa Ra Rb) as (ff'&fa&fa').
  pose proof (RBconv := instKripkeSubst wfΓ (kripkeLRlrefl (wfΓ:=wfΓ) (normRedΣ RΣ).(PolyRed.posRed)) RA (fst (SirrLR _ _ _ _) fa)).
  eapply canonSig_inv.
  unshelve eapply build_sigRedTmEq'; tea.
  + unshelve eapply pairSigRedTm; tea; eapply lrefl; tea; [eapply SirrLR|eapply irrLR]; tea.
  + unshelve eapply pairSigRedTm; tea; eapply urefl. now eapply SirrLR.
    eapply irrLRConv; tea; eapply (instKripkeSubst wfΓ (kripkeLRlrefl (wfΓ:=wfΓ) (normRedΣ RΣ).(PolyRed.posRed)) RA Ra).
  + cbn; eapply SirrLR, pairFstRed; tea.
  + unshelve now cbn -[Wpack]; eapply irrLR, pairSndRed; tea; symmetry.
    now eapply (instKripkeSubst wfΓ (normRedΣ RΣ).(PolyRed.posRed)).
Qed.

End SigmaRed.





