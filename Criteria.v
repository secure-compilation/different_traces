Require Import ClassicalExtras.
Require Import Setoid.
Require Import Events.
Require Import CommonST.
Require Import TraceModel.
Require Import Robustdef.
Require Import Properties.
Require Import Topology.

(** *property free criteria *)


(*********************************************************)
(* Criterium for all Properties Preservation             *)
(*********************************************************)

Definition RC : Prop :=
  forall P C' t, exists C,
      sem tgt  (C' [ P ↓ ] ) t ->
      sem src  (C  [ P  ] ) t.

(*
   assuming there exists a source context and using
   classical logic we can move the existential in RC
   after the implication.
 *)
Axiom some_ctx : ctx src. 

Lemma RC' : RC <-> (forall P C' t, sem tgt  (C' [ P ↓ ] ) t ->
                        exists C, sem src  (C  [ P  ] ) t).
Proof.
  unfold RC. split.
  - intros rc P C' t H0. destruct (rc P C' t) as [C H1]. clear rc.
    exists C. apply (H1 H0).
  - intros rc' P C' t.
    assert (K : sem tgt  (C' [ P ↓ ] ) t \/ ~ sem tgt  (C' [ P ↓ ] ) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx. intros H. exfalso. apply (k H).
Qed.

(* RC is equivalent to the preservation of robust satisfaction of every property *)
Theorem RC_RPP : RC <-> (forall P π, RP P π).
Proof.
  rewrite RC'. split.
  - intros rc P π. rewrite contra_RP.
    intros [C' [t' [H0 H1]]].
    destruct (rc P C' t' H0) as [C H]. clear rc. exists C,t'. auto.
  - intros rp P C' t H. specialize (rp P (fun b => b <> t)).
    rewrite contra_RP in rp. destruct rp as [C [t' [H0 H1]]].
    exists C',t. auto. apply NNPP in H1. subst t'. now exists C.
Qed.


(*********************************************************)
(* Criterium for Safety Properties Preservation          *)
(*********************************************************)

Definition RSC : Prop :=
  forall P C' t, sem tgt (C' [ P ↓ ] ) t ->
    forall m, (prefix m t -> exists C t', sem src (C [ P ] ) t' /\ prefix m t').

(*
   robustly safe compilation criterium is equivalent to the
   preservation of robust satisfaction of all Safety properties
 *)
Theorem RSC_RSP : RSC <-> (forall P π, Safety π -> RP P π).
Proof.
 unfold RSC. split.
 - intros rsc P π S. rewrite contra_RP. intros [C' [t [H0 H1]]].
   destruct (S t H1) as [m [pmt S']].
   destruct (rsc P C' t H0 m pmt) as [C [t' [K0 pmt']]].
   exists C, t'. specialize (S' t' pmt'). now auto.
 - intros rsp P C' t H0 m pmt.
   assert (s : Safety (fun b => ~ prefix m b)).
   { unfold Safety. intros b H. apply NNPP in H. exists m. split.
     + assumption.
     + intros b' H' c. apply (c H'). }
   specialize (rsp P (fun b => ~ prefix m b) s).
   rewrite contra_RP in rsp. destruct rsp as [C [t' [K0 K1]]].
   exists C', t. now auto. apply NNPP in K1.
   now exists C,t'.
Qed.

(** ** Stronger variant of Robustly Safe Compilation *)
Lemma stronger_rsc : (forall P C' t, sem tgt ( C' [ P ↓ ]) t  ->
  forall m, prefix m t -> exists C, sem src ( C [ P ] ) (embedding m))
  -> RSC.
Proof.
  unfold RSC. intros H P c t Hsem' m Hprefix.
  specialize (H P c t Hsem' m Hprefix). destruct H as [C Hsem].
  exists C. exists (embedding m). split. assumption. apply embed_pref.
Qed.

(* The reverse direction doesn't hold *)

(*********************************************************)
(* Criterium for Liveness Properties Preservation        *)
(*********************************************************)
Definition Liveness (π : prop) : Prop :=
  forall m : finpref, exists t : trace,
      (prefix m t /\ π t).


(* Robust liveness compilation criterium *)
Definition RLC : Prop :=
  forall P C' t, inf t ->
     (exists C, sem tgt ( C' [ P ↓ ]) t ->
           sem src ( C [ P ]) t).

(* the same as for RC *)
Lemma RLC' : RLC <-> (forall P C' t, inf t -> sem tgt ( C' [ P ↓ ]) t ->
                                  exists C,  sem src ( C [ P ]) t).
Proof.
   unfold RLC. split.
  - intros rc P C' t Hi H0. destruct (rc P C' t) as [C H1]. clear rc.
    assumption. exists C. apply (H1 H0).
  - intros rc' P C' t Hi.
    assert (K :  sem tgt ( C' [ P ↓ ]) t \/ ~  sem tgt ( C' [ P ↓ ]) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t Hi k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx. intros H. exfalso. apply (k H).
Qed.

Theorem RLC_RLP : RLC <-> (forall P π, Liveness π -> RP P π).
Proof.
  rewrite RLC'. split.
  - intros rlc P π Hl. rewrite contra_RP. intros [C' [t [H0 H1]]].
    assert(Hi : inf t) by (rewrite (not_in_liv_inf π) in Hl; now apply ( Hl t H1)).
    destruct (rlc P C' t Hi H0) as [C K0]. clear rlc.
    now exists C,t.
  - intros rlp P C' t Hi H0.
    specialize (rlp P (fun b => b <> t) (inf_excluded_is_liv t Hi)).
    rewrite contra_RP in rlp. destruct rlp as [C [t' [K0 K1]]].
    now exists C', t. apply NNPP in K1. subst t'.
    now exists C.
Qed.

(*********************************************************)
(* Criterium for Observable Properties Preservation  
    it's the same as all Properties Preservation         *)
(*********************************************************)


(* CA: this condition is trace equality 
       if one of the two traces is finite then 
       also the other one is finite. 
 *)
Lemma rewriting_lemma : forall t1 t2,
    (forall m, prefix m t1 -> prefix m t2) ->
    (forall π, π t1 -> π t2).
Admitted.

Theorem RobsP_RPP : (forall P π, Observable π -> RP P π) <->
                    (forall P π, RP P π).
Proof.
  split; try now firstorder.
  intros hr P π. rewrite contra_RP.
  intros [C' [t [hsem ht]]].
  specialize (hr P (fun b => exists m, prefix m b /\ ~ prefix m t)). 
  assert (Observable (fun b => exists m, prefix m b /\ ~ prefix m t)).
  { unfold Observable. intros t0 [m [h1 h2]].
    exists m. split; try now auto.
    intros t' h'. now exists m. }
  rewrite contra_RP in hr. destruct (hr H) as [C [t' [k1 k2]]]; clear H. 
  exists C',t. split; try now auto. intros [m [hc1 hc2]]. now auto. 
  exists C, t'. split; try now auto.
  intros ff. apply ht.
  apply (rewriting_lemma t' t). intros m hm.
  rewrite not_ex_forall_not in k2. specialize (k2 m). rewrite <- not_imp in k2.
  apply NNPP in k2. now auto. assumption.
Qed. 

Theorem RobsP_RC : (forall P π, Observable π -> RP P π) <-> RC.
Proof. now rewrite RobsP_RPP, RC_RPP. Qed. 

(******************************************************************************)

(** *hyperproperty free criteria *)

Require Import FunctionalExtensionality.
Require Import Logic.ClassicalFacts.


(*********************************************************)
(* Criterium for all HyperProperties Preservation        *)
(*********************************************************)
Definition HRC : Prop :=
  forall P C',
    (exists C, (forall t,  sem tgt ( C' [ P ↓ ]) t  <->  sem src ( C [ P ]) t)).

Lemma Hequiv_lemma : forall (π1 π2 : prop) (H : hprop),
     (forall t, π1 t <-> π2 t) ->
     (H π1 <-> H π2).
Proof.
  intros π1 π2 H H0. assert (π1 = π2).
  { apply functional_extensionality.
    intros t. specialize (H0 t). now apply prop_ext. }
  now subst.
Qed.  

Theorem HRC_RHP : HRC <-> forall P H, RHP P H.
Proof.
  split.
  - intros H0 P H. rewrite contra_RHP. intros [C' H1].
    specialize (H0 P C'). destruct H0 as [C H0].
    exists C. intros ff. eapply Hequiv_lemma in ff.
    apply (H1 ff). now auto.
  - unfold HRC. intros hrp P C'.
    specialize (hrp P (fun π => π <>  (sem tgt ( C' [ P ↓ ])))).
    rewrite contra_RHP in hrp. destruct hrp as [C H0].
    exists C'. rewrite <- dne. now auto.
    rewrite <- dne in H0. exists C. intros t.
    now  rewrite <- H0. 
Qed.

(*********************************************************)
(* Criterium for SSC HyperProperties Preservation        *)
(*********************************************************)

Definition ssc_cr : Prop :=
  forall P C', 
  exists C, forall b,  sem tgt ( C' [ P ↓ ]) b ->  sem src ( C [ P ]) b.

Lemma SSC_criterium :
  (forall P H, SSC H -> RHP P H) <-> ssc_cr.
Proof.
  split.
  - unfold ssc_cr. intros h0 P C'.
    assert  (s : SSC (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b))).
    { unfold SSC. intros π h1 k Hk ff.
      assert (foo : forall b,  sem tgt ( C' [ P ↓ ]) b -> π b) by now auto.
      now apply (h1 foo). }   
    specialize (h0 P (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b)) s).
    rewrite contra_RHP in h0.
    destruct h0 as [C h1]. exists C'. 
    now rewrite <- dne. rewrite <- dne in h1.
    now exists C.
  - intros ssc P H HH. rewrite contra_RHP. intros [C' H0].
    destruct (ssc P C') as [C h0]. exists C. now firstorder.
Qed.

(*********************************************************)
(* Criterium for HyperSafety Preservation                *)
(*********************************************************)

Definition HSRC : Prop :=
  forall P C' M, Observations M ->
            spref M (sem tgt ( C' [ P ↓ ]))  ->
            exists C, spref M (sem src ( C [ P])).

Theorem RHSP_HSRC : (forall P H, HSafe H -> RHP P H) <-> HSRC.
Proof.
  split.
  - unfold HSRC. intros h P C' M h0 h1.
    assert (hs : HSafe (fun π => ~ spref M π)).
    { unfold HSafe. intros T hm. rewrite <- dne in hm.
      exists M. split; now auto. }
    specialize (h P (fun π => ~ spref M π) hs). rewrite contra_RHP in h.
    destruct h as [C hh]. now exists C'. exists C. now apply NNPP. 
  - intros hsrc P H hs. rewrite contra_RHP. intros [C' h0].
    destruct (hs (fun b : trace => sem tgt ( C' [ P ↓ ]) b)) as [M [hm0 [hm1 hm2]]].
    assumption. destruct (hsrc P C' M) as [C hh]; auto. 
    exists C. now apply hm2.
Qed.


(*********************************************************)
(* Criterium for HyperLiveness Preservation      
   is the same as the one for 
   all Hyperproperties Preservation                      *)
(*********************************************************)

Definition Embedding (M : finpref -> Prop) : prop :=
  fun t => exists m, M m /\ t = embedding m.

Lemma infinite_trace_not_in_embed : forall M, ~ (Embedding M) (constant_trace an_event).
Proof.
  intros M hf. inversion hf. destruct H as [h1 h2].
  assert (inf (constant_trace an_event)) by now apply inf_constant_trace.
  assert (fin (embedding x)) by now apply embed_fin.
  rewrite <- h2 in H0.  now apply (H H0).
Qed.  

Lemma bad_HyperLiv : forall C' P,
    HLiv (fun π : prop => π <> (sem tgt ( C' [ P ↓ ] ))).
Proof.
  unfold HLiv. intros C' P M obsM.
  assert (sem tgt (C' [P ↓]) = Embedding M \/  sem tgt (C' [P ↓]) <> Embedding M)
    by now apply classic.
  destruct H.
  + rewrite H; clear H. exists (fun t => (exists m, M m /\ t = embedding m) \/ t = constant_trace an_event).
    split.
    ++ unfold spref. intros m hm. exists (embedding m).
       split.
       +++ left. now exists m. 
       +++ now apply embed_pref.
     ++ intros hf. apply (infinite_trace_not_in_embed M). 
        rewrite <- hf. now right.
  + exists (Embedding M). split; try now auto.
    unfold spref, Embedding. intros m hm.
    exists (embedding m). split.
    ++ now exists m.
    ++ now apply embed_pref. 
Qed. 

Theorem RHLP_RHP : 
    (forall P H, HLiv H -> RHP P H) <-> (forall P H, RHP P H).
Proof.
 split; try now firstorder.
 intros rhlp P H. rewrite contra_RHP. intros [C' K].
 specialize (rhlp P (fun π : prop => π <> sem tgt (C' [ P ↓]) ) (bad_HyperLiv C' P)).
 rewrite contra_RHP in rhlp.
 destruct rhlp as [C KK]. exists C'. now rewrite <- dne. apply NNPP in KK.
 exists C. now rewrite KK.
Qed.

Theorem RHLP_HRC : 
    (forall P H, HLiv H -> RHP P H) <-> HRC.
Proof. now rewrite (RHLP_RHP), (HRC_RHP). Qed. 