Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import ClassicalExtras.

(** This file contains several lemmas that are used in other proofs *)

(* Fixpoint reverse_list {A : Type} (l : list A) := *)
(*   match l with *)
(*   | nil => nil *)
(*   | cons x xs => snoc (reverse_list xs) x *)
(*   end. *)

(* Lemma reverse_snoc {A : Type} : forall (l : list A) (a : A), *)
(*     reverse_list (snoc l a) = cons a (reverse_list l).  *)
(* Proof. *)
(*   induction l; auto. intros a0. *)
(*   simpl; now rewrite IHl.  *)
(* Qed.  *)
  
(* Lemma reverse_involutive {A : Type}: forall (l : list A), *)
(*     reverse_list (reverse_list l) = l. *)
(* Proof. *)
(*   induction l; auto. *)
(*   simpl. rewrite reverse_snoc. now rewrite IHl. *)
(* Qed. *)


Lemma longest_in_psem {K : language} : forall (P' : prg K) l,
    exists ll, (list_list_prefix ll l) /\ (psem P' (ftbd ll)) /\
          (forall l', list_list_prefix l' l -> psem P' (ftbd l') -> list_list_prefix l' ll).
Proof.  
  intros P' l.
  induction l using list_ind_snoc.
  - exists nil; repeat (split; try now auto).
    + destruct (non_empty_sem K P') as [t Ht].
      exists t; split; simpl; auto. now case t. 
  - destruct IHl as [ll [Hprefll [Hpsem Hmaxll]]].
    destruct (classic (psem P' (ftbd (snoc l a)))) as [Hsnoc | Hsnoc].
    + exists (snoc l a).  repeat (split; try now auto).
      now apply list_list_prefix_ref. 
    + exists ll. repeat (split; try now auto).
      ++ simpl. now apply (list_prefix_snoc_list_prefix ll l a).
      ++ intros l' Hprefl' Hseml'.
         destruct (list_proper_or_equal l' (snoc l a)) as [Hequal | [aa Hproper]]; auto.
         +++ subst. contradiction.
         +++ apply list_pref_snoc_pref in Hproper.
             now apply (Hmaxll l').
Qed.

 
(* (* TODO: TM#2 *) *)
(* Lemma a_technical_lemma: forall (P' : prg tgt) m, *)
(*     psem P' m -> *)
(*     (exists egood, psem P' (fsnoc m egood)) \/ *)
(*      (exists es, psem P' (m[fstop es/ftbd])) \/ *)
(*      (exists t, prefix m t /\ diverges t /\ sem tgt P' t). *)
(* Proof. *)
(*   intros P' m Hpsem. destruct (fstopped m) eqn:Hstop. *)
(*   + right. left. *)
(*     destruct m as [m es | m]; try easy. *)
(*     exists es. now rewrite <- if_fstopped_equal. *)
(*   + destruct Hpsem as [b [Hpref Hsem]]. *)

(*     assert ((exists es, embedding es m = b) \/ ~ (exists es, embedding es m = b)) by apply classic. *)
(*    destruct H as [H | H]. *)
(*     ++ right. left. destruct H as [es H]. exists es. exists b. split; try now auto. *)
(*        simpl. rewrite <- H. rewrite embedding_is_the_same. *)
(*        now apply embed_pref. *)
(*     ++ assert (Hdiv : diverges b \/ ~ diverges b) by now apply classic. *)
(*        destruct Hdiv as [Hdiv | Hdiv]. *)
(*        - right. right. now exists b. *)
(*        - left. *)
(*          rewrite not_ex_forall_not in H. *)
(*          destruct (proper_prefix m b Hpref H Hstop Hdiv) as [e He]. *)
(*          now exists e, b. *)
(* Qed. *)

(* Lemma longest_contra {K : language} : *)
(*   forall W t, *)
(*     ( ~ sem K W t -> *)
(*       (exists m, prefix m t /\ psem W m /\ *)
(*             (forall m', prefix m' t -> psem W m' -> fpr m' m))) *)
(*     <-> *)
(*     ((forall m, (psem W m /\ prefix m t) -> *)
(*            exists m', fpr m m' /\ m <> m' /\ prefix m' t /\ psem W m') *)
(*      -> sem K W t). *)
(* Proof. *)
(*   intros; split. *)
(*   - intros H. *)
(*     apply contra. intros Hsem; specialize (H Hsem). *)
(*     apply ex_not_not_all. destruct H as [m H]. *)
(*     exists m. *)
(*     rewrite imp_equiv. *)
(*     apply de_morgan2. destruct H as [H1 [H2 H3]]. *)
(*     split. rewrite <- dne; split; assumption. *)
(*     apply all_not_not_ex. intros n. *)
(*     apply de_morgan1. apply imp_equiv. intros Hfpr. *)
(*     apply de_morgan1. apply imp_equiv. intros Hneq. unfold not. intros Hpsem. *)
(*     destruct Hpsem. *)
(*     specialize (H3 n H H0). *)
(*     assert (Hi : fpr m n /\ fpr n m) by auto. *)
(*     pose proof (fpr_antisymmetry m n Hi). now subst. *)
(*   - intros H. *)
(*     apply contra. intros Hn. *)
(*     rewrite not_ex_forall_not in Hn. *)
(*     rewrite <- dne. *)
(*     apply H. intros m; specialize (Hn m). *)
(*     intros [H1 H2]. *)
(*     apply de_morgan1 in Hn. rewrite <- imp_equiv in Hn. *)
(*     specialize (Hn H2). *)
(*     apply de_morgan1 in Hn. rewrite <- imp_equiv in Hn. *)
(*     specialize (Hn H1). *)
(*     rewrite not_forall_ex_not in Hn. *)
(*     destruct Hn as [m' Hm']. *)
(*     exists m'. rewrite -> imp_equiv in Hm'. *)
(*     apply de_morgan2 in Hm'. destruct Hm' as [Hm1' Hm2']. *)
(*     apply dne in Hm1'. rewrite -> imp_equiv in Hm2'. *)
(*     apply de_morgan2 in Hm2'. destruct Hm2' as [Hm2' Hm3']. *)
(*     apply dne in Hm2'. *)
(*     repeat (try split); try now assumption. *)
(*     + pose proof (same_ext m m' t H2 Hm1'). *)
(*       now destruct H0. *)
(*     + unfold not; intros Hnot. *)
(*       subst. now pose proof (fpr_reflexivity m'). *)
(* Qed. *)


(* Lemma tapp_pref : forall m t t', t = tapp m t' -> prefix m t. *)
(* Proof. *)
(*   intros []. *)
(*   + induction p; intros t t' H.   *)
(*     ++ now rewrite H. *)
(*     ++ destruct t; try now inversion H. *)
(*        simpl. split; try now inversion H.  *)
(*        +++ apply (IHp t t'). now inversion H.  *)
(*   + induction p; intros t t' H.   *)
(*     ++ now rewrite H. *)
(*     ++ destruct t; try now inversion H. *)
(*        simpl. split; try now inversion H.  *)
(*        +++ apply (IHp t t'). now inversion H. *)
(* Qed. *)

(* Lemma prefix_fin_fpr : forall m mt t es, prefix m t -> *)
(*                                  t = tapp mt (tstop es) -> *)
(*                                  fstopped m = false -> *)
(*                                  fpr m mt. *)
(* Proof. *)
(*   intros []; induction p; intros [] t es Hpref Happ Hstop; try now inversion Hstop. *)
(*   + destruct t; try now auto. *)
(*     inversion Hpref; subst. destruct p0; try now auto. *)
(*     inversion Happ. rewrite H1 in *. *)
(*     assert (foo : fstopped (ftbd p) = false) by auto. *)
(*     assert (app_foo : t = tapp (fstop p0 e) (tstop es)) by auto. *)
(*     specialize (IHp (fstop p0 e) t es H0 app_foo foo). now auto. *)
(*   + destruct t; try now auto. *)
(*     inversion Hpref; subst. destruct p0; try now auto. *)
(*     inversion Happ. rewrite H1 in *. *)
(*     assert (foo : fstopped (ftbd p) = false) by auto. *)
(*     assert (app_foo : t = tapp (ftbd p0) (tstop es)) by auto.  *)
(*     specialize (IHp (ftbd p0) t es H0 app_foo foo). now auto. *)
(* Qed.    *)

(* Lemma stopped_pref_app : forall t m, prefix m t -> fstopped m = true -> *)
(*                                 exists es, t = tapp m (tstop es). *)
(* Proof. *)
(*   intros t [] Hpref Hstop; try now inversion Hstop. *)
(*   generalize dependent t. induction p; intros [] Hpref; try now auto. *)
(*   inversion Hpref; subst. exists e0. reflexivity. *)
(*   inversion Hpref; subst. assert (Hfoo : fstopped (fstop p e) = true) by reflexivity. *)
(*   destruct (IHp Hfoo t H0) as [es Hes]. *)
(*   exists an_endstate; subst; eauto. *)
(* Qed. *)


(* (* explicit hypothesis about the structure of m. It's not needed, will have to remove that later *) *)
(* Lemma not_sem_psem_not_stopped {K : language} : *)
(*   forall W t m p es, (m = ftbd p \/ m = fstop p es) -> ~ sem K W t -> prefix m t -> psem W m  -> *)
(*                 fstopped m = false.  *)
(* Proof. *)
(*   intros W t m p es Hdis Hsemt Hpref Hpsem. *)
(*   destruct Hdis. *)
(*   - subst. destruct (fstopped (ftbd p)) eqn:Hstop; auto. *)
(*   - destruct (fstopped m) eqn:Hstop; auto. *)
(*     apply stopped_pref_app in Hpref; auto. *)
(*     destruct Hpref as [es' Hes]. *)
(*     destruct Hpsem as [t1 [H1 H2]]. *)
(*     apply stopped_pref_app in H1; auto. *)
(*     destruct H1 as [es'' Hes'']. subst. *)
(*     now auto. *)
(* Qed. *)

(* Lemma longest_prefix_tstop {K : language} {HK : semantics_safety_like K} : *)
(*   forall W t es, (exists m, t = tapp m (tstop es)) -> ~ sem K W t -> *)
(*          (exists mm, prefix mm t /\ psem W mm /\ *)
(*                (forall m', prefix m' t -> psem W m' -> fpr m' mm)). *)
(* Proof. *)
(*   intros W t es [m Hm] Hsem. *)
(*   destruct (longest_in_psem W m) as [m0 [Hfpr [Hpsem [Hstopped Hm0]]]]. *)
(*   assert (forall n, prefix n t -> psem W n -> fstopped n = false). *)
(*   { intros n H H0. *)
(*     destruct n. *)
(*     now eapply (not_sem_psem_not_stopped W t); eauto. *)
(*     now eapply (not_sem_psem_not_stopped W t); eauto. *)
(*   } *)
(*   exists m0. repeat split;auto. *)
(*   - apply (fpr_pref_pref m0 m t); auto. now apply (tapp_pref m t (tstop es)). *)
(*   - intros m' H0 H1. apply Hm0; auto. apply (prefix_fin_fpr m' m t es); auto. *)
(*     Unshelve. *)
(*     exact an_endstate. *)
(* Qed. *)

(* Lemma fstopped_prefix_fpr : forall m m', *)
(*     (fstopped m = false -> prefix m' (tapp m tsilent) -> fpr m' m /\ fstopped m' = false). *)
(* Proof. *)
(*   intros m m'. generalize dependent m. *)
(*   induction finpref m' as e' es' p' IHp'; *)
(*   intros [p | p] H1 H2; try now auto. *)
(* - simpl in H2. now destruct p. *)
(* - simpl in H2. destruct p as [|e p]. *)
(*   + contradiction. *)
(*   + specialize (IHp' (ftbd p)). assert (fstopped (ftbd p) = false) by auto. *)
(*     specialize (IHp' H). simpl in *. *)
(*     destruct H2. specialize (IHp' H2). now destruct IHp'. *)
(* - destruct p as [|e p]. *)
(*   + contradiction. *)
(*   + specialize (IHp' (ftbd p)). assert (fstopped (ftbd p) = false) by auto. *)
(*     specialize (IHp' H). simpl in *. *)
(*     destruct H2. specialize (IHp' H2). now destruct IHp'. *)
(* Qed. *)

(* Lemma continuum_lemma : forall m m' e1, *)
(*     fpr m m' -> fpr m' (fsnoc m e1) -> m = m' \/ m' = fsnoc m e1. *)
(* Proof. *)
(*   induction finpref m as e es p IHp; intros; try now auto. *)
(*   - destruct finpref m' as e' es' p'; try now auto. *)
(*     inversion H; subst; try now auto. simpl in *. inversion H. *)
(*     inversion H1. *)
(*   - destruct finpref m' as e' es' p'; try now auto. *)
(*     inversion H; subst. now left. *)
(*     simpl in *. inversion H; inversion H1; subst. now auto. *)
(*   - destruct finpref m' as e' es' p'; try now auto. *)
(*     inversion H0; subst. simpl in *. *)
(*     assert (p' = nil) by now destruct p'. *)
(*     subst; now right. *)
(*   - destruct finpref m' as e' es' p'; try now auto. *)
(*     destruct H; subst. *)
(*     destruct H0; subst. *)
(*     specialize (IHp (ftbd p') e1 H1 H0). *)
(*     destruct IHp as [IHp | IHp]; inversion IHp; subst. *)
(*     now left. *)
(*     now right. *)
(* Qed.              *)

(* Lemma longest_prefix {K : language} {HK : semantics_safety_like K} : *)
(*   forall W t, ~ sem K W t -> *)
(*               (exists m, prefix m t /\ psem W m /\ *)
(*                          (forall m', prefix m' t -> psem W m' -> fpr m' m)). *)
(* Proof. *)
(*   intros W t. *)
(*   (* apply longest_contra. *) *)
(*   intros H. *)
(*   destruct (fin_or_inf t) as [Ht | Ht]. *)
(*   - (* fin t *) *)
(*     pose proof (tapp_fin_pref t Ht). destruct H0 as [m [es Hes]]. *)
(*     apply (@longest_prefix_tstop K HK W t es). *)
(*     now (exists m). *)
(*     assumption. *)
(*   - (* inf t *) *)
(*     destruct (classic (diverges t)) as [Ht' | Ht']. *)
(*     + (* diverges t *) *)
(*       pose proof (tapp_div_pref t Ht') as [m [Hnstopped Hsilent]]. *)
(*       pose proof (longest_in_psem W m) as [mm [Hfpr [Hpsem [Hnstopped' Hmax]]]]. *)
(*       subst. *)
(*       exists mm. repeat (split; auto). *)
(*       ++ apply fpr_pref_pref with (m2 := m). *)
(*          assumption. *)
(*          now apply tapp_pref with (t' := tsilent). *)
(*       ++ intros m' Hpref' Hpsem'. *)
(*          apply Hmax; auto; *)
(*          now destruct (fstopped_prefix_fpr m m' Hnstopped Hpref'). *)
(*     + (* ~ diverges t *) *)
(*       unfold semantics_safety_like in HK. *)
(*       specialize (HK t W H Ht Ht'). *)
(*       destruct HK as [m [ebad [Hpsem [Hpref Hnpsem]]]]. *)
(*       exists m. repeat (split; auto). *)
(*       ++ apply fpr_pref_pref with (m2 := (fsnoc m ebad)). *)
(*          apply fpr_snoc_fpr. now apply fpr_reflexivity. assumption. *)
(*       ++ intros m' Hpref' Hpsem'. *)
(*          destruct (same_ext m' m t); auto. *)
(*          apply fpr_pref_pref with (m2 := (fsnoc m ebad)). *)
(*          apply fpr_snoc_fpr. now apply fpr_reflexivity. assumption. *)
(*          destruct (same_ext m' (fsnoc m ebad) t); try now auto. *)
(*          +++ destruct (continuum_lemma m m' ebad H0 H1); subst. *)
(*              now apply fpr_reflexivity. *)
(*              contradiction. *)
(*          +++ exfalso. apply Hnpsem. *)
(*              unfold psem in Hpsem'. destruct Hpsem' as [t' [Hm't' H'']]. *)
(*              exists t'. split; try now auto. *)
(*              now apply fpr_pref_pref with (m2 := m'). *)
(* Qed. *)

(* Lemma longest_prefix_safety_like : forall (K : language), *)
(*     (forall W t, ~ sem K W t -> *)
(*            (exists m, prefix m t /\ psem W m /\ *)
(*                  (forall m', prefix m' t -> psem W m' -> fpr m' m))) *)
(*     -> semantics_safety_like K. *)
(* Proof. *)
(*   intros K HK. *)
(*   unfold semantics_safety_like. *)
(*   intros t W Hnsem Hinf Hndiv. *)
(*   specialize (HK W t Hnsem). *)
(*   destruct HK as [m [Hpref [Hpsem Hmax]]]. *)

(*   destruct (pref_inf_ndiv_pref m t Hpref Hinf Hndiv) as [e He]. *)
(*   exists m, e. repeat split; auto. *)
(*   intros Hn. *)
(*   specialize (Hmax (fsnoc m e) He Hn). *)
(*   assert (fstopped m = false -> fpr (fsnoc m e) m -> False). *)
(*   { clear. *)
(*     generalize dependent e. *)
(*     induction finpref m as e es p IHp; intros; try now auto. *)
(*     simpl in *. destruct H0 as [_ H0]. *)
(*     apply (IHp e0 H H0). *)
(*   } *)
(*   assert (inf t -> prefix m t -> fstopped m = false). *)
(*   { clear. *)
(*     generalize dependent t. *)
(*     induction finpref m as e es p IHp; intros; try now auto. *)
(*     - destruct t; try now auto. *)
(*       exfalso. apply H. constructor. *)
(*     - destruct t; try now auto. *)
(*       simpl in *. destruct H0; subst. *)
(*       apply (IHp t (inf_tcons e0 t H) H1). *)
(*   } *)
(*   now apply (H (H0 Hinf Hpref) Hmax). *)
(* Qed. *)

(* Theorem semantics_safety_like_equiv_longest_prefix : forall (K : language), *)
(*     semantics_safety_like K <-> (forall W t, ~ sem K W t -> *)
(*            (exists m, prefix m t /\ psem W m /\ *)
(*                  (forall m', prefix m' t -> psem W m' -> fpr m' m))). *)
(* Proof. *)
(*   intros K; split. *)
(*   - intros HK; apply (@longest_prefix K HK). *)
(*   - intros HK; apply (longest_prefix_safety_like K HK). *)
(* Qed. *)
