Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import List.

Require Import XPrefix.
Require Import Criteria.
Require Import TechnicalLemmas. 

(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : input_totality tgt.
Hypothesis determinacy_src    : determinacy src.
Hypothesis tgt_sem           : semantics_safety_like tgt.
(**********************************************************)

(* CA: before trying to prove a lemma check if it is actually used or not! *)

(* Definition xsnoc (m : xpref) (e : event) := *)
(*   match m with *)
(*   | xstop _ _ | xsilent _ => m *)
(*   | xtbd  l               => xtbd (snoc l e) *)
(*   end.  *)


(* Fixpoint list_pref { A : Type } (l1 l2 : list A) : Prop := *)
(*   match l1, l2 with *)
(*   | nil, _ => True *)
(*   | cons x xs, cons y ys => x = y /\ list_pref xs ys *)
(*   | _, _ => False *)
(*   end. *)

(* Fixpoint list_pref_trace (l : list event) (t : trace) : Prop := *)
(*   match l with   *)
(*   | nil => True *)
(*   | cons x xs => match t with *)
(*                 | tcons e t' => x = e /\ list_pref_trace xs t' *)
(*                 | _ => False *)
(*                 end *)
(*   end.  *)

    
(* Definition xpr (x1 x2 : xpref) : Prop := *)
(*   match x1 with *)
(*   | xstop m1 s1 => match x2 with *)
(*                   | xstop m2 s2 => m1 = m2 /\ s1 = s2 *)
(*                   | _ => False *)
(*                   end *)
                    
(*   | xsilent m1 => match x2 with *)
(*                  | xsilent m2 => m1 = m2 *)
(*                  | _ => False *)
(*                  end *)
                   
(*   | xtbd m1 => match x2 with *)
(*               | xstop m2 s1 => list_pref m1 m2 *)
(*               | xsilent m2  => list_pref m1 m2 *)
(*               | xtbd m2 =>  list_pref m1 m2 *)
(*               end *)
                
(*   end. *)

(* Definition xstopped x : bool := *)
(*   match x with *)
(*   | xstop _ _ => true *)
(*   | _ => false *)
(*   end. *)

(* Lemma xpr_snoc : forall p a1 a2,  *)
(*     xpr (xtbd (snoc p a1)) (xtbd (snoc p a2)) -> a1 = a2. *)
(* Proof. *)
(*   induction p; intros a1 a2 H; simpl in *; destruct H as [H1 H2]; auto.    *)
(* Qed. *)

(* Fixpoint list_to_stop_trace (l : list event) (e : endstate) : trace := *)
(*   match l with *)
(*   | nil => tstop e *)
(*   | cons l ls => tcons l (list_to_stop_trace ls e) *)
(*   end.  *)

(* Lemma xstop_prefix_list : forall p e, xprefix (xstop p e) (list_to_stop_trace p e). *)
(* Proof. *)
(*   induction p; intros e; simpl; auto.   *)
(*   split; auto. now apply IHp. *)
(* Qed. *)

(* Lemma unique_continuation_stop: forall l e t, xprefix (xstop l e) t -> t = list_to_stop_trace l e.  *)
(* Proof. *)
(*   intros l e. induction l. *)
(*   + intros [] Hxpref; auto; inversion Hxpref; now subst.  *)
(*   + intros [] Hxpref; inversion Hxpref. subst.  *)
(*     simpl. now rewrite (IHl t).     *)
(* Qed. *)

(* Fixpoint list_to_silent_trace (l : list event) : trace := *)
(*   match l with *)
(*   | nil => tsilent *)
(*   | cons l ls => tcons l (list_to_silent_trace ls) *)
(*   end. *)

(* Lemma xsilent_prefix_list : forall p, xprefix (xsilent p) (list_to_silent_trace p). *)
(* Proof. *)
(*   induction p; simpl; auto.   *)
(* Qed. *)

(* Lemma unique_continuation_silent : forall l t, xprefix (xsilent l) t -> t = list_to_silent_trace l. *)
(* Proof.   *)
(*    intros l. induction l; intros [] Hxpref; auto; inversion Hxpref; subst.  *)
(*    simpl. now rewrite (IHl t).     *)
(* Qed.  *)
  
(* Lemma three_continuations_tbd : *)
(*   forall l t, xprefix (xtbd l) t -> *)
(*          ( (exists e, t = list_to_stop_trace l e) \/                                      *)
(*                  (t = list_to_silent_trace l) \/ *)
(*             (exists e, xprefix (xtbd (snoc l e)) t)).  *)
(* Proof. *)
(*   intros l. induction l. *)
(*   + intros [] Hxpref. *)
(*     ++ left. now exists e. *)
(*     ++ right. now left. *)
(*     ++ right. right. now exists e. *)
(*   + intros [] Hxpref; inversion Hxpref; subst. *)
(*     destruct  (IHl t) as [K1 | [K2 | K3]]; auto.   *)
(*     ++ left. destruct K1 as [e0 K1]. exists e0. simpl. now rewrite K1. *)
(*     ++ right. left. simpl. now rewrite K2. *)
(*     ++ right. right. destruct K3 as [e0 K3]. now exists e0. *)
(* Qed. *)

(* Lemma xpr_longer_stop_contra : forall p a e, xpr (xtbd (snoc p a)) (xstop p e) -> False. *)
(* Proof. *)
(*   induction p; auto. *)
(*   simpl. intros a0 e [Hfoo H]. now apply (IHp a0 e).  *)
(* Qed. *)

(* Lemma xpr_longer_silent_contra : forall p a, xpr (xtbd (snoc p a)) (xsilent p) -> False. *)
(* Proof. *)
(*   induction p; auto. *)
(*   simpl. intros a0 [Hfoo H]. now apply (IHp a0). *)
(* Qed.  *)

(* Lemma xpr_longer_xtbd_contra: forall p a, xpr (xtbd (snoc p a)) (xtbd p) -> False. *)
(* Proof. *)
(*   induction p; auto. *)
(*   simpl. intros a0 [Hfoo H]. now apply (IHp a0). *)
(* Qed.  *)

(* Lemma list_snoc_pointwise: forall (l p : list event) i1 i2 a1 a2, *)
(*                           i1 <> i2 -> *)
(*                           list_pref (snoc l i1) (snoc p a1) -> *)
(*                           list_pref (snoc l i2) (snoc p a2) -> *)
(*                           (i1 = a1 /\ i2 = a2). *)
(* Proof. *)
(*   induction l; intros p i1 i2 a1 a2 diff_i l1_pref l2_pref. *)
(*   + destruct p; inversion l1_pref; inversion l2_pref; auto.  *)
(*     subst. exfalso. now apply diff_i. *)
(*   + destruct p; simpl in l1_pref, l2_pref. *)
(*     ++ destruct l1_pref as [aa1 contra]. *)
(*        now destruct l. *)
(*     ++ destruct l1_pref as [ae l1_pref]. destruct l2_pref as [foo l2_pref]. *)
(*        now apply (IHl p i1 i2 a1 a2). *)
(* Qed.    *)

(* Lemma no_silent_and_stop: forall l1 l2 e, *)
(*     list_to_silent_trace l1 <> list_to_stop_trace l2 e. *)
(* Proof.   *)
(*   intros l. induction l; intros []; try now auto.  *)
(*   + intros e1. intros Hf. inversion Hf. *)
(*     apply ((IHl l0 e1) H1). *)
(* Qed.     *)

(* Lemma list_same_ext : forall l1 l2 t, *)
(*     list_pref_trace l1 t -> *)
(*     list_pref_trace l2 t -> *)
(*     list_pref l1 l2 \/ list_pref l2 l1. *)
(* Proof. *)
(*   induction l1; intros l2 t H1 H2. *)
(*   + now left. *)
(*   + destruct l2. *)
(*     ++ now right. *)
(*     ++ destruct t; inversion H1; inversion H2; subst. *)
(*        simpl. destruct (IHl1 l2 t); auto.  *)
(* Qed.  *)

(* Lemma xsilent_prefix_xftbd_prefix : forall p t, *)
(*     xprefix (xsilent p) t -> xprefix (xtbd p) t.  *)
(* Proof. *)
(*   induction p; intros t H; try now auto.   *)
(*   destruct t; inversion H; subst. simpl. *)
(*   split; auto. now apply (IHp t).  *)
(* Qed. *)

(* Lemma same_x_ext : forall x1 x2 t, xprefix x1 t -> xprefix x2 t -> xpr x1 x2 \/ xpr x2 x1.  *)
(* Proof. *)
(*   intros []; induction p; intros x2 t H1 H2.  *)
(*   + apply unique_continuation_stop in H1. subst. *)
(*     destruct x2. *)
(*     ++ destruct p. simpl in H2. subst. now left. *)
(*        simpl in *. contradiction. *)
(*     ++ destruct p. simpl in H2. subst. now right. *)
(*        simpl in *. contradiction. *)
(*     ++ destruct p. simpl in H2. contradiction. *)
(*        simpl in *. contradiction. *)
(*   + destruct t; simpl in H1; try contradiction.  *)
(*     inversion H1. subst. *)
(*     destruct x2. *)
(*     ++ destruct p0; simpl in H2. contradiction. *)
(*        inversion H2. subst. *)
(*        destruct (IHp (xstop p0 e1) t) as [K1 | K2]; auto.  *)
(*        +++ left. subst. simpl in *. firstorder. now rewrite H. *)
(*        +++ right. simpl in *. firstorder. now rewrite H. *)
(*     ++ destruct p0; simpl in H2. now right.  *)
(*        destruct (IHp (xtbd p0) t) as [K1 | K2]; auto.  *)
(*        +++ simpl. now destruct H2.   *)
(*        +++ right. simpl. firstorder. *)
(*     ++ apply unique_continuation_silent in H2.  *)
(*        apply unique_continuation_stop in H0. *)
(*        destruct p0; inversion H2.   *)
(*        rewrite H0 in H4. exfalso. symmetry in H4. *)
(*        now apply no_silent_and_stop in H4.      *)
(*   + left. now case x2. *)
(*   + destruct t; inversion H1; subst. *)
(*     destruct x2; simpl in H2. *)
(*     ++ destruct p0; inversion H2; subst. *)
(*        simpl. destruct (IHp (xstop p0 e0) t); auto.  *)
(*     ++ destruct p0; inversion H2; subst. *)
(*        simpl. now right. *)
(*        simpl. destruct (IHp (xtbd p0) t); auto.  *)
(*     ++ admit. *)
(*   + destruct t; try now auto. *)
(*     destruct x2; simpl in  H2;  *)
(*     destruct p; try now auto. *)
(*     now left.   *)
(*   + admit.     *)
(* Admitted. *)


(* Lemma ftbd_prefix_stop_sublist: forall l p e, ftbd_prefix l (list_to_stop_trace p e) -> list_pref l p.  *)
(* Proof. *)
(*   induction l; intros p e Hpref; auto. *)
(*   destruct p; inversion Hpref. *)
(*   subst. simpl. split; auto. now apply (IHl p e).  *)
(* Qed. *)

(* Lemma ftbd_prefix_silent_sublist: forall l p, ftbd_prefix l (list_to_silent_trace p) -> list_pref l p. *)
(* Proof. *)
(*   induction l; intros p Hpref; auto. *)
(*   destruct p; inversion Hpref. *)
(*   subst. simpl. split; auto. *)
(* Qed. *)

(* Lemma snocs_same_continuation: forall (l p : list event) e1 e2, *)
(*     list_pref (snoc l e1) p -> list_pref (snoc l e2) p -> e1 = e2.  *)
(* Proof. *)
(*   induction l; intros [] e1 e2 H1 H2; inversion H1; inversion H2; subst; auto.   *)
(*   now apply (IHl l0 e1 e2).    *)
(* Qed.  *)

(* Lemma snocs_aux_lemma: forall (l p : list event) i1 i2 a, *)
(*     i1 <> i2 -> list_pref (snoc l i1) (snoc p a) -> list_pref (snoc l i2) p -> False. *)
(* Proof. *)
(*   induction l; intros [] i1 i2 ev Hdiff Hpref1 Hpref2; *)
(*     inversion Hpref1; inversion Hpref2; subst. *)
(*   + now apply Hdiff.  *)
(*   + now apply (IHl l0 i1 i2 ev).      *)
(* Qed. *)

(*********************************************************************************)

Definition myXr (x1 x2: xpref) : Prop :=
  (xpr x1 x2) \/ (xpr x2 x1) \/
  (exists l i1 i2, is_input i1 /\
               is_input i2 /\
               i1 <> i2 /\
               xpr (xtbd (snoc l i1)) x1 /\
               xpr (xtbd (snoc l i2)) x2).


Lemma myXr_symmetric : forall x1 x2, myXr x1 x2 -> myXr x2 x1.
 Proof. firstorder. Qed. 

Lemma auXiliary_tstop :
  forall x2 l1 e1 t2, xprefix x2 t2 ->
                  traces_match (tstop l1 e1) t2 -> myXr (xstop l1 e1) x2.
Proof.
  intros x2 l1 e1 t2 xprefix2 [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]].
  + rewrite <- Heq in *. destruct (xsame_ext (xstop l1 e1) x2 (tstop l1 e1)); simpl; auto;
                          [now left |  right; now left].
  + destruct x2, t2; simpl in xprefix2; simpl in l_prefix1, l_prefix2; try now auto.   
    ++ inversion xprefix2; subst.  
       right. right. now exists ll, i1, i2.
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.  
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.
    ++ destruct (list_stream_same_ext l (snoc ll i2) s); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.  
    ++ subst. right. right. now exists ll, i1, i2. 
Qed. 

Lemma auXiliary_tsilent :
  forall x2 l1 t2, xprefix x2 t2 ->
                traces_match (tsilent l1) t2 -> myXr (xsilent l1) x2.
Proof.
  intros x2 l1 t2 xprefix2 [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]].
  + rewrite <- Heq in *. destruct (xsame_ext (xsilent l1) x2 (tsilent l1)); simpl; auto;
                          [now left |  right; now left].
   + destruct x2, t2; simpl in xprefix2; simpl in l_prefix1, l_prefix2; try now auto.   
    ++ inversion xprefix2; subst.  
       right. right. now exists ll, i1, i2.
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.  
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.
    ++ destruct (list_stream_same_ext l (snoc ll i2) s); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.  
    ++ subst. right. right. now exists ll, i1, i2.
Qed. 


Lemma auXiliary_xtbd:
  forall l1 l2 t1 t2, xprefix (xtbd l1) t1 -> xprefix (xtbd l2) t2 ->
                  traces_match t1 t2 -> myXr (xtbd l1) (xtbd l2).
Proof.
  intros l1 l2 t1 t2 xpref1 xpref2 [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]].
  + subst. destruct (xsame_ext (xtbd l1) (xtbd l2) t2); auto; [now left | right; now left]. 
  + assert (H1: xprefix (xtbd (snoc ll i1)) t1).
    { destruct t1; simpl in *; now auto. }
    assert (H2 : xprefix (xtbd (snoc ll i2)) t2).
    { destruct t2; simpl in *; now auto. }
    destruct (xsame_ext (xtbd l1) (xtbd (snoc ll i1)) t1) as [l1_shorter | l1_longer]; auto. 
    ++ destruct (xsame_ext (xtbd l2) (xtbd (snoc ll i2)) t2) as [l2_shorter | l2_longer]; auto.
       destruct (list_proper_or_equal _ _ l1_shorter) as [l1_ll | [a1 l1_ll]]; subst.
       * destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
          ** right. right. now exists ll, i1, i2. 
          ** apply list_pref_snoc_pref in l2_ll. right. left. simpl.
             apply (list_list_prefix_trans l2 ll _); auto. now apply snoc_longer.  
       * apply list_pref_snoc_pref in l1_ll.
         destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
         **  left. simpl. apply (list_list_prefix_trans l1 ll _ ); auto. now apply snoc_longer.  
         ** apply list_pref_snoc_pref in l2_ll. destruct (list_list_same_ext l1 l2 ll); auto;
                                                  [now left | right; now left].  
       * destruct (list_proper_or_equal  _ _ l1_shorter); auto; subst. 
         ** right. right. now exists ll, i1, i2.  
         ** destruct H as [a H]. apply list_pref_snoc_pref in H. left.
            simpl. apply (list_list_prefix_trans l1 ll l2); auto.
            simpl in l2_longer. apply (list_list_prefix_trans ll (snoc ll i2) l2); auto.
            now apply snoc_longer.  
    ++ destruct (xsame_ext (xtbd l2) (xtbd (snoc ll i2)) t2) as [l2_shorter | l2_longer]; auto.
       * destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
          ** right. right. now exists ll, i1, i2. 
          ** apply list_pref_snoc_pref in l2_ll. right. left. simpl.
             apply (list_list_prefix_trans l2 ll _); auto.
             apply (list_list_prefix_trans ll (snoc ll i1) _); auto. now apply snoc_longer.
        * right. right. now exists ll, i1, i2.
Qed.   
    

Lemma auXiliary_lemma (t1 t2 : trace) :
  traces_match t1 t2 ->
  forall x1 x2,  xprefix x1 t1 -> xprefix x2 t2 -> myXr x1 x2.
Proof.
  intros [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]] x1 x2 xprefix1 xprefix2. 
  - subst. unfold myXr. destruct (xsame_ext x1 x2 t2) as [go_left | go_right_left]; auto. 
  - destruct x1, x2.
    ++ destruct t1, t2; inversion xprefix1; inversion xprefix2; subst.
       right. right. now exists ll, i1, i2.
    ++ destruct t1; inversion xprefix1; subst.  
       apply (auXiliary_tstop (xtbd l0) l1 e0 t2); auto.
       right. now exists ll, i1, i2. 
    ++ destruct t1, t2; inversion xprefix1; inversion xprefix2; subst.
       simpl in *. right. right. now exists ll, i1, i2.
    ++ destruct t2; inversion xprefix2; subst. apply myXr_symmetric. 
       apply (auXiliary_tstop (xtbd l) l1 e0 t1); auto.
       right. exists ll, i2, i1. repeat (split; try now auto). 
    ++ apply (auXiliary_xtbd l l0 t1 t2); auto. right. now exists ll, i1, i2.  
    ++ destruct t2; inversion xprefix2; subst. apply myXr_symmetric.  
       apply (auXiliary_tsilent (xtbd l) l1 t1); auto.
       right. exists ll, i2, i1. repeat (split; try now auto).  
    ++ destruct t1, t2; inversion xprefix1; inversion xprefix2; subst.
       simpl in *. right. right. now exists ll, i1, i2.
    ++ destruct t1; inversion xprefix1; subst.   
       apply (auXiliary_tsilent (xtbd l0) l1 t2); auto.
       right. now exists ll, i1, i2.
    ++ destruct t1, t2; inversion xprefix1; inversion xprefix2; subst.
       simpl in *. right. right. now exists ll, i1, i2.   
Qed. 
  
Lemma teq_premises_myXr_holds : forall P1 P2,
    (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
    (forall Cs x1 x2, xsem (Cs [P1]) x1 -> xsem (Cs [P2]) x2 ->
                 myXr x1 x2).
Proof.
  intros P1 P2 H Cs x1 x2 [t1 [xpref1 sem1]] [t2 [xpref2 sem2]].
    rewrite (H Cs t1) in sem1.
   specialize (determinacy_src (Cs[P2]) t1 t2 sem1 sem2). 
   intros Hmatch. now apply (auXiliary_lemma t1 t2).
Qed.
    

Lemma  longest_in_xsem :
  forall W t, ~ sem tgt W t ->
    exists x, xprefix x t /\ xsem W x /\
     (forall x', xprefix x' t -> xsem W x' -> xpr x' x).
Proof.
  intros W [] HsemWt.  
  + destruct (list_longest_in_psem W l) as [ll [Hpref [Hpsem Hmax]]].
    exists (xtbd ll). repeat (split; try now auto). 
    intros [] Hx Hsemx.
    ++ inversion Hx; subst. destruct Hsemx as [tx [Hprefxtx Hsemx]].
       destruct tx; inversion Hprefxtx; subst. contradiction.  
    ++ simpl in *. apply Hmax; auto. 
    ++ inversion Hx. 
  + destruct (list_longest_in_psem W l) as [ll [Hpref [Hpsem Hmax]]].
    exists (xtbd ll). repeat (split; try now auto). 
    intros [] Hx Hsemx.
    ++ inversion Hx; subst.   
    ++ simpl in *. apply Hmax; auto. 
    ++ inversion Hx; subst. simpl in *.
       destruct Hsemx as [tx [Hprefxtx Hsemx]].
       destruct tx; inversion Hprefxtx; subst. contradiction.
  + destruct (tgt_sem (tstream s) W) as [l [ebad [Hseml [Hprefl Hnsem_longer]]]]; auto. 
    exists (xtbd l). simpl in *. repeat (split; try now auto).
    ++ apply (list_stream_prefix_trans l (snoc l ebad) s); auto.
       now apply snoc_longer.
    ++ intros [] Hpref_x HxsemW; try now inversion Hpref_x.   
       simpl in *. destruct (list_stream_same_ext l0 (snoc l ebad) s); auto.
       * apply list_proper_or_equal in H. destruct H as [H | [a H]].
         ** subst. exfalso. apply Hnsem_longer. destruct HxsemW as [tx [H1 H2]]. 
                 now exists tx. 
         ** now apply list_pref_snoc_pref in H.
       * exfalso. apply Hnsem_longer. destruct HxsemW as [tx [H1 H2]].
             exists tx. split; try now auto.
             destruct tx; simpl in *; try now apply (list_list_prefix_trans (snoc l ebad) l0 l1). 
             now apply (list_stream_prefix_trans (snoc l ebad) l0 s0).
Qed.


Definition  two_rRXC : Prop :=
  forall (r : xpref -> xpref -> Prop) P1 P2 ,
    ((forall Cs x1 x2, xsem (Cs [P1]) x1 ->
                  xsem (Cs [P2]) x2 ->
                   r x1 x2) ->
     (forall Ct x1 x2, xsem (Ct [P1 ↓]) x1 ->
                  xsem (Ct [P2 ↓]) x2 ->
                  r x1 x2)).

Lemma R2rXP_two : R2rXP <->  two_rRXC.
Proof. 
  rewrite R2rXP_R2rXC.  
  unfold R2rXP, two_rRXC. split.
  - intros H r P1 P2 H' Ct m1 m2 Hsem1 Hsem2.
    specialize (H Ct P1 P2 m1 m2 Hsem1 Hsem2).
    destruct H as [Cs [Hsem1' Hsem2']].
    specialize (H' Cs m1 m2 Hsem1' Hsem2'). now assumption.
  - intros H Ct P1 P2 m1 m2 Hsem1 Hsem2.
    specialize (H (fun m1 m2 => exists Cs, xsem (Cs [P1]) m1 /\ xsem (Cs [P2]) m2)); simpl in H.
    specialize (H P1 P2).    
    assert (H' : forall Cs m1 m2, xsem (Cs [P1]) m1 -> xsem (Cs [P2]) m2 ->
                             (exists Cs, xsem (Cs [P1]) m1 /\ xsem (Cs [P2]) m2)).
    { clear. intros Cs m1 m2 Hsem1 Hsem2. exists Cs; now auto. }
    specialize (H H' Ct m1 m2 Hsem1 Hsem2). now assumption.
Qed.


Lemma input_tot_consequence (W : prg tgt): forall l i1 i2,
    is_input i1 -> is_input i2 -> 
    xsem W (xtbd (snoc l i1)) -> xsem W (xtbd (snoc l i2)).
Proof.
  intros l i1 i2 Hi1 Hi2 [t [xpref_x_t Hsemt]].
  assert (psem W (ftbd  (snoc l i1))).
  { simpl in *. now exists t. }
  now apply (input_totality_tgt W l i1 i2) in H.
Qed.  

Lemma t_being_tstop_leads_to_contra (W1 W2 : prg tgt) t l2 e2 
                                    (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 (tstop l2 e2))
                                    (nsem12: ~ sem tgt W2 t)
                                    (xpref_x_t : xprefix (xtbd l2) t)
  : 
    (forall x1 x2, xsem W1 x1 -> xsem W2 x2 -> myXr x1 x2) -> False.
Proof.
 intros twoX. destruct t.
 - simpl in *. destruct (twoX (xstop l e) (xstop l2 e2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]].
   now exists (tstop l e). now exists (tstop l2 e2).
   + inversion xpr1; subst. contradiction.
   + inversion xpr2; subst. contradiction.                                
   + simpl in Hxpr1, Hxpr2.
     apply (list_list_prefix_trans (snoc xx i2) l2 l Hxpr2) in xpref_x_t.   
     destruct (list_list_same_ext (snoc xx i1) (snoc xx i2) l) as [F | F]; auto;
       apply Hdiff; apply (list_snoc_diff xx _ _ ) in F; congruence.
 - simpl in xpref_x_t.  destruct (twoX (xsilent l) (xstop l2 e2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]].
    now exists (tsilent l). try now exists (tstop l2 e2).  
    + now inversion xpr1.                              
    + now inversion xpr2.
    + simpl in Hxpr1, Hxpr2.
     apply (list_list_prefix_trans (snoc xx i2) l2 l Hxpr2) in xpref_x_t.   
     destruct (list_list_same_ext (snoc xx i1) (snoc xx i2) l) as [F | F]; auto;
       apply Hdiff; apply (list_snoc_diff xx _ _ ) in F; congruence.
 - simpl in xpref_x_t.
   destruct (tgt_sem (tstream s) W2 nsem12) as [l [ebad [Hpsem [Hpref Hnpsem]]]]; auto. 
   simpl in Hpref.
   destruct (twoX (xtbd (snoc l ebad)) (xstop l2 e2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]]; auto.  
   now exists (tstream s). now exists (tstop l2 e2).
   + simpl in xpr1. apply Hnpsem. now exists (tstop l2 e2).
   + simpl in *.
     apply (list_stream_prefix_trans _ _ s) in Hxpr1; auto.  
     apply (list_stream_prefix_trans _ _ s) in Hxpr2; auto.  
     destruct (list_stream_same_ext (snoc xx i1) (snoc xx i2) s) as [F | F]; auto;                              apply Hdiff; apply (list_snoc_diff xx _ _) in F; congruence.         
Qed. 

Lemma t_being_tsilent_leads_to_contra (W1 W2 : prg tgt) t l2  
                                      (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 (tsilent l2))
                                      (nsem12: ~ sem tgt W2 t)
                                      (xpref_x_t : xprefix (xtbd l2) t)
  : 
    (forall x1 x2, xsem W1 x1 -> xsem W2 x2 -> myXr x1 x2) -> False.
Proof.
 intros twoX. destruct t.
 - simpl in *. destruct (twoX (xstop l e) (xsilent l2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]].
   now exists (tstop l e). now exists (tsilent l2).
   + now inversion xpr1. 
   + now inversion xpr2.                                
   + simpl in Hxpr1, Hxpr2.
     apply (list_list_prefix_trans (snoc xx i2) l2 l Hxpr2) in xpref_x_t.   
     destruct (list_list_same_ext (snoc xx i1) (snoc xx i2) l) as [F | F]; auto;
       apply Hdiff; apply (list_snoc_diff xx _ _ ) in F; congruence.
 - simpl in xpref_x_t.  destruct (twoX (xsilent l) (xsilent l2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]].
    now exists (tsilent l). try now exists (tsilent l2).  
    + simpl in xpr1. now subst.                              
    + simpl in xpr2. now subst. 
    + simpl in Hxpr1, Hxpr2.
     apply (list_list_prefix_trans (snoc xx i2) l2 l Hxpr2) in xpref_x_t.   
     destruct (list_list_same_ext (snoc xx i1) (snoc xx i2) l) as [F | F]; auto;
       apply Hdiff; apply (list_snoc_diff xx _ _ ) in F; congruence.
 - simpl in xpref_x_t.
   destruct (tgt_sem (tstream s) W2 nsem12) as [l [ebad [Hpsem [Hpref Hnpsem]]]]; auto. 
   simpl in Hpref.
   destruct (twoX (xtbd (snoc l ebad)) (xsilent l2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]]; auto.  
   now exists (tstream s). now exists (tsilent l2).
   + simpl in xpr1. apply Hnpsem. now exists (tsilent l2).
   + simpl in *.
     apply (list_stream_prefix_trans _ _ s) in Hxpr1; auto.  
     apply (list_stream_prefix_trans _ _ s) in Hxpr2; auto.  
     destruct (list_stream_same_ext (snoc xx i1) (snoc xx i2) s) as [F | F]; auto;                              apply Hdiff; apply (list_snoc_diff xx _ _) in F; congruence.         
Qed. 
 

Lemma violates_xmax  (W1 W2 : prg tgt) t t2 p a aa
                     (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 t2)
                     (nsem12: ~ sem tgt W2 t)
                     (xpref_x_t : xprefix (xtbd (snoc p aa)) t)
                     (x_t2 : xprefix (xtbd (snoc p a)) t2)
                       
  :
    (forall x' : xpref, xprefix x' t -> xsem W2 x' -> xpr x' (xtbd p)) -> 
    (forall x1 x2, xsem W1 x1 -> xsem W2 x2 ->  myXr x1 x2) -> False.
Proof.
  intros xmax twoX.
  assert (xsem1 : xsem W1 (xtbd (snoc p aa))) by now exists t.
  assert (xsem2 : xsem W2 (xtbd (snoc p a))) by now exists t2.
  specialize (twoX (xtbd (snoc p aa)) (xtbd (snoc p a)) xsem1 xsem2).
  destruct twoX as [xpr1 | [xpr2 | matching]].
  + apply xpr_snoc in xpr1. subst.
    specialize (xmax (xtbd (snoc p a)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax.
  + apply xpr_snoc in xpr2. subst.
    specialize (xmax (xtbd (snoc p aa)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax.
  + destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff_is [Hxpr1 Hxpr2 ]]]]]]].
    simpl in Hxpr1, Hxpr2.  
    apply (list_snoc_pointwise xx p i1 i2 aa a) in Hxpr2; auto.  
    destruct Hxpr2 as [H1 H2]. subst.
    apply (input_tot_consequence W2 p a aa) in xsem2; auto. 
    specialize (xmax (xtbd (snoc p aa)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax. 
Qed. 
    

Theorem R2rXP_RTEP : R2rXP -> teq_preservation.
Proof.  
  rewrite R2rXP_two. unfold two_rRXC, teq_preservation.
  intros twoX P1 P2 Hsrc Ct t.
  specialize (twoX myXr P1 P2 (teq_premises_myXr_holds P1 P2 Hsrc) Ct).
  split.
  + intros case1.
    apply NNPP. intros t_not_sem2.
    destruct (longest_in_xsem (Ct [P2↓]) t t_not_sem2) as [x [xpref_x_t [xsem2_x x_max]]].
    destruct xsem2_x as [t2 [x_t2 t2_sem2]].
    destruct x.
    ++ (* it can only be t2 '=' xstop p e = t *)
       apply (unique_continuation_stop p e t) in xpref_x_t.
       apply (unique_continuation_stop p e t2) in x_t2.
       congruence.
    ++ destruct (three_continuations_tbd p t2 x_t2) as [t2stop | [t2silent | t2longer]].
       +++ now apply (t_being_tstop_leads_to_contra (Ct [P1↓]) (Ct [P2↓]) t t2 p).
         
       +++ now apply (t_being_tsilent_leads_to_contra  (Ct [P1↓]) (Ct [P2↓]) t t2 p).
         
       +++ destruct t2longer as [a t2longer].
           assert (xsem2 : xsem (Ct [P2↓]) (xtbd (snoc p a))) by now exists t2. 
           destruct (three_continuations_tbd p t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].
           - destruct ttstop as [e ttstop].
             assert (xsem1 : xsem (Ct [P1↓]) (xstop p e)).
             { exists t. split; auto.
               rewrite ttstop. now apply xstop_prefix_list. }
             specialize (twoX (xstop p e) (xtbd (snoc p a)) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1. 
             -- now apply xpr_longer_stop_contra in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2.
                apply (snocs_aux_lemma xx p i2 i1 a); congruence.       
           - assert (xsem1 : xsem (Ct [P1↓]) (xsilent p)).
             { exists t. split; auto.
               rewrite ttsilent. now apply xsilent_prefix_list. }
             specialize (twoX (xsilent p) (xtbd (snoc p a)) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1.
             -- now apply xpr_longer_silent_contra in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2.
                 apply (snocs_aux_lemma xx p i2 i1 a); congruence. 
           - destruct ttlonger as [aa ttlonger].
             now apply (violates_xmax (Ct [P1↓]) (Ct [P2↓]) t t2 p a aa).              
   ++ (*  it can only be t2 '=' xsilent p e = t *)
      apply (unique_continuation_silent p t) in xpref_x_t.
      apply (unique_continuation_silent p t2) in x_t2.
      congruence.
     
  + admit. (* symmetric case *)
Admitted. 

     
    