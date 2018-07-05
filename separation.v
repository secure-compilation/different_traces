Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.

CoInductive t_eq : trace -> trace -> Prop :=
| etrace : forall (e : event) t1 t2, t_eq t1 t2 -> t_eq (tcons e t1) (tcons e t2).

Lemma t_eq_symm : forall t1 t2, t_eq t1 t2 -> t_eq t2 t1.
Admitted.

Lemma prefix_preserved : forall m t1 t2, prefix m t1 -> t_eq t1 t2 -> prefix m t2.
Proof.
  intros m. induction m; intros t1 t2 hpref heq; try now auto.
  + now destruct t1, t2. 
  + destruct t1, t2; try now auto. inversion hpref. subst.   
    inversion heq. subst. simpl. split; try now auto.
    now apply (IHm t1 t2). 
Qed.

Lemma same_finite_prefixes : forall t1 t2, t_eq t1 t2 ->
                             forall m, (prefix m t1) <-> prefix m t2.
Proof.
  intros t1 t2 heq m. split; intros H;
  [now apply (prefix_preserved m t1 t2)
  |apply (prefix_preserved m t2 t1); try now auto].
  now apply t_eq_symm. 
Qed. 

Lemma neq_finitely_refutable : forall t1 t2,
    ~ (t_eq t1 t2) <-> (exists m1 m2, prefix m1 t1 /\ prefix m2 t2 /\ ~ (prefix m1 t2 /\ prefix m2 t1)).
Proof.
  intros t1 t2. split.
  - admit.
  - intros [m1 [m2 [h1 [h2 hn]]]] hf. apply hn. split.
    + now apply (same_finite_prefixes t1 t2).
    + apply t_eq_symm in hf. now apply (same_finite_prefixes t2 t1).
Admitted.


Axiom L : level. 

Definition ϕ_prg := prod nat (prg L). 
Definition ϕ_ctx  := prod nat (ctx L). 
Definition ϕ_plug : ϕ_prg -> ϕ_ctx -> ϕ_prg :=
  fun P C =>  (fst C , plug L (snd P) (snd C)).

Fixpoint length (m : finpref) : nat :=
  match m with
  | fstop | ftbd => 0
  | fcons x xs => S (length xs)
  end.

Fixpoint take_n (t : trace) (n : nat) : trace :=
  match n, t with
  | 0, _ | _ ,tstop => tstop
  | S m, tcons x xs => tcons x (take_n xs m)
 end.                               

Fixpoint take_nth_pref (t : trace) (n : nat) : finpref :=
  match n, t with
  | 0, _ | _ ,tstop => ftbd
  | S m, tcons x xs => fcons x (take_nth_pref xs m)
 end.                               

Lemma nth_pref_pref : forall t n, prefix (take_nth_pref t n) t.
Proof.
  intros t n. generalize dependent t. induction n; intros t; try now auto.
  destruct t; try now auto.
Qed. 

Lemma pref_take_pref : forall m t,
    prefix m t ->
    prefix m (take_n t (length m)).
Proof.
  intros m t. generalize dependent t. induction m; intros t hpref; try now auto.
  + destruct t; try now auto. 
    simpl in *. destruct hpref as [h1 h2]. split; try now auto.
Qed.   

Lemma take_embedding : forall t m,
    prefix m t -> 
    (take_n t (length m)) = embedding m.
Proof.
  intros t m. generalize dependent t. induction m; intros t hpref; try now auto.
  destruct t; try now auto. simpl in *. destruct hpref as [h1 h2].
  subst. now rewrite (IHm t).
Qed. 

Definition ϕ_sem : ϕ_prg -> prop :=
  fun P => 
  (fun t : trace =>
     exists m, t = embedding m /\ psem (snd P) m /\ length m <= (fst P)).

Lemma z_min : forall n, 0 <= n. 
Proof.
  induction n; try now auto.
Qed.

Lemma succ_leq : forall n m, n <= m -> S n <= S m.
Admitted.

Lemma leq_trans : forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Admitted.

Lemma length_take_n : forall n t,
    length (take_nth_pref t n) <= n.
Proof.
  intros n. induction n; intros t; try now auto.
  destruct t; try now auto.
  + simpl. now apply z_min.
  + simpl. apply succ_leq. now apply IHn.
Qed. 
  
Lemma length_smaller : forall P t,
    sem L (snd P) t -> length (take_nth_pref t (fst P)) <= fst P.  
Proof.
  intros P t hsem.
  now apply length_take_n.
Qed. 

Lemma non_empty_ϕ : forall P, exists t, ϕ_sem P t.
Proof.
  intros P. destruct (non_empty_sem L (snd P)) as [t h].
  exists (embedding (take_nth_pref t (fst P))). unfold ϕ_sem.
  exists (take_nth_pref t (fst P)). repeat (split; try now auto).
  + unfold psem. exists t. split; try now auto. now apply nth_pref_pref.
  + now apply length_smaller.  
Qed.

Lemma fpr_shorter: forall m1 m2, fpr m1 m2 -> length m1 <= length m2.
Proof.
  induction m1; intros m2 hpref; simpl; 
  try now apply z_min.
  + destruct m2; try now auto. inversion hpref; subst.
    simpl. apply succ_leq. now apply IHm1.
Qed.     

(*TODO : move to Tracemdel.v *)
Lemma prefix_embed_fpr : forall t m mm,
    prefix m t -> embedding mm = t ->
    fpr m mm.
Admitted.

(* intuition there in t in sem longer than m *)
Lemma psem_consequence : forall C P t m,
    ϕ_sem (ϕ_plug P C) t ->
    prefix m t ->  
    length m <= fst C.
Proof.
  intros C P t m [mm [hem [h1 h2]]] hpref. simpl in *. 
  assert (fpr m mm) by now apply (prefix_embed_fpr t m mm).    
  apply (leq_trans (length m) (length mm) (fst C)); try now auto. 
  now apply fpr_shorter. 
Qed. 
    
Definition ϕ := Build_level ϕ_plug
                            ϕ_sem
                            non_empty_ϕ.
                            

(**********************************************************)
(* RSP =/=> RPP                                           *) 
(**********************************************************)

Definition c : prg ϕ -> prg L :=
  fun Pn => snd Pn.

Definition c_RPP (P : prg ϕ) (π : prop) : Prop :=
  rsat P π -> rsat (c P) π.

Lemma C_robustly_safety : forall P S, Safety S -> c_RPP P S. 
Proof. 
  intros P S Hsafety. unfold c_RPP. rewrite contra.
  unfold rsat. repeat rewrite not_forall_ex_not.   
  intros [C hC]. unfold sat in *. rewrite not_forall_ex_not in *.
  destruct hC as [t hh]. rewrite not_imp in hh.
  destruct hh as [h1 h2]. destruct (Hsafety t h2) as [m [hpref hwit]]. 
  exists (length m, C). intros ff. simpl in ff. 
  specialize (hwit (take_n t (length m))). apply hwit.
  now apply pref_take_pref. apply ff. 
  
  
  (* two cases : + |m| <= snd P 
                                    

                 + |m| >= than snd P 
   *)
  
  (* specialize (hwit (take_n t (snd P))).  *)
  (* apply hwit. now apply (pref_take_pref m t).    *)
  (* apply ff. simpl. unfold ϕ_sem, ϕ_plug. exists m. repeat (split; simpl; try now auto). *)
  (* now apply take_embedding. now exists t.   *)
  (* apply (psem_consequence C P (take_n t (snd P)) ). unfold ϕ_sem, ϕ_plug; try now auto.   *)
  (* exists m. repeat (split; simpl; try now auto). *)
  (* now apply take_embedding. now exists t.  *)
                                  
Qed.

CoFixpoint an_omega := tcons an_event an_omega. 
CoFixpoint another_omega := tcons an_event another_omega.

Axiom an_omega_produced : exists P, forall C, sem L (plug L P C) an_omega.
Axiom another_omega_produced : exists P, forall C, sem L (plug L P C) another_omega.

Lemma not_equal: ~ t_eq an_omega another_omega.
Admitted.

Definition my_pi := fun t => fin t \/ t_eq t an_omega.

Lemma another_omega_not_in_my_pi : ~ my_pi another_omega.
Admitted. 

Lemma cut_lemma : forall C P t, sem ϕ (plug ϕ P C) t -> fin t.
Proof.
  intros C P t H. simpl in*.
  unfold ϕ_sem, ϕ_plug in *. destruct H as [m [hp H]]. rewrite hp.
  now apply embed_fin.
Qed.

Axiom some_ctx_L : ctx L. 

Theorem separation_RSP_RPP : (forall P π, Safety π -> c_RPP P π) /\ ~  (forall P π, c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H]. 
    specialize (ff (P, 42) my_pi). unfold c_RPP, rsat, sat in ff.
    simpl in ff. 
    assert (hh :  (forall (C : ctx ϕ) (t : trace), sem ϕ (ϕ_plug (P, 42) C) t -> my_pi t)).
    { intros C t H0. simpl in H0. unfold ϕ_sem, ϕ_plug in H0.
      destruct H0 as [m [hm H0]]. left. rewrite hm. 
      now apply embed_fin. } 
    specialize (ff  hh).  specialize (ff some_ctx_L another_omega).
    assert (sem L (some_ctx_L [P]) another_omega) by now apply (H some_ctx_L).
    specialize (ff H0). now apply another_omega_not_in_my_pi. 
Qed.     
    