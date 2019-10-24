Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences Semantics.
Require Import List.
Import ListNotations.
Require Import Machine MachineStackLimited.
Require Import LanguageModel TraceModel ChainModel.
Require Import TraceCriterion.
Require Import Compiler.
Require Import Stream.
Require Import ClassicalExtras.
Require Import ResourceExhaustion.
Require Import Logic.Classical.
Require Import Logic.IndefiniteDescription.

Set Bullet Behavior "Strict Subproofs".

(** * 3. Semantic preservation *)

(** ** Correctness of generated code for expressions. *)

(** Remember the informal specification we gave for the code generated
  for an arithmetic expression [a].  It should
- execute in sequence (no branches)
- deposit the value of [a] at the top of the stack
- preserve the variable state.

We now prove that the code [compile_aexp a] fulfills this contract.
The proof is a nice induction on the structure of [a]. *)
Ltac choose_side stk :=
  destruct (stack_limit <=? length stk) eqn:Hstk;
  [right; rewrite Nat.leb_le in Hstk 
  | left; rewrite leb_iff_conv in Hstk].


Ltac compile_aexp_correct_simpl_t trans_thm :=
  apply star_one;
  econstructor; last eassumption;
  apply trans_thm; eauto with codeseq.

Ltac compile_aexp_correct_compl_t IHa2' trans_thm :=
  eapply starans; first eauto;
  replace [] with ([] ++ [] : list nat); last reflexivity;
  eapply starans;
  [eapply IHa2' |
   apply star_one; normalize; econstructor;
   [apply trans_thm; eauto with codeseq | eassumption]].


Lemma compile_aexp_correct:
  forall C st a pc stk,
    codeseq_at C pc (compile_aexp a) ->
    star (transition_limited C)
            (Some (pc, stk, st)) nil
            (Some (pc + length (compile_aexp a), aeval st a :: stk, st)) \/
      star (transition_limited C) (Some (pc, stk, st)) nil None.
Proof.
  intros C st a. 
  (* rewrite <- Nat.leb_le. *)
  (* destruct (stack_limit <=? length stk) eqn:Hlt. *)
  (* now left. *)
  (* right. *)
  (* rewrite leb_iff_conv in Hlt. *)
  (* revert pc stk H Hlt. *)
  induction a; simpl; intros.
  - (* ANum *)
    choose_side (n :: stk);
      compile_aexp_correct_simpl_t trans_const.
  - (* AId *)
    choose_side (st i :: stk);
      compile_aexp_correct_simpl_t trans_var.
  - (* APlus *)
    replace ([] : list nat) with ([] ++ []: list nat); last reflexivity.
    replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk); last reflexivity.
    edestruct IHa1 as [IHa1' | IHstk1]; edestruct IHa2 as [IHa2' | IHstk2]; eauto with codeseq.
    + choose_side ([aeval st a1 + aeval st a2] ++ stk).
      * compile_aexp_correct_compl_t IHa2' trans_add.
      * compile_aexp_correct_compl_t IHa2' trans_add.
    + right. eapply starans. eauto.
      assumption.
  - (* AMinus *)
    replace ([] : list nat) with ([] ++ []: list nat); last reflexivity.
    replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk); last reflexivity.
    edestruct IHa1 as [IHa1' | IHstk1]; edestruct IHa2 as [IHa2' | IHstk2]; eauto with codeseq.
    + choose_side ([aeval st a1 + aeval st a2] ++ stk).
      * compile_aexp_correct_compl_t IHa2' trans_sub.
      * compile_aexp_correct_compl_t IHa2' trans_sub.
    + right. eapply starans. eauto.
      assumption.
  - (* APlus *)
    replace ([] : list nat) with ([] ++ []: list nat); last reflexivity.
    replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk); last reflexivity.
    edestruct IHa1 as [IHa1' | IHstk1]; edestruct IHa2 as [IHa2' | IHstk2]; eauto with codeseq.
    + choose_side ([aeval st a1 + aeval st a2] ++ stk).
      * compile_aexp_correct_compl_t IHa2' trans_mul.
      * compile_aexp_correct_compl_t IHa2' trans_mul.
    + right. eapply starans. eauto.
      assumption.
      Unshelve.
      all: exact stk.
Qed.

(** Here is a similar proof for the compilation of boolean expressions. *)
Ltac compile_bexp_correct_simpl_t trans_thm ofs :=
  apply star_one;
  econstructor; last eassumption;
  apply trans_thm with ofs; eauto with codeseq.

Ltac compile_bexp_correct_compl_t st a a0 ofs trans_thm:=
  destruct (beq_nat (aeval st a) (aeval st a0)) eqn:Heq;
          simpl;
          (replace [] with ([] ++ [] : list nat); last reflexivity);
          eapply starans; eauto with codeseq;
            (replace [] with ([] ++ [] : list nat); last reflexivity);
            eapply starans; eauto with codeseq;
              apply star_one;
              econstructor; eauto;
                [eapply trans_thm with ofs | eapply trans_thm with ofs];
                eauto with codeseq.

Lemma compile_bexp_correct:
  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (transition_limited C)
          (Some (pc, stk, st)) nil
          (Some (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st)) \/
  star (transition_limited C)
          (Some (pc, stk, st)) nil
          None.
Proof.
  induction b; simpl; intros.
  - (* BTrue *)
    destruct cond; simpl;
      [| left; repeat rewrite plus_0_r; apply star_refl].
    destruct (stack_limit <=? length stk) eqn:Hstk;
      [ rewrite Nat.leb_le in Hstk
      | rewrite leb_iff_conv in Hstk].
    + right. compile_bexp_correct_simpl_t trans_branch_forward ofs.
    + left. compile_bexp_correct_simpl_t trans_branch_forward ofs.
  - (* BFalse *)
    destruct cond; simpl;
      [left; repeat rewrite plus_0_r; apply star_refl|].
    destruct (stack_limit <=? length stk) eqn:Hstk;
      [ rewrite Nat.leb_le in Hstk
      | rewrite leb_iff_conv in Hstk].
    + right. compile_bexp_correct_simpl_t trans_branch_forward ofs.
    + left. compile_bexp_correct_simpl_t trans_branch_forward ofs.
  - (* BEq *)
    edestruct compile_aexp_correct with (a := a); first eauto with codeseq;
      edestruct compile_aexp_correct with (a := a0); first eauto with codeseq;
        (destruct (stack_limit <=? length stk) eqn:Hstk;
        [ rewrite Nat.leb_le in Hstk
        | rewrite leb_iff_conv in Hstk]);
        try (right;
             replace [] with ([] ++ [] : list nat); last reflexivity;
             eapply starans; now eauto);
        eauto with codeseq.
    + destruct cond; right;
        [ compile_bexp_correct_compl_t st a a0 ofs trans_beq
        | compile_bexp_correct_compl_t st a a0 ofs trans_bne].
    + destruct cond; left;
        try (compile_bexp_correct_compl_t st a a0 ofs trans_beq; normalize; rewrite Heq; omega);
        try (compile_bexp_correct_compl_t st a a0 ofs trans_bne; normalize; rewrite Heq; omega).
  - (* BLe *)
    edestruct compile_aexp_correct with (a := a); first eauto with codeseq;
      edestruct compile_aexp_correct with (a := a0); first eauto with codeseq;
        (destruct (stack_limit <=? length stk) eqn:Hstk;
        [ rewrite Nat.leb_le in Hstk
        | rewrite leb_iff_conv in Hstk]);
        try (right;
             replace [] with ([] ++ [] : list nat); last reflexivity;
             eapply starans; now eauto);
        eauto with codeseq.
    + destruct cond; right;
        [ compile_bexp_correct_compl_t st a a0 ofs trans_ble
        | compile_bexp_correct_compl_t st a a0 ofs trans_bgt].
    + destruct cond; left;
        try (compile_bexp_correct_compl_t st a a0 ofs trans_ble; normalize; rewrite Heq; omega);
        try (compile_bexp_correct_compl_t st a a0 ofs trans_bgt; normalize; rewrite Heq; omega).
      try (destruct (aeval st a <=? aeval st a0) eqn:Hle; eauto;
           compile_bexp_correct_compl_t st a a0 ofs trans_ble; normalize; rewrite Hle; omega).
      try (destruct (aeval st a <=? aeval st a0) eqn:Hle; eauto;
           compile_bexp_correct_compl_t st a a0 ofs trans_bgt; normalize; rewrite Hle; omega).
      (* very ugly *)
  - (* BNot *)
    replace (eqb (negb (beval st b)) cond)
    with (eqb (beval st b) (negb cond)).
    apply IHb; auto. 
    destruct (beval st b); destruct cond; auto.

  - (*BAnd *)
    replace ([] : list nat) with ([] ++ []: list nat); last reflexivity.
    edestruct IHb1 as [IHb1' | IHstk1]; edestruct IHb2 as [IHb2' | IHstk2]; eauto with codeseq;
      (destruct (stack_limit <=? length stk) eqn:Hstk;
       [ rewrite Nat.leb_le in Hstk
       | rewrite leb_iff_conv in Hstk]).
    + destruct cond; left.
      * eapply starans; eauto;
          destruct (beval st b1); destruct (beval st b2); simpl in *;
            normalize; eauto;
              eapply star_refl.
      * destruct (beval st b1); destruct (beval st b2); simpl in *;
          normalize; eauto;
        (replace [] with ([] ++ [] : list nat); last reflexivity);
        eapply starans; eauto;
        rewrite <- plus_assoc; rewrite (plus_comm ofs); rewrite plus_assoc;
          apply star_refl.
    + destruct cond; left.
      * eapply starans; eauto;
          destruct (beval st b1); destruct (beval st b2); simpl in *;
            normalize; eauto;
              eapply star_refl.
      * destruct (beval st b1); destruct (beval st b2); simpl in *;
          normalize; eauto;
        (replace [] with ([] ++ [] : list nat); last reflexivity);
        eapply starans; eauto;
        rewrite <- plus_assoc; rewrite (plus_comm ofs); rewrite plus_assoc;
          apply star_refl.
    + set (code_b2 := compile_bexp b2 cond ofs) in *.
      set (ofs' := if cond then length code_b2 else ofs + length code_b2) in *.
      set (code_b1 := compile_bexp b1 false ofs').
      destruct cond, (beval st b1), (beval st b2);
        try (now right; eapply starans; eauto; simpl; rewrite plus_0_r; eauto);
        try (now left; normalize; eauto);
        try (now left; subst ofs'; normalize; rewrite <- plus_assoc; rewrite <- (plus_comm ofs); eauto).
    + set (code_b2 := compile_bexp b2 cond ofs) in *.
      set (ofs' := if cond then length code_b2 else ofs + length code_b2) in *.
      set (code_b1 := compile_bexp b1 false ofs').
      destruct cond, (beval st b1), (beval st b2);
        try (now right; eapply starans; eauto; simpl; rewrite plus_0_r; eauto);
        try (now left; normalize; eauto);
        try (now left; subst ofs'; normalize; rewrite <- plus_assoc; rewrite <- (plus_comm ofs); eauto).
      Unshelve.
      all: exact nil.
      Grab Existential Variables.
      all: eauto.
Qed.

(** ** Correctness of generated code for commands: terminating case. *)

Lemma compile_com_correct_terminating:
  forall C st c st' l,
  c / st \\ st' --> l ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star (transition_limited C)
       (Some (pc, stk, st)) l
       (Some (pc + length (compile_com c), stk, st')) \/
  exists l', list_list_prefix l' l /\
  star (transition_limited C)
          (Some (pc, stk, st)) l'
          None.
Proof.
  induction 1; intros stk pc AT.

- (* SKIP *)
  simpl in *. rewrite plus_0_r. left. apply star_refl.

- (* := *)
  simpl in *. subst n.
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  edestruct compile_aexp_correct; eauto with codeseq.
  + choose_side stk;
      [exists ([] ++ []); split; [now simpl |] |];
      eapply starans; try eassumption;
        eapply star_one;
        [eapply transition_OOM | eapply transition_some]; eauto;
          normalize; eapply trans_setvar; eauto with codeseq.
  + right.
    exists [].
    split; first now simpl.
    eassumption.

- (* sequence *)
  edestruct IHceval1; edestruct IHceval2;
    eauto with codeseq.
  + left.
    eapply starans; eauto.
    destruct c1; repeat (normalize; eauto).
  + right.
    destruct H2 as [l'0 [H3 H2]].
    exists (l ++ l'0); split; eauto.


    now apply list_list_prefix_app. (* trivial *)
    eapply starans; eauto.
  + right.
    destruct H1 as [l1' [H3 H1]].
    exists l1'. split; eauto.
    eapply list_list_prefix_trans. eauto.
    replace l with (l ++ []); last apply app_nil_r. rewrite <- app_assoc.
    now apply list_list_prefix_app.
  + destruct H1 as [l1' [H3 H1]].
    right.
    exists l1'. split; eauto.
    eapply list_list_prefix_trans; eauto.
    replace l with (l ++ []); last apply app_nil_r. rewrite <- app_assoc.
    now apply list_list_prefix_app.

- (* if true *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  replace l with ([] ++ l); last reflexivity.
  edestruct compile_bexp_correct with (b := b); edestruct IHceval;
    eauto with codeseq.
  + rewrite H in *;
      choose_side stk; [exists l; split; first (simpl; apply list_list_prefix_ref);
                          try replace l with ([] ++ l); last reflexivity |];
        eapply starans;
        try eassumption;
        simpl; fold codeb; normalize;
          replace l with (l ++ []); try apply app_nil_r;
            eapply starans; try eassumption;
              apply star_one;
              econstructor; try eassumption;
                eapply trans_branch_forward; eauto with codeseq; omega.
  + destruct H2 as [l' [Hpref Hstar]].
    right; exists l'; split; eauto.
    fold codeb in H1; rewrite H in *; normalize.
    replace l' with ([] ++ l'); last reflexivity.
    eapply starans; eauto.
  + right; exists []; split; now eauto.
  + right; exists []; split; now eauto.

- (* if false *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  replace l with ([] ++ l); last reflexivity.
  edestruct compile_bexp_correct with (b := b) (cond := false); edestruct IHceval;
    eauto with codeseq.
  + rewrite H in *;
     left; 
     eapply starans;
     try eassumption;
     simpl; fold codeb; normalize;
       replace (pc + length codeb + length code1 + S(length code2))
         with (pc + length codeb + length code1 + 1 + length code2);
       eauto; omega.
  + destruct H2 as [l' [Hpref Hstar]].
    right; exists l'; split; eauto.
    fold codeb in H1; rewrite H in *; normalize.
    replace l' with ([] ++ l'); last reflexivity.
    eapply starans; normalize; eauto.
  + right; exists []; split; now eauto.
  + right; exists []; split; now eauto.

- (* while false *)
  simpl in *. 
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  edestruct compile_bexp_correct; eauto with codeseq.
  + left; eapply starans; eauto; rewrite H; simpl; normalize;
    apply star_refl.
  + right; exists []; now split.

- (* while true *)
  edestruct compile_bexp_correct; eauto with codeseq.
  + rewrite H in *; simpl in *.
    edestruct IHceval1; eauto with codeseq.
    * edestruct IHceval2; eauto with codeseq.
      -- choose_side stk.
         ++ exists (l ++ []). split; last first.
            eapply starans.
            replace l with ([] ++ l); try reflexivity.
            eapply starans; eauto.
            replace l with (l ++ []); last apply app_nil_r.
            rewrite plus_0_r.
            eapply starans. eauto.
            eapply star_one.
            econstructor. eapply trans_branch_backward.
            eauto with codeseq; omega. reflexivity. eauto. eapply star_refl.
            now apply list_list_prefix_app.
         ++ eapply starans.
            replace l with ([] ++ l); try reflexivity.
            eapply starans; eauto.
            replace l with (l ++ []); last apply app_nil_r.
            rewrite plus_0_r.
            eapply starans. eauto.
            eapply star_one.
            eapply transition_some.
            eapply trans_branch_backward.
            eauto with codeseq; omega. reflexivity. eauto. 
            normalize.
            replace (pc +
                     length (compile_bexp b false (length (compile_com c) + 1)) + length (compile_com c) + 1 -
                     (length (compile_bexp b false (length (compile_com c) + 1)) + length (compile_com c) + 1))
              with pc; last omega.
            eauto.
      -- destruct H4 as [l'0 [Hpref Hstar]].
         destruct (stack_limit <=? length stk) eqn:Hstk;
           [rewrite Nat.leb_le in Hstk | rewrite leb_iff_conv in Hstk].
         ++ right.
            exists (l ++ []); split; first now apply list_list_prefix_app.
            eapply starans.
            replace l with ([] ++ l); try reflexivity.
            eapply starans; eauto.
            replace l with (l ++ []); last apply app_nil_r.
            rewrite plus_0_r.
            eapply starans. eauto.
            eapply star_one.
            econstructor.
            eapply trans_branch_backward.
            eauto with codeseq; omega. reflexivity. eauto.
            eapply star_refl.
         ++ right.
            exists (l ++ l'0); split; first now apply list_list_prefix_app.
            eapply starans.
            replace l with ([] ++ l); try reflexivity.
            eapply starans; eauto.
            replace l with (l ++ []); last apply app_nil_r.
            rewrite plus_0_r.
            eapply starans. eauto.
            eapply star_one.
            eapply transition_some.
            eapply trans_branch_backward.
            eauto with codeseq; omega. reflexivity. eauto.
            normalize.
            replace (pc +
                     length (compile_bexp b false (length (compile_com c) + 1)) + length (compile_com c) + 1 -
                     (length (compile_bexp b false (length (compile_com c) + 1)) + length (compile_com c) + 1))
              with pc; last omega.
            eauto.
    * destruct H3 as [l'0 [Hpref Hstar]].
      right; exists ([] ++ l'0); split.
      simpl. eapply list_list_prefix_trans; eauto.
      replace l with (l ++ []); last apply app_nil_r. rewrite <- app_assoc.
      now apply list_list_prefix_app.
      eapply starans. eauto. rewrite plus_0_r; eauto.
  + right; exists []; split; now eauto.

- (* output *)
  simpl in *. subst n.
  edestruct compile_aexp_correct; eauto with codeseq.
  + choose_side stk.
    * exists [].
      replace [] with ([] ++ [] : list nat); last reflexivity.
      split; first now auto.
      eapply starans. eauto.
      apply star_one. 
      eapply transition_OOM; eauto.
      econstructor; eauto with codeseq.
    * replace [aeval st a] with ([] ++ [aeval st a]); last reflexivity.
      eapply starans; eauto.
      apply star_one.
      econstructor; eauto.
      normalize; eapply trans_out; eauto with codeseq.
  + right; eexists; split; now eauto.
    Unshelve.
    all: eauto.
Qed.

Theorem compile_program_correct_terminating:
  forall c st st' l,
  c / st \\ st' --> l ->
  mach_terminates (compile_program c) st st' l \/
  exists l', list_list_prefix l' l /\ mach_OOM (compile_program c) st l'.
Proof.
  intros. unfold compile_program. 
  edestruct compile_com_correct_terminating with (pc := 0);
    eauto.
  eapply codeseq_at_intro with (C1 := nil); eauto.
  left. red.
    exists (length (compile_com c)); split.
    apply code_at_app. auto.
    eauto.
Qed.


(** ** Correctness of generated code for commands: general case. *)

(** We would like to strengthen the correctness result above so that it
  is not restricted to terminating source programs, but also applies to
  source program that diverge.  To this end, we abandon the big-step
  semantics for commands and switch to the small-step semantics with continuations.
  We then show a simulation theorem, establishing that every transition_limited
  of the small-step semantics in the source program is simulated (in a sense
  to be made precise below) by zero, one or several transition_limiteds of the
  machine executing the compiled code for the source program. *)

(** Our first task is to relate configuration_limiteds [(c, k, st)] of the small-step
  semantics with configuration_limiteds [(C, pc, stk, st)] of the machine.
  We already know how to relate a command [c] with the machine code,
  using the [codeseq_at] predicate.  What needs to be defined is a relation
  between the continuation [k] and the machine code.

  Intuitively, when the machine finishes executing the generated code for
  command [c], that is, when it reaches the program point
  [pc + length(compile_com c)], the machine should continue by executing
  instructions that perform the pending computations described by
  continuation [k], then reach an [Ihalt] instruction to stop cleanly.

  We formalize this intution by the following inductive predicate
  [compile_cont C k pc], which states that, starting at program point [pc],
  there are instructions that perform the computations described in [k]
  and reach an [Ihalt] instruction. *)

Inductive compile_cont (C: code): cont -> nat -> Prop :=
  | ccont_stop: forall pc,
      code_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      codeseq_at C pc (compile_com c) ->
      pc' = pc + length (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc ofs pc' pc'',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      codeseq_at C pc' (compile_com (WHILE b DO c END)) ->
      pc'' = pc' + length (compile_com (WHILE b DO c END)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall ofs k pc pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      compile_cont C k pc' ->
      compile_cont C k pc.

(** Then, a configuration_limited [(c,k,st)] of the small-step semantics matches
  a configuration_limited [(C, pc, stk, st')] of the machine if the following conditions hold:
- The memory states are identical: [st' = st].
- The machine stack is empty: [stk = nil].
- The machine code at point [pc] is the compiled code for [c]:
  [codeseq_at C pc (compile_com c)].
- The machine code at point [pc + length (compile_com c)] matches continuation
  [k], in the sense of [compile_cont] above.
*)

Inductive match_config_lim (C : code) : com * cont * state -> configuration_limited -> Prop :=
| match_config_lim_intro : forall c k st pc,
      codeseq_at C pc (compile_com c) ->
      compile_cont C k (pc + length (compile_com c)) ->
      match_config_lim C (c, k, st) (Some (pc, nil, st)).



(** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
After trial and error, we find that the following measure works.  It is
the sum of the sizes of the command [c] under focus and all the commands
appearing in the continuation [k]. *)


(** A few technical lemmas to help with the simulation proof. *)

Lemma compile_cont_Kstop_inv:
  forall C pc m,
  compile_cont C Kstop pc ->
  exists pc',
    star (transition_limited C) (Some (pc, nil, m)) [] (Some (pc', nil, m))
  /\ code_at C pc' = Some Ihalt.
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. auto.
- destruct IHcompile_cont as [pc'' [A B]]; auto.
  exists pc''; split; auto.
  replace (star (transition_limited C) (Some (pc, [], m)) [] (Some (pc'', [], m)))
          with (star (transition_limited C) (Some (pc, [], m)) ([] ++ []) (Some (pc'', [], m))).
  eapply star_step; eauto. econstructor.  eapply trans_branch_forward; eauto.
  unfold stack_limit. simpl; omega.
  reflexivity.
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc m,
  compile_cont C (Kseq c k) pc ->
  exists pc',
    star (transition_limited C) (Some (pc, nil, m)) [] (Some (pc', nil, m))
  /\ codeseq_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + length(compile_com c)).
Proof.
  intros. dependent induction H. 
  exists pc; split. apply star_refl. split; congruence. 
  destruct (IHcompile_cont _ _ eq_refl) as [pc'' [A [B D]]].
  exists pc''; split; auto. 
  replace (star (transition_limited C) (Some (pc, [], m)) [] (Some (pc'', [], m)))
          with (star (transition_limited C) (Some (pc, [], m)) ([] ++ []) (Some (pc'', [], m))).
  eapply star_step; eauto.
  econstructor.
  eapply trans_branch_forward; eauto.
  unfold stack_limit; simpl; omega.
  reflexivity. 
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc m,
  compile_cont C (Kwhile b c k) pc ->
  exists pc', 
  plus (transition_limited C) (Some (pc, nil, m)) [] (Some (pc', nil, m))
  /\ codeseq_at C pc' (compile_com (WHILE b DO c END))
  /\ compile_cont C k (pc' + length(compile_com (WHILE b DO c END))).
Proof.
  intros. dependent induction H.
- exists (pc + 1 - ofs); split.
  apply plus_one. econstructor.
  eapply trans_branch_backward; eauto.
  unfold stack_limit; simpl; omega.
  split; congruence.
- destruct (IHcompile_cont _ _ _ (refl_equal _)) as [pc'' [A [B D]]].
  exists pc''; split; auto.
  replace (plus (transition_limited C) (Some (pc, [], m)) [] (Some (pc'', [], m))) with
      (plus (transition_limited C) (Some (pc, [], m)) ([] ++ []) (Some (pc'', [], m))).

  eapply plus_left. eapply transition_some. eapply trans_branch_forward; eauto.
  unfold stack_limit; simpl; omega.
  apply plus_star; eauto.
  reflexivity.
Qed.

Lemma match_config_lim_skip:
  forall C k m pc,
  compile_cont C k pc ->
  match_config_lim C (SKIP, k, m) (Some (pc, nil, m)).
Proof.
  intros C.
  assert (forall k pc, compile_cont C k pc -> codeseq_at C pc nil).
    induction 1.
    eapply code_at_codeseq; eauto.
    change (compile_com c) with (nil ++ compile_com c) in H. eauto with codeseq.
    eapply code_at_codeseq; eauto.
    eapply code_at_codeseq; eauto.
  intros. constructor. simpl. eauto. simpl. rewrite plus_0_r; auto.
Qed.

(** At long last, we can state and prove the right simulation diagram. *)

Lemma simulation_step:
  forall C impstate1 impstate2 machstate1 l,
  kstep impstate1 l impstate2 ->
  match_config_lim C impstate1 machstate1 ->
  exists machstate2 l',
      (plus (transition_limited C) machstate1 l' machstate2
       \/ (star (transition_limited C) machstate1 l' machstate2 /\ measure impstate2 < measure impstate1))
   /\ ((match_config_lim C impstate2 machstate2 /\ l = l') \/ (machstate2 = None /\ list_list_prefix l' l)).
Proof.
  intros until l; intros KSTEP MATCH. 
  inversion KSTEP; clear KSTEP; subst; inversion MATCH; clear MATCH; subst; simpl in *.

- (* assign *)
  edestruct compile_aexp_correct; eauto with codeseq.
  + eexists; eexists; split. left.
    replace [] with ([] ++ [] : list nat); last reflexivity.
    eapply plus_right. eauto.
    eapply transition_some.
    eapply trans_setvar; eauto with codeseq.
    unfold stack_limit; simpl; omega.
    left; split; eauto.
    normalize. apply match_config_lim_skip. auto.
  + eexists; eexists; split. left.
    replace [] with ([] ++ [] : list nat); eauto.
    inversion H; subst.
    assert (l1 = []) by now induction l1. subst. simpl in *.
    econstructor; eauto; subst; eauto.
    now right.

- (* seq *)
  econstructor; eexists; split.
  right; split. apply star_refl. omega. 
  normalize. left; split; auto. constructor. eauto with codeseq.
  eapply ccont_seq; eauto with codeseq.

- (* if true *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  edestruct compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1);
    eauto with codeseq.
  + eexists; eexists; split.
    right; split; eauto; omega.
    left. rewrite H; simpl; fold codeb; normalize.
    split; auto.
    constructor; eauto with codeseq.
    eapply ccont_branch; eauto with codeseq.
    change (S (length code2)) with (1 + length code2) in *; normalize; auto.
  + exists None; eexists. split.
    right; split; eauto; omega.
    now right.

- (* if false *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  edestruct compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1);
    eauto with codeseq.
  + eexists; eexists; split.
    right; split; eauto; omega.
    left; split; auto. rewrite H; simpl; fold codeb; normalize.
    constructor; eauto with codeseq.
    change (S (length code2)) with (1 + length code2) in H5; normalize; auto.
  + exists None; eexists. split.
    right; split; eauto; omega.
    now right.

- (* while true *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  edestruct compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1);
    eauto with codeseq.
  + eexists; eexists; split.
    right; split; eauto; omega.
    left. rewrite H; simpl; fold codeb; normalize.
    split; auto.
    constructor; eauto with codeseq.
    fold codec.
    assert (PC: pc + length codeb + length codec + 1 - (length codeb + length codec + 1) = pc)
      by omega.
    eapply ccont_while; eauto with codeseq. rewrite PC; auto.
    rewrite PC; simpl; normalize; auto.
  + exists None; eexists. split; eauto.
    right; split; eauto; omega.
    now right.

- (* while false *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  edestruct compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1);
    eauto with codeseq.
  + eexists; eexists; split.
    right; split.
    eauto. 
    generalize (com_size_nonzero c). omega.
    rewrite H; simpl; fold codeb; normalize; left; split; auto; apply match_config_lim_skip; auto.
  + exists None; eexists; split.
    right; split; eauto.
    generalize (com_size_nonzero c). omega.
    now right.

- (* skip seq *)
  normalize.
  destruct (compile_cont_Kseq_inv _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; eexists; split.
  right; split. eexact X. omega.
  left; split; auto; constructor; auto. 

- (* skip while *)
  normalize.
  destruct (compile_cont_Kwhile_inv _ _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; eexists; split.
  left. eexact X. 
  left; split; auto; constructor; auto.

- (* out *)
  edestruct compile_aexp_correct; eauto with codeseq.
  + eexists; eexists; split. left.
    replace [aeval st a] with ([] ++ [aeval st a] : list nat); last reflexivity.
    eapply plus_right. eauto.
    eapply transition_some.
    eapply trans_out; eauto with codeseq.
    unfold stack_limit; simpl; omega.
    left.
    normalize. split; auto. apply match_config_lim_skip. auto.
  + eexists; eexists; split. left.
    replace [] with ([] ++ [] : list nat); eauto.
    inversion H; subst.
    assert (l1 = []) by now induction l1. subst. simpl in *; subst.
    econstructor; eauto; subst; eauto.
    now right.
Qed.

(** Simulation diagrams such as [simulation_step] above imply semantic preservation
  for terminating programs and for diverging programs.  We now develop a generic
  proof of this fact that we can reuse later for other program transformations. *)

Section SIMULATION_DIAGRAM.

(** The generic proof is parameterized over the small-step semantics for the
  source and target languages, and over an invariant between their states. *)

  Variable event : Type.

  Variable state1: Type.	     (**r the type of configuration_limiteds for the source language *)
  Variable step1: state1 -> list event -> state1 -> Prop.   (**r the small-step semantics for the source language *)

  Variable state2': Type.	     (**r the type of configuration_limiteds for the target language *)
  Definition state2 := option state2'.
Variable step2: state2 -> list event -> state2 -> Prop.   (**r the small-step semantics for the target language *)

Variable match_states: state1 -> state2 -> Prop.  (**r the invariant *)

Variable measure: state1 -> nat.                  (**r the anti-stuttering measure *)

(*

Lemma simulation_step:
  forall C impstate1 impstate2 machstate1 l,
  kstep impstate1 l impstate2 ->
  match_config_lim C impstate1 machstate1 ->
  exists machstate2 l',
      (plus (transition_limited C) machstate1 l' machstate2
       \/ (star (transition_limited C) machstate1 l' machstate2 /\ measure impstate2 < measure impstate1))
   /\ ((match_config_lim C impstate2 machstate2 /\ l = l') \/ (machstate2 = None /\ list_list_prefix l' l)).
 *)
Hypothesis simulation :
  forall S1 S1' S2 l,
    step1 S1 l S1' -> match_states S1 S2 ->
    exists S2' l',
      (plus step2 S2 l' S2' \/ (star step2 S2 l' S2' /\ measure S1' < measure S1))
      /\ ((match_states S1' S2' /\ l = l') \/ (S2' = None /\ list_list_prefix l' l))
.

(** We first extend the simulation to finite sequences of source transition_limiteds.
  This will show semantic preservation for terminating programs. *)

Lemma simulation_star:
  forall S1 S1' l,
    star step1 S1 l S1' ->
    forall S2, match_states S1 S2 ->
          exists S2' l', star step2 S2 l' S2' /\( (match_states S1' S2' /\ l = l') \/ (S2' = None /\ list_list_prefix l' l)).
Proof.
  induction 1; intros.
- (* zero transition_limited *)
  exists S2, []; split. apply star_refl. auto.
- (* one or more transition_limiteds *)
  destruct (simulation _ _ _ _ H H1) as [S2' [l [P Q]]].
  destruct Q as [[Q1 Q2] | [Q1 Q2]].
  + destruct (IHstar _ Q1) as [S2'' [l' [U V]]].
    subst.
    destruct V as [[V1 V2] | [V1 V2]].
    * subst.
      exists S2''; exists (l ++ l'); split. 
      eapply starans; eauto. destruct P. apply plus_star; auto. destruct H2; auto.
      auto.
    * subst.
      exists None. exists (l++l'); split.
      eapply starans; eauto. destruct P. apply plus_star; auto. destruct H2; auto.
      right. split; auto.
      clear -V2.
      induction l. eauto.
      simpl. now split.
  + exists S2'. exists l. subst.
    split. destruct P; try now apply plus_star. destruct H2; auto.
    right. split; auto.
    eapply list_list_prefix_trans; eauto.
    clear.
    induction l1; now simpl.
Qed.

(** Turning to infinite sequences, we first show that the target program
  can always make progress, while preserving the [match_states] relation,
  if the source diverges.  The proof is an induction on the maximal number
  [N] of stutterings the target can make before performing at least one transition_limited. *)

(** It follows that the target performs infinitely many transition_limiteds if
  started in a configuration_limited that matches a diverging source configuration_limited. *)

Lemma simulation_infseq:
  forall S1 S2 s,
  infseq step1 s S1 ->
  match_states S1 S2 ->
  (forall l, list_stream_prefix l s -> not (star step2 S2 l None)) ->
  infseq step2 s S2.
Proof.
  assert (forall S1 S2 s,
             infseq step1 s S1 ->
             match_states S1 S2 ->
             (forall l, list_stream_prefix l s -> not (star step2 S2 l None)) ->
             infseq_N step2 s (measure S1) S2).
  {
    clear -simulation.
    cofix Hfix; intros S1 S2 s H H0 H1.
    inversion H; subst; clear H.
    destruct (simulation _ _ _ _ H2 H0) as [S2' [l' [[Hplus | [Hstar Hmeas]] Hmatch]]].
    - destruct Hmatch as [[Hmatch1 Match2] | [Hmatch1 Hmatch2]]; subst.
      + eapply infseq_N_plus; eauto.
        eapply Hfix. eauto. eauto.
        intros l H Hn.
        apply (H1 (l' ++ l)).
               now apply list_stream_prefix_app.
        eapply starans; eauto. eapply plus_star; eauto.
      + eapply plus_star in Hplus.
        assert (H: list_stream_prefix l' (app_list_stream l s0)) by now apply list_list_prefix_stream_app.
        specialize (H1 l' H).
        now auto.
    - destruct Hmatch as [[Hmatch1 Hmatch2] | [Hmatch1 Hmatch2]]; subst.
      + eapply infseq_N_star; eauto.
        eapply Hfix. eauto. eauto.
        intros l H Hn.
        apply (H1 (l' ++ l)).
        now apply list_stream_prefix_app.
        eapply starans; eauto.
      + assert (H: list_stream_prefix l' (app_list_stream l s0)) by now apply list_list_prefix_stream_app.
        specialize (H1 l' H).
        now auto.
  }
  intros S1 S2 s H0 H1 H2.
  eapply infseq_N_infseq. eauto.
Qed.

Lemma simulation_infseq' :
  forall S1 S2 s,
    infseq step1 s S1 ->
    match_states S1 S2 ->
    infseq step2 s S2 \/ (exists l, list_stream_prefix l s /\ star step2 S2 l None).
Proof.
  intros S1 S2 s H H0.
  pose proof simulation_infseq S1 S2 s H H0 as H'.
  setoid_rewrite imp_equiv in H';
    setoid_rewrite not_forall_ex_not in H';
    setoid_rewrite not_imp in H';
    setoid_rewrite <- dne in H';
    setoid_rewrite or_comm in H'.
  now apply H'.
Qed.

Lemma simulation_infseq_prod:
  forall S1 S2 s,
    infseq_prod step1 s S1 ->
    match_states S1 S2 ->
    infseq_prod step2 s S2 \/ (exists l, list_stream_prefix l s /\ star step2 S2 l None).
Proof.
  assert (H: forall S1 S2 s,
             infseq_prod step1 s S1 ->
             match_states S1 S2 ->
             (forall l, list_stream_prefix l s -> not (star step2 S2 l None)) ->
             infseq_prod step2 s S2).
  {
    cofix Hfix; intros S1 S2 s H H0 Hnot.
    inversion H; subst; clear H.
    edestruct simulation_star
      as [S2' [l' [Hstar [[Hmatch1 Hmatch2] | [Hmatch1 Hmatch2]]]]];
      eauto; subst.
    - econstructor; eauto.
      eapply Hfix; eauto.
      intros l Hl Hn.
      eapply (Hnot (l' ++ l)); try eapply starans; eauto.
      now apply list_stream_prefix_app.
    - exfalso. (* eapply (Hnot _ _ Hstar). *)
      eapply Hnot. eapply list_list_prefix_stream_app; eauto.
      eauto.
  }
  intros S1 S2 s H0 H1.
  specialize (H S1 S2 s H0 H1).
  setoid_rewrite imp_equiv in H;
    setoid_rewrite not_forall_ex_not in H;
    setoid_rewrite not_imp in H;
    setoid_rewrite <- dne in H;
    setoid_rewrite or_comm in H.
  now assumption.
Qed.

Lemma simulation_infseq_silent :
  forall S1 S2,
    infseq_silent step1 S1 ->
    match_states S1 S2 ->
    (forall l, l = [] -> not (star step2 S2 l None)) ->
    infseq_silent step2 S2.
Proof.
  assert (forall S1 S2, 
             infseq_silent step1 S1 ->
             match_states S1 S2 ->
             (forall l, l = [] -> not (star step2 S2 l None)) ->
             infseq_silent_N step2 (measure S1) S2).
  {
    clear -simulation.
    cofix Hfix; intros S1 S2 H H0 H1.
    inversion H; subst; clear H.
    destruct (simulation _ _ _ _ H2 H0) as [S2' [l' [[Hplus | [Hstar Hmeas]] [[Hmatch1 Hmatch2] | [Hmatch1 Hmatch2]]]]];
      subst.
    - eapply infseq_silent_N_plus; eauto.
      eapply Hfix; eauto. intros l H Hn; subst.
      eapply plus_star in Hplus.
      apply (H1 ([] ++ []) eq_refl).
      eapply starans; eauto.
    - assert (l' = []) by now destruct l'. subst.
      eapply plus_star in Hplus; specialize (H1 [] eq_refl).
      now auto.
    - eapply infseq_silent_N_star; eauto.
      eapply Hfix; eauto.
      intros l Heq Hn; subst.
      eapply (H1 ([] ++ []) eq_refl); eapply starans; eauto.
    - assert (l' = []) by now destruct l'.
      subst.
      now specialize (H1 [] eq_refl).
  }
  intros S1 S2 H0 H1 H2.
  eapply infseq_silent_N_infseq_silent. eauto.
Qed.

Lemma simulation_infseq_silent' :
  forall S1 S2,
  infseq_silent step1 S1 ->
  match_states S1 S2 ->
  infseq_silent step2 S2 \/ exists l, l = [] /\ star step2 S2 l None.
Proof.
  intros S1 S2 s H.
  pose proof simulation_infseq_silent S1 S2 s H as H'.
  setoid_rewrite imp_equiv in H';
    setoid_rewrite not_forall_ex_not in H';
    setoid_rewrite not_imp in H';
    setoid_rewrite <- dne in H';
    setoid_rewrite or_comm in H'.
  now apply H'.
Qed.

End SIMULATION_DIAGRAM.
(** We now apply these results to the Imp compiler.  We first obtain
  an alternate proof of semantic preservation for terminating Imp programs. *)

Lemma match_config_lim_initial:
  forall c st,
  match_config_lim (compile_program c) (c, Kstop, st) (Some (0, nil, st)).
Proof.
  intros. constructor.
  change (compile_program c) with (nil ++ compile_com c ++ Ihalt :: nil). constructor. auto.
  simpl. unfold compile_program. constructor. apply code_at_app. auto.
Qed.

Theorem compile_program_correct_terminating_2:
  forall c st st' l,
  kterminates c st st' l ->
  mach_terminates (compile_program c) st st' l \/ exists l', list_list_prefix l' l /\ mach_OOM (compile_program c) st l'.
Proof.
  intros.
  assert (exists machconf2 l',
           star (transition_limited (compile_program c)) (Some (0, nil, st)) l' machconf2
           /\ ((match_config_lim (compile_program c) (SKIP, Kstop, st') machconf2 /\ l = l') \/
             (machconf2 = None /\ list_list_prefix l' l))).
  eapply simulation_star; eauto. eapply simulation_step. apply match_config_lim_initial.
  destruct H0 as [machconf2 [l' [STAR [[MS EQ] | [EQ PREF]]]]].
  + inversion MS; subst. simpl in *. normalize.
    destruct (compile_cont_Kstop_inv _ _ st' H5) as [pc' [A B]].
    left. red. exists pc'; split. auto.
    replace l' with (l' ++ [] : list (ev event)); last apply app_nil_r.
    eapply starans; eauto.
  + subst. right.
    exists l'; now split.
Qed.

(** More interestingly, we also prove semantic preservation for diverging
  Imp programs. *)

Theorem compile_program_correct_diverging:
  forall c st s,
  kdiverges c st s ->
  mach_diverges (compile_program c) st s \/ exists l', list_stream_prefix l' s /\ mach_OOM (compile_program c) st l'.
Proof.
  intros c st s H.
  edestruct simulation_infseq' with (match_states := match_config_lim (compile_program c));
    eauto using simulation_step, match_config_lim_initial.
Qed.

Theorem compile_program_correct_silent:
  forall c st st' l,
    ksilent c st st' l ->
    mach_silent (compile_program c) st st' l \/ exists l', list_list_prefix l' l /\ mach_OOM (compile_program c) st l'.
Proof.
  intros.
  destruct H as [c' [k' [H1 H2]]].
  assert (exists machconf2 l', star (transition_limited (compile_program c)) (Some (0, nil, st)) l' machconf2
                          /\ ((match_config_lim (compile_program c) (c',k', st') machconf2 /\ l = l') \/
                             machconf2 = None /\ list_list_prefix l' l)).
  eapply simulation_star; eauto. eapply simulation_step. apply match_config_lim_initial.
  destruct H as [machconf2 [l' [STAR [[MS1 MS2] | [MS1 MS2]]]]]; subst.
  - inversion MS1; subst. simpl in *.
    edestruct simulation_infseq_silent' with (match_states := match_config_lim (compile_program c)); eauto.
    eapply simulation_step.
    + left. red.
      exists pc, nil.
      now split.
    + destruct H as [l [? Hstar]]; subst.
      right.
      exists (l' ++ []).
      split. rewrite app_nil_r; now apply list_list_prefix_ref.
      unfold mach_OOM.
      eapply starans; eauto.
  - right.
    now (exists l').
Qed.


Theorem compile_program_correct_reacting:
  forall c st s,
    kreacts c st s ->
    mach_reacts (compile_program c) st s \/ exists l, list_stream_prefix l s /\ mach_OOM (compile_program c) st l.
Proof.
  intros.
  unfold mach_reacts, mach_OOM.
  eapply simulation_infseq_prod with (match_states := match_config_lim (compile_program c)); eauto using simulation_step, match_config_lim_initial.
Qed.

Section Traces.
  Definition event := Imp.event.
  Definition endstate := {| es := unit; an_es := tt |}.
  Definition trace := @TraceModel.trace event endstate.
End Traces.

Section Source.

  Definition traceS := @ResourceExhaustion.traceS event endstate.

  Definition sprg := com.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition semS (p : sprg) (t : traceS) : Prop :=
    match t with
    | tstop l e => exists st', kterminates p empty_state st' l
    | tsilent l => exists st', ksilent p empty_state st' l
    | tstream s => kreacts p empty_state s
    end.
Definition trace_app (t1 t2 : trace) : trace :=
    match t1 with
    | tstop l e =>
      match t2 with
      | tstop l' e' => tstop (l ++ l') e'
      | tsilent l' => tsilent (l ++ l')
      | tstream s => tstream (Stream.app_list_stream l s)
      end
    | tsilent l => tsilent l
    | tstream s => tstream s
    end.


  Section Reacts.
    Variable s0 : (com * cont * state).
    Hypothesis reacts:
      forall s1 t1, star kstep s0 t1 s1 ->
               exists s2, exists t2, star kstep s1 t2 s2 /\ t2 <> [].

    Lemma reacts':
      forall s1 t1, star kstep s0 t1 s1 ->
               { s2 & { t2 : list (ev Imp.event) | star kstep s1 t2 s2 /\ t2 <> [] } }.
    Proof.
      intros.
      destruct (constructive_indefinite_description _ (reacts _ _ H)) as [s2 A].
      destruct (constructive_indefinite_description _ A) as [t2 [B C]].
      exists s2; exists t2; auto.
    Qed.

    
    CoFixpoint build_stream' s1 (t1: list (ev Imp.event)) (ST: star kstep s0 t1 s1) : @stream' (ev Imp.event) :=
      match (reacts' _ _ ST) with
      | existT s2 (exist t2 (conj A B)) =>
        @scons' _ t2 (build_stream' _ _ (starans ST A)) B
      end.

    Lemma reacts_forever_reactive_rec:
      forall s1 t1 (ST: star kstep s0 t1 s1),
        infseq_prod kstep (stream_of_stream' (build_stream' _ _ ST)) s1.
    Proof.
      cofix COINDHYP; intros.
      rewrite (unroll_stream' (build_stream' _ _ ST)).
      simpl.
      destruct (reacts' _ _ ST) as [s2 [t2 [A B]]].
      rewrite stream_stream'_app.
      econstructor. eassumption. auto. apply COINDHYP.
    Qed.

    Lemma reacts_forever_reactive:
      exists s, infseq_prod kstep s s0.
    Proof.
      exists (stream_of_stream' (build_stream' _ _ (star_refl _ _))).
      apply reacts_forever_reactive_rec.
    Qed.
  End Reacts.


  Lemma non_empty_semS : forall W, exists t, semS W t.
  Proof.
    intros W.
    unfold semS.
    destruct (classic (forall s1 t1, star kstep (W, Kstop, empty_state) t1 s1 -> exists s2, exists t2, kstep s1 t2 s2)).
    - (* Divergence *)
      destruct (classic (exists s1, exists t1, star kstep (W, Kstop, empty_state) t1 s1 /\
                                     (forall s2 t2, star kstep s1 t2 s2 -> exists s3,
                                           kstep s2 [] s3))).
      + (* Silent divergence *)
        destruct H0 as [[[]] [t1 [A B]]].
        exists (tsilent t1); econstructor; eauto.
        unfold ksilent. subst.
        eexists; eexists; split; eauto.
        now apply diverges_infseq_silent.
      + (*reactive divergence *)
        destruct (@reacts_forever_reactive (W, Kstop, empty_state)) as [T FR].
        intros.
        generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
        generalize (not_ex_all_not _ _ A t1). intro B; clear A.
        destruct (not_and_or _ _ B). contradiction.
        destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0.
        destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
        destruct (imply_to_and _ _ D) as [E F]; clear D.
        destruct (H s2 (List.app t1 t2)) as [s3 [t3 G]]. eapply starans; eauto.
        exists s3; exists (List.app t2 t3); split.
        eapply plus_star; eapply plus_right; eauto.
        (* eapply star_step_right; eauto. *)
        red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
        exists (tstream T). assumption.
    - (* Termination *)
      destruct (not_all_ex_not _ _ H) as [[[]] A]; clear H.
      destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
      destruct (imply_to_and _ _ B) as [C D]; clear B.
      assert (c = SKIP /\ c0 = Kstop).
      {
        destruct c;
          try now (exfalso; apply D; eexists; eexists; econstructor; eauto).
        - split; first reflexivity.
          destruct c0; first reflexivity;
            try now (exfalso; apply D;
                     eexists; eexists; econstructor; eauto).
        - exfalso; apply D.
          destruct (beval s b) eqn:Heq.
          + eexists; eexists; now apply KS_IfTrue.
          + eexists; eexists; now apply KS_IfFalse.
        - exfalso; apply D.
          destruct (beval s b) eqn:Heq.
          + eexists; eexists; now apply KS_WhileTrue.
          + eexists; eexists; now apply KS_WhileFalse.
      }
      exists (tstop t1 (tt : es endstate)).
      econstructor; eauto.
      unfold kterminates.
      destruct H; subst; eauto.
  Qed.

  Definition semanticsS : Semantics source trace :=
    {| sem := semS : prg source -> trace -> Prop;
       non_empty_sem := non_empty_semS |}.

End Source.

Section Target.

  Definition traceT := @ResourceExhaustion.traceT event endstate.

  Definition tprg := code.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition semT (p : tprg) (t : traceT) : Prop :=
    match t with
    | tstop l (inl e) => exists st', mach_terminates p (empty_state) st' l \/ mach_goes_wrong p empty_state l
    | tstop l (inr e) => mach_OOM p (empty_state) l
    | tsilent l => exists st', mach_silent p empty_state st' l
    | tstream s => mach_reacts p empty_state s
    end.

  Section Reacts.
    Variable s0 : configuration_limited.
    Variable C : code.
    Hypothesis reacts:
      forall s1 t1, star (transition_limited C) s0 t1 s1 ->
               exists s2, exists t2, star (transition_limited C) s1 t2 s2 /\ t2 <> [].

    Lemma reacts'_mach:
      forall s1 t1, star (transition_limited C) s0 t1 s1 ->
               { s2 & { t2 : list (ev Imp.event) | star (transition_limited C) s1 t2 s2 /\ t2 <> [] } }.
    Proof.
      intros.
      destruct (constructive_indefinite_description _ (reacts _ _ H)) as [s2 A].
      destruct (constructive_indefinite_description _ A) as [t2 [B C']].
      exists s2; exists t2; auto.
    Qed.

    
    CoFixpoint build_stream'_mach s1 (t1: list (ev Imp.event)) (ST: star (transition_limited C) s0 t1 s1) : @stream' (ev Imp.event) :=
      match (reacts'_mach _ _ ST) with
      | existT s2 (exist t2 (conj A B)) =>
        @scons' _ t2 (build_stream'_mach _ _ (starans ST A)) B
      end.

    Lemma reacts_forever_reactive_rec_mach:
      forall s1 t1 (ST: star (transition_limited C) s0 t1 s1),
        infseq_prod (transition_limited C) (stream_of_stream' (build_stream'_mach _ _ ST)) s1.
    Proof.
      cofix COINDHYP; intros.
      rewrite (unroll_stream' (build_stream'_mach _ _ ST)).
      simpl.
      destruct (reacts'_mach _ _ ST) as [s2 [t2 [A B]]].
      rewrite stream_stream'_app.
      econstructor. eassumption. auto. apply COINDHYP.
    Qed.

    Lemma reacts_forever_reactive_mach:
      exists s, infseq_prod (transition_limited C) s s0.
    Proof.
      exists (stream_of_stream' (build_stream'_mach _ _ (star_refl _ _))).
      apply reacts_forever_reactive_rec_mach.
    Qed.
  End Reacts.

  Lemma non_empty_semT : forall W, exists t, semT W t.
  Proof.
    intros W.
    unfold semT.
    destruct (classic (forall s1 t1, star (transition_limited W) (Some (0, [], empty_state)) t1 s1 -> exists s2, exists t2, (transition_limited W) s1 t2 s2)).
    - (* Divergence *)
      destruct (classic (exists s1, exists t1, star (transition_limited W) (Some (0, [], empty_state)) t1 s1 /\
                                     (forall s2 t2, star (transition_limited W) s1 t2 s2 -> exists s3,
                                           (transition_limited W) s2 [] s3))).
      + (* Silent divergence *)
        destruct H0 as [[[[]]|] [t1 [A B]]].
        exists (tsilent (t1 : list (ev Imp.event))); econstructor; eauto.
        eexists; eexists; split; eauto.
        now apply diverges_infseq_silent.
        exists (tstop (t1 : list (ev Imp.event)) (inr tt : es (endstateT endstate))).
        eauto.
      + (*reactive divergence *)
        destruct (@reacts_forever_reactive_mach (Some (0, [], empty_state))) with (C := W) as [T FR].
        intros.
        generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
        generalize (not_ex_all_not _ _ A t1). intro B; clear A.
        destruct (not_and_or _ _ B). contradiction.
        destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0.
        destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
        destruct (imply_to_and _ _ D) as [E F]; clear D.
        destruct (H s2 (List.app t1 t2)) as [s3 [t3 G]]. eapply starans; eauto.
        exists s3; exists (List.app t2 t3); split.
        eapply plus_star; eapply plus_right; eauto.
        (* eapply star_step_right; eauto. *)
        red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
        exists (tstream (T : @Stream.stream (ev Imp.event))). assumption.
    - (* Termination *)
      destruct (not_all_ex_not _ _ H) as [[[[]]|] A]; clear H.
      destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
      destruct (imply_to_and _ _ B) as [C D]; clear B.
      exists (tstop (t1 : list (ev Imp.event)) (inl tt : es (endstateT endstate))).
      exists s0.
      destruct (code_at W n) as [[]|] eqn:Heq;
        destruct s as [| i s'] eqn:Heq';
      match goal with
      | Hcode : code_at W n = Some Ihalt,  Hstk : s = [] |- _ => left
      | _ => right; econstructor; exists s; exists s0; split; subst; try eassumption;
              split;
              try (now intros b e; apply not_ex_all_not with (n := b) in D;
                   apply not_ex_all_not with (n := e) in D; assumption);
              match goal with
              | |- _ \/ [] = [] => now right
              | |- _ \/ (_ :: _) <> [] => now right
                         | _ => idtac
              end;
              left
      end;
      try now rewrite Heq.
      econstructor; eauto.
      destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
      destruct (imply_to_and _ _ B) as [C D]; clear B.
      exists (tstop (t1 : list (ev Imp.event)) (inr tt : es (endstateT endstate))).
      auto.
  Qed.

  Definition semanticsT : Semantics target traceT :=
    {| sem := semT : prg target -> traceT -> Prop;
       non_empty_sem := non_empty_semT |}.

End Target.


Section CompilationChain.

  Definition compile : prg source -> prg target := compile_program.
  Hint Unfold compile.

  Definition compiler : CompilationChain source target :=
    {| compile_whole := compile;
       compile_par := compile;
       compile_ctx := fun x => x |}.

End CompilationChain.

Definition rel' := ResourceExhaustion.rel event endstate.
Hint Unfold rel'.

Definition rel (t1 : traceS) (t2 : traceT) :=
  match t1, t2 with
  | tstream s1, tstream s2 => Stream.stream_eq s1 s2
  | _, _ => rel' t1 t2
  end.

Definition trace_eq (t1 t2 : traceT) :=
  match t1, t2 with
  | tstream s1, tstream s2 => Stream.stream_eq s1 s2
  | _, _ => t1 = t2
  end.

Definition rel_TC := TraceCriterion.rel_TC compiler semanticsS semanticsT rel.

Definition rel_TC_fwd := forall W s, semS W s -> exists t, rel s t /\ semT (compile W) t.

Lemma target_determinism : forall W s1 s2,
    semT W s1 ->
    semT W s2 ->
    trace_eq s1 s2.
Proof.
  intros W s1 s2 H1 H2. unfold rel.
  unfold semT in *.
  destruct s1 as [ l1 [[] | []] | l1 | s1 ];
    destruct s2 as [ l2 [[] | []] | l2 | s2];
    repeat
      match goal with
      | Hor : exists _ : state, _ \/ _ |- _ => destruct Hor as [? []]
      | Hsile: exists _ : state, mach_silent _ _ _ _ |- _ => destruct Hsile
      end;
    try (now exfalso; eapply terminates_goeswrong_exclusive; eassumption);
    try (now exfalso; eapply terminates_silent_exclusive; eassumption);
    try (now exfalso; eapply terminates_diverges_exclusive; eassumption);
    try (now exfalso; eapply terminates_reacts_exclusive; eassumption);
    try (now exfalso; eapply terminates_OOM_exclusive; eassumption);
    try (now exfalso; eapply goeswrong_silent_exclusive; eassumption);
    try (now exfalso; eapply goeswrong_diverges_exclusive; eassumption);
    try (now exfalso; eapply goeswrong_reacts_exclusive; eassumption);
    try (now exfalso; eapply goeswrong_OOM_exclusive; eassumption);
    try (now exfalso; eapply silent_diverges_exclusive; eassumption);
    try (now exfalso; eapply silent_reacts_exclusive; eassumption);
    try (now exfalso; eapply silent_OOM_exclusive; eassumption);
    try (now exfalso; eapply reacts_OOM_exclusive; eassumption).
  - match goal with
    | Ht1 : mach_terminates _ _ _ _, Ht2 : mach_terminates _ _ _ _ |- _ =>
      destruct (terminates_unique _ _ _ _ _ _ Ht1 Ht2)
    end; now subst.
  - match goal with
    | Ht1 : mach_goes_wrong _ _ _, Ht2 : mach_goes_wrong _ _ _ |- _ =>
      destruct (goeswrong_unique _ _ _ _ Ht1 Ht2)
    end; now subst.
  - match goal with
    | Ht1 : mach_OOM _ _ _, Ht2 : mach_OOM _ _ _ |- _ =>
      destruct (OOM_unique _ _ _ _ Ht1 Ht2)
    end; now subst.
  - match goal with
    | Ht1 : mach_silent _ _ _ _, Ht2 : mach_silent _ _ _ _ |- _ =>
      destruct (silent_unique _ _ _ _ _ _ Ht1 Ht2)
    end; now subst.
  - match goal with
    | Ht1 : mach_reacts _ _ _, Ht2 : mach_reacts _ _ _ |- _ =>
      destruct (reacts_unique _ _ _ _ Ht1 Ht2)
    end; now econstructor.
Qed.

Lemma rel_TC_fwd_rel_TC : rel_TC_fwd -> rel_TC.
Proof.
  unfold rel_TC_fwd, rel_TC, TraceCriterion.rel_TC.
  intros H W t H0.
  destruct (non_empty_semS W) as [s Hs].
  specialize (H W s Hs).
  destruct H as [t' [H1 H2]].
  simpl in H0.
  assert (trace_eq t t') by
      now apply target_determinism with (W := compile W).
  subst.
  exists s. split; eauto.
  destruct s, t, t'; try now rewrite H.
  - simpl in *.
    inversion H1.
    inversion H3.
    destruct H3 as [m [H31 H32]].
    inversion H31.
  - simpl in *. inversion H1.
    inversion H3.
    destruct H3 as [m [H31 H32]].
    inversion H31.
  - simpl in *. eapply stream_eq_trans. eauto. eapply stream_eq_sym. eauto.
Qed.

Theorem correctness : rel_TC.
Proof.
  apply rel_TC_fwd_rel_TC.
  unfold rel_TC_fwd.
  intros W t H; simpl in H.
  destruct t as [l e | l | s].
  - simpl in *.
    destruct H as [st' Hterm].
    apply compile_program_correct_terminating_2 in Hterm.
    destruct Hterm as [H | H].
    + exists (tstop (l : list (ev event)) (inl e : es (endstateT endstate))).
      split.
      repeat constructor.
      now (exists st'; left).
    + destruct H as [l' [H1 H2]].
      exists (tstop (l' : list (ev event)) (OOM (endstate))).
      split.
      right. eexists; split; eauto.
      eauto.
  - simpl in *.
    destruct H as [st' Hsil].
    apply compile_program_correct_silent in Hsil.
    destruct Hsil as [H | H].
    + exists (tsilent (l : list (ev event))).
      split.
      repeat constructor.
      now (exists st').
    + destruct H as [l' [H1 H2]].
      exists (tstop (l' : list (ev event)) (OOM (endstate))).
      split.
      right. eexists; split; simpl; eauto.
      eauto.
  - simpl in *.
    apply compile_program_correct_reacting in H.
    destruct H as [H | H].
    + exists (tstream (s : @stream (ev event))).
      split.
      repeat constructor; eauto.
      eauto.
    + destruct H as [l' [H1 H2]].
      exists (tstop (l' : list (ev event)) (OOM (endstate))).
      split.
      right. eexists; split; eauto.
      eauto.
Qed.
