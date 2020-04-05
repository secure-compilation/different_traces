From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FunctionalExtensionality.
Require Import ClassicalExtras.
Require Import MyNotation.

Require Import TraceModel.
Require Import Galois.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

(* CA: let us keep prop as more general as possible, in case
         one day we want traces to be just values.
 *)
Parameter E : Events.
Parameter Es : Endstates.

Definition prop (trace_set : Type)  := trace_set -> Prop.
Definition hprop (trace_set : Type) := (prop trace_set) -> Prop.
Definition h_true (trace_set : Type) : hprop (trace_set) := fun (b : prop (trace_set)) => True.
Definition hh_true (trace_set : Type) : (@hprop trace_set) -> Prop :=  fun _ => True.


Definition fprop {E : Events} {Es: Endstates} :=
  @finpref E Es -> Prop.

Notation "M <<< b" := (forall m, M m -> exists t, b t /\ prefix m t) (at level 50).

Definition Safety {E : Events}
           {Es : Endstates}
           (π : prop (@trace E Es)) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
             (forall t', prefix m t' -> ~ π t')).

(* Alternate characterization of safety *)
Definition Safety'{E : Events}
           {Es : Endstates}
           (π : prop (@trace E Es)) : Prop:=
  exists π': fprop,
  forall t:trace, ~(π t) <-> (exists m, prefix m t /\ π' m).

Lemma safety_safety'  {E : Events} {Es : Endstates} :
  forall π, @Safety E Es π <-> @Safety' E Es π.
Proof.
  unfold Safety, Safety'. intro π. split; intro H.
  - exists (fun m => forall t, prefix m t -> ~π t).
    intros t. split; intro H'.
    + specialize (H t H'). destruct H as [m [H1 H2]].
      exists m. split. assumption. intros t' H. apply H2. assumption.
    + destruct H' as [m [H1 H2]]. apply H2. assumption.
  - intros t H0. destruct H as [π' H].
    apply H in H0. destruct H0 as [m [H1 H2]].
    exists m. split; try now auto.
    intros. rewrite H. now exists m.
Qed.

Inductive Observations  {E : Events} {Es : Endstates} : (@finpref E Es -> Prop) -> Prop :=
  empty :  Observations (fun m : finpref => False)
| finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

(*****************************************************************************)
(** *Safety closure operator                                                 *)
(*****************************************************************************)

Definition Cl  {E : Events} {Es : Endstates}
               (π : prop (@trace E Es)) : prop (@trace E Es) :=
  fun t => forall S, Safety S -> π ⊆ S -> S t.

Lemma Cl_bigger  {E : Events} {Es : Endstates}
                 (π: prop (@trace E Es)) : π ⊆ (Cl π).
Proof. firstorder. Qed.

Lemma Cl_Safety {E : Events} {Es : Endstates}
                (π: prop (@trace E Es)): Safety (Cl π).
Proof.
  move => t not_π_t.
  move/not_forall_ex_not: not_π_t. move => [π' H].
  move/not_imp: H. move => [safety_π' H].
  move/not_imp: H. move => [π_leq_π' not_π'_t].
  destruct (safety_π' t not_π'_t) as [m [m_leq_t m_wit]].
  exists m. split; auto. move => t' m_leq_t' Hf.
  apply: (m_wit t'). assumption. by apply: Hf.
Qed.

Lemma Cl_id_on_Safe {E : Events} {Es : Endstates}
                    (π: prop (@trace E Es)) :
  Safety π -> Cl π = π.
Proof.
  move => Safety_π. apply: functional_extensionality => t.
  apply: prop_extensionality.
    by firstorder.
Qed.

Lemma Cl_smallest {E : Events} {Es : Endstates}
                  (π: prop (@trace E Es)) :
    forall S, Safety S -> π ⊆ S -> Cl π ⊆ S.
Proof. by firstorder. Qed.

Lemma Cl_mono {E : Events} {Es : Endstates} : monotone (@Cl E Es).
Proof.
  move => π1 π2 sub t cl2_t.
  apply: cl2_t.
  apply: Cl_Safety. apply: subset_trans. exact: sub. exact: Cl_bigger.
Qed.

Lemma Cl_idmp {E : Events} {Es : Endstates} : idempotent (@Cl E Es).
Proof. move => π. apply: Cl_id_on_Safe. apply: Cl_Safety. Qed.


Definition safety_uco {E : Events} {Es : Endstates} := Build_Uco (@Cl_mono E Es)
                                                                (@Cl_idmp E Es)
                                                                (@Cl_bigger E Es).


Lemma Safety_Cl_prop {E : Events} {Es : Endstates} :
  @Safety E Es = (lift (uco safety_uco)) (@h_true (@trace E Es)).
Proof.
  apply: functional_extensionality => π.
  apply: prop_extensionality. split => H.
  + exists π. split; rewrite //=.
      by rewrite Cl_id_on_Safe.
  + move: H. rewrite //=. move => [b [H Heq]]. subst.
    apply: Cl_Safety.
Qed.


(*****************************************************************************)


(*****************************************************************************)
(** *Dense closure operator *)
(*****************************************************************************)

Definition Dense {E : Events} {Es : Endstates}
                 (π: prop (@trace E Es)) : Prop :=
  forall t, finite t -> π t.

Definition dCl {E : Events} {Es : Endstates} : prop (@trace E Es) -> prop (@trace E Es) :=
  fun π => (fun t => finite t \/ π t).

Lemma Dense_dCl {E : Events} {Es : Endstates}
                  (π: prop (@trace E Es)) : Dense (dCl π).
Proof. firstorder. Qed.

Lemma dCl_mono {E : Events} {Es : Endstates} :
  monotone (@dCl E Es).
Proof.
  move => π1 π2 sub t1. rewrite /dCl.
  move => [K1 | K2]; [by left | right; by apply: sub].
Qed.

Lemma dCl_idmp {E : Events} {Es : Endstates} :
  idempotent (@dCl E Es).
Proof.
  rewrite /dCl => π.
  apply: functional_extensionality => t.
  apply: prop_extensionality.
  firstorder.
Qed.

Lemma dCl_ext {E : Events} {Es : Endstates} :
  extensive (@dCl E Es).
Proof.
  rewrite /dCl => π t π_t. by right.
Qed.

Lemma dCl_id_on_Dense {E : Events} {Es : Endstates}
                      (π: prop (@trace E Es)):
  Dense π -> dCl π = π.
Proof.
  rewrite /Dense /dCl => H_dense.
  apply: functional_extensionality => t.
  apply: prop_extensionality.
  split; auto. move => [k | k]; [by apply: H_dense | by []].
Qed.

Definition dense_uco {E : Events} {Es : Endstates} :=
  Build_Uco (@dCl_mono E Es)
            dCl_idmp
            dCl_ext.

Lemma Dense_Cl_prop {E : Events} {Es : Endstates} :
  Dense = (lift (uco dense_uco)) (@h_true (@trace E Es)).
Proof.
  apply: functional_extensionality => π.
  apply: prop_extensionality.
  split; rewrite /h_true //= => H.
  + exists π. split; auto. by rewrite dCl_id_on_Dense.
  + destruct H as [b [Heq H]]. subst.
      by apply: Dense_dCl.
Qed.

(*****************************************************************************)

(*CA: also for SSC hprop we only need a set of traces, not our particular model *)
Definition SSC {trace_set : Type} (H: hprop trace_set)  : Prop :=
  forall h, H h ->
       (forall b : (prop trace_set), b ⊆ h -> H b).

(*****************************************************************************)
(** *SSC closure operator*)
(*****************************************************************************)

Definition sCl {trace_set : Type}
               (H : hprop trace_set) :
               hprop trace_set :=
  fun b => exists b', H b' /\ b ⊆ b'.

Lemma sCl_bigger {trace_set : Type} (H : hprop trace_set) : H ⊆ (sCl H).
Proof. firstorder. Qed.

Lemma sCl_SCH {trace_set : Type} (H : hprop trace_set) : SSC (sCl H).
Proof.
  move => h [b' [Hb' bb']] b b_h. exists b'; auto.
Qed.

Lemma sCl_id_on_SSC {trace_set : Type} (H: hprop trace_set): SSC H -> sCl H = H.
Proof.
  move => H_SSC. apply: functional_extensionality => b.
  apply: prop_extensionality. firstorder.
Qed.

Lemma sCl_smallest {trace_set : Type} (H: hprop trace_set):
  forall H', SSC H' -> H ⊆ H' -> (sCl H) ⊆ H'.
Proof.
  move => H' ssc_H' H_leq_H' b [b' [ b_leq_b' H_b']].
  apply: (ssc_H' b'); auto.
Qed.

Lemma sCl_mono {trace_set : Type} (H1 H2 : hprop trace_set) :
  H1 ⊆ H2 -> (sCl H1) ⊆ (sCl H2).
Proof. by firstorder. Qed.

Lemma sCl_idmp {trace_set : Type} (H : hprop trace_set) :
  sCl (sCl H) = sCl H.
Proof. apply: sCl_id_on_SSC. apply: sCl_SCH. Qed.

Definition ssch_uco {trace_set : Type} : @Uco (trace_set -> Prop) :=
  @Build_Uco (prop trace_set)
             sCl
             sCl_mono
             sCl_idmp
             sCl_bigger.


(*****************************************************************************)

(*CA: for hypersafety we need the set of traces to have structure like in our def of trace *)

Definition HSafe {E : Events} {Es : Endstates}
                 (H: hprop (@trace E Es)) :=
  forall b, ~ H b -> (exists M, Observations M /\ M <<< b /\
                     (forall b', M <<< b' -> ~ H b')).


(*****************************************************************************)
(** *HSafe closure operator*)
(*****************************************************************************)

Definition hsCl {E : Events} {Es : Endstates}
                 (H: hprop (@trace E Es)) : (hprop (@trace E Es)) :=
  fun b => forall Hs, HSafe Hs -> H ⊆ Hs -> Hs b.

Lemma hsCl_bigger {E : Events} {Es : Endstates}
                  (H: hprop (@trace E Es)) :  H ⊆ hsCl H.
Proof. by firstorder. Qed.

Lemma hsCl_HSafe {E : Events} {Es : Endstates}
                 (H: hprop (@trace E Es)) : HSafe (hsCl H).
Proof.
  move => b. move/not_forall_ex_not => not_H_b.
  destruct not_H_b as [H' not_H'_b].
  move/not_imp: not_H'_b. move => [HSafe_H' not_H'_b].
  move/not_imp: not_H'_b. move => [H_leq_H' not_H'_b].
  destruct (HSafe_H' b not_H'_b) as [M [obs_M [M_leq_b M_wit]]].
  exists M. repeat (split; auto).
  move => b' M_leq_b' Hf. apply: (M_wit b'); auto.
    by apply: Hf.
Qed.

Lemma HSafe_SCH {E : Events} {Es : Endstates} :
  forall H, @HSafe E Es H -> SSC H.
Proof.
  move => H HSafe_H b Hb b' b'_leq_b.
  apply: NNPP => not_H_b'.
  destruct (HSafe_H b' not_H_b') as [M [obs_M [M_leq_b' M_wit]]].
  apply: (M_wit b); firstorder.
Qed.

Lemma hsCl_id_on_HSafe {E : Events} {Es : Endstates} :
  forall H, @HSafe E Es H -> hsCl H = H.
Proof.
  move => H HSafe_H.
  apply: functional_extensionality => b.
  apply: prop_extensionality. by firstorder.
Qed.

Lemma sCl_id_on_HSafe {E : Events} {Es : Endstates} :
  forall H, @HSafe E Es H -> sCl H = H.
Proof.
  move => H HSafe_H.
  have SSC_H: (SSC H) by apply: HSafe_SCH.
    by rewrite (sCl_id_on_SSC SSC_H).
Qed.

Lemma hsCl_sCl {E : Events} {Es : Endstates} :
  forall H : (hprop (@trace E Es)), sCl H ⊆ hsCl H.
Proof.
  move => H.
  have ssc: SSC (hsCl H).
  { apply: HSafe_SCH. apply: hsCl_HSafe. }
  apply: sCl_smallest; auto.
    by apply: hsCl_bigger.
Qed.

Lemma hsCl_smallest {E : Events} {Es : Endstates}
                    (H: hprop (@trace E Es)):
  forall H', HSafe H' -> H ⊆ H' -> (hsCl H) ⊆ H'.
Proof. by firstorder. Qed.

Lemma hsCl_mono {E : Events} {Es : Endstates}:
  forall H1 H2 : hprop (@trace E Es),
    H1 ⊆ H2 -> (hsCl H1) ⊆ (hsCl H2).
Proof. by firstorder. Qed.

Lemma hsCl_idmp  {E : Events} {Es : Endstates}
                 (H : hprop (@trace E Es)):
  hsCl (hsCl H) = hsCl H.
Proof.
  rewrite hsCl_id_on_HSafe.
  reflexivity.
  exact: hsCl_HSafe.
Qed.

Definition hsafe_uco {E : Events} {Es : Endstates} :
  @Uco ((@trace E Es) -> Prop) :=
  @Build_Uco (prop (@trace E Es))
             hsCl
             hsCl_mono
             hsCl_idmp
             hsCl_bigger.

(*****************************************************************************)
(** *2relSCH*)
(*****************************************************************************)

Definition SCH2 {trace_set : Type} (Π : (prop trace_set) * (prop trace_set) -> Prop) : Prop :=
  forall β1 β2 β1' β2': prop trace_set,
    Π (β1, β2) -> β1' ⊆ β1 -> β2' ⊆ β2 -> Π (β1', β2').

Definition sCl2 {trace_set : Type}
                (Π : (prop trace_set) * (prop trace_set) -> Prop) :
                (prop  trace_set) * (prop trace_set) -> Prop  :=
  fun b => exists b1 b2, Π (b1, b2) /\ (fst b) ⊆ b1 /\ (snd b) ⊆ b2.


Lemma sCl2_SCH2 {trace_set : Type} (Π : (prop trace_set) * (prop trace_set) -> Prop) :
  SCH2 (sCl2 Π).
Proof.
  move => β1 β2 β1' β2' [γ1 [γ2 [H_Π [Hsub1' Hbsu2']]]] H_sub1 H_sub2.
  exists γ1, γ2. split; apply: subset_trans; eauto.
  split; apply: subset_trans; eauto.
Qed.

(*****************************************************************************)
(** *2relSafety*)
(*****************************************************************************)

Definition Safety2 {E : Events} {Es : Endstates}
                   (R: (@trace E Es) * (@trace E Es) -> Prop) : Prop :=
  forall t1 t2, ~ R (t1, t2) ->
           exists m1 m2, (prefix m1 t1) /\ (prefix m2 t2) /\
                    (forall t1' t2', (prefix m1 t1') -> (prefix m2 t2') -> ~ R (t1', t2')). 

(*****************************************************************************)
(** *2relSafe closure operator*)
(*****************************************************************************)

Definition s2Cl {E : Events} {Es : Endstates}
                (R: (@trace E Es) * (@trace E Es) -> Prop) :
                (@trace E Es) * (@trace E Es) -> Prop  :=
  fun t => forall B, Safety2 B -> R ⊆ B -> B t.

Lemma s2Cl_bigger {E : Events} {Es : Endstates}
                  (R: (@trace E Es) * (@trace E Es) -> Prop) :  R ⊆ s2Cl R.
Proof. by firstorder. Qed.

Lemma s2Cl_Safety2 {E : Events} {Es : Endstates}
                   (π: (@trace E Es) * (@trace E Es) -> Prop): Safety2 (s2Cl π).
Proof.
  move => t1 t2 not_π_t.
  move/not_forall_ex_not: not_π_t. move => [π' H].
  move/not_imp: H. move => [safety_π' H].
  move/not_imp: H. move => [π_leq_π' not_π'_t].
  destruct (safety_π' t1 t2 not_π'_t) as [m1 [m2 [m1_leq_t1 [m2_leq_t2 m_wit]]]].
  exists m1, m2. split; auto. split; auto. move => t1' t2' m1_leq_t' m2_leqt2' Hf.
  apply: (m_wit t1' t2'); try assumption. by apply: Hf.
Qed.

Lemma s2Cl_id_on_Safety2 {E : Events} {Es : Endstates}
                         (π: (@trace E Es) * (@trace E Es) -> Prop) :
  Safety2 π -> s2Cl π = π.
Proof.
  move => Safety_π. apply: functional_extensionality => t.
  apply: prop_extensionality.
    by firstorder.
Qed.

Lemma s2Cl_smallest {E : Events} {Es : Endstates}
                    (π: (@trace E Es) * (@trace E Es) -> Prop) :
    forall S, Safety2 S -> π ⊆ S -> s2Cl π ⊆ S.
Proof. by firstorder. Qed.

Lemma s2Cl_mono {E : Events} {Es : Endstates} : monotone (@s2Cl E Es).
Proof.
  move => π1 π2 sub t cl2_t.
  apply: cl2_t.
  apply: s2Cl_Safety2. apply: subset_trans. exact: sub. exact: s2Cl_bigger.
Qed.

Lemma s2Cl_idmp {E : Events} {Es : Endstates} : idempotent (@s2Cl E Es).
Proof. move => π. apply: s2Cl_id_on_Safety2. apply: s2Cl_Safety2. Qed.


Definition safety2_uco {E : Events} {Es : Endstates} := Build_Uco (@s2Cl_mono E Es)
                                                                (@s2Cl_idmp E Es)
                                                                (@s2Cl_bigger E Es).



