From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Definition prop {k : level} := @trace k -> Prop.
Definition fprop {k : level} := @finpref k -> Prop. 

Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Notation "M <<< b" := (forall m, M m -> exists t, b t /\ prefix m t) (at level 50).  

Definition Safety {k : level} (π : @prop k) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
             (forall t', prefix m t' -> ~ π t')).

Inductive Observations {k : level} : (@finpref k -> Prop) -> Prop :=
  empty :  Observations (fun m : finpref => False)
| finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

          
(* CA: for now this is axiomatized but we can recover it by modifying
       results from TraceTopology.v *)
Axiom Cl: forall {k: level}, @prop k -> @prop k.
Axiom Cl_bigger: forall {k: level} (π: @prop k), π ⊆ (Cl π). 
Axiom Cl_Safety: forall {k: level} π, Safety (@Cl k π).

Lemma Cl_id_on_Safe {k: level} : forall (π: @prop k), Safety π -> Cl π = π.
Admitted.

Lemma Cl_smallest {k: level} (π :@prop k) : forall S, @Safety k S -> π ⊆ S -> Cl π ⊆ S.
Admitted. 

Definition hprop {k : level} := @prop k -> Prop.

Definition SSC {k: level} (H: @hprop k)  : Prop :=
  forall h, H h ->
       (forall b : prop, b ⊆ h -> H b).

Definition sCl {k : level} (H : @hprop k) : @hprop k :=
  fun b => exists b', H b' /\ b ⊆ b'.

Lemma sCl_bigger {k : level} (H : @hprop k) : H ⊆ (sCl H). 
Proof. firstorder. Qed.   
  
Lemma sCl_SCH {k : level} (H : @hprop k) : SSC (sCl H).
Proof.
  move => h [b' [Hb' bb']] b b_h. exists b'; auto.
Qed.


Definition HSafe {k : level} (H: @hprop k) :=
  forall b, ~ H b -> (exists M, Observations M /\ M <<< b /\
                     (forall b', M <<< b' -> ~ H b')). 

Axiom hsCl : forall {k : level} (H: @hprop k), @hprop k.
Axiom hsCl_bigger : forall {k : level} (H: @hprop k), H ⊆ hsCl H.
Axiom hsCl_HSafe : forall {k: level} (H: @hprop k), HSafe H. 


Lemma HSafe_SCH {k: level} : forall (H: @hprop k), HSafe H -> SSC H.
Admitted. 

Lemma sCl_id_on_HSafe {k: level} : forall (H: @hprop k), HSafe H -> sCl H = H.
Admitted. 

(* CA: it will be proved once hsCl will no longer be an axiom, 
   (informal) Proof. 
    hsCl H is Hypersafety and hence subset-closed, so that is contains
    sCl H.
    Qed.
 *)
Lemma hsCl_sCl {k : level} : forall (H: @hprop k), sCl H ⊆ hsCl H.  
Proof. Admitted. 