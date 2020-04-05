From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.

Require Import Robust2relTraceProperty. 

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section Robust2relSafetyPreservation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Locate Safety.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition Safety__S := @Safety S_evs S_end.
  Local Definition prop__T := prop trace__T.
  Local Definition Safety__T := @Safety T_evs T_end.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target.
  Local Definition rsat__S := rsat2 Source_Semantics.
  Local Definition rsat__T := rsat2 Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable σ : (trace__T * trace__T -> Prop) -> (trace__S * trace__S -> Prop).
  Variable τ : (trace__S * trace__S -> Prop) -> (trace__T * trace__T -> Prop).

  Definition σR2rP (P1 P2 : par__S) (π : trace__T * trace__T -> Prop) :=
    rsat__S P1 P2 (σ π) -> rsat__T (P1 ↓) (P2 ↓) π.


   Lemma contra_σR2rP (P1 P2 : par__S) (T : trace__T * trace__T -> Prop) :
    (σR2rP P1 P2 T) <->  ((exists C__T t1 t2, sem__T ( plug__T (P1 ↓) C__T) t1 /\
                                      sem__T ( plug__T (P2 ↓) C__T) t2 /\  ~ (T (t1,t2))) ->
                        (exists C__S s1 s2, sem__S (plug__S P1 C__S) s1 /\
                                      sem__S (plug__S P2 C__S) s2 /\
                                    ~ (σ T) (s1, s2))).
  Proof.
    rewrite /σR2rP. by rewrite [_ -> _] contra !neg_rsat2.
  Qed.

  
  Definition σR2rSP := forall P1 P2 π, Safety2 π -> σR2rP P1 P2 π.

  Definition s2Cl_τR2rP (P1 P2 : par__S) (S : trace__S * trace__S -> Prop) :=
    rsat__S P1 P2 S -> rsat__T (P1 ↓) (P2 ↓) ((s2Cl ∘ τ) S).

  Definition s2Cl_τR2rTP := forall P1 P2 S, s2Cl_τR2rP P1 P2 S.

  Theorem Adj_σR2rSP_iff_s2Cl_τR2rTP :
    Adjunction_law τ σ -> (σR2rSP <-> s2Cl_τR2rTP).
  Proof.
    rewrite Galois_equiv. 
    move => [mono1 [mono2 [G1 G2]]]. split.
    - move => Hσ P1 P2 S Hrsat_src. apply: (Hσ P1 P2 ((s2Cl ∘ τ) S)).
      apply: s2Cl_Safety2.
      apply: rsat2_upper_closed. exact Hrsat_src.
      apply: subset_trans.
      { apply: G1. } 
      apply: mono2.
      by apply: s2Cl_bigger. 
    - move => Hτ P1 P2 T Hrrsat_tgt Hsrc.
      have H : rsat__T (P1 ↓) (P2 ↓) ((s2Cl ∘ τ) (σ T)) by apply: Hτ.
      apply: rsat2_upper_closed. exact H.
      have heq: s2Cl T = T by apply: s2Cl_id_on_Safety2. 
      rewrite -heq.
      apply: s2Cl_mono. rewrite heq. 
      by apply: G2.
  Qed.
 
End Robust2relSafetyPreservation.