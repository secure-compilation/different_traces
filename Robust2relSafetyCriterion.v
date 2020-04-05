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

Require Import Robust2relSafetyProperty.
(* Require Import Robust2relTraceProperty. 
Require Import Robust2relTraceCriterion. *) 

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section Robust2relSafetyCriterion.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Locate Safety.

  Local Definition trace__S:= @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition Safety__S := @Safety2 S_evs S_end.
  Local Definition prop__T := prop trace__T.
  Local Definition Safety__T := @Safety2 T_evs T_end.

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

  Variable rel : trace__S -> trace__T -> Prop. 
  
  Local Definition σ : (trace__T * trace__T -> Prop) -> (trace__S * trace__S -> Prop) :=
                       γ (@induced_connection_prod (trace__T) (trace__S) rel).

  Local Definition τ : (trace__S * trace__S -> Prop) -> (trace__T * trace__T -> Prop) :=
                       α (@induced_connection_prod (trace__T) (trace__S) rel).

  Local Definition induced_adj : Adjunction_law τ σ :=
    adjunction_law (induced_connection_prod rel).

  
  Local Definition σR2rSP := σR2rSP compilation_chain
                                    Source_Semantics Target_Semantics
                                    σ.

  Local Definition s2Cl_τR2rTP := s2Cl_τR2rTP compilation_chain
                                  Source_Semantics Target_Semantics
                                  τ.

  Definition rel_R2rSC : Prop :=
    forall C__T P1 P2 t1 t2 m1 m2,
      prefix m1 t1 ->
      prefix m2 t2 -> 
      sem__T (plug__T (P1 ↓) C__T) t1 ->
      sem__T (plug__T (P2 ↓) C__T) t2 ->
      exists C__S t1' t2' s1 s2,
        rel s1 t1' /\ rel s2 t2' /\ prefix m1 t1' /\ prefix m2 t2' /\
        sem__S (plug__S P1 C__S) s1 /\ sem__S (plug__S P2 C__S) s2.

  Theorem rel_R2rSC_σR2rSP : rel_R2rSC <-> σR2rSP.
  Proof.
   have G2 : Galois_snd τ σ by firstorder.
    split.
    - move => Htilde P1 P2 π HSafety. setoid_rewrite contra_σR2rP.
      move => [C__T [t1 [t2 [Hsemt1 [Hsemt2 Hnot_t]]]]].
      destruct (HSafety t1 t2 Hnot_t) as [m1 [m2 [Hpref_m1_t1 [Hpref_m2_t2 m_witness]]]].
      destruct (Htilde C__T P1 P2 t1 t2 m1 m2) as
          [C__S [t1' [t2' [s1 [s2 [Hrel_s1_t1' [Hrel_s2_t2' [Hpref_m1_t1' [Hpref_m2_t2' [Hsem_s1 Hsem_s2]]]]]]]]]]; auto.
      exists C__S, s1, s2. split; auto. split; auto => Hσs.
      have Ht0 : π (t1', t2').
      { apply: G2; auto. now exists (s1, s2). }
        by apply: (m_witness t1' t2').
    - move => H_RP C__T P1 P2 t1 t2 m1 m2 Hpref_m1_t1 Hpref_m2_t2 Hsemt1 Hsemt2.
      have HSafetyπ : Safety__T (fun t => ~ prefix m1 (fst t) \/ ~ prefix m2 (snd t)).
      { move => t1' t2' /=. rewrite de_morgan2. move => [prefix_m1_t1' prefix_m2_t2'].
      rewrite <- dne in prefix_m1_t1', prefix_m2_t2'.  
      exists m1, m2. 
      repeat split; auto. 
      move => t0 t00 m1_t0 m2_t0. rewrite de_morgan2. by repeat (rewrite -dne).  
      }
      move : (H_RP P1 P2  (fun t => ~ prefix m1 (fst t) \/ ~ prefix m2 (snd t)) HSafetyπ).
      setoid_rewrite contra_σR2rP => Himp. destruct Himp as [C__S [s1 [s2 [Hsem_s1 [Hsem_s2 Hσ]]]]].
      exists C__T, t1, t2. repeat split; auto. 
      rewrite de_morgan2 /=. by repeat (rewrite -dne).  
      move: Hσ. rewrite /σ. rewrite not_forall_ex_not. 
      move => [[t1' t2'] H]. 
      move/not_imp: H => [rel1 H]. 
      move/not_imp: H => [rel2 H].
      simpl in *. move/de_morgan2: H. repeat (rewrite -dne). move => [pref1 pref2]. 
      by exists C__S, t1', t2', s1, s2.  
Qed. 

  Theorem rel_R2rSC_2sCl_τR2rTP : rel_R2rSC <-> s2Cl_τR2rTP.
  Proof.
    setoid_rewrite <- (Adj_σR2rSP_iff_s2Cl_τR2rTP _ _ _ induced_adj).
    exact rel_R2rSC_σR2rSP.
  Qed. 

End Robust2relSafetyCriterion.