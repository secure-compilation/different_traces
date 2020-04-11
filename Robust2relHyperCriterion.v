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
Require Import Robust2relHyperProperty.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section Robust2relHCrit.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target.
  Local Definition rhsat__S := rhsat2 Source_Semantics.
  Local Definition rhsat__T := rhsat2 Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable rel : trace__S -> trace__T -> Prop.

  (* __π to highlights these maps are mappings between properties  *)
  Local Definition σ__π : (trace__T -> Prop) -> (trace__S -> Prop) :=
                       γ (@induced_connection (trace__T) (trace__S) rel).

  Local Definition τ__π : (trace__S -> Prop) -> (trace__T -> Prop) :=
                       α (@induced_connection (trace__T) (trace__S) rel).

  Local Definition induced_adj : Adjunction_law τ__π σ__π :=
    adjunction_law (induced_connection rel).

  Local Definition σ : (prop__T * prop__T -> Prop) -> (prop__S * prop__S -> Prop) := σ σ__π.
  Local Definition τ : (prop__S * prop__S -> Prop) -> (prop__T * prop__T -> Prop) := τ τ__π.

  Local Definition τR2HP := τR2HP compilation_chain
                                  Source_Semantics Target_Semantics
                                  τ__π.
  
  Local Definition σR2HP := σR2HP compilation_chain
                                  Source_Semantics Target_Semantics
                                  σ__π.
  

  Definition rel_R2HC :=  forall P1 P2 C__T, exists C__S,
                          (forall t__T, beh__T (plug__T (P1 ↓) C__T) t__T <->
                                 (exists t__S, rel t__S t__T /\ beh__S (plug__S P1 C__S) t__S))
                          /\
                          (forall t__T, (beh__T (plug__T (P2 ↓) C__T) t__T <->
                                  (exists t__S, rel t__S t__T /\ beh__S (plug__S P2 C__S) t__S))).

  Lemma rel_R2HC' : rel_R2HC <-> forall P1 P2 C__T, exists C__S,
          (beh__T (plug__T (P1 ↓) C__T) = τ__π (beh__S (plug__S P1 C__S))) /\
          (beh__T (plug__T (P2 ↓) C__T) = τ__π (beh__S (plug__S P2 C__S))).
  Proof. 
    split => Hrel P1 P2 C__T.
    + destruct (Hrel P1 P2 C__T) as [C__S [Hrel1' Hrel2']].
      exists C__S. split;
      apply functional_extensionality => t__T; apply: prop_extensionality;
        [rewrite Hrel1' | rewrite Hrel2']; by firstorder.
    + destruct (Hrel P1 P2 C__T) as [C__S [Hrel1' Hrel2']].
      rewrite Hrel1' Hrel2'. by firstorder.
  Qed.

  Theorem rel_RHC_τRHP : rel_R2HC <-> τR2HP.
  Proof.
    rewrite rel_R2HC'. split.
    - move => H_rel P1 P2 h__S H_src C__T.
      destruct (H_rel P1 P2 C__T) as [C__S [H_rel1' H_rel2']].
      exists (beh__S (plug__S P1 C__S)), (beh__S (plug__S P2 C__S)).
      rewrite /=. split.
      + exact H_rel1'.
      + split. exact H_rel2'.   
       apply: (H_src C__S). 
    - move => H_τHP P1 P2 C__T.
      specialize (H_τHP P1 P2 (fun π__S => exists C__S, π__S = (beh__S (plug__S P1 C__S), beh__S (plug__S P2 C__S)))).
      have Hfoo : rhsat__S P1 P2 (fun π__S => exists C__S, π__S = (beh__S (plug__S P1 C__S), beh__S (plug__S P2 C__S))).
       { move => C__S. by exists C__S. } 
       destruct (H_τHP Hfoo C__T) as [bs1 [bs2 [H1 [H2 [C__S Heq]]]]].
       exists C__S. inversion Heq. subst. simpl in *.
       by rewrite -H1 -H2.
  Qed.

  (* 
     To prove the following we need
      τ ⇆ σ to be an insertion   
  *)

  Lemma rel_R2HC_σR2HP : (Insertion_snd τ__π σ__π) ->
    rel_R2HC -> σR2HP.
  Proof.
    rewrite rel_R2HC' => HIns Hrel P1 P2 H__T Hsrc C__T.
    move: (Hrel P1 P2 C__T).
    move => [C__S [Heq1 Heq2]].
    move: (Hsrc C__S).  move => [b1 [b2 [Hb1 [Hb2 Hσ]]]].
    simpl in *. 
    have [Hfoo1 Hfoo2]: beh__T (plug__T (P1 ↓) C__T) = b1 /\ beh__T (plug__T (P2 ↓) C__T) = b2. 
    { split; [rewrite Heq1 | rewrite Heq2];
        [have Hsuff: beh__S (plug__S P1 C__S) = (σ__π b1) by apply Hb1 |
         have Hsuff: beh__S (plug__S P2 C__S) = (σ__π b2) by apply Hb2];
      by rewrite Hsuff HIns. }  
    rewrite /hsat2.
    rewrite <- Hfoo1 in Hσ. rewrite <- Hfoo2 in Hσ. 
    exact Hσ.  
  Qed.

   Lemma σRHP_rel_RHC:  
    (Reflection_fst τ__π σ__π) ->
    σR2HP -> rel_R2HC.
  Proof.
    rewrite rel_R2HC' => Hrefl Hσpres P1 P2 Ct.
    have Hfoo: (rhsat__S P1 P2 (σ (fun π__T =>
                              exists C__S : ctx Source,
                               π__T = (τ__π (beh__S (plug__S P1 C__S)),
                                     τ__π (beh__S (plug__S P2 C__S))) ))).
    { 
      move => C__S. rewrite /hsat2.
      exists (fun t : trace__T => (τ__π (beh__S (plug__S P1 C__S)) t)),
         (fun t : trace__T => (τ__π (beh__S (plug__S P2 C__S)) t)).
      simpl.  
      rewrite !Hrefl. 
      repeat split; auto.
        by exists C__S.   
    }  
    move: (Hσpres P1 P2 _  Hfoo Ct). move => [Cs H].
    exists Cs.
    by inversion H.  
  Qed. 
  

End Robust2relHCrit.