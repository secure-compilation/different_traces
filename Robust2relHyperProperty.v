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
Require Import RobustTraceProperty.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section Robust2relHyperPreservation.


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
  Local Definition rsat__S := rhsat2 Source_Semantics.
  Local Definition rsat__T := rhsat2 Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* still mappings on trace properties *)
  Variable σ__π : (trace__T -> Prop) -> (trace__S -> Prop).
  Variable τ__π : (trace__S -> Prop) -> (trace__T -> Prop).

  Definition σ : (prop__T * prop__T -> Prop) -> (prop__S * prop__S -> Prop) :=
    fun T =>
      fun Π => exists π__T π__T', fst Π = σ__π π__T /\
                        snd Π = σ__π π__T' /\
                        T (π__T, π__T').

  Definition τ : (prop__S * prop__S -> Prop) -> (prop__T * prop__T -> Prop) :=
    fun S =>
      fun Π => exists π__S π__S', fst Π = τ__π π__S /\
                        snd Π = τ__π π__S' /\
                        S (π__S, π__S').


  Definition σR2hP (P1 P2 : par__S) (H__T : prop__T * prop__T -> Prop) :=
    rsat__S P1 P2 (σ H__T) -> rsat__T (P1 ↓) (P2 ↓) H__T.

  Definition σR2HP := forall P1 P2 H__T, σR2hP P1 P2 H__T.

  Lemma contra_σR2hP (P1 P2 : par__S) (H__T : prop__T * prop__T -> Prop) :
    (σR2hP P1 P2 H__T) <->  ((exists C__T, ~ H__T ((beh__T (plug__T (P1 ↓) C__T)), (beh__T (plug__T (P2 ↓) C__T)))) ->
                         (exists C__S, ~ (σ H__T) ((beh__S ( plug__S  P1 C__S)), (beh__S ( plug__S  P2 C__S))))).
  Proof.
    rewrite /σR2hP. by rewrite [_ -> _] contra !neg_rhsat2.
  Qed.

  Lemma contra_σR2HP :
    σR2HP <-> (forall P1 P2 H__T,   ((exists C__T, ~ H__T ((beh__T (plug__T (P1 ↓) C__T)), (beh__T (plug__T (P2 ↓) C__T)))) ->
                         (exists C__S, ~ (σ H__T) ((beh__S ( plug__S  P1 C__S)), (beh__S ( plug__S  P2 C__S)))))).
  Proof.
    rewrite /σR2HP.
    split => H P1 P2 H__T; by move/contra_σR2hP: (H P1 P2 H__T).
  Qed.

  Definition τR2hP (P1 P2 : par__S) (H__S : prop__S * prop__S -> Prop) :=
    rsat__S P1 P2 H__S -> rsat__T (P1 ↓) (P2 ↓) (τ H__S).

  Definition τR2HP := forall P1 P2 H__S, τR2hP P1 P2 H__S.

  Lemma contra_τR2hP (P1 P2 : par__S) (H__S : prop__S * prop__S -> Prop) :
    (τR2hP P1 P2 H__S) <-> ((exists C__T, ~ (τ H__S) ((beh__T (plug__T (P1 ↓) C__T)), (beh__T (plug__T (P2 ↓) C__T)))) ->
                        (exists C__S, ~  H__S ((beh__S (plug__S P1 C__S)), (beh__S (plug__S P2 C__S))))).
  Proof.
    rewrite /τR2hP. by rewrite [_ -> _] contra !neg_rhsat2.
  Qed.

  Lemma contra_τRHP :
    τR2HP <-> (forall P1 P2 H__S, ((exists C__T, ~ (τ H__S) ((beh__T (plug__T (P1 ↓) C__T)), (beh__T (plug__T (P2 ↓) C__T)))) ->
                          (exists C__S, ~  H__S ((beh__S (plug__S P1 C__S)), (beh__S (plug__S P2 C__S)))))).
  Proof.
    rewrite /τR2HP.
    split => H P1 P2 H__S; by move/contra_τR2hP: (H P1 P2 H__S).
  Qed.

End Robust2relHyperPreservation.