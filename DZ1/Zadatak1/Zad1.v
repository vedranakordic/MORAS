(* 1a *)
Goal forall X Y, ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) <-> ~(X /\ Y).
Proof.
 split.
 - intros. destruct H.
 * apply H.
 * destruct H.
  ** unfold not. intros. apply H. destruct H0. apply H0.
  ** unfold not. intros. apply H. destruct H0. apply H1.
 - intros. left. apply H.
Qed. 

(* 1b *)
Goal forall X Y Z, ~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ 
                   (X /\ ~Y /\ ~Z) <-> (X /\ ~(Y \/ Z)).
Proof.
 intros. split.
 - intros. destruct H. destruct H0. destruct H1. split.
  * apply H1.
  * unfold not. intros. apply H2. destruct H3.
  -- destruct H2. exfalso. apply H2. apply H3.
  -- destruct H2. exfalso. apply H4. apply H3.
 - intros. destruct H. split.
  * unfold not. intros. apply H1. destruct H0, H1. destruct H1. exfalso. apply H0. apply H.
  * unfold not. intros. split.
  -- intros. apply H0. destruct H0, H1. destruct H1. left. apply H1.
  -- intros. split.
   ** apply H.
   **  intros. split.
      --- intros. apply H0. left. apply H1.
      ---  intros. apply H0. right. apply H1.
Qed.