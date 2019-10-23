Require Import Relations Classical.
From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet.

Inductive value : term -> Prop :=
  | value_abs t : value (Abs t)
  | value_vcons c ls : value (VCons c ls).

Inductive context_name :=
  | context_app of term
  | context_case of seq (cons * nat * term).

Definition apply_context_name :=
  foldl (fun t c =>
    match c with
    | context_app t2 => App t t2
    | context_case pts => Case t pts
    end).

Inductive eval_name : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | eval_name_loc H H' l t v :
      nth None H l = Some t ->
      eval_name H t H' v ->
      eval_name H (Loc l) H' v
  | eval_name_app H H' H'' t0 t1 t2 v :
      eval_name H t1 H' (Abs t0) ->
      eval_name (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) H'' v ->
      eval_name H (App t1 t2) H'' v
  | eval_name_abs H t0 :
      eval_name H (Abs t0) H (Abs t0)
  | eval_name_let H H' ts t v :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      eval_name (H ++ map (Some \o subst s) ts) (subst s t) H' v ->
      eval_name H (Let ts t) H' v
  | eval_name_vcons H c ls :
      eval_name H (VCons c ls) H (VCons c ls)
  | eval_name_cons H c ts :
      eval_name H (Cons c ts) (H ++ map Some ts)
        (VCons c (mkseq (addn (size H)) (size ts)))
  | eval_name_case H H' H'' i c ls t t0 pts v :
      eval_name H t H' (VCons c ls) ->
      (forall d, nth d pts i = (c, size ls, t0)) ->
      (forall j d t0, nth d pts j = (c, size ls, t0) -> i <= j) ->
      eval_name H' (subst (scat (map Loc ls) Var) t0) H'' v ->
      eval_name H (Case t pts) H'' v.

CoInductive diverge_name : seq (option term) -> term -> Prop :=
  | diverge_name_loc H l t :
      nth None H l = Some t ->
      diverge_name H t ->
      diverge_name H (Loc l)
  | diverge_name_appL H t1 t2 :
      diverge_name H t1 ->
      diverge_name H (App t1 t2)
  | diverge_name_beta H H' t0 t1 t2 :
      eval_name H t1 H' (Abs t0) ->
      diverge_name (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) ->
      diverge_name H (App t1 t2)
  | diverge_name_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      diverge_name (H ++ map (Some \o subst s) ts) (subst s t) ->
      diverge_name H (Let ts t)
  | diverge_name_case H t pts :
      diverge_name H t ->
      diverge_name H (Case t pts)
  | diverge_name_casematch H H' i c ls t t0 pts :
      eval_name H t H' (VCons c ls) ->
      (forall d, nth d pts i = (c, size ls, t0)) ->
      (forall j d t0, nth d pts j = (c, size ls, t0) -> i <= j) ->
      diverge_name H' (subst (scat (map Loc ls) Var) t0) ->
      diverge_name H (Case t pts).

Inductive red_name : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | red_name_loc H l t :
      nth None H l = Some t ->
      red_name H (Loc l) H t
  | red_name_appL H H' t1 t1' t2 :
      red_name H t1 H' t1' ->
      red_name H (App t1 t2) H' (App t1' t2)
  | red_name_beta H t11 t2 :
      red_name H (App (Abs t11) t2) (rcons H (Some t2)) (subst (scons (Loc (size H)) Var) t11)
  | red_name_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      red_name H (Let ts t) (H ++ map (Some \o subst s) ts) (subst s t)
  | red_name_cons H c ts :
      red_name H (Cons c ts) (H ++ map Some ts)
        (VCons c (mkseq (addn (size H)) (size ts)))
  | red_name_case H H' t t' pts :
      red_name H t H' t' ->
      red_name H (Case t pts) H' (Case t' pts)
  | red_name_casematch H i c ls t0 pts :
      (forall d, nth d pts i = (c, size ls, t0)) ->
      (forall j d t0, nth d pts j = (c, size ls, t0) -> i <= j) ->
      red_name H (Case (VCons c ls) pts) H (subst (scat (map Loc ls) Var) t0).

Inductive wf_term (p : nat -> Prop) : term -> Prop :=
  | wf_term_loc l :
      p l ->
      wf_term p (Loc l)
  | wf_term_var x :
      wf_term p (Var x)
  | wf_term_abs t :
      wf_term p t ->
      wf_term p (Abs t)
  | wf_term_app t1 t2 :
      wf_term p t1 ->
      wf_term p t2 ->
      wf_term p (App t1 t2)
  | wf_term_let ts t :
      ( forall x, x < size ts -> forall d,
        wf_term p (nth d ts x) ) ->
      wf_term p t ->
      wf_term p (Let ts t)
  | wf_term_vcons c ls :
      ( forall x, x < size ls -> forall d,
        p (nth d ls x) ) ->
      wf_term p (VCons c ls)
  | wf_term_cons c ts :
      ( forall x, x < size ts -> forall d,
        wf_term p (nth d ts x) ) ->
      wf_term p (Cons c ts)
  | wf_term_case t pts :
      wf_term p t ->
      ( forall x, x < size pts -> forall d,
        wf_term p (nth d pts x).2 ) ->
      wf_term p (Case t pts).

Inductive corr_term (f : nat -> nat -> Prop) : term -> term -> Prop :=
  | corr_term_loc l l' :
      f l l' ->
      corr_term f (Loc l) (Loc l')
  | corr_term_var x :
      corr_term f (Var x) (Var x)
  | corr_term_abs t t' :
      corr_term f t t' ->
      corr_term f (Abs t) (Abs t')
  | corr_term_app t1 t1' t2 t2' :
      corr_term f t1 t1' ->
      corr_term f t2 t2' ->
      corr_term f (App t1 t2) (App t1' t2')
  | corr_term_let ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term f (nth d ts x) (nth d ts' x) ) ->
      corr_term f t t' ->
      corr_term f (Let ts t) (Let ts' t')
  | corr_term_vcons c ls ls' :
      size ls = size ls' ->
      ( forall x, x < size ls -> forall d,
        f (nth d ls x) (nth d ls' x) ) ->
      corr_term f (VCons c ls) (VCons c ls')
  | corr_term_cons c ts ts' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term f (nth d ts x) (nth d ts' x) ) ->
      corr_term f (Cons c ts) (Cons c ts')
  | corr_term_case t t' pts pts' :
      corr_term f t t' ->
      size pts = size pts' ->
      ( forall x d,
        (nth d pts x).1 = (nth d pts' x).1 ) ->
      ( forall x, x < size pts -> forall d,
        corr_term f (nth d pts x).2 (nth d pts' x).2 ) ->
      corr_term f (Case t pts) (Case t' pts').

Hint Constructors value eval_name diverge_name red_name clos_refl_trans eval_name diverge_name wf_term corr_term wf_term corr_term.

Definition wf_heap_segment (p p' : nat -> Prop) H :=
  forall l, p l ->
  exists t, nth None H l = Some t /\ wf_term p' t.

Definition wf_heap p := wf_heap_segment p p.

Definition iso_heap_segment (f f' : nat -> nat -> Prop) H1 H2 :=
  forall l1 l2, f l1 l2 ->
  exists t1, nth None H1 l1 = Some t1 /\
  exists t2, nth None H2 l2 = Some t2 /\
  corr_term f' t1 t2.

Definition iso_heap f := iso_heap_segment f f.

Lemma value_eval_name H v :
  value v -> eval_name H v H v.
Proof. by inversion 1. Qed.

Lemma eval_name_value H H' t v :
  eval_name H t H' v -> value v.
Proof. by induction 1. Qed.

Lemma eval_name_det H H' t v :
  eval_name H t H' v ->
  forall H'' v',
  eval_name H t H'' v' ->
  H' = H'' /\ v = v'.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (IHeval_name1 _ _ H5). inversion 2. subst. eauto.
  - case: (IHeval_name1 _ _ H6). inversion 2. subst.
    have ? : i = i0.
    { apply: anti_leq.
      by rewrite (H1 _ _ _ (H7 (0, 0, Var 0))) (H9 _ _ _ (H0 (0, 0, Var 0))). } subst.
    move: (H0 (0, 0, Var 0)) (H7 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Lemma eval_name_diverge_name_disjoint H H' t v :
  eval_name H t H' v ->
  diverge_name H t ->
  False.
Proof.
  induction 1; inversion 1; subst; auto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (eval_name_det _ _ _ _ H0_ _ _ H5).
    inversion 2. subst. eauto.
  - case: (eval_name_det _ _ _ _ H0_ _ _ H6).
    inversion 2. subst.
    have ? : i = i0.
    { apply: anti_leq.
      by rewrite (H1 _ _ _ (H7 (0, 0, Var 0))) (H9 _ _ _ (H0 (0, 0, Var 0))). } subst.
    move: (H0 (0, 0, Var 0)) (H7 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Corollary value_diverge_name_disjoint H v :
  value v ->
  diverge_name H v ->
  False.
Proof.
  move => /(value_eval_name H).
  exact: eval_name_diverge_name_disjoint.
Qed.

Lemma value_red_name_disjoint H H' t t' :
  red_name H t H' t' ->
  value t ->
  False.
Proof. inversion 1; inversion 1. Qed.

Lemma red_name_apply_context_name H H' cs : forall t t',
  red_name H t H' t' ->
  red_name H (apply_context_name t cs) H' (apply_context_name t' cs).
Proof. elim cs => [ | [ ? ? ? ? ? /red_name_appL | ? ? ? ? ? /red_name_case ] ]; eauto. Qed.

Lemma red_name_appL_multi_aux p p' t2 :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t1 t1',
  p = (H, t1) ->
  p' = (H', t1') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, App t1 t2) (H', App t1' t2).
Proof.
  elim =>
    [ [ ? ? ] [ ? ? ] /= ? |
    | [ ? ? ] [ ? ? ] [ ? ? ] /= ? ? ? ? ];
  inversion 1; inversion 1; subst; eauto.
  apply: rt_step.
  by apply: red_name_appL => /=.
Qed.

Corollary red_name_appL_multi H H' t1 t1' t2 :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, App t1 t2) (H', App t1' t2).
Proof. move => /red_name_appL_multi_aux. by apply. Qed.

Lemma red_name_case_multi_aux p p' pts :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t t',
  p = (H, t) ->
  p' = (H', t') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, Case t pts) (H', Case t' pts).
Proof.
  elim =>
    [ [ ? ? ] [ ? ? ] /= ? |
    | [ ? ? ] [ ? ? ] [ ? ? ] /= ? ? ? ? ];
  inversion 1; inversion 1; subst; eauto.
  apply: rt_step.
  by apply: red_name_case => /=.
Qed.

Corollary red_name_case_multi H H' t t' pts :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, Case t pts) (H', Case t' pts).
Proof. move => /red_name_case_multi_aux. by apply. Qed.

Lemma red_name_apply_context_name_multi H H' cs : forall t t',
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, apply_context_name t cs) (H', apply_context_name t' cs).
Proof. elim cs => [ | [ ? ? ? ? ? /red_name_appL_multi | ? ? ? ? ? /red_name_case_multi ] ]; eauto. Qed.

Lemma value_normal t :
  value t ->
  forall H H' t',
  red_name H t H' t' ->
  False.
Proof. inversion 1; inversion 1. Qed.

Lemma red_name_det H t H' t' :
  red_name H t H' t' ->
  forall H'' t'',
  red_name H t H'' t'' ->
  H' = H'' /\ t' = t''.
Proof.
  induction 1; inversion 1; subst;
  try match goal with
  | H : red_name _ (Abs _) _ _ |- _ => inversion H
  | H : red_name _ (Cons _ _) _ _ |- _ => inversion H
  end; eauto.
  - by move: H0 H5 => ->; inversion 1.
  - by case (IHred_name _ _ H8) => ? ?; subst.
  - by case (IHred_name _ _ H8) => ? ?; subst.
  - inversion H0.
  - inversion H9.
  - have ? : i = i0.
    { apply: anti_leq.
      by rewrite (H11 _ _ _ (H0 (0, 0, Var 0))) (H1 _ _ _ (H10 (0, 0, Var 0))). } subst.
    move: (H0 (0, 0, Var 0)) (H10 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Lemma red_name_heap H t H' t' :
  red_name H t H' t' ->
  forall l t,
  nth None H l = Some t ->
  nth None H' l = Some t.
Proof.
  induction 1 => l0 ?; eauto;
  rewrite ?nth_rcons ?nth_cat;
  by case (leqP (size H) l0) => [ /(nth_default _) -> | ].
Qed.

Lemma red_name_multi_heap p p' :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall l t,
  nth None p.1 l = Some t ->
  nth None p'.1 l = Some t.
Proof.
  induction 1; eauto.
  apply: red_name_heap. eauto.
Qed.

Theorem eval_name_red_name_multi H t H' v :
  eval_name H t H' v ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', v).
Proof.
  induction 1 => //.
  - refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - refine (rt_trans _ _ _ (_, _) _
      (red_name_appL_multi _ _ _ _ _ IHeval_name1)
      (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _)) => /=; eauto.
  - refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - by apply: rt_step => /=.
  - refine (rt_trans _ _ _ (_, _) _
      (red_name_case_multi _ _ _ _ _ IHeval_name1)
      (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _)) => /=; eauto.
Qed.

Corollary eval_name_heap H H' t v :
  eval_name H t H' v ->
  forall l t,
  nth None H l = Some t ->
  nth None H' l = Some t.
Proof. by move => /eval_name_red_name_multi /red_name_multi_heap. Qed.

Hint Resolve eval_name_heap.

Lemma red_name_eval_name H t H' t' :
  red_name H t H' t' ->
  forall H'' v,
  eval_name H' t' H'' v ->
  eval_name H t H'' v.
Proof.
  induction 1; eauto.
  - inversion 1. subst. eauto.
  - inversion 1. subst. eauto.
  - inversion 1. subst. eauto.
Qed.

Theorem red_name_multi_eval_name_aux p p' :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' H'' t t' v,
  p = (H, t) ->
  p' = (H', t') ->
  eval_name H' t' H'' v ->
  eval_name H t H'' v.
Proof.
  move => /clos_rt_rt1n_iff.
  induction 1; inversion 1; inversion 1; subst; eauto.
  destruct y => [ ? ].
  apply: red_name_eval_name; eauto.
Qed.

Corollary red_name_multi_eval_name H t H' v :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', v) ->
  value v ->
  eval_name H t H' v.
Proof.
  move => Hrt Hv.
  apply: red_name_multi_eval_name_aux; eauto.
  exact: value_eval_name.
Qed.

Lemma diverge_reducible H t :
  diverge_name H t ->
  exists H' t', red_name H t H' t' /\ diverge_name H' t'.
Proof.
  induction t; inversion 1; subst; eauto.
  - case (IHt1 H4) => ? [ ? [ ] ]; eauto 6.
  - move: (eval_name_red_name_multi _ _ _ _ H5) => /clos_rt_rt1n_iff Hrt.
    inversion Hrt; subst; eauto.
    destruct y.
    move: H2 => /clos_rt_rt1n_iff /red_name_multi_eval_name. eauto 7.
  - case (IHt H4) => ? [ ? [ ] ]. eauto 6.
  - move: (eval_name_red_name_multi _ _ _ _ H4) => /clos_rt_rt1n_iff Hrt.
    inversion Hrt; subst; eauto.
    destruct y.
    move: H2 => /clos_rt_rt1n_iff /red_name_multi_eval_name. eauto 7.
Qed.
  
Lemma diverge_name_red_name_aux p p' :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t t',
  p = (H, t) ->
  p' = (H', t') ->
  diverge_name H t ->
  diverge_name H' t'.
Proof.
  move => /clos_rt_rt1n_iff Hrt.
  induction Hrt; inversion 1; inversion 1; subst; eauto.
  destruct y => [ /diverge_reducible [ ? [ ? [ /(red_name_det _ _ _ _ H) /= [ <- <- ] ] ] ] ]; eauto.
Qed.

Theorem diverge_name_red_name H t :
  diverge_name H t ->
  forall H' t',
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
  exists H'' t'', red_name H' t' H'' t''.
Proof.
  move => Hdiv ? ?
    /diverge_name_red_name_aux /(_ _ _ _ _ erefl erefl Hdiv)
    /diverge_reducible [ ? [ ? [ ] ] ]. eauto.
Qed.

Theorem red_name_multi_diverge_name :
  forall H t,
  ( forall H' t',
    clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
    exists H'' t'', red_name H' t' H'' t'' ) ->
  diverge_name H t.
Proof.
  cofix red_name_multi_diverge_name.
  move => H [ ? | ? | ? | t1 ? | ? ? | ? ? | ? ? | t ? ] Hdiv.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1. subst.
    apply: diverge_name_loc; eauto.
    apply: red_name_multi_diverge_name => ? ? ?.
    apply: Hdiv.
    refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1.
  - case (classic (exists H' v1, eval_name H t1 H' v1)) =>
      [ [ ? [ ? Heval ] ] | Hdiv1 ].
    { move:
        (Hdiv _ _
          (red_name_appL_multi _ _ _ _ _
            (eval_name_red_name_multi _ _ _ _ Heval))) => [ ? [ ] ].
      inversion 1; subst.
      - case (value_red_name_disjoint _ _ _ _ H6 (eval_name_value _ _ _ _ Heval)).
      - apply: diverge_name_beta; eauto.
        apply: red_name_multi_diverge_name => ? ? ?.
        apply: Hdiv.
        refine (rt_trans _ _ _ (_, _) _ _ _).
        + apply: red_name_appL_multi.
          apply: eval_name_red_name_multi. eauto.
        + refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto. }
    { apply: diverge_name_appL.
      apply: red_name_multi_diverge_name => ? ? Hrt.
      move: (Hdiv _ _ (red_name_appL_multi _ _ _ _ _ Hrt)) => [ ? [ ] ];
      inversion 1; subst; eauto.
      case Hdiv1. repeat eexists.
      apply: red_name_multi_eval_name; eauto. }
  - apply: diverge_name_let.
    apply: red_name_multi_diverge_name => ? ? ?.
    apply: Hdiv.
    refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ].
    inversion 1.
  - move: (Hdiv _ _ (rt_step _ _ (_, _) (_, _) (red_name_cons _ _ _))) => [ ? [ ] ].
    inversion 1.
  - case (classic (exists H' v, eval_name H t H' v)) =>
      [ [ ? [ ? Heval ] ] | Hdiv' ].
    { move:
        (Hdiv _ _
          (red_name_case_multi _ _ _ _ _
            (eval_name_red_name_multi _ _ _ _ Heval))) => [ ? [ ] ].
      inversion 1; subst.
      - case (value_red_name_disjoint _ _ _ _ H6 (eval_name_value _ _ _ _ Heval)).
      - apply: diverge_name_casematch; eauto.
        apply: red_name_multi_diverge_name => ? ? ?.
        apply: Hdiv.
        refine (rt_trans _ _ _ (_, _) _ _ _).
        + apply: red_name_case_multi.
          apply: eval_name_red_name_multi. eauto.
        + refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto. }
    { apply: diverge_name_case.
      apply: red_name_multi_diverge_name => ? ? Hrt.
      move: (Hdiv _ _ (red_name_case_multi _ _ _ _ _ Hrt)) => [ ? [ ] ];
      inversion 1; subst; eauto.
      case Hdiv'. repeat eexists.
      apply: red_name_multi_eval_name; eauto. }
Qed.

Lemma wf_term_impl (p p' : nat -> Prop) t :
  wf_term p t ->
  (forall l, p l -> p' l) ->
  wf_term p' t.
Proof. induction 1; constructor; eauto. Qed.

Lemma corr_term_value R v v' :
  corr_term R v v' ->
  value v <-> value v'.
Proof. by inversion 1; split; inversion 1; eauto. Qed.

Lemma corr_term_valueL R v v' :
  corr_term R v v' ->
  value v ->
  value v'.
Proof. by move => Hcorr /(corr_term_value _ _ _ Hcorr). Qed.

Lemma corr_term_valueR R v v' :
  corr_term R v v' ->
  value v' ->
  value v.
Proof. by move => Hcorr /(corr_term_value _ _ _ Hcorr). Qed.

Hint Resolve corr_term_valueL corr_term_valueR.

Lemma corr_term_refl (p : nat -> Prop) t :
  wf_term p t ->
  corr_term (fun l l' => l = l' /\ p l) t t.
Proof. induction 1; econstructor; eauto. Qed.

Lemma corr_term_sym R t t' :
  corr_term R t t' ->
  corr_term (fun l l' => R l' l) t' t.
Proof. induction 1; econstructor; eauto. Qed.

Lemma corr_term_comp R R' t t' :
  corr_term R t t' ->
  forall t'', corr_term R' t' t'' ->
  corr_term (fun l l'' => exists l', R l l' /\ R' l' l'') t t''.
Proof.
  induction 1; inversion 1; subst; econstructor; (congruence || eauto 6).
  move => ? Hlt.
  move: H Hlt (H0 _ Hlt) => -> /H6. eauto.
Qed.

Lemma corr_term_impl (R R' : nat -> nat -> Prop) t t' :
  corr_term R t t' ->
  (forall l l', R l l' -> R' l l') ->
  corr_term R' t t'.
Proof. induction 1; eauto. Qed.

Lemma corr_term_wf_termL f t t' :
  corr_term f t t' ->
  wf_term (fun l => exists l', f l l') t.
Proof. induction 1; constructor; eauto. Qed.

Corollary corr_term_wf_termR f t t' :
  corr_term f t t' ->
  wf_term (fun l' => exists l, f l l') t'.
Proof. by move => /corr_term_sym /corr_term_wf_termL. Qed.

Lemma corr_term_rename R t t' :
  corr_term R t t' ->
  forall r,
  corr_term R (rename r t) (rename r t').
Proof.
  induction 1 => /=; constructor; rewrite ?size_map; eauto.
  - move => ? ? d.
    rewrite !(nth_map d) -?H; eauto.
  - by rewrite H.
  - move => ? ? d.
    rewrite !(nth_map d) -?H; eauto.
  - move => x d.
    case (leqP (size pts) x) => ?.
    + by rewrite !nth_default ?size_map -?H0.
    + rewrite !(nth_map d) -?H0; eauto.
  - move => ? ? d.
    rewrite !(nth_map d) -?H0 ?H1; eauto.
Qed.

Lemma corr_term_subst R t t' :
  corr_term R t t' ->
  forall s s',
  (forall x, corr_term R (s x) (s' x)) ->
  corr_term R (subst s t) (subst s' t').
Proof.
  induction 1 => ? ? Hs /=; (constructor || apply: Hs); rewrite ?size_map; eauto.
  - apply IHcorr_term => [ [ | ? ] ].
    + exact: corr_term_var.
    + exact: corr_term_rename.
  - move => ? ? d.
    rewrite !(nth_map d) -?H => //.
    apply: H1 => // y.
    rewrite !upn_unfold.
    case: (leqP (size ts) y) => ? //.
    exact: corr_term_rename.
  - apply: IHcorr_term => x.
    rewrite !upn_unfold -?H.
    case: (leqP (size ts) x) => ? //.
    exact: corr_term_rename.
  - move => ? ? d.
    rewrite !(nth_map d) -?H => //.
    exact: H1.
  - move => x d.
    case (leqP (size pts) x) => ?.
    + by rewrite !nth_default ?size_map -?H0.
    + rewrite !(nth_map d) -?H0; eauto.
  - move => x ? d.
    rewrite !(nth_map d) -?H0 => //=.
    apply: H3 => // y.
    rewrite !upn_unfold -?H1 => //.
    case: (leqP (nth d pts x).1.2 y) => ? //.
    exact: corr_term_rename.
Qed.

Lemma wf_heap_segment_weaken (p p' q q' : nat -> Prop) H H' :
  wf_heap_segment p q H ->
  ( forall l, p' l -> p l ) ->
  ( forall l, q l -> q' l ) ->
  ( forall l, p' l ->
    forall t, 
    nth None H l = Some t -> 
    nth None H' l = Some t ) ->
  wf_heap_segment p' q' H'.
Proof.
  move => Hwf Hdom ? Hext ? Hp.
  move: (Hp) => /Hdom /Hwf [ ? [ /(Hext _ Hp) -> ] ].
  eauto using wf_term_impl.
Qed.

Definition wf_heap_segment_dom p p' q H Hwf Hdom :=
  wf_heap_segment_weaken p p' q _ H _ Hwf Hdom (fun _ H => H) (fun _ _ _ H => H).
Definition wf_heap_segment_cod p q q' H Hwf Hcod :=
  wf_heap_segment_weaken p _ q q' H _ Hwf (fun _ H => H) Hcod (fun _ _ _ H => H).
Definition wf_heap_segment_ext p p' H H' Hwf :=
  wf_heap_segment_weaken p _ p' _ H H' Hwf (fun _ H => H) (fun _ H => H).

Lemma wf_heap_segment_union p p' q H :
  wf_heap_segment p q H ->
  wf_heap_segment p' q H ->
  wf_heap_segment (fun l => p l \/ p' l) q H.
Proof. move => Hwf Hwf' ? [ /Hwf | /Hwf' ] [ ? [ -> ] ]; eauto. Qed.

Lemma wf_heap_segment_bound p q H :
  wf_heap_segment p q H ->
  forall l, p l ->
  l < size H.
Proof.
  move => Hwf l /Hwf [ ? [ ] ].
  by case: (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Corollary wf_heap_segment_cat p q H Hd :
  wf_heap_segment p q H ->
  wf_heap_segment p q (H ++ Hd).
Proof.
  move => /wf_heap_segment_ext.
  apply => l ?.
  by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary wf_heap_segment_rcons p q H o :
  wf_heap_segment p q H ->
  wf_heap_segment p q (rcons H o).
Proof. rewrite -cats1. exact: wf_heap_segment_cat. Qed.

Lemma iso_heap_segment_weaken (fdom fdom' fcod fcod' : nat -> nat -> Prop) H1 H1' H2 H2' :
  iso_heap_segment fdom fcod H1 H2 ->
  ( forall l l', fdom' l l' -> fdom l l' ) ->
  ( forall l l', fcod l l' -> fcod' l l' ) ->
  ( forall l l', fdom' l l' ->
    forall t,
    nth None H1 l = Some t ->
    nth None H1' l = Some t ) ->
  ( forall l l', fdom' l l' ->
    forall t,
    nth None H2 l' = Some t ->
    nth None H2' l' = Some t ) ->
  iso_heap_segment fdom' fcod' H1' H2'.
Proof.
  move => Hiso Hdom Hcod HL HR ? ? Hf.
  move: (Hf) => /Hdom /Hiso [ ? [ /(HL _ _ Hf) -> [ ? [ /(HR _ _ Hf) -> ] ] ] ].
  eauto 6 using corr_term_impl.
Qed.

Definition iso_heap_segment_dom (fdom fdom' fcod : nat -> nat -> Prop) H1 H2 Hiso Hdom :=
  iso_heap_segment_weaken fdom fdom' fcod _ H1 _ H2 _ Hiso Hdom (fun _ _ H => H) (fun _ _ _ _ H => H) (fun _ _ _ _ H => H).
Definition iso_heap_segment_cod (fdom fcod fcod' : nat -> nat -> Prop) H1 H2 Hiso Hcod :=
  iso_heap_segment_weaken fdom _ fcod fcod' H1 _ H2 _ Hiso (fun _ _ H => H) Hcod (fun _ _ _ _ H => H) (fun _ _ _ _ H => H).
Definition iso_heap_segment_extL (fdom fcod : nat -> nat -> Prop) H1 H1' H2 Hiso HextL :=
  iso_heap_segment_weaken fdom _ fcod _ H1 H1' H2 _ Hiso (fun _ _ H => H) (fun _ _ H => H) HextL (fun _ _ _ _ H => H).
Definition iso_heap_segment_extR (fdom fcod : nat -> nat -> Prop) H1 H2 H2' Hiso :=
  iso_heap_segment_weaken fdom _ fcod _ H1 _ H2 H2' Hiso (fun _ _ H => H) (fun _ _ H => H) (fun _ _ _ _ H => H).

Lemma iso_heap_segment_union fdom fdom' fcod H1 H2 :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom' fcod H1 H2 ->
  iso_heap_segment (fun l l' => fdom l l' \/ fdom' l l') fcod H1 H2.
Proof. by move => Hiso Hiso' ? ? [ /Hiso | /Hiso' ]. Qed.

Lemma iso_heap_segment_refl p q H :
  wf_heap_segment p q H ->
  iso_heap_segment (fun l l' => l = l' /\ p l) (fun l l' => l = l' /\ q l) H H.
Proof.
  move => Hwf ? ? [ -> /Hwf [ ? [ -> ] ] ].
  eauto 6 using corr_term_refl.
Qed.

Lemma iso_heap_segment_sym f f' H H' :
  iso_heap_segment f f' H H' ->
  iso_heap_segment (fun l l' => f l' l) (fun l l' => f' l' l) H' H.
Proof.
  move => Hiso ? ? /Hiso [ ? [ -> [ ? [ -> ] ] ] ].
  eauto 6 using corr_term_sym.
Qed.

Lemma iso_heap_segment_comp fdom fdom' fcod fcod' H H' H'' :
  iso_heap_segment fdom fcod H H' ->
  iso_heap_segment fdom' fcod' H' H'' ->
  iso_heap_segment
    (fun l l'' => exists l', fdom l l' /\ fdom' l' l'')
    (fun l l'' => exists l', fcod l l' /\ fcod' l' l'') H H''.
Proof.
  move => Hiso Hiso' ? ? [ ? [ ] ]
    /Hiso [ ? [ -> [ ? [ Hnth ? ] ] ] ]
    /Hiso' [ ? [ Hnth' [ ? [ -> ? ] ] ] ].
  move: Hnth Hnth' => ->. inversion 1. subst.
  eauto 6 using corr_term_comp.
Qed.

Lemma iso_heap_segment_boundL f f' H H' :
  iso_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l < size H.
Proof.
  move => Hiso l ? /Hiso [ ? [ ] ].
  by case: (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Lemma iso_heap_boundR f f' H H' :
  iso_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l' < size H'.
Proof.
  move => Hiso ? l' /Hiso [ ? [ ? [ ? [ ] ] ] ].
  by case: (leqP (size H') l') => [ /(nth_default _) -> | ].
Qed.

Lemma iso_heap_segment_wf_heap_segmentL f f' H H' :
  iso_heap_segment f f' H H' ->
  wf_heap_segment (fun l => exists l', f l l') (fun l => exists l', f' l l') H.
Proof.
  move => Hiso ? [ ? ] /Hiso [ ? [ -> [ ? [ ] ] ] ].
  eauto using corr_term_wf_termL.
Qed.

Corollary iso_heap_segment_wf_heap_segmentR f f' H H' :
  iso_heap_segment f f' H H' ->
  wf_heap_segment (fun l' => exists l, f l l') (fun l' => exists l, f' l l') H'.
Proof. by move => /iso_heap_segment_sym /iso_heap_segment_wf_heap_segmentL. Qed.

Corollary iso_heap_segment_catL f f' H1 H2 Hd :
  iso_heap_segment f f' H1 H2 ->
  iso_heap_segment f f' (H1 ++ Hd) H2.
Proof.
  move => /iso_heap_segment_extL.
  apply => l ?.
  by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary iso_heap_segment_rconsL f f' H1 H2 o :
  iso_heap_segment f f' H1 H2 ->
  iso_heap_segment f f' (rcons H1 o) H2.
Proof. by rewrite -cats1 => /iso_heap_segment_catL. Qed.

Corollary iso_heap_segment_catR f f' H1 H2 Hd :
  iso_heap_segment f f' H1 H2 ->
  iso_heap_segment f f' H1 (H2 ++ Hd).
Proof. by move => /iso_heap_segment_sym /iso_heap_segment_catL /iso_heap_segment_sym. Qed.

Corollary iso_heap_segment_rconsR f f' H1 H2 o :
  iso_heap_segment f f' H1 H2 ->
  iso_heap_segment f f' H1 (rcons H2 o).
Proof. by rewrite -cats1 => /iso_heap_segment_catR. Qed.

Theorem red_name_iso_heap H1 H1' t1 t1' :
  red_name H1 t1 H1' t1' ->
  forall R H2 t2,
  corr_term R t1 t2 ->
  iso_heap R H1 H2 ->
  exists R' H2' t2',
  corr_term R' t1' t2' /\
  iso_heap R' H1' H2' /\
  red_name H2 t2 H2' t2' /\
  (forall l1 l2, R l1 l2 -> R' l1 l2).
Proof.
  induction 1; inversion 1; subst => Hheap.
  - move: H0 (Hheap _ _ H4) => -> [ ? [ ] ].
    inversion 1. subst => [ [ ? [ ? Hterm ] ] ]. repeat (eexists; eauto).
  - move: (IHred_name _ _ _ H5 Hheap) => [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto using corr_term_impl).
  - inversion H4. subst.
    exists (fun l l' => R l l' \/ l = size H /\ l' = size H2),
      (rcons H2 (Some t2')), (subst (scons (Loc (size H2)) Var) t').
    repeat split; eauto.
    + apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl.
    + apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
      * apply: iso_heap_segment_rconsL.
        apply: iso_heap_segment_rconsR.
        apply: iso_heap_segment_cod; eauto.
      * rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl.
  - eexists (fun l l' => R l l' \/ exists n, n < size ts /\ l = size H + n /\ l' = size H2 + n),
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts'),
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var) t'). repeat split; eauto.
    + apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite /s !nth_scat.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6.
    + apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
      * apply: iso_heap_segment_catL.
        apply: iso_heap_segment_catR.
        apply: iso_heap_segment_cod; eauto.
      * rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite /s !nth_scat.
        { case (leqP (size ts) y) => ?.
          - by rewrite !nth_default ?size_mkseq.
          - rewrite !nth_mkseq => /=; eauto 6. }
    + by rewrite H4.
  - exists (fun l l' => R l l' \/ exists n, n < size ts /\ l = size H + n /\ l' = size H2 + n),
      (H2 ++ map Some ts'),
      (VCons c (mkseq (addn (size H2)) (size ts'))). repeat split; eauto.
    + (constructor; rewrite !size_mkseq) => [ | ? ? ? ]; rewrite ?nth_mkseq -?H4; eauto.
    + apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
      * apply: iso_heap_segment_catL.
        apply: iso_heap_segment_catR.
        apply: iso_heap_segment_cod; eauto.
      * rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists. eauto using corr_term_impl.
  - move: (IHred_name _ _ _ H5 Hheap) =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto using corr_term_impl).
  - inversion H6. subst.
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H0 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H11). }
    exists R, H2, (subst (scat (map Loc ls') Var) (nth (0, 0, Var 0) pts' i).2).
    repeat split; eauto.
    + apply: corr_term_subst => [ | x ].
      * by move: H0 (H10 _ Hlt (0, 0, Var 0)) => ->.
      * rewrite !nth_scat !size_map H9.
        { case (leqP (size ls) x) => ?.
          - rewrite !nth_default ?size_map -?H9; eauto.
          - rewrite !(nth_map 0) -?H9; eauto. }
    + apply red_name_casematch with (i := i) => [ d | j d ].
      * rewrite (surjective_pairing (nth d pts' i)) -H9 -H8 H0 => /=.
        do 2 f_equal. apply: set_nth_default. congruence.
      * move: (H1 j d).
        rewrite
          (surjective_pairing (nth d pts j))
          (surjective_pairing (nth d pts' j)) H8 H9 => Hcontra.
        inversion 1. subst.
        apply: Hcontra. f_equal. eauto.
Qed.

Lemma red_name_multi_iso_heap p p' :
  clos_refl_trans_1n _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H1 H1' t1 t1',
  p = (H1, t1) ->
  p' = (H1', t1') ->
  forall R H2 t2,
  corr_term R t1 t2 ->
  iso_heap R H1 H2 ->
  exists R' H2' t2',
  corr_term R' t1' t2' /\
  iso_heap R' H1' H2' /\
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H2, t2) (H2', t2') /\
  (forall l1 l2, R l1 l2 -> R' l1 l2).
Proof.
  induction 1 => ? ? ? ?; inversion 1; inversion 1; subst => [ ? ? ? Hterm Hheap ]; subst.
  - repeat (eexists; eauto).
  - destruct y.
    move: (red_name_iso_heap _ _ _ _ H _ _ _ Hterm Hheap) =>
      /= [ ? [ ? [ ? [ Hterm' [ Hheap' [ ? ? ] ] ] ] ] ].
    move: (IHclos_refl_trans_1n _ _ _ _ erefl erefl _ _ _ Hterm' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
    refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
Qed.
    
Theorem eval_name_iso_heap H1 H1' t1 v1
  (Heval : eval_name H1 t1 H1' v1) R H2 t2
  (Hterm : corr_term R t1 t2)
  (Hheap : iso_heap R H1 H2) :
  exists R' H2' v2,
  corr_term R' v1 v2 /\
  iso_heap R' H1' H2' /\
  eval_name H2 t2 H2' v2 /\
  (forall l1 l2, R l1 l2 -> R' l1 l2).
Proof.
  move: (Heval) =>
    /eval_name_red_name_multi /clos_rt_rt1n_iff /red_name_multi_iso_heap
    /(_ _ _ _ _ erefl erefl _ _ _ Hterm Hheap) [ ? [ ? [ ? [ Hterm' [ ? [ ] ] ] ] ] ]
    /red_name_multi_eval_name Heval'.
  move: (eval_name_value _ _ _ _ Heval) => /(corr_term_value _ _ _ Hterm') /Heval' ? ?.
  repeat (eexists; eauto).
Qed.

Lemma clos_trans_clos_refl_trans A R x y :
  clos_trans A R x y ->
  clos_refl_trans A R x y.
Proof. induction 1; eauto. Qed.

Corollary clos_trans_clos_refl_trans_1n A R x z :
  clos_trans A R x z ->
  exists y, R x y /\ clos_refl_trans _ R y z.
Proof.
  move => /(clos_trans_t1n _ _ _ _).
  inversion 1; subst; repeat (eexists; eauto).
  apply: clos_trans_clos_refl_trans.
  exact: clos_t1n_trans.
Qed.

Lemma diverge_name_red_name_cycle_aux p p' :
  clos_refl_trans_1n _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall cs R H1 H1' H2' t1 t1' t2',
  p = (H1', t1') ->
  p' = (H2', t2') ->
  corr_term R t1 t1' ->
  iso_heap R H1 H1' ->
  clos_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H1, t1) (H1', apply_context_name t1' cs) ->
  exists R' H2 t2,
  clos_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H2, t2) (H2', apply_context_name t2' cs) /\
  corr_term R' t2 t2' /\
  iso_heap R' H2 H2' /\
  (forall l1 l2, R l1 l2 -> R' l1 l2).
Proof.
  induction 1; inversion 1; inversion 1; subst => [ Hterm Hheap ].
  - repeat (eexists; eauto).
  - destruct y => /(clos_trans_clos_refl_trans_1n _ _ _ _) [ [ H1_ t1_ ] /= [ Hred Hrt ] ].
    move: (red_name_iso_heap _ _ _ _ Hred _ _ _  Hterm Hheap) =>
      [ R' [ H1'_ [ t1'_ [ Hterm' [ Hheap' [ Hred' ? ] ] ] ] ] ].
    case: (red_name_det _ _ _ _ H _ _ Hred') => /= ? ?. subst.
    have Hrt' : clos_trans _
      (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H1_, t1_) (H1'_, apply_context_name t1'_ cs).
    { apply: clos_rt_t; eauto.
      constructor.
      apply: red_name_apply_context_name. eauto. }
    move: (IHclos_refl_trans_1n _ _ _ _ _ _ _ _ erefl erefl Hterm' Hheap' Hrt') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Lemma diverge_name_red_name_cycle R H H' t t' cs :
  iso_heap R H H' ->
  corr_term R t t' ->
  clos_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', apply_context_name t' cs) ->
  diverge_name H' t'.
Proof.
  move => Hheap Hterm Ht.
  apply: red_name_multi_diverge_name => ? ? Hrt.
  move: (diverge_name_red_name_cycle_aux _ _
    (clos_rt_rt1n _ _ _ _ Hrt) _ _ _ _ _ _ _ _ erefl erefl Hterm Hheap Ht) => 
  [ ? [ ? [ ? [ Ht' [ Hterm' [ Hheap' ? ] ] ] ] ] ].
  move: (clos_trans_clos_refl_trans_1n _ _ _ _ Ht') =>
    [ ? [ /red_name_iso_heap /(_ _ _ _ Hterm' Hheap')
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
  repeat (eexists; eauto).
Qed.
