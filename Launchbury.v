From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet Heaps.
Require Import Relations Classical.

Inductive eval_need : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | eval_need_loc H H' l t v :
      nth None H l = Some t ->
      eval_need (set_nth None H l None) t H' v ->
      eval_need H (Loc l) (set_nth None H' l (Some v)) v
  | eval_need_app H H' H'' t0 t1 t2 v :
      eval_need H t1 H' (Abs t0) ->
      eval_need H' (subst (scons t2 Var) t0) H'' v ->
      eval_need H (App t1 t2) H'' v
  | eval_need_abs H t0 :
      eval_need H (Abs t0) H (Abs t0)
  | eval_need_let H H' ts t v :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      eval_need (H ++ map (@Some _ \o subst s) ts) (subst s t) H' v ->
      eval_need H (Let ts t) H' v
  | eval_need_ctor H c ts :
      eval_need H (Ctor c ts) H (Ctor c ts)
  | eval_need_case H H' H'' c i t t0 ts pts v :
      eval_need H t H' (Ctor c ts) ->
      ( forall d, nth d pts i = (c, size ts, t0) ) ->
      ( forall j, j < i ->
        forall d t0, 
        nth d pts j = (c, size ts, t0) ->
        False ) ->
      eval_need H' (subst (scat ts Var) t0) H'' v ->
      eval_need H (Case t pts) H'' v.

CoInductive diverge_need : seq (option term) -> term -> Prop :=
  | diverge_need_loc H l t :
      nth None H l = Some t ->
      diverge_need (set_nth None H l None) t ->
      diverge_need H (Loc l)
  | diverge_need_appL H t1 t2 :
      diverge_need H t1 ->
      diverge_need H (App t1 t2)
  | diverge_need_appabs H H' t0 t1 t2 :
      eval_need H t1 H' (Abs t0) ->
      diverge_need H' (subst (scons t2 Var) t0) ->
      diverge_need H (App t1 t2)
  | diverge_need_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      diverge_need (H ++ map (@Some _ \o subst s) ts) (subst s t) ->
      diverge_need H (Let ts t)
  | diverge_need_case H t pts :
      diverge_need H t ->
      diverge_need H (Case t pts)
  | diverge_need_casematch H H' c i t t0 ts pts :
      eval_need H t H' (Ctor c ts) ->
      ( forall d, nth d pts i = (c, size ts, t0) ) ->
      ( forall j, j < i ->
        forall d t0, 
        nth d pts j = (c, size ts, t0) ->
        False ) ->
      diverge_need H' (subst (scat ts Var) t0) ->
      diverge_need H (Case t pts).

Inductive cycle_need : seq (option term) -> term -> Prop :=
  | cycle_need_locNone H l :
      nth None H l = None ->
      cycle_need H (Loc l)
  | cycle_need_locSome H l t :
      nth None H l = Some t ->
      cycle_need (set_nth None H l None) t ->
      cycle_need H (Loc l)
  | cycle_need_appL H t1 t2 :
      cycle_need H t1 ->
      cycle_need H (App t1 t2)
  | cycle_need_appabs H H' t0 t1 t2 :
      eval_need H t1 H' (Abs t0) ->
      cycle_need H' (subst (scons t2 Var) t0) ->
      cycle_need H (App t1 t2)
  | cycle_need_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      cycle_need (H ++ map (@Some _ \o subst s) ts) (subst s t) ->
      cycle_need H (Let ts t)
  | cycle_need_case H t pts :
      cycle_need H t ->
      cycle_need H (Case t pts)
  | cycle_need_casematch H H' c i t t0 ts pts :
      eval_need H t H' (Ctor c ts) ->
      ( forall d, nth d pts i = (c, size ts, t0) ) ->
      ( forall j, j < i ->
        forall d t0, 
        nth d pts j = (c, size ts, t0) ->
        False ) ->
      cycle_need H' (subst (scat ts Var) t0) ->
      cycle_need H (Case t pts).

Definition consistent_segment (R R' : nat -> nat -> Prop) H2 :=
  iso_heap_segment
    (fun l2 l2' => exists l1, R l1 l2 /\ R l1 l2')
    (fun l2 l2' => exists l1, R' l1 l2 /\ R' l1 l2') H2 H2.

Definition consistent R := consistent_segment R R.

Definition corr_heap_segment (R R' : nat -> nat -> Prop) H1 H2 :=
  forall l1 l2, R l1 l2 ->
  exists t1, nth None H1 l1 = Some t1 /\
  exists t2, nth None H2 l2 = Some t2 /\
  ( corr_term R' t1 t2 \/
    exists H2' v2,
    eval_name H2 t2 H2' v2 /\
    exists S,
    iso_heap S H2 H2' /\
    corr_term (fun l1 l2' => exists l2, R' l1 l2 /\ S l2 l2') t1 v2 ).

Definition trace_segment (R R' : nat -> nat -> Prop) (H1 H2 : seq (option term)) t2 C :=
  forall l1 l2, R l1 l2 ->
  nth None H1 l1 = None /\ l1 < size H1 /\
  exists R0 H0 l0,
  R0 l1 l0 /\
  consistent R0 H0 /\
  clos_trans _
    (fun p p' => red_name p.1 p.2 p'.1 p'.2)
    (H0, Loc l0) (H2, apply_context_name t2 (C l1)) /\
  forall l1 l2, R0 l1 l2 -> R' l1 l2.

Hint Constructors eval_need cycle_need.

Lemma value_eval_need H v :
  value v -> eval_need H v H v.
Proof. by inversion 1. Qed.

Lemma eval_need_value H H' t v :
  eval_need H t H' v -> value v.
Proof. by induction 1. Qed.

Lemma eval_need_det H H' t v :
  eval_need H t H' v ->
  forall H'' v',
  eval_need H t H'' v' ->
  H' = H'' /\ v = v'.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst.
    by case: (IHeval_need _ _ H7) => -> ->.
  - case: (IHeval_need1 _ _ H5) => ?. inversion 1. subst. eauto.
  - case: (IHeval_need1 _ _ H6). inversion 2. subst.
    have ? : i = i0.
    { by case: (ltngtP i i0) =>
        [ /H9 /(_ (0, 0, Var 0) _ (H0 _))
        | /H1 /(_ (0, 0, Var 0) _ (H7 _)) | ]. } subst.
    move: (H0 (0, 0, Var 0)) (H7 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Lemma eval_need_diverge_need_disjoint H H' t v :
  eval_need H t H' v ->
  diverge_need H t ->
  False.
Proof.
  induction 1; inversion 1; subst; auto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (eval_need_det _ _ _ _ H0_ _ _ H5).
    inversion 2. subst. eauto.
  - case: (eval_need_det _ _ _ _ H0_ _ _ H6).
    inversion 2. subst.
    have ? : i = i0.
    { by case: (ltngtP i i0) =>
        [ /H9 /(_ (0, 0, Var 0) _ (H0 _))
        | /H1 /(_ (0, 0, Var 0) _ (H7 _)) | ]. } subst.
    move: (H0 (0, 0, Var 0)) (H7 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Lemma eval_need_cycle_need_disjoint H H' t v :
  eval_need H t H' v ->
  cycle_need H t ->
  False.
Proof.
  induction 1; inversion 1; subst; auto; try congruence.
  - case: (eval_need_det _ _ _ _ H0_ _ _ H5).
    inversion 2. subst. eauto.
  - case: (eval_need_det _ _ _ _ H0_ _ _ H6).
    inversion 2. subst.
    have ? : i = i0.
    { by case: (ltngtP i i0) =>
        [ /H9 /(_ (0, 0, Var 0) _ (H0 _))
        | /H1 /(_ (0, 0, Var 0) _ (H7 _)) | ]. } subst.
    move: (H0 (0, 0, Var 0)) (H7 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Lemma cycle_need_diverge_need_disjoint H t :
  cycle_need H t ->
  diverge_need H t ->
  False.
Proof.
  induction 1; inversion 1; subst; auto; try congruence.
  - apply: eval_need_cycle_need_disjoint; eauto.
  - apply: eval_need_diverge_need_disjoint; eauto.
  - case (eval_need_det _ _ _ _ H0 _ _ H7).
    inversion 2. subst. eauto.
  - apply: eval_need_cycle_need_disjoint; eauto.
  - apply: eval_need_diverge_need_disjoint; eauto.
  - case: (eval_need_det _ _ _ _ H0 _ _ H8).
    inversion 2. subst.
    have ? : i = i0.
    { by case: (ltngtP i i0) =>
        [ /H11 /(_ (0, 0, Var 0) _ (H1 _))
        | /H2 /(_ (0, 0, Var 0) _ (H9 _)) | ]. } subst.
    move: (H1 (0, 0, Var 0)) (H9 (0, 0, Var 0)) => ->.
    inversion 1. subst. eauto.
Qed.

Corollary value_diverge_need_disjoint H v :
  value v ->
  diverge_need H v ->
  False.
Proof.
  move => /(value_eval_need H).
  exact: eval_need_diverge_need_disjoint.
Qed.

Corollary value_cycle_need_disjoint H v :
  value v ->
  cycle_need H v ->
  False.
Proof.
  move => /(value_eval_need H).
  exact: eval_need_cycle_need_disjoint.
Qed.

Corollary consistent_segment_bound Rdom Rcod H :
  consistent_segment Rdom Rcod H ->
  forall l1 l2, Rdom l1 l2 ->
  l2 < size H.
Proof.
  move => Hcon ? ? ?.
  apply: (iso_heap_segment_boundL _ _ _ _ Hcon); eauto.
Qed.
  
Corollary consistent_segment_weaken (Rdom Rdom' Rcod Rcod' : nat -> nat -> Prop) H H' :
  consistent_segment Rdom Rcod H ->
  ( forall l1 l2, Rdom' l1 l2 -> Rdom l1 l2 ) ->
  ( forall l1 l2, Rcod l1 l2 -> Rcod' l1 l2 ) ->
  ( forall l1 l2, Rdom' l1 l2 ->
    forall t,
    nth None H l2 = Some t ->
    nth None H' l2 = Some t ) ->
  consistent_segment Rdom' Rcod' H'.
Proof.
  move => Hcon Hdom Hcod Hext.
  apply: (iso_heap_segment_weaken _ _ _ _ _ _ _ _ Hcon) =>
    [ ? ? [ ? [ /Hdom ? /Hdom ? ] ]
    | ? ? [ ? [ /Hcod ? /Hcod ? ] ]
    | ? ? [ ? [ /Hext ] ]
    | ? ? [ ? [ ? /Hext ] ] ] //;
  repeat eexists; eauto.
Qed.

Definition consistent_segment_dom Rdom Rdom' Rcod H Hcon Hdom :=
  consistent_segment_weaken Rdom Rdom' Rcod Rcod H H Hcon Hdom (fun _ _ H => H) (fun _ _ _ _ H => H).
Definition consistent_segment_cod Rdom Rcod Rcod' H Hcon Hcod :=
  consistent_segment_weaken Rdom Rdom Rcod Rcod' H H Hcon (fun _ _ H => H) Hcod (fun _ _ _ _ H => H).
Definition consistent_segment_ext Rdom Rcod H H' Hcon Hext :=
  consistent_segment_weaken Rdom Rdom Rcod Rcod H H' Hcon (fun _ _ H => H) (fun _ _ H => H) Hext.

Corollary consistent_segment_cat R R' H Hd :
  consistent_segment R R' H ->
  consistent_segment R R' (H ++ Hd).
Proof. move => /iso_heap_segment_catL /iso_heap_segment_catR. by apply. Qed.

Corollary consistent_segment_rcons R R' H o :
  consistent_segment R R' H ->
  consistent_segment R R' (rcons H o).
Proof.
  rewrite -cats1.
  exact: consistent_segment_cat.
Qed.

Corollary consistent_segment_iso_heap_segment_comp Rdom Rdom' Rcod Rcod' H H' :
  consistent_segment Rdom Rcod H ->
  iso_heap_segment Rdom' Rcod' H H' ->
  consistent_segment
    (fun l1 l2' => exists l2, Rdom l1 l2 /\ Rdom' l2 l2')
    (fun l1 l2' => exists l2, Rcod l1 l2 /\ Rcod' l2 l2') H'.
Proof.
  move => Hcon Hiso.
  refine (iso_heap_segment_weaken _ _ _ _ _ _ _ _
    (iso_heap_segment_comp _ _ _ _ _ _ _
      (iso_heap_segment_sym _ _ _ _ Hiso)
      (iso_heap_segment_comp _ _ _ _ _ _ _ Hcon Hiso))
    _ _ (fun _ _ _ _ H => H) (fun _ _ _ _ H => H)) =>
    [ ? ? [ ? [ [ ? [ ? ? ] ] [ ? [ ? ? ] ] ] ]
    | ? ? [ ? [ ? [ ? [ [ ? [ ? ? ] ] ? ] ] ] ] ];
  repeat (eexists; eauto).
Qed.

Lemma consistent_segment_union Rdom Rdom' Rcod H :
  consistent_segment Rdom Rcod H ->
  consistent_segment Rdom' Rcod H ->
  ( forall l1 l2 l2',
    Rdom l1 l2 -> Rdom' l1 l2' ->
    exists t2, nth None H l2 = Some t2 /\
    exists t2', nth None H l2' = Some t2' /\
    corr_term (fun l2 l2' => exists l1, Rcod l1 l2 /\ Rcod l1 l2' ) t2 t2' ) ->
  consistent_segment (fun l1 l2 => Rdom l1 l2 \/ Rdom' l1 l2) Rcod H.
Proof.
  move => Hcon Hcon' Hrest ? ? [ ? [ [ ? | Hdom1' ] [ Hdom2 | ? ] ] ];
  [ apply: Hcon
  | apply: Hrest
  | move: (Hrest _ _ _ Hdom2 Hdom1') =>
      [ ? [ -> [ ? [ -> /corr_term_sym Hterm ] ] ] ];
    repeat eexists;
    apply: (corr_term_impl _ _ _ _ Hterm) => ? ? [ ? [ ? ? ] ]
  | apply: Hcon' ]; eauto.
Qed.

Corollary consistent_segment_wf_heap_segment R R' H :
  consistent_segment R R' H ->
  wf_heap_segment (fun l2 => exists l1, R l1 l2) (fun l2 => exists l1, R' l1 l2) H.
Proof.
  move => /iso_heap_segment_wf_heap_segmentR Hwf.
  refine (wf_heap_segment_weaken _ _ _ _ _ _ Hwf _ _ (fun _ _ _ H => H)) =>
    [ ? [ ? ? ] | ? [ ? [ ? [ ? ? ] ] ] ]; eauto.
Qed.

Lemma iso_heap_segment_corr_heap_segment R R' H1 H2 :
  iso_heap_segment R R' H1 H2 ->
  corr_heap_segment R R' H1 H2.
Proof.
  move => Hiso ? ? /Hiso
    [ ? [ -> [ ? [ -> ? ] ] ] ].
  repeat eexists. eauto.
Qed.

Lemma corr_heap_segment_boundL R R' H1 H2 :
  corr_heap_segment R R' H1 H2 ->
  forall l1 l2, R l1 l2 ->
  l1 < size H1.
Proof.
  move => Hcorr l1 ? /Hcorr [ ? [ ] ].
  by case: (leqP (size H1) l1) => [ /(nth_default _) -> | ].
Qed.

Lemma corr_heap_segment_boundR R R' H1 H2 :
  corr_heap_segment R R' H1 H2 ->
  forall l1 l2, R l1 l2 ->
  l2 < size H2.
Proof.
  move => Hcorr ? l2 /Hcorr [ ? [ ? [ ? [ ] ] ] ].
  by case: (leqP (size H2) l2) => [ /(nth_default _) -> | ].
Qed.

Lemma corr_heap_segment_weaken (Rdom Rdom' Rcod Rcod' : nat -> nat -> Prop) H1 H1' H2 :
  corr_heap_segment Rdom Rcod H1 H2 ->
  ( forall l1 l2, Rdom' l1 l2 -> Rdom l1 l2 ) ->
  ( forall l1 l2, Rcod l1 l2 -> Rcod' l1 l2 ) ->
  ( forall l1 l2, Rdom' l1 l2 ->
    forall t1,
    nth None H1 l1 = Some t1 ->
    nth None H1' l1 = Some t1 ) ->
  corr_heap_segment Rdom' Rcod' H1' H2.
Proof.
  move => Hcorr Hdom Hcod HextL ? ? HR.
  move: (HR) => /Hdom /Hcorr
    [ ? [ /(HextL _ _ HR) -> [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ];
  repeat (eexists; eauto).
  - left. apply: corr_term_impl; eauto.
  - right. do 5 (eexists; eauto).
    apply: corr_term_impl; eauto.
    move => ? ? [ ? [ ? ? ] ]. eauto.
Qed.

Definition corr_heap_segment_dom Rdom Rdom' Rcod H1 H2 Hcorr Hdom :=
  corr_heap_segment_weaken Rdom Rdom' Rcod Rcod H1 H1 H2 Hcorr Hdom
    (fun _ _ H => H) (fun _ _ _ _ H => H).
Definition corr_heap_segment_cod Rdom Rcod Rcod' H1 H2 Hcorr Hcod :=
  corr_heap_segment_weaken Rdom Rdom Rcod Rcod' H1 H1 H2 Hcorr
    (fun _ _ H => H) Hcod (fun _ _ _ _ H => H).
Definition corr_heap_segment_extL Rdom Rcod H1 H1' H2 Hcorr :=
  corr_heap_segment_weaken Rdom Rdom Rcod Rcod H1 H1' H2 Hcorr
    (fun _ _ H => H) (fun _ _ H => H).

Corollary corr_heap_segment_catL fdom fcod H1 H2 Hd :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod (H1 ++ Hd) H2.
Proof.
  move => Hcorr.
  apply (corr_heap_segment_extL _ _ _ _ _ Hcorr) => l1 ?.
  by move: nth_cat (leqP (size H1) l1) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rconsL fdom fcod H1 H2 o :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod (rcons H1 o) H2.
Proof. by rewrite -cats1 => /corr_heap_segment_catL. Qed.

Lemma corr_heap_segment_union Rdom Rdom' Rcod H1 H2 :
  corr_heap_segment Rdom Rcod H1 H2 ->
  corr_heap_segment Rdom' Rcod H1 H2 ->
  corr_heap_segment (fun l l' => Rdom l l' \/ Rdom' l l') Rcod H1 H2.
Proof. by move => Hcorr Hcorr' ? ? [ /Hcorr | /Hcorr' ]. Qed.

Lemma corr_heap_segment_iso_heap_comp Rdom Rcod S H1 H2 H2' :
  corr_heap_segment Rdom Rcod H1 H2 ->
  iso_heap S H2 H2' ->
  (forall l1 l2, Rcod l1 l2 -> S l2 l2) ->
  corr_heap_segment
    (fun l1 l2' => exists l2, Rdom l1 l2 /\ S l2 l2')
    (fun l1 l2' => exists l2, Rcod l1 l2 /\ S l2 l2') H1 H2'.
Proof.
  move => Hcorr Hiso Hsur.
  move => ? ? [ ? [ ] ]
    /Hcorr [ ? [ -> [ ? [ Hnth [ Hterm | [ ? [ ? [ Hcbn [ ? [ Hiso' Hterm ] ] ] ] ] ] ] ] ] ]
    /Hiso [ ? [ Hnth' [ ? [ -> Hterm' ] ] ] ];
  move: Hnth Hnth' => ->; inversion 1; subst;
  repeat eexists.
  - left. apply: corr_term_comp; eauto.
  - right.
    move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _ Hterm' Hiso) =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    do 5 (eexists; eauto).
    + apply: iso_heap_segment_comp; eauto.
      apply: iso_heap_segment_comp; eauto.
      apply: iso_heap_segment_sym. eauto.
    + apply: corr_term_impl.
      * apply: corr_term_comp; eauto.
      * move => ? ? [ ? [ [ ? [ ? ? ] ] ? ] ].
        repeat (eexists; eauto).
Qed.

Corollary corr_heap_segment_extR R R' H1 H2 H2' :
  corr_heap_segment R R' H1 H2 ->
  consistent R' H2 ->
  ( forall l1 l2, R l1 l2 -> R' l1 l2 ) ->
  ( forall l1 l2, R' l1 l2 ->
    forall t2,
    nth None H2 l2 = Some t2 ->
    nth None H2' l2 = Some t2 ) ->
  corr_heap_segment R R' H1 H2'.
Proof.
  move => Hcorr Hcon Himpl HextR.
  refine
    (corr_heap_segment_weaken _ _ _ _ _ _ _
      (corr_heap_segment_iso_heap_comp _ _ _ _ _ _ Hcorr
        (iso_heap_segment_extR _ _ _ _ _
          (iso_heap_segment_refl _ _ _ 
            (consistent_segment_wf_heap_segment _ _ _ Hcon)) _) _) _ _ _) => /=
  [ ? ? [ -> [ ? /HextR ] ] | | 
  | ? ? [ ? [ ? [ <- [ ? ? ] ] ] ] | ]; eauto 7.
Qed.

Corollary corr_heap_segment_catR R R' H1 H2 Hd :
  corr_heap_segment R R' H1 H2 ->
  consistent R' H2 ->
  ( forall l1 l2, R l1 l2 -> R' l1 l2 ) ->
  corr_heap_segment R R' H1 (H2 ++ Hd).
Proof.
  move => Hcorr Hcon Himpl.
  apply: (corr_heap_segment_extR _ _ _ _ _ Hcorr Hcon Himpl) => ? l2 ? ?.
  by move: nth_cat (leqP (size H2) l2) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rconsR R R' H1 H2 o :
  corr_heap_segment R R' H1 H2 ->
  consistent R' H2 ->
  ( forall l1 l2, R l1 l2 -> R' l1 l2 ) ->
  corr_heap_segment R R' H1 (rcons H2 o).
Proof. rewrite -cats1. exact: corr_heap_segment_catR. Qed.

Lemma trace_segment_boundL R R' H1 H2 t2 C :
  trace_segment R R' H1 H2 t2 C ->
  forall l1 l2, R l1 l2 ->
  l1 < size H1.
Proof. by move => Htr ? ? /Htr [ ? [ -> ] ]. Qed.

Lemma clos_t_rt A R y z :
  clos_refl_trans A R y z ->
  forall x,
  clos_trans A R x y ->
  clos_trans A R x z.
Proof. induction 1; eauto using t_step, t_trans. Qed.
  
Lemma trace_segment_red_name_multi R R' H1 H2 H2' t2 t2' C :
  trace_segment R R' H1 H2 t2 C ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H2, t2) (H2', t2') ->
  trace_segment R R' H1 H2' t2' C.
Proof.
  move => Htr Hred2 ? ? /Htr [ -> [ -> [ ? [ ? [ ? [ ? [ ? [ Hred1 ? ] ] ] ] ] ] ] ].
  repeat (eexists; eauto).
  refine (clos_t_rt _ _ (_, _) _ _ _ Hred1).
  exact: red_name_apply_context_name_multi.
Qed.

Corollary trace_segment_red_name R R' H1 H2 H2' t2 t2' C :
  trace_segment R R' H1 H2 t2 C ->
  red_name H2 t2 H2' t2' ->
  trace_segment R R' H1 H2' t2' C.
Proof.
  move => Htr ?.
  apply: (trace_segment_red_name_multi _ _ _ _ _ _ _ _ Htr).
  by apply: rt_step => /=.
Qed.

Lemma trace_segment_weaken (Rdom Rdom' Rcod Rcod' : nat -> nat -> Prop) H1 H1' H2 t2 C C' :
  trace_segment Rdom Rcod H1 H2 t2 C ->
  (forall l1 l2, Rdom' l1 l2 -> exists l2, Rdom l1 l2) ->
  (forall l1 l2, Rcod l1 l2 -> Rcod' l1 l2) ->
  ( forall l1 l2, Rdom' l1 l2 ->
    l1 < size H1' /\
    ( nth None H1 l1 = None -> nth None H1' l1 = None ) ) ->
  ( forall l1 l2, Rdom' l1 l2 -> C l1 = C' l1 ) ->
  trace_segment Rdom' Rcod' H1' H2 t2 C'.
Proof.
  move => Htr Hdom Hcod HextL HC ? ? HR.
  move: (HC _ _ HR) (HextL _ _ HR) => <- [ -> HextL' ].
  move: (HR) => /Hdom [ ? ] /Htr [ /HextL' -> [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
  repeat (eexists; eauto).
Qed.

Definition trace_segment_dom Rdom Rdom' Rcod H1 H2 t2 C Htr Hdom :=
  trace_segment_weaken Rdom Rdom' Rcod _ H1 _ H2 t2 C _ Htr Hdom (fun _ _ H => H)
    (fun _ _ H => ex_ind (fun _ H => conj (trace_segment_boundL _ _ _ _ _ _ Htr _ _ H) (fun H => H)) (Hdom _ _ H)) (fun _ _ _ => erefl).
Definition trace_segment_cod Rdom Rcod Rcod' H1 H2 t2 C Htr Hcod :=
  trace_segment_weaken Rdom _ Rcod Rcod' H1 _ H2 t2 C _ Htr (fun _ _ H => ex_intro _ _ H) Hcod
    (fun _ _ H => conj (trace_segment_boundL _ _ _ _ _ _ Htr _ _ H) (fun H => H)) (fun _ _ _ => erefl).
Definition trace_segment_extL Rdom Rcod H1 H1' H2 t2 C Htr HextL :=
  trace_segment_weaken Rdom _ Rcod _ H1 H1' H2 t2 C _ Htr
    (fun _ _ H => ex_intro _ _ H) (fun _ _ H => H) HextL (fun _ _ _ => erefl).
Definition trace_segment_context Rdom Rcod H1 H2 t2 C C' Htr HC :=
  trace_segment_weaken Rdom _ Rcod _ H1 _ H2 t2 C C' Htr (fun _ _ H => ex_intro _ _ H) (fun _ _ H => H)
    (fun _ _ H => conj (trace_segment_boundL _ _ _ _ _ _ Htr _ _ H) (fun H => H)) HC.

Lemma trace_segment_union Rdom Rdom' Rcod H1 H2 t2 C :
  trace_segment Rdom Rcod H1 H2 t2 C -> 
  trace_segment Rdom' Rcod H1 H2 t2 C -> 
  trace_segment (fun l1 l2 => Rdom l1 l2 \/ Rdom' l1 l2) Rcod H1 H2 t2 C.
Proof. by move => Htr Htr' ? ? [ /Htr | /Htr' ]. Qed.

Theorem eval_need_sound H1 t1 H1' v1 :
  eval_need H1 t1 H1' v1 ->
  forall R S H2 t2 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  exists R' S' H2' v2,
  eval_name H2 t2 H2' v2 /\
  consistent (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H2' /\
  corr_term (fun l1 l2 => R' l1 l2 \/ S' l1 l2) v1 v2 /\
  corr_heap_segment R' (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H2' /\
  trace_segment S' (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H2' v2 C /\
  ( forall l1 l2, R l1 l2 \/ S l1 l2 -> R' l1 l2 \/ S' l1 l2 ).
Proof.
  induction 1; inversion 2; subst => [ Hcorr Hhole ].
  - case H6 => [ /Hcorr [ t1 [ ] ] | /Hhole [ ] ];
    rewrite H0; inversion 1.
    subst => [ [ t2 [ Hnth [ Hterm | [ H2' [ ? [ Hcbn [ T [ ? Hterm' ] ] ] ] ] ] ] ] ].
    + have Himpl : forall l1 l2,
        R l1 l2 \/ S l1 l2 ->
        l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2.
      { move => l1 ? [ ]; eauto.
        case (@eqP _ l1 l); eauto. }
      have Hcon' : consistent (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) H2.
      { refine (consistent_segment_weaken
          _ _ _ _ _ _ H3 _ _ (fun _ _ _ _ H => H)) =>
        [ ? ? [ [ ] | [ [ ] | ] ] | ]; eauto. }
      have Hterm' : corr_term (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) t1 t2.
      { refine (corr_term_impl _ _ _ _ Hterm _); eauto. }
      have Hcorr' : corr_heap_segment
        (fun l1 l2 => l1 != l /\ R l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) (set_nth None H l None) H2.
      { refine (corr_heap_segment_weaken
          _ _ _ _ _ _ _ Hcorr _ _ _) => l1 ? [ ]; eauto.
        by rewrite nth_set_nth => /= /negbTE ->. }
      have Hhole' : trace_segment
        (fun l1 l2 => l1 == l /\ R l1 l2 \/ S l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2)
        (set_nth None H l None) H2 t2 [eta C with l |-> nil].
      { apply: (trace_segment_dom (fun l1 l2 => l1 == l /\ (R l1 l2 \/ S l1 l2) \/ l1 != l /\ S l1 l2)).
        - apply: trace_segment_union => [ ? ? [ /eqP -> HR ] | ].
          + move: nth_set_nth size_set_nth leq_max eqxx => -> -> -> /= ->.
            repeat split.
            * by move: HR orbT =>
                [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
                | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ] -> ->.
            * exists (fun l1 l2 => R l1 l2 \/ S l1 l2), H2, l'.
              repeat split; eauto.
              apply: t_step => /=. eauto.
          + refine
              (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
                (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _) _ _ _ _) =>
              [ | ? ? [ ] | | ? ? [ ] | ? ? [ ] /= /negbTE -> ]; eauto.
            rewrite size_set_nth leq_max nth_set_nth =>
              /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->.
            by rewrite orbT.
          + move => l1 ? [ [ ? ? ] | ? ]; eauto.
            case (@eqP _ l1 l); eauto. }
      move: (IHeval_need _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole') =>
        [ R' [ S' [ ? [ ? [ Hcbn [ Hcon'' [ ? [ Hcorr'' [ Hhole'' Himpl' ] ] ] ] ] ] ] ] ].
      exists
        (fun l1 l2 => R' l1 l2 \/ l1 == l /\ S' l1 l2),
        (fun l1 l2 => l1 != l /\ S' l1 l2).
      do 4 (eexists; eauto).
      { refine (consistent_segment_weaken
          _ _ _ _ _ _ Hcon'' _ _ (fun _ _ _ _ H => H)) =>
          [ ? ? [ [ | [ ] ] | [ ] ]
          | l1 ? [ ] ]; eauto.
        case (@eqP _ l1 l); eauto. }
      split.
      { apply: corr_term_impl; eauto.
        move => l1 ? [ ]; eauto.
        case (@eqP _ l1 l); eauto. }
      split.
      { apply: (corr_heap_segment_dom
          (fun l1 l2 => l1 != l /\ R' l1 l2 \/ l1 == l /\ (R' l1 l2 \/ S' l1 l2))).
        - apply: corr_heap_segment_union => [ | ? ? [ /eqP -> HRS' ] ].
          + refine (corr_heap_segment_weaken _ _ _ _ _ _ _ Hcorr'' _ _ _) => l1 ? [ ]; eauto.
            * case (@eqP _ l1 l); eauto.
            * by rewrite nth_set_nth => /= /negbTE ->.
          + move: nth_set_nth (Hcon'' _ _ (ex_intro _ _ (conj HRS' (Himpl' _ _ (Himpl _ _ H6))))) =>
              -> /= [ ? [ Hnth' [ ? [ ] ] ] ].
            rewrite Hnth' (eval_name_heap _ _ _ _ Hcbn _ _ Hnth) eqxx.
            inversion 1. subst => [ Hterm0 ].
            repeat eexists. right.
            move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _
              (corr_term_comp _ _ _ _
                (corr_term_comp _ _ _ _ (corr_term_sym _ _ _ Hterm) _ Hterm) _
                  (corr_term_sym _ _ _ Hterm0))
                (iso_heap_segment_comp _ _ _ _ _ _ _ 
                  (iso_heap_segment_extR _ _ _ _ _ H3
                    (fun _ _ _ => eval_name_heap _ _ _ _ Hcbn _))
                  (iso_heap_segment_sym _ _ _ _ Hcon''))) =>
            [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
            do 5 (eexists; eauto).
            apply: corr_term_impl.
            * apply: corr_term_comp; eauto.
            * move => l1 ? [ ? [ [ ? | ? ] ? ] ]; eauto.
              case (@eqP _ l1 l); repeat eexists; eauto.
        - move => l1 ? [ | [ ] ]; eauto.
          case (@eqP _ l1 l); eauto. }
      split.
      { apply (trace_segment_weaken _ _ _ _ _ _ _ _ _ _ Hhole'') =>
          [ ? ? [ ] | /= l1 ? [ ] | ? ? [ ] | /= l1 ? [ /negbTE -> ] ]; eauto.
        - case (@eqP _ l1 l); eauto.
        - rewrite size_set_nth leq_max nth_set_nth =>
            /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole'') ->.
          by rewrite orbT. }
      { move => l1 ? /Himpl /Himpl' [ ]; eauto.
        case (@eqP _ l1 l); eauto. }
    + case: (eval_need_det _ _ _ _ H1 _ _
        (value_eval_need _ _
          (corr_term_valueR _ _ _ Hterm' (eval_name_value _ _ _ _ Hcbn)))) => ? ?. subst.
      have Hiso: iso_heap (fun l2 l2' => T l2 l2' \/ l2 = l2' /\ exists l1, R l1 l2 \/ S l1 l2) H2 H2'.
      { apply: iso_heap_segment_union.
        - apply: iso_heap_segment_cod; eauto.
        - apply: iso_heap_segment_extR.
          + apply: iso_heap_segment_cod.
            * apply: iso_heap_segment_refl.
              apply: consistent_segment_wf_heap_segment; eauto.
            * move => ? ? /=. eauto.
          + move => ? ? ?.
            apply: eval_name_heap. eauto. }
      exists
        (fun l1 l2' => R l1 l2' \/ exists l2, R l1 l2 /\ T l2 l2'),
        (fun l1 l2' => S l1 l2' \/ exists l2, S l1 l2 /\ T l2 l2').
      rewrite set_set_nth eqxx.
      do 4 (eexists; eauto).
      { refine (consistent_segment_weaken _ _ _ _ _ _ _ _ _ (fun _ _ _ _ H => H)).
        - apply: consistent_segment_iso_heap_segment_comp; eauto.
        - move => ? ? [ [ ? | [ ? [ ? ? ] ] ] | [ ? | [ ? [ ? ? ] ] ] ]; repeat (eexists; eauto).
        - move => ? ? [ ? [ [ ? | ? ] [ ? | [ ? [ ? [ ? | ? ] ] ]   ] ] ]; subst; eauto. }
      split.
      { apply: corr_term_impl; eauto.
        move => ? ? [ ? [ [ ? | ? ] ? ] ]; eauto. }
      split.
      { apply: corr_heap_segment_weaken.
        - apply: corr_heap_segment_iso_heap_comp.
          + apply: Hcorr.
          + apply: Hiso.
          + move => ? ? [ ]; eauto.
        - move => ? ? [ ? | [ ? [ ? ? ] ] ]; eauto 7.
        - move => ? ? [ ? [ [ ? | ? ] [ ? | [ ? [ ? [ ? | ? ] ] ] ] ] ]; subst; eauto 6.
        - move => l1 ? ? ?.
          rewrite nth_set_nth => /=.
          by move: (@eqP _ l1 l) H0 => [ -> -> | ]. }
      split.
      { refine (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
          (trace_segment_red_name_multi _ _ _ _ _ _ _ _ Hhole
            (eval_name_red_name_multi _ _ _ _ _)) _ _ _ _) =>
          [ | ? ? [ | [ ? [ ] ] ] | ? ? [ ] | l1 ? HRS | ]; eauto.
        rewrite size_set_nth leq_max nth_set_nth => /=.
        split.
        - move: HRS => [ | [ ? [ ] ] ] /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->;
          by rewrite orbT.
        - case (@eqP _ l1 l) => [ -> | // ].
          by rewrite H0. }
      { move => ? ? [ ]; eauto. }
  - move: (IHeval_need1 _ _ _ _ (cons (context_app t2') \o C) H3 H7 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' Himpl ] ] ].
    have Hterm'' : corr_term
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2)
      (subst (scons t2 Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst => [ | [ | ? ] ] /=; eauto.
      apply: corr_term_impl; eauto. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scons t2' Var) t') C.
    { exact: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). }
    move: (IHeval_need2 _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Himpl : forall l1 l2,
      R l1 l2 \/ S l1 l2 ->
      ( R l1 l2 \/
        exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
      S l1 l2.
    { move => ? ? [ ]; eauto. }
    have Hiso' : iso_heap_segment
      (fun l1 l2 => exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n )
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { move => ? ? [ x [ ? [ -> -> ] ] ].
      rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
      repeat eexists.
      apply: corr_term_subst => [ | y ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') y) => ?.
      + by rewrite !nth_default ?size_mkseq.
      + rewrite !nth_mkseq => /=; eauto 7. }
    have Hcon' : consistent
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H2 ++ map (Some \o
        subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { apply: (consistent_segment_dom
        (fun l1 l2 =>
          ( R l1 l2 \/ S l1 l2 ) \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n)).
      - apply: consistent_segment_union.
        + apply: consistent_segment_cat.
          apply: consistent_segment_cod; eauto.
        + apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        + move => ? ? ? HRS [ ? [ Hlt [ ? ? ] ] ]. subst.
          case HRS =>
            [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
            | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ];
          by rewrite ltnNge leq_addr.
      - move => ? ? [ [ ] | ]; eauto. }
    have Hterm' : corr_term
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var) t').
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 7. }
    have Hcorr' : corr_heap_segment
      (fun l1 l2 =>
        R l1 l2 \/
        exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n)
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_catL.
        apply: corr_heap_segment_cod.
        + apply: corr_heap_segment_catR; eauto.
          move => /=. eauto.
        + eauto.
      - apply: iso_heap_segment_corr_heap_segment. eauto. }
    have Hhole' : trace_segment S
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts')
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var) t') C.
    { apply: (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
        (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _)) =>
      [ | | ? ? [ ] | ? ? /(trace_segment_boundL _ _ _ _ _ _ Hhole) Hlt | ]; eauto.
      by rewrite size_cat nth_cat Hlt (ltn_addr _ Hlt). }
    move: (IHeval_need _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - move: (IHeval_need1 _ _ _ _ (cons (context_case pts') \o C) H5 H9 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' ? ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H14). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H12 -H11 H1.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts' j = (c, size ts', t1) -> False => [ j Hlt' d | ].
    { move: (H2 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H11 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term
      (fun l1 l2 : nat => R' l1 l2 \/ S' l1 l2)
      (subst (scat ts Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x ].
      - move: H1 (H13 _ Hlt (0, 0, Var 0)) => ->.
        eauto using corr_term_impl.
      - rewrite !nth_scat H12.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H12; eauto.
        + eauto using corr_term_impl. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2) C.
    { apply: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). eauto. }
    move: (IHeval_need2 _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_need_sound :
  forall H1 t1,
  diverge_need H1 t1 ->
  forall R S H2 t2 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  diverge_name H2 t2.
Proof.
  cofix diverge_need_sound.
  inversion 1; subst => [ R S H2_ ? C ];
  inversion 2; subst => [ Hcorr Hhole ].
  - case H6 => [ /Hcorr [ t1 [ ] ] | /Hhole [ ] ];
    rewrite H2; inversion 1.
    subst => [ [ t2 [ ? [ Hterm | [ ? [ ? [ Hcbn [ ? [ ? Hterm ] ] ] ] ] ] ] ] ].
    + have Himpl : forall l1 l2,
        R l1 l2 \/ S l1 l2 ->
        l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2.
      { move => l1 ? [ ]; eauto.
        case (@eqP _ l1 l); eauto. }
      have Hcon' : consistent (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) H2_.
      { refine (consistent_segment_weaken
          _ _ _ _ _ _ H0 _ _ (fun _ _ _ _ H => H)) =>
        [ ? ? [ [ ] | [ [ ] | ] ] | ]; eauto. }
      have Hterm' : corr_term (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) t1 t2.
      { refine (corr_term_impl _ _ _ _ Hterm _); eauto. }
      have Hcorr' : corr_heap_segment
        (fun l1 l2 => l1 != l /\ R l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) (set_nth None H1 l None) H2_.
      { refine (corr_heap_segment_weaken
          _ _ _ _ _ _ _ Hcorr _ _ _) => l1 ? [ ]; eauto.
        by rewrite nth_set_nth => /= /negbTE ->. }
      have Hhole' : trace_segment
        (fun l1 l2 => l1 == l /\ R l1 l2 \/ S l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2)
        (set_nth None H1 l None) H2_ t2 [eta C with l |-> nil].
      { apply: (trace_segment_dom (fun l1 l2 => l1 == l /\ (R l1 l2 \/ S l1 l2) \/ l1 != l /\ S l1 l2)).
        - apply: trace_segment_union => [ ? ? [ /eqP -> HR ] | ].
          + move: nth_set_nth size_set_nth leq_max eqxx => -> -> -> /= ->.
            repeat split.
            * by move: HR orbT =>
                [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
                | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ] -> ->.
            * exists (fun l1 l2 => R l1 l2 \/ S l1 l2), H2_, l'.
              repeat split; eauto.
              apply: t_step => /=. eauto.
          + refine
              (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
                (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _) _ _ _ _) =>
              [ | ? ? [ ] | | ? ? [ ] | ? ? [ ] /= /negbTE -> ]; eauto.
            rewrite size_set_nth leq_max nth_set_nth =>
              /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->.
            by rewrite orbT.
          + move => l1 ? [ [ ? ? ] | ? ]; eauto.
            case (@eqP _ l1 l); eauto. }
      by refine (diverge_name_loc _ _ _ _ (diverge_need_sound _ _ _ _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole')).
    + case: (value_diverge_need_disjoint _ _
        (corr_term_valueR _ _ _ Hterm (eval_name_value _ _ _ _ Hcbn)) H3).
  - apply: diverge_name_appL.
    apply: (diverge_need_sound _ _ H2 _ _ _ _ (cons (context_app t2') \o C)); eauto.
  - move: (eval_need_sound _ _ _ _ H2 _ _ _ _ (cons (context_app t2') \o C) H0 H7 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' Himpl ] ] ].
    have Hterm'' : corr_term
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2)
      (subst (scons t3 Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst => [ | [ | ? ] ] /=; eauto.
      apply: corr_term_impl; eauto. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scons t2' Var) t') C.
    { exact: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). }
    refine (diverge_name_appabs _ _ _ _ _ _
      (diverge_need_sound _ _ _ _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'')); eauto.
  - have Himpl : forall l1 l2,
      R l1 l2 \/ S l1 l2 ->
      ( R l1 l2 \/
        exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
      S l1 l2.
    { move => ? ? [ ]; eauto. }
    have Hiso' : iso_heap_segment
      (fun l1 l2 => exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n )
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (H2_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var)) ts').
    { move => ? ? [ x [ ? [ -> -> ] ] ].
      rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
      repeat eexists.
      apply: corr_term_subst => [ | y ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') y) => ?.
      + by rewrite !nth_default ?size_mkseq.
      + rewrite !nth_mkseq => /=; eauto 7. }
    have Hcon' : consistent
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
        S l1 l2 )
      (H2_ ++ map (Some \o
        subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var)) ts').
    { apply: (consistent_segment_dom
        (fun l1 l2 =>
          ( R l1 l2 \/ S l1 l2 ) \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n)).
      - apply: consistent_segment_union.
        + apply: consistent_segment_cat.
          apply: consistent_segment_cod; eauto.
        + apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        + move => ? ? ? HRS [ ? [ Hlt [ ? ? ] ] ]. subst.
          case HRS =>
            [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
            | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ];
          by rewrite ltnNge leq_addr.
      - move => ? ? [ [ ] | ]; eauto. }
    have Hterm' : corr_term
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
        S l1 l2 )
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var) t)
      (subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var) t').
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 7. }
    have Hcorr' : corr_heap_segment
      (fun l1 l2 =>
        R l1 l2 \/
        exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n)
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (H2_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var)) ts').
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_catL.
        apply: corr_heap_segment_cod.
        + apply: corr_heap_segment_catR; eauto.
          move => /=. eauto.
        + eauto.
      - apply: iso_heap_segment_corr_heap_segment. eauto. }
    have Hhole' : trace_segment S
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H1 + n /\ l2 = size H2_ + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (H2_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var)) ts')
      (subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var) t') C.
    { apply: (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
        (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _)) =>
      [ | | ? ? [ ] | ? ? /(trace_segment_boundL _ _ _ _ _ _ Hhole) Hlt | ]; eauto.
      by rewrite size_cat nth_cat Hlt (ltn_addr _ Hlt). }
    refine (diverge_name_let _ _ _
      (diverge_need_sound _ _ _ _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole')); eauto.
  - apply: diverge_name_case.
    apply: (diverge_need_sound _ _ H2 _ _ _ _ (cons (context_case pts') \o C)); eauto.
  - move: (eval_need_sound _ _ _ _ H2 _ _ _ _ (cons (context_case pts') \o C) H0 H9 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' ? ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H3 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H14). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H11 -H12 H3.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts' j = (c, size ts', t1) -> False => [ j Hlt' d | ].
    { move: (H4 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H11 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term
      (fun l1 l2 : nat => R' l1 l2 \/ S' l1 l2)
      (subst (scat ts Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x ].
      - move: H3 (H13 _ Hlt (0, 0, Var 0)) => ->.
        eauto using corr_term_impl.
      - rewrite !nth_scat H12.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H12; eauto.
        + eauto using corr_term_impl. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2) C.
    { apply: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). eauto. }
    apply: diverge_name_casematch; eauto.
Qed.

Theorem cycle_need_sound H1 t1 :
  cycle_need H1 t1 ->
  forall R S H2 t2 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  diverge_name H2 t2.
Proof.
  induction 1; inversion 2; subst => [ Hcorr Hhole ].
  - case H5 => [ /Hcorr [ t1 [ ] ] | /Hhole [ ] ];
    rewrite H0; inversion 1 => [ [ ? [ R0 [ H2' [ l2 [ ? [ ? [ Hrt ? ] ] ] ] ] ] ] ].
    refine (diverge_name_red_name_cycle _ _ _ _ _ _ _ _ Hrt).
    + refine (iso_heap_segment_comp _ _ _ _ _ _ _ _ H1).
      apply: iso_heap_segment_extR; eauto.
      move => ? ? ?.
      exact: (red_name_multi_heap _ _ (clos_trans_clos_refl_trans _ _ _ _ Hrt)).
    + constructor.
      repeat (eexists; eauto).
  - case H6 => [ /Hcorr [ t1 [ ] ] | /Hhole [ ] ];
    rewrite H0; inversion 1.
    subst => [ [ t2 [ Hnth [ Hterm | [ H2' [ ? [ Hcbn [ T [ ? Hterm' ] ] ] ] ] ] ] ] ].
    + have Himpl : forall l1 l2,
        R l1 l2 \/ S l1 l2 ->
        l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2.
      { move => l1 ? [ ]; eauto.
        case (@eqP _ l1 l); eauto. }
      have Hcon' : consistent (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) H2.
      { refine (consistent_segment_weaken
          _ _ _ _ _ _ H3 _ _ (fun _ _ _ _ H => H)) =>
        [ ? ? [ [ ] | [ [ ] | ] ] | ]; eauto. }
      have Hterm' : corr_term (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) t1 t2.
      { refine (corr_term_impl _ _ _ _ Hterm _); eauto. }
      have Hcorr' : corr_heap_segment
        (fun l1 l2 => l1 != l /\ R l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2) (set_nth None H l None) H2.
      { refine (corr_heap_segment_weaken
          _ _ _ _ _ _ _ Hcorr _ _ _) => l1 ? [ ]; eauto.
        by rewrite nth_set_nth => /= /negbTE ->. }
      have Hhole' : trace_segment
        (fun l1 l2 => l1 == l /\ R l1 l2 \/ S l1 l2)
        (fun l1 l2 => l1 != l /\ R l1 l2 \/ l1 == l /\ R l1 l2 \/ S l1 l2)
        (set_nth None H l None) H2 t2 [eta C with l |-> nil].
      { apply: (trace_segment_dom (fun l1 l2 => l1 == l /\ (R l1 l2 \/ S l1 l2) \/ l1 != l /\ S l1 l2)).
        - apply: trace_segment_union => [ ? ? [ /eqP -> HR ] | ].
          + move: nth_set_nth size_set_nth leq_max eqxx => -> -> -> /= ->.
            repeat split.
            * by move: HR orbT =>
                [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
                | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ] -> ->.
            * exists (fun l1 l2 => R l1 l2 \/ S l1 l2), H2, l'.
              repeat split; eauto.
              apply: t_step => /=. eauto.
          + refine
              (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
                (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _) _ _ _ _) =>
              [ | ? ? [ ] | | ? ? [ ] | ? ? [ ] /= /negbTE -> ]; eauto.
            rewrite size_set_nth leq_max nth_set_nth =>
              /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->.
            by rewrite orbT.
          + move => l1 ? [ [ ? ? ] | ? ]; eauto.
            case (@eqP _ l1 l); eauto. }
      refine (diverge_name_loc _ _ _ _
        (IHcycle_need _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole')); eauto.
    + case: (value_cycle_need_disjoint _ _
        (corr_term_valueR _ _ _ Hterm' (eval_name_value _ _ _ _ Hcbn)) H1).
  - apply: diverge_name_appL.
    apply: (IHcycle_need _ _ _ _ (cons (context_app t2') \o C)); eauto.
  - move: (eval_need_sound _ _ _ _ H0 _ _ _ _ (cons (context_app t2') \o C) H3 H7 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' Himpl ] ] ].
    have Hterm'' : corr_term
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2)
      (subst (scons t2 Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst => [ | [ | ? ] ] /=; eauto.
      apply: corr_term_impl; eauto. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scons t2' Var) t') C.
    { exact: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). }
    refine (diverge_name_appabs _ _ _ _ _ _
      (IHcycle_need _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'')); eauto.
  - have Himpl : forall l1 l2,
      R l1 l2 \/ S l1 l2 ->
      ( R l1 l2 \/
        exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
      S l1 l2.
    { move => ? ? [ ]; eauto. }
    have Hiso' : iso_heap_segment
      (fun l1 l2 => exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n )
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { move => ? ? [ x [ ? [ -> -> ] ] ].
      rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
      repeat eexists.
      apply: corr_term_subst => [ | y ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') y) => ?.
      + by rewrite !nth_default ?size_mkseq.
      + rewrite !nth_mkseq => /=; eauto 7. }
    have Hcon' : consistent
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H2 ++ map (Some \o
        subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { apply: (consistent_segment_dom
        (fun l1 l2 =>
          ( R l1 l2 \/ S l1 l2 ) \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n)).
      - apply: consistent_segment_union.
        + apply: consistent_segment_cat.
          apply: consistent_segment_cod; eauto.
        + apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        + move => ? ? ? HRS [ ? [ Hlt [ ? ? ] ] ]. subst.
          case HRS =>
            [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
            | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ];
          by rewrite ltnNge leq_addr.
      - move => ? ? [ [ ] | ]; eauto. }
    have Hterm' : corr_term
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var) t').
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts') x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 7. }
    have Hcorr' : corr_heap_segment
      (fun l1 l2 =>
        R l1 l2 \/
        exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n)
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_catL.
        apply: corr_heap_segment_cod.
        + apply: corr_heap_segment_catR; eauto.
          move => /=. eauto.
        + eauto.
      - apply: iso_heap_segment_corr_heap_segment. eauto. }
    have Hhole' : trace_segment S
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts /\ l1 = size H + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts')
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var) t') C.
    { apply: (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
        (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _)) =>
      [ | | ? ? [ ] | ? ? /(trace_segment_boundL _ _ _ _ _ _ Hhole) Hlt | ]; eauto.
      by rewrite size_cat nth_cat Hlt (ltn_addr _ Hlt). }
    refine (diverge_name_let _ _ _
      (IHcycle_need _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole')).
  - apply: diverge_name_case.
    apply: (IHcycle_need _ _ _ _ (cons (context_case pts') \o C) H1 H6 Hcorr Hhole).
  - move: (eval_need_sound _ _ _ _ H0 _ _ _ _ (cons (context_case pts') \o C) H5 H9 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' ? ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H14). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H12 -H11 H1.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts' j = (c, size ts', t1) -> False => [ j Hlt' d | ].
    { move: (H2 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H11 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term
      (fun l1 l2 : nat => R' l1 l2 \/ S' l1 l2)
      (subst (scat ts Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x ].
      - move: H1 (H13 _ Hlt (0, 0, Var 0)) => ->.
        eauto using corr_term_impl.
      - rewrite !nth_scat H12.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H12; eauto.
        + eauto using corr_term_impl. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H' H2'
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2) C.
    { apply: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). eauto. }
    refine (diverge_name_casematch _ _ _ _ _ _ _ _ _ _ _ (IHcycle_need _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'')); eauto.
Qed.

Lemma eval_need_complete H2 t2 H2' v2 :
  eval_name H2 t2 H2' v2 ->
  forall R S H1 t1 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  exists R' S' H1' v1,
  eval_need H1 t1 H1' v1 /\
  consistent (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H2' /\
  corr_term (fun l1 l2 => R' l1 l2 \/ S' l1 l2) v1 v2 /\
  corr_heap_segment R' (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H2' /\
  trace_segment S' (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H2' v2 C /\
  ( forall l1 l2, R l1 l2 \/ S l1 l2 -> R' l1 l2 \/ S' l1 l2 ).
Proof.
  induction 1; inversion 2; subst => [ Hcorr Hhole ].
  - case H7 => [ /Hcorr [ t1 [ Hnth [ t2 [ ] ] ] ] | /Hhole [ ? ] ].
    + rewrite H0. inversion 1.
      subst => [ [ Hterm | [ H2' [ ? [ Hcbn [ T [ ? Hterm' ] ] ] ] ] ] ].
      * have Himpl : forall l1 l2,
          R l1 l2 \/ S l1 l2 ->
          l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2.
        { move => l1 ? [ ]; eauto.
          case (@eqP _ l1 l0); eauto. }
        have Hcon' : consistent (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) H.
        { refine (consistent_segment_weaken
            _ _ _ _ _ _ H3 _ _ (fun _ _ _ _ H => H)) =>
          [ ? ? [ [ ] | [ [ ] | ] ] | ]; eauto. }
        have Hterm' : corr_term (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) t1 t2.
        { refine (corr_term_impl _ _ _ _ Hterm _); eauto. }
        have Hcorr' : corr_heap_segment
          (fun l1 l2 => l1 != l0 /\ R l1 l2)
          (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) (set_nth None H2 l0 None) H.
        { refine (corr_heap_segment_weaken
            _ _ _ _ _ _ _ Hcorr _ _ _) => l1 ? [ ]; eauto.
          by rewrite nth_set_nth => /= /negbTE ->. }
        have Hhole' : trace_segment
          (fun l1 l2 => l1 == l0 /\ R l1 l2 \/ S l1 l2)
          (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2)
          (set_nth None H2 l0 None) H t2 [eta C with l0 |-> nil].
        { apply: (trace_segment_dom (fun l1 l2 => l1 == l0 /\ (R l1 l2 \/ S l1 l2) \/ l1 != l0 /\ S l1 l2)).
          - apply: trace_segment_union => [ ? ? [ /eqP -> HR ] | ].
            + move: nth_set_nth size_set_nth leq_max eqxx => -> -> -> /= ->.
              repeat split.
              * by move: HR orbT =>
                [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
                | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ] -> ->.
              * exists (fun l1 l2 => R l1 l2 \/ S l1 l2), H, l.
                repeat split; eauto.
                apply: t_step => /=. eauto.
            + refine
                (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
                  (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _) _ _ _ _) =>
              [ | ? ? [ ] | | ? ? [ ] | ? ? [ ] /= /negbTE -> ]; eauto.
              rewrite size_set_nth leq_max nth_set_nth =>
                /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->.
              by rewrite orbT.
            + move => l1 ? [ [ ? ? ] | ? ]; eauto.
              case (@eqP _ l1 l0); eauto. }
        move: (IHeval_name _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole') =>
          [ R' [ S' [ ? [ ? [ Hcbn [ Hcon'' [ ? [ Hcorr'' [ Hhole'' Himpl' ] ] ] ] ] ] ] ] ].
        exists
          (fun l1 l2 => R' l1 l2 \/ l1 == l0 /\ S' l1 l2),
          (fun l1 l2 => l1 != l0 /\ S' l1 l2).
        do 4 (eexists; eauto).
        { refine (consistent_segment_weaken
            _ _ _ _ _ _ Hcon'' _ _ (fun _ _ _ _ H => H)) =>
          [ ? ? [ [ | [ ] ] | [ ] ]
          | l1 ? [ ] ]; eauto.
          case (@eqP _ l1 l0); eauto. }
        split.
        { apply: corr_term_impl; eauto.
          move => l1 ? [ ]; eauto.
          case (@eqP _ l1 l0); eauto. }
        split.
        { apply: (corr_heap_segment_dom
            (fun l1 l2 => l1 != l0 /\ R' l1 l2 \/ l1 == l0 /\ (R' l1 l2 \/ S' l1 l2))).
          - apply: corr_heap_segment_union => [ | ? ? [ /eqP -> HRS' ] ].
            + refine (corr_heap_segment_weaken _ _ _ _ _ _ _ Hcorr'' _ _ _) => l1 ? [ ]; eauto.
              * case (@eqP _ l1 l0); eauto.
              * by rewrite nth_set_nth => /= /negbTE ->.
            + move: nth_set_nth (Hcon'' _ _ (ex_intro _ _ (conj HRS' (Himpl' _ _ (Himpl _ _ H7))))) =>
                -> /= [ ? [ Hnth' [ ? [ ] ] ] ].
              rewrite Hnth' (eval_name_heap _ _ _ _ H1 _ _ H0) eqxx.
            inversion 1. subst => [ Hterm0 ].
            repeat eexists. right.
            move: (eval_name_iso_heap _ _ _ _ H1 _ _ _
              (corr_term_comp _ _ _ _
                (corr_term_comp _ _ _ _ (corr_term_sym _ _ _ Hterm) _ Hterm) _
                  (corr_term_sym _ _ _ Hterm0))
                (iso_heap_segment_comp _ _ _ _ _ _ _ 
                  (iso_heap_segment_extR _ _ _ _ _ H3
                    (fun _ _ _ => eval_name_heap _ _ _ _ H1 _))
                  (iso_heap_segment_sym _ _ _ _ Hcon''))) =>
            [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
            do 5 (eexists; eauto).
            apply: corr_term_impl.
            * apply: corr_term_comp; eauto.
            * move => l1 ? [ ? [ [ ? | ? ] ? ] ]; eauto.
              case (@eqP _ l1 l0); repeat eexists; eauto.
        - move => l1 ? [ | [ ] ]; eauto.
          case (@eqP _ l1 l0); eauto. }
      split.
      { apply (trace_segment_weaken _ _ _ _ _ _ _ _ _ _ Hhole'') =>
          [ ? ? [ ] | /= l1 ? [ ] | ? ? [ ] | /= l1 ? [ /negbTE -> ] ]; eauto.
        - case (@eqP _ l1 l0); eauto.
        - rewrite size_set_nth leq_max nth_set_nth =>
            /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole'') ->.
          by rewrite orbT. }
      { move => l1 ? /Himpl /Himpl' [ ]; eauto.
        case (@eqP _ l1 l0); eauto. }
    + case: (eval_name_det _ _ _ _ H1 _ _ Hcbn) => ? ?. subst.
      have Hiso: iso_heap (fun l2 l2' => T l2 l2' \/ l2 = l2' /\ exists l1, R l1 l2 \/ S l1 l2) H H2'.
      { apply: iso_heap_segment_union.
        - apply: iso_heap_segment_cod; eauto.
        - apply: iso_heap_segment_extR.
          + apply: iso_heap_segment_cod.
            * apply: iso_heap_segment_refl.
              apply: consistent_segment_wf_heap_segment; eauto.
            * move => ? ? /=. eauto.
          + move => ? ? ?.
            apply: eval_name_heap. eauto. }
      exists
        (fun l1 l2' => R l1 l2' \/ exists l2, R l1 l2 /\ T l2 l2'),
        (fun l1 l2' => S l1 l2' \/ exists l2, S l1 l2 /\ T l2 l2').
      do 3 (eexists; eauto).
      { econstructor; eauto.
        apply: value_eval_need.
        apply: corr_term_valueR; eauto.
        apply: eval_name_value. eauto. }
      split.
      { refine (consistent_segment_weaken _ _ _ _ _ _ _ _ _ (fun _ _ _ _ H => H)).
        - apply: consistent_segment_iso_heap_segment_comp; eauto.
        - move => ? ? [ [ ? | [ ? [ ? ? ] ] ] | [ ? | [ ? [ ? ? ] ] ] ]; repeat (eexists; eauto).
        - move => ? ? [ ? [ [ ? | ? ] [ ? | [ ? [ ? [ ? | ? ] ] ]   ] ] ]; subst; eauto. }
      split.
      { apply: corr_term_impl; eauto.
        move => ? ? [ ? [ [ ? | ? ] ? ] ]; eauto. }
      split.
      { apply: corr_heap_segment_weaken.
        - apply: corr_heap_segment_iso_heap_comp.
          + apply: Hcorr.
          + apply: Hiso.
          + move => ? ? [ ]; eauto.
        - move => ? ? [ ? | [ ? [ ? ? ] ] ]; eauto 7.
        - move => ? ? [ ? [ [ ? | ? ] [ ? | [ ? [ ? [ ? | ? ] ] ] ] ] ]; subst; eauto 6.
        - move => l1 ? ? ?.
          rewrite set_set_nth eqxx nth_set_nth => /=.
          by move: (@eqP _ l1 l0) Hnth => [ -> -> | ]. }
      split.
      { refine (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
          (trace_segment_red_name_multi _ _ _ _ _ _ _ _ Hhole
            (eval_name_red_name_multi _ _ _ _ _)) _ _ _ _) =>
          [ | ? ? [ | [ ? [ ] ] ] | ? ? [ ] | l1 ? HRS | ]; eauto.
        rewrite set_set_nth eqxx size_set_nth leq_max nth_set_nth => /=.
        split.
        - move: HRS => [ | [ ? [ ] ] ] /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->;
          by rewrite orbT.
        - case (@eqP _ l1 l0) => [ -> | // ].
          by rewrite Hnth. }
      { move => ? ? [ ]; eauto. }
  - refine (False_ind _
      (eval_name_diverge_name_disjoint _ _ _ _ _
        (cycle_need_sound _ _ _ _ _ _ _ _ H3 H4 Hcorr Hhole))); eauto.
  - move: (IHeval_name1 _ _ _ _ (cons (context_app t2) \o C) H3 H8 Hcorr Hhole) =>
      [ R' [ S' [ H1' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' Himpl ] ] ].
    have Hterm'' : corr_term
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2)
      (subst (scons t5 Var) t)
      (subst (scons t2 Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] ] /=; eauto.
      apply: corr_term_impl; eauto. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H'
      (subst (scons t2 Var) t0) C.
    { exact: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). }
    move: (IHeval_name2 _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Himpl : forall l1 l2,
      R l1 l2 \/ S l1 l2 ->
      ( R l1 l2 \/
        exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
      S l1 l2.
    { move => ? ? [ ]; eauto. }
    have Hiso' : iso_heap_segment
      (fun l1 l2 => exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n )
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { move => ? ? [ x [ ? [ -> -> ] ] ].
      rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
      repeat eexists.
      apply: corr_term_subst => [ | y ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts) y) => ?.
      + by rewrite !nth_default ?size_mkseq.
      + rewrite !nth_mkseq => /=; eauto 7. }
    have Hcon' : consistent
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
        S l1 l2 )
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { apply: (consistent_segment_dom
        (fun l1 l2 =>
          ( R l1 l2 \/ S l1 l2 ) \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n)).
      - apply: consistent_segment_union.
        + apply: consistent_segment_cat.
          apply: consistent_segment_cod; eauto.
        + apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        + move => ? ? ? HRS [ ? [ Hlt [ ? ? ] ] ]. subst.
          case HRS =>
            [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
            | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ];
          by rewrite ltnNge leq_addr.
      - move => ? ? [ [ ] | ]; eauto. }
    have Hterm' : corr_term
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
        S l1 l2 )
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var) t0)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t).
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H6.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 7. }
    have Hcorr' : corr_heap_segment
      (fun l1 l2 =>
        R l1 l2 \/
        exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n)
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_catL.
        apply: corr_heap_segment_cod.
        + apply: corr_heap_segment_catR; eauto.
          move => /=. eauto.
        + eauto.
      - apply: iso_heap_segment_corr_heap_segment. eauto. }
    have Hhole' : trace_segment S
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1 + n /\ l2 = size H + n ) \/
        S l1 l2 )
      (H1 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (H ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t) C.
    { apply: (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
        (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _)) =>
      [ | | ? ? [ ] | ? ? /(trace_segment_boundL _ _ _ _ _ _ Hhole) Hlt | ]; eauto.
      by rewrite size_cat nth_cat Hlt (ltn_addr _ Hlt). }
    move: (IHeval_name _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ _ (cons (context_case pts) \o C) H5 H9 Hcorr Hhole) =>
      [ R' [ S' [ H2' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' ? ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H11). }
    have ? : forall d, nth d pts0 i = (c, size ts0, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H12 H14 H1 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts0 j = (c, size ts0, t1) -> False => [ j Hlt' d | ].
    { move: (H2 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H12 H14 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term
      (fun l1 l2 : nat => R' l1 l2 \/ S' l1 l2)
      (subst (scat ts0 Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x ].
      - move: H10 Hlt => <- /H13 /(_ (0, 0, Var 0)).
        rewrite H1.
        eauto using corr_term_impl.
      - rewrite !nth_scat H14.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H14; eauto.
        + eauto using corr_term_impl. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H2' H'
      (subst (scat ts Var) t0) C.
    { refine (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). eauto 6. }
    move: (IHeval_name2 _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Lemma diverge_need_complete_aux :
  forall H2 t2,
  diverge_name H2 t2 ->
  forall R S H1 t1 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  ~ cycle_need H1 t1 ->
  diverge_need H1 t1.
Proof.
  cofix diverge_need_complete_aux;
  inversion 1; subst => [ R S H1_ ? C Hcon ];
  inversion 1; subst => [ Hcorr Hhole HNcycle ].
  - case H6 => [ /Hcorr [ t1 [ ? [ t2 [ ] ] ] ] | /Hhole [ ? ? ] ].
    + rewrite H1. inversion 1.
      subst => [ [ Hterm | [ ? [ ? [ Hcbn [ ? [ ? Hterm ] ] ] ] ] ] ].
      * have Himpl : forall l1 l2,
          R l1 l2 \/ S l1 l2 ->
          l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2.
        { move => l1 ? [ ]; eauto.
          case (@eqP _ l1 l0); eauto. }
        have Hcon' : consistent (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) H2.
        { refine (consistent_segment_weaken
                    _ _ _ _ _ _ Hcon _ _ (fun _ _ _ _ H => H)) =>
          [ ? ? [ [ ] | [ [ ] | ] ] | ]; eauto. }
        have Hterm' : corr_term (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) t1 t2.
        { refine (corr_term_impl _ _ _ _ Hterm _); eauto. }
        have Hcorr' : corr_heap_segment
          (fun l1 l2 => l1 != l0 /\ R l1 l2)
          (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2) (set_nth None H1_ l0 None) H2.
        { refine (corr_heap_segment_weaken
                    _ _ _ _ _ _ _ Hcorr _ _ _) => l1 ? [ ]; eauto.
            by rewrite nth_set_nth => /= /negbTE ->. }
        have Hhole' : trace_segment
          (fun l1 l2 => l1 == l0 /\ R l1 l2 \/ S l1 l2)
          (fun l1 l2 => l1 != l0 /\ R l1 l2 \/ l1 == l0 /\ R l1 l2 \/ S l1 l2)
          (set_nth None H1_ l0 None) H2 t2 [eta C with l0 |-> nil].
        { apply: (trace_segment_dom (fun l1 l2 => l1 == l0 /\ (R l1 l2 \/ S l1 l2) \/ l1 != l0 /\ S l1 l2)).
          - apply: trace_segment_union => [ ? ? [ /eqP -> HR ] | ].
            + move: nth_set_nth size_set_nth leq_max eqxx => -> -> -> /= ->.
              repeat split.
              * by move: HR orbT =>
                [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
                | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ] -> ->.
              * exists (fun l1 l2 => R l1 l2 \/ S l1 l2), H2, l.
                repeat split; eauto.
                apply: t_step => /=. eauto.
            + refine
                (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
                  (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _) _ _ _ _) =>
              [ | ? ? [ ] | | ? ? [ ] | ? ? [ ] /= /negbTE -> ]; eauto.
              rewrite size_set_nth leq_max nth_set_nth =>
                /= /negbTE -> /(trace_segment_boundL _ _ _ _ _ _ Hhole) ->.
              by rewrite orbT.
            + move => l1 ? [ [ ? ? ] | ? ]; eauto.
              case (@eqP _ l1 l0); eauto. }
        by refine (diverge_need_loc _ _ _ _ (diverge_need_complete_aux _ _ _ _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole' _)); eauto.
      * case: (eval_name_diverge_name_disjoint _ _ _ _ Hcbn H3).
    + by case HNcycle; eauto.
  - apply: diverge_need_appL.
    refine (diverge_need_complete_aux _ _ _ _ _ _ _ (cons (context_app t0) \o C) Hcon H6 Hcorr Hhole _); eauto.
  - move: (eval_need_complete _ _ _ _ H1 _ _ _ _ (cons (context_app t3) \o C) Hcon H7 Hcorr Hhole) =>
      [ R' [ S' [ H1' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' Himpl ] ] ].
    have Hterm'' : corr_term
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2)
      (subst (scons t4 Var) t)
      (subst (scons t3 Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] ] /=; eauto.
      apply: corr_term_impl; eauto. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H'
      (subst (scons t3 Var) t0) C.
    { apply: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole'). eauto. }
    refine (diverge_need_appabs _ _ _ _ _ _
      (diverge_need_complete_aux _ _ _ _ _ _ _ _ Hcon' Hterm'' Hcorr' Hhole'' _)); eauto.
  - have Himpl : forall l1 l2,
      R l1 l2 \/ S l1 l2 ->
      ( R l1 l2 \/
        exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
      S l1 l2.
    { move => ? ? [ ]; eauto. }
    have Hiso' : iso_heap_segment
      (fun l1 l2 => exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n )
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H1_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts).
    { move => ? ? [ x [ ? [ -> -> ] ] ].
      rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
      repeat eexists.
      apply: corr_term_subst => [ | y ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts) y) => ?.
      + by rewrite !nth_default ?size_mkseq.
      + rewrite !nth_mkseq => /=; eauto 7. }
    have Hcon' : consistent
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts).
    { apply: (consistent_segment_dom
        (fun l1 l2 =>
          ( R l1 l2 \/ S l1 l2 ) \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n)).
      - apply: consistent_segment_union.
        + apply: consistent_segment_cat.
          apply: consistent_segment_cod; eauto.
        + apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        + move => ? ? ? HRS [ ? [ Hlt [ ? ? ] ] ]. subst.
          case HRS =>
            [ /(corr_heap_segment_boundL _ _ _ _ Hcorr)
            | /(trace_segment_boundL _ _ _ _ _ _ Hhole) ];
          by rewrite ltnNge leq_addr.
      - move => ? ? [ [ ] | ]; eauto. }
    have Hterm' : corr_term
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var) t0)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var) t).
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 7. }
    have Hcorr' : corr_heap_segment
      (fun l1 l2 =>
        R l1 l2 \/
        exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n)
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H1_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_catL.
        apply: corr_heap_segment_cod.
        + apply: corr_heap_segment_catR; eauto.
          move => /=. eauto.
        + eauto.
      - apply: iso_heap_segment_corr_heap_segment. eauto. }
    have Hhole' : trace_segment S
      (fun l1 l2 =>
        ( R l1 l2 \/
          exists n, n < size ts0 /\ l1 = size H1_ + n /\ l2 = size H2 + n ) \/
        S l1 l2 )
      (H1_ ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0)
      (H2 ++ map (Some \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var) t) C.
    { apply: (trace_segment_weaken _ _ _ _ _ _ _ _ _ _
        (trace_segment_red_name _ _ _ _ _ _ _ _ Hhole _)) =>
      [ | | ? ? [ ] | ? ? /(trace_segment_boundL _ _ _ _ _ _ Hhole) Hlt | ]; eauto.
      by rewrite size_cat nth_cat Hlt (ltn_addr _ Hlt). }
    refine (diverge_need_let _ _ _
      (diverge_need_complete_aux _ _ _ _ _ _ _ _ Hcon' Hterm' Hcorr' Hhole' _)); eauto.
  - refine (diverge_need_case _ _ _
      (diverge_need_complete_aux _ _ _ _ _ _ _ (cons (context_case pts) \o C) Hcon H5 Hcorr Hhole _)); eauto.
  - move: (eval_need_complete _ _ _ _ H1 _ _ _ _ (cons (context_case pts) \o C) Hcon H8 Hcorr Hhole) =>
      [ R' [ S' [ H1' [ ? [ ? [ Hcon' [ ] ] ] ] ] ] ].
    inversion 1. subst => [ [ Hcorr' [ Hhole' ? ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H3 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H10). }
    have ? : forall d, nth d pts0 i = (c, size ts0, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H11 H13 H3 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts0 j = (c, size ts0, t1) -> False => [ j Hlt' d | ].
    { move: (H4 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H11 H13 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term
      (fun l1 l2 : nat => R' l1 l2 \/ S' l1 l2)
      (subst (scat ts0 Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x ].
      - move: H9 Hlt => <- /H12 /(_ (0, 0, Var 0)).
        rewrite H3.
        eauto using corr_term_impl.
      - rewrite !nth_scat H13.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H14; eauto.
        + eauto using corr_term_impl. }
    have Hhole'' : trace_segment S'
      (fun l1 l2 => R' l1 l2 \/ S' l1 l2) H1' H'
      (subst (scat ts Var) t0) C.
    { apply: (trace_segment_red_name _ _ _ _ _ _ _ C Hhole' _). eauto. }
    apply: diverge_need_casematch; eauto.
Qed.

Corollary diverge_need_complete :
  forall H2 t2,
  diverge_name H2 t2 ->
  forall R S H1 t1 C,
  consistent (fun l1 l2 => R l1 l2 \/ S l1 l2) H2 ->
  corr_term (fun l1 l2 => R l1 l2 \/ S l1 l2) t1 t2 ->
  corr_heap_segment R (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 ->
  trace_segment S (fun l1 l2 => R l1 l2 \/ S l1 l2) H1 H2 t2 C ->
  cycle_need H1 t1 \/ diverge_need H1 t1.
Proof.
  move => ? ? Hdiv ? ? H1 t1 ? Hcon Hterm Hcorr Hhole.
  case (classic (cycle_need H1 t1)) =>
    [ | /(diverge_need_complete_aux _ _ Hdiv _ _ _ _ _ Hcon Hterm Hcorr Hhole) ]; eauto.
Qed.
