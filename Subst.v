Require Import Relations Classical.
From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet.
Require Heaps.

Inductive eval_name : term -> term -> Prop :=
  | eval_name_app t0 t1 t2 v :
      eval_name t1 (Abs t0) ->
      eval_name (subst (scons t2 Var) t0) v ->
      eval_name (App t1 t2) v
  | eval_name_abs t0 :
      eval_name (Abs t0) (Abs t0)
  | eval_name_let ts t v :
      eval_name (subst (scat (map (Let ts) ts) Var) t) v ->
      eval_name (Let ts t) v
  | eval_name_cons c ts :
      eval_name (Cons c ts) (Cons c ts)
  | eval_name_case c i t t0 ts pts v :
      eval_name t (Cons c ts) ->
      (forall d, nth d pts i = (c, size ts, t0)) ->
      (forall j d t0, nth d pts j = (c, size ts, t0) -> i <= j) ->
      eval_name (subst (scat ts Var) t0) v ->
      eval_name (Case t pts) v.

CoInductive diverge_name : term -> Prop :=
  | diverge_name_appL t1 t2 :
      diverge_name t1 ->
      diverge_name (App t1 t2)
  | diverge_name_beta t0 t1 t2 :
      eval_name t1 (Abs t0) ->
      diverge_name (subst (scons t2 Var) t0) ->
      diverge_name (App t1 t2)
  | diverge_name_let ts t :
      diverge_name (subst (scat (map (Let ts) ts) Var) t) ->
      diverge_name (Let ts t)
  | diverge_name_case t pts :
      diverge_name t ->
      diverge_name (Case t pts)
  | diverge_name_casematch c i t t0 ts pts :
      eval_name t (Cons c ts) ->
      (forall d, nth d pts i = (c, size ts, t0)) ->
      (forall j d t0, nth d pts j = (c, size ts, t0) -> i <= j) ->
      diverge_name (subst (scat ts Var) t0) ->
      diverge_name (Case t pts).

Hint Constructors eval_name diverge_name.

Inductive corr_term (P : nat -> Prop) :
      seq (option term) -> (nat -> term) -> term -> term -> Prop :=
  | corr_term_indir H mu l t t' :
      nth None H l = Some t ->
      corr_term P H mu t t' ->
      corr_term P H mu (Loc l) t'
  | corr_term_loc H mu l t' :
      P l ->
      mu l = t' ->
      corr_term P H mu (Loc l) t'
  | corr_term_var H mu x :
      corr_term P H mu (Var x) (Var x)
  | corr_term_abs H mu t t' :
      corr_term P (map (omap (rename succn)) H) (rename succn \o mu) t t' ->
      corr_term P H mu (Abs t) (Abs t')
  | corr_term_app H mu t1 t1' t2 t2' :
      corr_term P H mu t1 t1' ->
      corr_term P H mu t2 t2' ->
      corr_term P H mu (App t1 t2) (App t1' t2')
  | corr_term_let H mu ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term P
          (map (omap (rename (addn (size ts)))) H)
          (rename (addn (size ts)) \o mu)
          (nth d ts x) (nth d ts' x) ) ->
      corr_term P
        (map (omap (rename (addn (size ts)))) H)
        (rename (addn (size ts)) \o mu) t t' ->
      corr_term P H mu (Let ts t) (Let ts' t')
  | corr_term_vcons H mu c ls ts' :
      size ls = size ts' ->
      ( forall x, x < size ls -> forall d d',
        corr_term P H mu (Loc (nth d ls x)) (nth d' ts' x) ) ->
      corr_term P H mu (VCons c ls) (Cons c ts')
  | corr_term_cons H mu c ts ts' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term P H mu (nth d ts x) (nth d ts' x) ) ->
      corr_term P H mu (Cons c ts) (Cons c ts')
  | corr_term_case H mu t t' (pts pts' : seq (cons * nat * term)) :
      corr_term P H mu t t' ->
      size pts = size pts' ->
      ( forall x d, (nth d pts x).1 = (nth d pts' x).1 ) ->
      ( forall x, x < size pts -> forall d,
        corr_term P
          (map (omap (rename (addn (nth d pts x).1.2))) H)
          (rename (addn (nth d pts x).1.2) \o mu)
          (nth d pts x).2 (nth d pts' x).2 ) ->
      corr_term P H mu (Case t pts) (Case t' pts').

Hint Constructors corr_term.

Definition corr_heap_segment (P P' : nat -> Prop) H mu :=
  forall l, P l ->
  exists t, nth None H l = Some t /\
  exists ts' t', mu l = Let ts' t' /\
  corr_term P' H mu t (subst (scat (map (Let ts') ts') Var) t').
Definition corr_heap P := corr_heap_segment P P.

Lemma eq_omap A B (f g : A -> B) : forall o,
  (forall x, f x = g x) ->
  omap f o = omap g o.
Proof. by move => [ ? /= -> | ]. Qed.

Lemma omap_id A : forall (o : option A), omap id o = o.
Proof. by move => [ ]. Qed.

Lemma omap_comp A B C (f : B -> C) (g : A -> B) : forall o,
  omap f (omap g o) = omap (f \o g) o.
Proof. by move => [ ]. Qed.

Lemma nth_map_heap A B H l (f : A -> B) :
  nth None (map (omap f) H) l = omap f (nth None H l).
Proof.
  case (leqP (size H) l) => ?.
  - by rewrite !nth_default ?size_map.
  - exact: nth_map.
Qed.

Lemma corr_term_impl P H mu t t' :
  corr_term P H mu t t' ->
  forall (P' : nat -> Prop) H' mu',
  ( forall l, P l -> P' l ) ->
  ( forall l,
    nth None H l = None \/
    nth None H l = nth None H' l ) ->
  ( forall l, P l -> mu l = mu' l ) ->
  corr_term P' H' mu' t t'.
Proof.
  induction 1 => ? H' ? HP HQ HPmu; eauto.
  - apply: corr_term_indir; eauto.
    by move: H0 (HQ l) => -> [ ].
  - apply: corr_term_loc; eauto.
    erewrite <- HPmu; eauto.
  - constructor.
    ( apply: IHcorr_term; eauto ) => l.
    + rewrite !nth_map_heap.
      case (HQ l) => ->; eauto.
    + by move => /HPmu /= ->.
  - constructor; eauto.
    + move => ? ? ?.
      ( apply: H2; eauto ) => l.
      * rewrite !nth_map_heap.
        case (HQ l) => ->; eauto.
      * by move => /HPmu /= ->.
    + ( apply: IHcorr_term; eauto ) => l.
      * rewrite !nth_map_heap.
        case (HQ l) => ->; eauto.
      * by move => /HPmu /= ->.
  - constructor; eauto.
    move => ? ? ?.
    ( apply: H4; eauto ) => l.
    + rewrite !nth_map_heap.
      case (HQ l) => ->; eauto.
    + by move => /HPmu /= ->.
Qed.

Lemma corr_term_rename P H mu t t' :
  corr_term P H mu t t' ->
  forall H' mu' r,
  (forall l, mu' l = rename r (mu l)) ->
  (forall l, nth None H' l = omap (rename r) (nth None H l)) ->
  corr_term P H' mu' (rename r t) (rename r t').
Proof.
  induction 1 => H' ? ? Hmu Hnth /=; eauto.
  - apply: corr_term_indir; eauto.
    by rewrite Hnth H0.
  - apply: corr_term_loc; eauto.
    by rewrite Hmu H1.
  - constructor.
    apply: IHcorr_term => ?.
    + rewrite /funcomp Hmu !rename_rename_comp.
      exact: eq_rename.
    + rewrite !nth_map_heap Hnth !omap_comp.
      apply: eq_omap => ?.
      rewrite /funcomp !rename_rename_comp.
      exact: eq_rename.
  - constructor; rewrite !size_map -?H0; eauto.
    + move => ? ? d.
      rewrite !(nth_map d) -?H0 => //.
      apply: H2 => // ?.
      * rewrite /funcomp Hmu !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp !rename_rename_comp.
        apply: eq_rename => x /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
    + apply: IHcorr_term => ?.
      * rewrite /funcomp Hmu !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
  - constructor; rewrite ?size_map; eauto.
    move => ? ? ? d'.
    rewrite (nth_map d') -?H0 => //.
    exact: H2.
  - constructor; rewrite !size_map; eauto.
    move => ? ? d.
    rewrite !(nth_map d) -?H0 => //.
    exact: H2.
  - constructor; rewrite ?size_map; eauto.
    + move => x d.
      case (leqP (size pts) x) => ?.
      * rewrite !nth_default ?size_map; congruence.
      * rewrite !(nth_map d) => /=; congruence.
    + move => ? ? d.
      rewrite !(nth_map d) -?H1 ?H2 => //.
      apply: H4 => // ?.
      * rewrite /funcomp Hmu !rename_rename_comp.
        apply: eq_rename => x /=.
        by rewrite upnren_unfold ltnNge H2 leq_addr addKn.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge H2 leq_addr addKn.
Qed.

Lemma corr_term_subst P H mu t t' :
  corr_term P H mu t t' ->
  forall H' mu' s s',
  (forall x, corr_term P H' mu' (s x) (s' x)) ->
  (forall l, nth None H' l = omap (subst s) (nth None H l)) ->
  (forall l, mu' l = subst s' (mu l)) ->
  corr_term P H' mu' (subst s t) (subst s' t').
Proof.
  induction 1 => ? ? ? ? Hs Hnth Hmu /=; eauto.
  - apply: corr_term_indir; eauto.
    by rewrite Hnth H0.
  - apply: corr_term_loc; eauto.
    by rewrite Hmu H1.
  - constructor.
    apply: IHcorr_term => [ [ | ? ] //= | ? | ? ].
    + ( apply: corr_term_rename; eauto ) => ?.
      by rewrite nth_map_heap.
    + rewrite !nth_map_heap Hnth !omap_comp.
      apply: eq_omap => ?.
      rewrite /funcomp rename_subst_comp subst_rename_comp.
      exact: eq_subst.
    + rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
      exact: eq_subst.
  - constructor; rewrite !size_map -?H0; eauto.
    + move => ? ? d.
      rewrite !(nth_map d) -?H0 => //.
      apply: H2 => // x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        ( apply: corr_term_rename; eauto ) => ?.
        by rewrite nth_map_heap.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
    + apply IHcorr_term => x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        ( apply: corr_term_rename; eauto ) => ?.
        by rewrite nth_map_heap.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
  - constructor; rewrite ?size_map -?H0; eauto.
    move => ? ? ? d'.
    rewrite (nth_map d') -?H0 => //.
    exact: H2.
  - constructor; rewrite !size_map; eauto.
    move => ? ? d.
    rewrite !(nth_map d) -?H0; eauto.
  - constructor; rewrite ?size_map -?H1; eauto.
    + move => x d.
      case (leqP (size pts) x) => ?.
      * rewrite !nth_default ?size_map; congruence.
      * rewrite !(nth_map d) => /=; congruence.
    + move => i ? d.
      rewrite !(nth_map d) -?H1 ?H2 => //.
      apply: H4 => // x.
      * rewrite !upn_unfold.
        case (leqP (nth d pts' i).1.2 x) => ? //.
        ( apply: corr_term_rename; eauto ) => ?.
        by rewrite nth_map_heap.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold H2 ltnNge leq_addr addKn.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold H2 ltnNge leq_addr addKn.
Qed.

Lemma corr_heap_segment_impl P P' H mu :
  corr_heap_segment P P' H mu ->
  forall (Q Q' : nat -> Prop) H',
  ( forall l, Q l -> P l ) ->
  ( forall l, P' l -> Q' l ) ->
  ( forall l t, nth None H l = Some t -> nth None H' l = Some t ) ->
  corr_heap_segment Q Q' H' mu.
Proof.
  move => Hheap ? ? ? Hdom Hcod Hnth ? /Hdom /Hheap
    [ ? [ /Hnth -> [ ? [ ? [ -> ? ] ] ] ] ].
  repeat (eexists; eauto).
  ( apply: corr_term_impl; eauto ) => l.
  move: (nth None H l) (Hnth l) => [ ? /(_ _ erefl) | ]; eauto.
Qed.

Lemma corr_heap_ext P H mu :
  corr_heap P H mu ->
  forall mu',
  ( forall l, P l -> mu l = mu' l ) ->
  corr_heap P H mu'.
Proof.
  move => Hheap ? HPmu ? HP.
  move: (HPmu _ HP) (Hheap _ HP) => ->
    [ ? [ -> [ ? [ ? [ -> ? ] ] ] ] ].
  repeat (eexists; eauto).
  apply: corr_term_impl; eauto.
Qed.

Corollary corr_heap_segment_cat P P' H Hd mu :
  corr_heap_segment P P' H mu ->
  corr_heap_segment P P' (H ++ Hd) mu.
Proof.
  move => /corr_heap_segment_impl.
  apply => l //.
  by move: nth_cat (leqP (size H) l) =>
    -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rcons P P' H o mu :
  corr_heap_segment P P' H mu ->
  corr_heap_segment P P' (rcons H o) mu.
Proof. by rewrite -cats1 => /corr_heap_segment_cat. Qed.

Lemma corr_heap_segment_union P P' Q H mu :
  corr_heap_segment P Q H mu ->
  corr_heap_segment P' Q H mu ->
  corr_heap_segment (fun l => P l \/ P' l) Q H mu.
Proof.
  move => Hheap Hheap' ? [ /Hheap | /Hheap' ]
    [ ? [ -> [ ? [ ? [ -> ? ] ] ] ] ];
  repeat (eexists; eauto).
Qed.
  
Lemma corr_heap_segment_bound P P' H mu :
  corr_heap_segment P P' H mu ->
  forall l, P l ->
  l < size H.
Proof.
  move => Hheap l /Hheap [ ? [ ] ].
  by case (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Lemma unwind_indirection P H mu t1 t2 :
  corr_term P H mu t1 t2 ->
  exists t1',
  clos_refl_trans _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H, t1') /\
  corr_term P H mu t1' t2 /\
  forall l, t1' = Loc l -> P l /\ mu l = t2.
Proof.
  induction 1.
  - move: IHcorr_term => [ t1' [ ? [ ? ? ] ] ].
    exists t1'. split; eauto.
    refine (rt_trans _ _ _ _ _ (rt_step _ _ _ (_, _) _) _) => /=; eauto.
  - do 3 (eexists; eauto).
    inversion 1. subst. eauto.
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
  - by do 3 (eexists; eauto).
Qed.

Theorem eval_name_sound H1 H1' t1 v1 :
  Heaps.eval_name H1 t1 H1' v1 ->
  forall P mu t2,
  corr_heap P H1 mu ->
  corr_term P H1 mu t1 t2 ->
  exists v2,
  eval_name t2 v2 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' H1' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ) /\
  ( forall l t, nth None H1 l = Some t -> mu l = mu' l ).
Proof.
  induction 1; inversion 2; subst.
  - move: (H0) H6 => ->. inversion 1. subst.
    exact: IHeval_name.
  - move: (H0) (H2 _ H6) => -> [ ? [ ] ].
    inversion 1. subst => [ [ ? [ ? [ -> ] ] ]
      /(IHeval_name _ _ _ H2) [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H2 H9) =>
      [ ? [ ? [ P' [ mu' [ Hheap [ ] ] ] ] ] ].
    inversion 1. subst => [ [ HP' [ ? HQmu' ] ] ].
    have Hterm' : corr_term P'
      (rcons H' (Some t2)) mu'
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H8 _
            (map (omap (rename succn)) (rcons H' (Some t2)))
            (rename succn \o mu')); eauto ) => l.
        rewrite !nth_map_heap nth_rcons.
        case (leqP (size H') l) => [ /(nth_default _) -> //= | ]; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto 2 ) => l /=.
          move: nth_rcons  (nth None H l)
            (Heaps.eval_name_heap _ _ _ _ H0 l) =>
              -> [ ? /(_ _ erefl) | ]; eauto.
          case (leqP (size H') l) => [ /(nth_default _) -> | ? -> ]; eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap' : corr_heap P' (rcons H' (Some t2)) mu'.
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto.
      move => l.
      by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu'' HQmu'' ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? HP.
      rewrite -HPmu'' => /=; eauto.
    + move => l t HQ.
      move: nth_rcons (leqP (size H') l)
        (Heaps.eval_name_heap _ _ _ _ H0 _ _ HQ) (HQmu'' l t) =>
          -> [ /(nth_default _) -> // | Hlt ? <- //= ]; eauto.
  - repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H11 _
            (map (omap (rename (addn (size ts))))
              (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
            (rename (addn (size ts)) \o
              (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H6.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H6; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H6.
      - move => l.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H6 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ H1 _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ H1) ->.
        + by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H6.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H9 _ _ _) _
              (map (omap (rename (addn (size ts))))
                (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
              (rename (addn (size ts)) \o
                (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H6.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H6 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H6. }
          { move => l.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H6 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu' HQmu' ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? HP.
      rewrite -HPmu'; eauto.
      erewrite corr_heap_segment_bound; eauto.
    + move => l t_.
      by move: nth_cat (leqP (size H) l) (HQmu' l t_) =>
        -> [ /(nth_default _) -> | ].
  - repeat (eexists; eauto).
  - do 2 (eexists; eauto).
    exists P, mu. split.
    { move => l /H0 [ ? [ ] ].
      move: nth_cat (leqP (size H) l) =>
        -> [ /(nth_default _) -> //
           | ? -> [ ? [ ? [ -> Hterm ] ] ] ].
      repeat (eexists; eauto).
      apply: (corr_term_impl _ _ _ _ _ Hterm) => // l0.
      move: nth_cat (leqP (size H) l0) =>
        -> [ /(nth_default _) -> | ]; eauto. }
    split; eauto.
    { constructor; rewrite size_mkseq; eauto.
      move => x ? ? d'.
      rewrite nth_mkseq => //.
      apply: corr_term_indir.
      - by rewrite nth_cat ltnNge leq_addr addKn (nth_map d').
      - refine (corr_term_impl _ _ _ _ _ (H9 _ _ _) _ _ _ _ _ _) => // l.
        move: nth_cat (leqP (size H) l) =>
          -> [ /(nth_default _) -> | ]; eauto. }
  - move: (IHeval_name1 _ _ _ H4 H9) => [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ].
    inversion 1. subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H8). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H13 -H14 H1.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts' j = (c, size ts', t1) -> i <= j => [ j d | ].
    { move: (H2 j d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H13 H14 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' H' mu'
      (subst (scat (map Loc ls) Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x | ? | ? ].
      - move: H1 (H15 _ Hlt (0, 0, Var 0)) => -> /corr_term_impl
          /(_ P' (map (omap (rename (addn (c, size ls, t0).1.2))) H')).
        apply => [ | l | /= ? /HPmu -> ] //=.
        rewrite !nth_map_heap.
        move: (nth None H l) (Heaps.eval_name_heap _ _ _ _ H0 l) =>
          [ ? /(_ _ erefl) -> | ] /=; eauto.
      - rewrite !nth_scat.
        case (leqP (size ls) x) => ?.
        + rewrite !nth_default ?size_map -?H14; eauto.
        + rewrite (nth_map 0) => //.
          exact: H17.
      - rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?leq_addr ?addKn.
      - rewrite subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H14 ?addKn ?leq_addr. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? ?.
      erewrite HPmu; eauto.
    + move => ? ? ?.
      erewrite HQmu; eauto.
Qed.

Theorem diverge_name_sound :
  forall H1 t1,
  Heaps.diverge_name H1 t1 ->
  forall P mu t2,
  corr_heap P H1 mu ->
  corr_term P H1 mu t1 t2 ->
  diverge_name t2.
Proof.
  cofix diverge_name_sound => H ? Hdiv P mu ? Hheap /unwind_indirection [ ? [ Hrt [ ] ] ].
  move: (Heaps.diverge_name_red_name_aux _ _ Hrt _ _ _ _ erefl erefl Hdiv).
  inversion 1; subst.
  - move => ? /(_ _ erefl) [ /Hheap [ ? [ ] ] ].
    rewrite H1. inversion 1.
    subst => [ [ ? [ ? [ -> ? ] ] ] <- ].
    apply: diverge_name_let. eauto.
  - inversion 1. subst => ?.
    apply: diverge_name_appL. eauto.
  - inversion 1. subst => ?.
    move: (eval_name_sound _ _ _ _ H1 _ _ _ Hheap H7) =>
      [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ].
    inversion 1. subst => [ [ HP' [ HPmu HQmu ] ] ].
    have Hterm'' : corr_term P'
      (rcons H' (Some t2)) mu'
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H6 _
            (map (omap (rename succn)) (rcons H' (Some t2)))
            (rename succn \o mu')); eauto ) => l.
        rewrite !nth_map_heap nth_rcons.
        case (leqP (size H') l) => [ /(nth_default _) -> //= | ]; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto 2 ) => l /=.
          move: (nth None H l) (Heaps.eval_name_heap _ _ _ _ H1 l) =>
            [ ? /(_ _ erefl) | ]; eauto.
          move: nth_rcons (leqP (size H') l) =>
            -> [ /(nth_default _) -> // | ? -> ]; eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap'' : corr_heap P' (rcons H' (Some t2)) mu'.
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap' _ _) _ _ _ _ _ _); eauto.
      move => l.
      by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    apply: diverge_name_beta; eauto.
  - inversion 1. subst => ?.
    have Hterm' : corr_term
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H9 _
            (map (omap (rename (addn (size ts))))
              (H ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
            (rename (addn (size ts)) \o
              (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H) l) => [ /(nth_default _) -> | ] /=; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H4.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H4; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H4.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H4 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
        + by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H4.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H7 _ _ _) _
                (map (omap (rename (addn (size ts))))
                  (H ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
                (rename (addn (size ts)) \o
                  (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H4.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H4 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H4. }
          { move => ?.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H4 ?leq_addr ?addKn. } }
    apply: diverge_name_let. eauto.
  - inversion 1. subst => ?.
    apply: diverge_name_case. eauto.
  - inversion 1. subst => ?.
    move: (eval_name_sound _ _ _ _ H1 _ _ _ Hheap H7) => [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ].
    inversion 1. subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H2 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H6). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H11 -H12 H2.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts' j = (c, size ts', t1) -> i <= j => [ j d | ].
    { move: (H3 j d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H11 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' H' mu'
      (subst (scat (map Loc ls) Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x | ? | ? ].
      - move: H2 (H13 _ Hlt (0, 0, Var 0)) => -> /corr_term_impl
          /(_ P' (map (omap (rename (addn (size ls)))) H')).
        apply => [ | l | /= ? /HPmu -> ] //=.
        rewrite !nth_map_heap.
        move: (nth None H l) (Heaps.eval_name_heap _ _ _ _ H1 l) =>
          [ ? /(_ _ erefl) -> | ] /=; eauto.
      - rewrite !nth_scat.
        case (leqP (size ls) x) => ?.
        + rewrite !nth_default ?size_map -?H12; eauto.
        + rewrite (nth_map 0) => //.
          eauto using corr_term_impl.
      - rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_map ?addKn ?leq_addr.
      - rewrite subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H12 ?addKn ?leq_addr. }
    apply: diverge_name_casematch; eauto.
Qed.
    
Theorem eval_name_complete t2 v2 :
  eval_name t2 v2 ->
  forall P mu H1 t1,
  corr_term P H1 mu t1 t2 ->
  corr_heap P H1 mu ->
  exists H1' v1,
  Heaps.eval_name H1 t1 H1' v1 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' H1' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ) /\
  ( forall l t, nth None H1 l = Some t -> mu l = mu' l ).
Proof.
  induction 1 => P mu H_ ? /unwind_indirection [ ? [ ? [ ] ] ];
  inversion 1; subst => Hloc Hheap.
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - move: (IHeval_name1 _ _ _ _ H7 Hheap) => [ H' [ ? [ Hcbn' [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn').
    inversion 1; inversion 1. subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hterm'' : corr_term P'
      (rcons H' (Some t4)) mu'
      (subst (scons (Loc (size H')) Var) t)
      (subst (scons t2 Var) t0).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H9 _
            (map (omap (rename succn)) (rcons H' (Some t4)))
            (rename succn \o mu')); eauto ) => l.
        rewrite !nth_map_heap nth_rcons.
        case (leqP (size H') l) => [ /(nth_default _) -> //= | ]; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto 2 ) => l /=.
          move: nth_rcons  (nth None H_ l)
            (Heaps.eval_name_heap _ _ _ _ Hcbn' l) =>
              -> [ ? /(_ _ erefl) | ]; eauto.
            case (leqP (size H') l) => [ /(nth_default _) -> | ? -> ]; eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap'' : corr_heap P' (rcons H' (Some t4)) mu'.
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap' _ _) _ _ _ _ _ _); eauto.
      move => l.
      by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ _ Hterm'' Hheap'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu'' HQmu'' ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
    + move => ? HP.
      rewrite -HPmu'' => /=; eauto.
    + move => l t_ HQ.
      move: nth_rcons (leqP (size H') l)
        (Heaps.eval_name_heap _ _ _ _ Hcbn' _ _ HQ) (HQmu'' l t_) =>
        -> [ /(nth_default _) -> // | Hlt ? <- //= ]. eauto.
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
  - move: (Hloc _ erefl) => [ /Hheap [ ? [ ] ] ].
    rewrite H1. inversion 1. subst => [ [ ? [ ? [ -> Hterm ] ] ] ].
    inversion 1. subst.
    move: (IHeval_name _ _ _ _ Hterm Hheap) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
  - move: (Hheap _ H1) => [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H2. inversion 1. subst => [ Hterm ].
    move: (IHeval_name _ _ _ _ Hterm Hheap) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
  - have Hterm' : corr_term
      (fun l => P l \/ size H_ <= l /\ l - size H_ < size ts0)
      (H_ ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H_)) (size ts0)) Var)) ts0)
      (fun l => if l < size H_ then mu l else nth (mu l) (map (Let ts) ts) (l - size H_))
      (subst (scat (mkseq (Loc \o addn (size H_)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts) ts) Var) t).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H8 _
            (map (omap (rename (addn (size ts0))))
              (H_ ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H_)) (size ts0)) Var)) ts0))
            (rename (addn (size ts0)) \o
              (fun l => if l < size H_ then mu l else nth (mu l) (map (Let ts) ts) (l - size H_)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H_) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H3; eauto.
        + rewrite nth_mkseq ?H3 => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map.
      - move => l.
        rewrite !nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H3 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H_ <= l /\ l - size H_ < size ts0)
      (H_ ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H_)) (size ts0)) Var)) ts0)
      (fun l => if l < size H_ then mu l else nth (mu l) (map (Let ts) ts) (l - size H_)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
        + by move: nth_cat (leqP (size H_) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) -?H3 => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H3.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H7 _ _ _) _
                (map (omap (rename (addn (size ts0))))
                  (H_ ++ map (Some \o subst (scat (mkseq (Loc \o addn (size H_)) (size ts0)) Var)) ts0))
              (rename (addn (size ts)) \o
                (fun l => if l < size H_ then mu l else nth (mu l) (map (Let ts) ts) (l - size H_))) _ _ _); eauto ) => l /=.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H_) l) => [ /(nth_default _) -> | ]; eauto.
            - by move: H3 => <- /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H3.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H3 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H3. }
          { move => l.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H3 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ _ Hterm' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu' HQmu' ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
    + move => ? HP.
      rewrite -HPmu'; eauto.
      erewrite corr_heap_segment_bound; eauto.
    + move => l t_.
      by move: nth_cat (leqP (size H_) l) (HQmu' l t_) =>
        -> [ /(nth_default _) -> | ].
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
  - do 3 (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
    exists P, mu. split.
    { move => l /Hheap [ ? [ ] ].
      move: nth_cat (leqP (size H_) l) =>
        -> [ /(nth_default _) -> //
           | ? -> [ ? [ ? [ -> Hterm ] ] ] ].
      repeat (eexists; eauto).
      apply: (corr_term_impl _ _ _ _ _ Hterm) => // l0.
      move: nth_cat (leqP (size H_) l0) =>
        -> [ /(nth_default _) -> | ]; eauto. }
    split; eauto.
    { constructor; rewrite size_mkseq; eauto.
      move => x ? ? d'.
      rewrite nth_mkseq => //.
      apply: corr_term_indir.
      - by rewrite nth_cat ltnNge leq_addr addKn (nth_map d').
      - refine (corr_term_impl _ _ _ _ _ (H6 _ _ _) _ _ _ _ _ _) => // l.
        move: nth_cat (leqP (size H_) l) =>
          -> [ /(nth_default _) -> | ]; eauto. }
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - by move: (Hloc _ erefl) => [ /Hheap [ ? [ ? [ ? [ ? [ -> ] ] ] ] ] ].
  - move: (IHeval_name1 _ _ _ _ H6 Hheap) => [ H' [ ? [ Hcbn [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn). inversion 1; inversion 1.
    subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H0 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H5). }
    have ? : forall d, nth d pts0 i = (c, size ls, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H11 H0 -H14.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts0 j = (c, size ls, t1) -> i <= j => [ j d | ].
    { move: (H1 j d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H11 H14 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' H' mu'
      (subst (scat (map Loc ls) Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x | ? | ? ].
      - move: H7 Hlt => <- /H12 /(_ (0, 0, Var 0)).
        rewrite H0 => /= /corr_term_impl
          /(_ P' (map (omap (rename (addn (nth (0, 0, Var 0) pts0 i).1.2))) H')).
        apply => [ | l | /= ? /HPmu -> ] //=.
        rewrite !nth_map_heap.
        move: (nth None H_ l) (Heaps.eval_name_heap _ _ _ _ Hcbn l) =>
          [ ? /(_ _ erefl) -> | ] /=; eauto.
      - rewrite !nth_scat.
        case (leqP (size ls) x) => ?.
        + rewrite !nth_default ?size_map -?H14; eauto.
        + rewrite (nth_map 0) => //.
          exact: H16.
      - rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id ?H11 ?H0 => //= ?.
        by rewrite nth_scat nth_default size_map H14 ?leq_addr ?addKn.
      - rewrite subst_rename_comp (eq_subst _ _ Var) ?subst_id ?H11 ?H0 => //= ?.
        by rewrite nth_scat nth_default -H14 ?leq_addr ?addKn. }
    move: (IHeval_name2 _ _ _ _ Hterm'' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto using Heaps.red_name_multi_eval_name_aux).
    + move => ? ?.
      erewrite HPmu; eauto.
    + move => ? ? ?.
      erewrite HQmu; eauto.
Qed.

Theorem diverge_name_complete :
  forall t2,
  diverge_name t2 ->
  forall P mu H1 t1,
  corr_term P H1 mu t1 t2 ->
  corr_heap P H1 mu ->
  Heaps.diverge_name H1 t1.
Proof.
  cofix diverge_name_complete.
  inversion 1; inversion 1; subst => [ Hheap ].
  - apply: Heaps.diverge_name_loc; eauto.
  - by move: H6 (Hheap _ H5) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - apply: Heaps.diverge_name_appL. eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - by move: H7 (Hheap _ H6) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (eval_name_complete _ _ H0 _ _ _ _ H11 Hheap) =>
      [ H1' [ ? [ Hcbn [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1; inversion 1; subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hterm' : corr_term
      P' (rcons H1' (Some t6)) mu'
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons t3 Var) t0).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H10 _
            (map (omap (rename succn)) (rcons H1' (Some t6)))
            (rename succn \o mu')); eauto ) => l.
        rewrite !nth_map_heap nth_rcons.
        case (leqP (size H1') l) => [ /(nth_default _) -> | ] /=; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto 2 ) => l /=.
          move: nth_rcons (nth None H3 l)
            (Heaps.eval_name_heap _ _ _ _ Hcbn l) =>
              -> [ ? /(_ _ erefl) | ]; eauto.
            case (leqP (size H1') l) => [ /(nth_default _) -> | ? -> ]; eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap'' : corr_heap P' (rcons H1' (Some t6)) mu'.
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap' _ _) _ _ _ _ _ _); eauto.
      move => l.
      by move: nth_rcons (leqP (size H1') l) => -> [ /(nth_default _) -> | ]. }
    apply: Heaps.diverge_name_beta; eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - move: H6 (Hheap _ H5) => -> [ ? [ ? [ ? [ ? []  ] ] ] ].
    inversion 1. subst => ?.
    apply: Heaps.diverge_name_loc; eauto.
  - have Hterm' : corr_term
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts) ts) Var) t).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H12 _
            (map (omap (rename (addn (size ts0))))
              (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0))
            (rename (addn (size ts0)) \o
              (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H2) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H7.
        case (leqP (size ts0) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H7; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H7.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H7 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cat.
        refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto.
        by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)). by rewrite -H7.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H11 _ _ _) _
              (map (omap (rename (addn (size ts0))))
                (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0))
              (rename (addn (size ts0)) \o
                (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H2) l) => [ /(nth_default _) -> | ] /=; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H7.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H7 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H7. }
          { move => ?.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
            by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr. }
          { move => ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H7 ?leq_addr ?addKn. } }
    apply: Heaps.diverge_name_let. eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - by move: H6 (Hheap _ H5) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - apply: Heaps.diverge_name_case. eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - by move: H9 (Hheap _ H8) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (eval_name_complete _ _ H0 _ _ _ _ H10 Hheap) =>
      [ H1' [ ? [ Hcbn [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1; inversion 1; subst => [ [ ? [ HPmu HQmu ] ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H8). }
    have ? : forall d, nth d pts0 i = (c, size ls, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H15 H1 H17. 
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts0 j = (c, size ls, t1) -> i <= j => [ j d | ].
    { move: (H2 j d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H15 H17 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' H1' mu'
      (subst (scat (map Loc ls) Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x | ? | ? ].
      - move: H11 Hlt => <- /H16 /(_ (0, 0, Var 0)) /corr_term_impl
          /(_ P' (map (omap (rename (addn (size ls)))) H1')).
        rewrite H1. apply => [ | l | /= ? /HPmu -> ] //=.
        rewrite !nth_map_heap H15 H1 H17 => /=.
        move: (nth None H5 l) (Heaps.eval_name_heap _ _ _ _ Hcbn l) =>
          [ ? /(_ _ erefl) -> | ] /=; eauto.
      - rewrite !nth_scat.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_map -?H17; eauto.
        + rewrite (nth_map 0) ?H17; eauto.
      - rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?leq_addr ?addKn.
      - rewrite subst_rename_comp H15 H1 (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default ?addKn ?leq_addr. }
    apply: Heaps.diverge_name_casematch; eauto.
Qed.
