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
  | eval_name_ctor c ts :
      eval_name (Ctor c ts) (Ctor c ts)
  | eval_name_case c i t t0 ts pts v :
      eval_name t (Ctor c ts) ->
      ( forall d, nth d pts i = (c, size ts, t0) ) ->
      ( forall j, j < i ->
        forall d t0, 
        nth d pts j = (c, size ts, t0) ->
        False ) ->
      eval_name (subst (scat ts Var) t0) v ->
      eval_name (Case t pts) v.

CoInductive diverge_name : term -> Prop :=
  | diverge_name_appL t1 t2 :
      diverge_name t1 ->
      diverge_name (App t1 t2)
  | diverge_name_appabs t0 t1 t2 :
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
      eval_name t (Ctor c ts) ->
      ( forall d, nth d pts i = (c, size ts, t0) ) ->
      ( forall j, j < i ->
        forall d t0, 
        nth d pts j = (c, size ts, t0) ->
        False ) ->
      diverge_name (subst (scat ts Var) t0) ->
      diverge_name (Case t pts).

Hint Constructors eval_name diverge_name.

Inductive corr_term (P : nat -> Prop) :
      (nat -> term) -> term -> term -> Prop :=
  | corr_term_loc mu l t' :
      P l ->
      mu l = t' ->
      corr_term P mu (Loc l) t'
  | corr_term_var mu x :
      corr_term P mu (Var x) (Var x)
  | corr_term_abs mu t t' :
      corr_term P (rename succn \o mu) t t' ->
      corr_term P mu (Abs t) (Abs t')
  | corr_term_app mu t1 t1' t2 t2' :
      corr_term P mu t1 t1' ->
      corr_term P mu t2 t2' ->
      corr_term P mu (App t1 t2) (App t1' t2')
  | corr_term_let mu ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term P
          (rename (addn (size ts)) \o mu)
          (nth d ts x) (nth d ts' x) ) ->
      corr_term P
        (rename (addn (size ts)) \o mu) t t' ->
      corr_term P mu (Let ts t) (Let ts' t')
  | corr_term_ctor mu c ts ts' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term P mu (nth d ts x) (nth d ts' x) ) ->
      corr_term P mu (Ctor c ts) (Ctor c ts')
  | corr_term_case mu t t' (pts pts' : seq (ctor * nat * term)) :
      corr_term P mu t t' ->
      size pts = size pts' ->
      ( forall x d, (nth d pts x).1 = (nth d pts' x).1 ) ->
      ( forall x, x < size pts -> forall d,
        corr_term P
          (rename (addn (nth d pts x).1.2) \o mu)
          (nth d pts x).2 (nth d pts' x).2 ) ->
      corr_term P mu (Case t pts) (Case t' pts').

Hint Constructors corr_term.

Definition corr_heap_segment (P P' : nat -> Prop) H mu :=
  forall l, P l ->
  exists t, nth None H l = Some t /\
  exists ts' t', mu l = Let ts' t' /\
  corr_term P' mu t (subst (scat (map (Let ts') ts') Var) t').
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

Lemma corr_term_impl P mu t t' :
  corr_term P mu t t' ->
  forall (P' : nat -> Prop) mu',
  ( forall l, P l -> P' l ) ->
  ( forall l, P l -> mu l = mu' l ) ->
  corr_term P' mu' t t'.
Proof.
  induction 1 => ? ? HP HPmu; constructor; eauto.
  - by rewrite -H0 (HPmu _ H).
  - ( apply: IHcorr_term; eauto ) => l.
    by move => /HPmu /= ->.
  - move => ? ? ?.
    ( apply: H1; eauto ) => l.
    by move => /HPmu /= ->.
  - ( apply: IHcorr_term; eauto ) => l.
    by move => /HPmu /= ->.
  - move => ? ? ?.
    ( apply: H3; eauto ) => l.
    by move => /HPmu /= ->.
Qed.

Lemma corr_term_rename P mu t t' :
  corr_term P mu t t' ->
  forall mu' r,
  (forall l, mu' l = rename r (mu l)) ->
  corr_term P mu' (rename r t) (rename r t').
Proof.
  induction 1 => ? ? Hmu /=; constructor; rewrite ?size_map; eauto.
  - by rewrite -H0.
  - apply: IHcorr_term => ?.
    rewrite /funcomp Hmu !rename_rename_comp.
    exact: eq_rename.
  - move => ? ? d.
    rewrite !(nth_map d) -?H => //.
    apply: H1 => // ?.
    rewrite /funcomp Hmu !rename_rename_comp.
    apply: eq_rename => ? /=.
    by rewrite upnren_unfold ltnNge leq_addr addKn.
  - rewrite -H.
    apply: IHcorr_term => ?.
    rewrite /funcomp Hmu !rename_rename_comp.
    apply: eq_rename => ? /=.
    by rewrite upnren_unfold ltnNge leq_addr addKn.
  - move => ? ? d.
    rewrite !(nth_map d) -?H => //.
    apply: H1 => // ?.
  - move => x d.
    case (leqP (size pts) x) => ?.
    + rewrite !nth_default ?size_map; congruence.
    + rewrite !(nth_map d) => /=; congruence.
  - move => ? ? d.
    rewrite !(nth_map d) -?H0 ?H1 => //.
    apply: H3 => // ?.
    rewrite /funcomp Hmu !rename_rename_comp.
    apply: eq_rename => ? /=.
    by rewrite H1 upnren_unfold ltnNge leq_addr addKn.
Qed.

Lemma corr_term_subst P mu t t' :
  corr_term P mu t t' ->
  forall mu' s s',
  (forall x, corr_term P mu' (s x) (s' x)) ->
  (forall l, mu' l = subst s' (mu l)) ->
  corr_term P mu' (subst s t) (subst s' t').
Proof.
  induction 1 => ? ? ? Hs Hmu /=; eauto.
  - apply: corr_term_loc; eauto.
    by rewrite Hmu H0.
  - constructor.
    apply: IHcorr_term => [ [ | ? ] //= | ? ].
    + apply: corr_term_rename; eauto.
    + rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
      exact: eq_subst.
  - constructor; rewrite !size_map -?H; eauto.
    + move => ? ? d.
      rewrite !(nth_map d) -?H => //.
      apply: H1 => // x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        apply: corr_term_rename; eauto.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
    + apply IHcorr_term => x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        apply: corr_term_rename; eauto.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
  - constructor; rewrite ?size_map -?H; eauto.
    move => ? ? d.
    rewrite !(nth_map d) -?H; eauto.
  - constructor; rewrite ?size_map -?H0; eauto.
    + move => x d.
      case (leqP (size pts) x) => ?.
      * rewrite !nth_default ?size_map; congruence.
      * rewrite !(nth_map d) => /=; congruence.
    + move => i ? d.
      rewrite !(nth_map d) -?H0 ?H1 => //.
      apply: H3 => // x.
      * rewrite !upn_unfold.
        case (leqP (nth d pts' i).1.2 x) => ? //.
        apply: corr_term_rename; eauto.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite H1 /funcomp upn_unfold ltnNge leq_addr addKn.
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

Theorem eval_name_sound H1 H1' t1 v1 :
  Heaps.eval_name H1 t1 H1' v1 ->
  forall P mu t2,
  corr_heap P H1 mu ->
  corr_term P mu t1 t2 ->
  exists v2,
  eval_name t2 v2 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ).
Proof.
  induction 1; inversion 2; subst.
  - move: (H0) (H2 _ H5) => -> [ ? [ ] ].
    inversion 1. subst => [ [ ? [ ? [ -> ] ] ]
      /(IHeval_name _ _ _ H2) [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H2 H7) =>
      [ ? [ ? [ P' [ mu' [ Hheap [ ] ] ] ] ] ].
    inversion 1. subst => [ [ HP' ? ] ].
    have Hterm' : corr_term P' mu'
      (subst (scons t2 Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_impl; eauto.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    move: (IHeval_name2 _ _ _ Hheap Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? HPmu'' ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    rewrite -HPmu'' => /=; eauto.
  - repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ H9 _
            (rename (addn (size ts)) \o
              (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)))); eauto ) => l.
        by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H5.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H5; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H5.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H5 ?addKn ?leq_addr. }
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
          by rewrite -H5.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ (H7 _ _ _) _
              (rename (addn (size ts)) \o
                (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))) _ _); eauto ) => l.
            by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H5.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H5 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H5. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H5 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? HPmu' ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    rewrite -HPmu'; eauto.
    erewrite corr_heap_segment_bound; eauto.
  - repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H4 H8) => [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ].
    inversion 1. subst => [ [ ? HPmu ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H10). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H11 -H12 H1.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts' j = (c, size ts', t1) -> False => [ j Hlt' d | ].
    { move: (H2 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H11 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' mu'
      (subst (scat ts Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x | ? ].
      - move: H1 (H13 _ Hlt (0, 0, Var 0)) => -> /corr_term_impl.
        by apply => [ | /= ? /HPmu -> ].
      - rewrite !nth_scat H12.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H12; eauto.
        + eauto using corr_term_impl.
      - rewrite subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H12 ?addKn ?leq_addr. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm'') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? HPmu' ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    erewrite HPmu; eauto.
Qed.

Theorem diverge_name_sound :
  forall H1 t1,
  Heaps.diverge_name H1 t1 ->
  forall P mu t2,
  corr_heap P H1 mu ->
  corr_term P mu t1 t2 ->
  diverge_name t2.
Proof.
  cofix diverge_name_sound.
  inversion 1; subst; inversion 2; subst.
  - move: (H2) (H0 _ H6) => -> [ ? [ ] ].
    inversion 1. subst => [ [ ? [ ? [ -> ? ] ] ] ].
    apply: diverge_name_let. eauto.
  - apply: diverge_name_appL. eauto.
  - move: (eval_name_sound _ _ _ _ H2 _ _ _ H0 H8) =>
      [ ? [ ? [ P' [ mu' [ Hheap [ ] ] ] ] ] ].
    inversion 1. subst => [ [ ? HPmu ] ].
    have Hterm' : corr_term P' mu'
      (subst (scons t3 Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_impl; eauto.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    apply: diverge_name_appabs; eauto.
  - have Hterm' : corr_term
      (fun l => P l \/ size H1 <= l /\ l - size H1 < size ts)
      (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts') ts') (l - size H1))
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ H10 _
            (rename (addn (size ts)) \o
              (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts') ts') (l - size H1)))); eauto ) => l.
        by move => /(corr_heap_segment_bound _ _ _ _ H0) /= ->.
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
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H6 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H1 <= l /\ l - size H1 < size ts)
      (H1 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts') ts') (l - size H1)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ H0 _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ H0) ->.
        + by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H6.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ (H8 _ _ _) _
              (rename (addn (size ts)) \o
                (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts') ts') (l - size H1))) _ _); eauto ) => l.
            by move => /(corr_heap_segment_bound _ _ _ _ H0) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H6.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H6 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H6. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H6 ?leq_addr ?addKn. } }
    apply: diverge_name_let. eauto.
  - apply: diverge_name_case. eauto.
  - move: (eval_name_sound _ _ _ _ H2 _ _ _ H0 H9) => [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ].
    inversion 1. subst => [ [ ? HPmu ] ].
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H3 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H11). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i)) -H12 -H13 H3.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts' j = (c, size ts', t1) -> False => [ j Hlt' d | ].
    { move: (H4 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) H12 H13 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' mu'
      (subst (scat ts Var) t0)
      (subst (scat ts' Var) (nth (0, 0, Var 0) pts' i).2).
    { apply: corr_term_subst => [ | x | ? ].
      - move: H3 (H14 _ Hlt (0, 0, Var 0)) => -> /corr_term_impl.
        by apply => [ | /= ? /HPmu -> ].
      - rewrite !nth_scat H13.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H13; eauto.
        + eauto using corr_term_impl.
      - rewrite subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H13 ?addKn ?leq_addr. }
    apply: diverge_name_casematch; eauto.
Qed.
    
Theorem eval_name_complete t2 v2 :
  eval_name t2 v2 ->
  forall P mu H1 t1,
  corr_term P mu t1 t2 ->
  corr_heap P H1 mu ->
  exists H1' v1,
  Heaps.eval_name H1 t1 H1' v1 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ).
Proof.
  induction 1; inversion 1; subst => [ Hheap ].
  - by move: H4 (Hheap _ H3) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (IHeval_name1 _ _ _ _ H7 Hheap) =>
      [ H1' [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    inversion 1; subst => [ [ HP' HPmu' ] ].
    { by move: H4 (Hheap' _ H3) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ]. }
    have Hterm' : corr_term P' mu'
      (subst (scons t5 Var) t)
      (subst (scons t2 Var) t0).
    { apply: corr_term_subst; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_impl; eauto.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    move: (IHeval_name2 _ _ _ _ Hterm' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    rewrite HPmu'; eauto.
  - by move: H2 (Hheap _ H0) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - repeat (eexists; eauto).
  - move: (H3) (Hheap _ H2) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    inversion 1. subst => [ Hterm ].
    move: (IHeval_name _ _ _ _ Hterm Hheap) =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l => P l \/ size H1 <= l /\ l - size H1 < size ts0)
      (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts) ts) (l - size H1))
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts) ts) Var) t).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ H8 _
            (rename (addn (size ts0)) \o
              (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts) ts) (l - size H1)))); eauto ) => l.
        by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H4.
        case (leqP (size ts0) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H4; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H4.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H4 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H1 <= l /\ l - size H1 < size ts0)
      (H1 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts) ts) (l - size H1)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
        + by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H4.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ (H7 _ _ _) _
              (rename (addn (size ts0)) \o
                (fun l => if l < size H1 then mu l else nth (mu l) (map (Let ts) ts) (l - size H1))) _ _); eauto ) => l.
            by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H4.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H4 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H4. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H4 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ _ Hterm' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? HPmu' ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    rewrite -HPmu'; eauto.
    erewrite corr_heap_segment_bound; eauto.
  - by move: H2 (Hheap _ H0) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - repeat (eexists; eauto).
  - by move: H6 (Hheap _ H5) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (IHeval_name1 _ _ _ _ H7 Hheap) => [ ? [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    inversion 1; subst => [ [ ? HPmu ] ].
    { by move: H6 (Hheap' _ H5) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ]. }
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H0 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H9). }
    have ? : forall d, nth d pts0 i = (c, size ts0, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H11 H13 H0.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts0 j = (c, size ts0, t1) -> False => [ j Hlt' d | ].
    { move: (H1 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H11 H13 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' mu'
      (subst (scat ts0 Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x | ? ].
      - move: H8 Hlt => <- /H12 /(_ (0, 0, Var 0)) /corr_term_impl.
        rewrite H0. by apply => [ | /= ? /HPmu -> ].
      - rewrite !nth_scat H13.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H13; eauto.
        + eauto using corr_term_impl.
      - rewrite subst_rename_comp H11 H0 (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H13 ?addKn ?leq_addr. }
    move: (IHeval_name2 _ _ _ _ Hterm'' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    move => ? ?.
    erewrite HPmu; eauto.
Qed.

Theorem diverge_name_complete :
  forall t2,
  diverge_name t2 ->
  forall P mu H1 t1,
  corr_term P mu t1 t2 ->
  corr_heap P H1 mu ->
  Heaps.diverge_name H1 t1.
Proof.
  cofix diverge_name_complete.
  inversion 1; inversion 1; subst => [ Hheap0 ].
  - by move: H5 (Hheap0 _ H4) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - apply: Heaps.diverge_name_appL; eauto.
  - by move: H6 (Hheap0 _ H5) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (eval_name_complete _ _ H0 _ _ _ _ H9 Hheap0) =>
      [ H1' [ ? [ ? [ P' [ mu' [ Hheap [ ] ] ] ] ] ] ].
    inversion 1; subst => [ [ ? HPmu ] ].
    { by move: H5 (Hheap _ H2) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ]. }
    have Hterm' : corr_term P' mu'
      (subst (scons t6 Var) t)
      (subst (scons t3 Var) t0).
    { apply: corr_term_subst; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_impl; eauto.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    apply: Heaps.diverge_name_appabs; eauto.
  - move: H5 (Hheap0 _ H4) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    inversion 1. subst => [ ? ].
    apply: Heaps.diverge_name_loc; eauto.
  - have Hterm' : corr_term
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts) ts) Var) t).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ H10 _
            (rename (addn (size ts0)) \o
              (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)))); eauto ) => l.
        by move => /(corr_heap_segment_bound _ _ _ _ Hheap0) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H6.
        case (leqP (size ts0) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H6; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H6.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H6 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cat.
        refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap0 _ _) _ _ _ _ _ _); eauto.
        by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap0) ->.
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)). by rewrite -H6.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ (H9 _ _ _) _
              (rename (addn (size ts0)) \o
                (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))) _ _); eauto ) => l.
            by move => /(corr_heap_segment_bound _ _ _ _ Hheap0) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H6.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H6 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H6. }
          { move => ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H6 ?leq_addr ?addKn. } }
    apply: Heaps.diverge_name_let. eauto.
  - by move: H5 (Hheap0 _ H4) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - apply: Heaps.diverge_name_case. eauto.
  - by move: H8 (Hheap0 _ H7) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (eval_name_complete _ _ H0 _ _ _ _ H9 Hheap0) =>
      [ ? [ ? [ ? [ P' [ mu' [ Hheap' [ ] ] ] ] ] ] ].
    inversion 1; subst => [ [ ? HPmu ] ].
    { by move: H7 (Hheap' _ H4) => -> [ ? [ ? [ ? [ ? [ ] ] ] ] ]. }
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1. subst.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H8). }
    have ? : forall d, nth d pts0 i = (c, size ts0, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i)) H13 H1 H12.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j, j < i -> forall d t1, nth d pts0 j = (c, size ts0, t1) -> False => [ j Hlt' d | ].
    { move: (H2 _ Hlt' d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) H13 H12 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm'' : corr_term P' mu'
      (subst (scat ts0 Var) (nth (0, 0, Var 0) pts0 i).2)
      (subst (scat ts Var) t0).
    { apply: corr_term_subst => [ | x | ? ].
      - move: H10 Hlt => <- /H14 /(_ (0, 0, Var 0)) /corr_term_impl.
        rewrite H1. by apply => [ | /= ? /HPmu -> ].
      - rewrite !nth_scat H12.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default -?H12; eauto.
        + eauto using corr_term_impl.
      - rewrite subst_rename_comp H13 H1 (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default -H12 ?addKn ?leq_addr. }
    apply: Heaps.diverge_name_casematch; eauto.
Qed.
