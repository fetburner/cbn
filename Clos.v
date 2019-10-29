From mathcomp Require Import all_ssreflect.

Require Import Util LambdaLet.
Require Heaps.
Require Import Relations.

Inductive env :=
  | Empty
  | Cat of env & seq term & env
  | Mut of seq term & env.

Definition clos := (env * term)%type.

Fixpoint eget E n : option clos :=
  match E with
  | Empty => None
  | Cat E ts E' => nth (eget E' (n - size ts)) (map (Some \o pair E) ts) n
  | Mut ts E => nth (eget E (n - size ts)) (map (@Some _ \o pair (Mut ts E)) ts) n
  end.

Inductive eval_name : env -> term -> clos -> Prop :=
  | eval_name_var E E' t x v :
      eget E x = Some (E', t) ->
      eval_name E' t v ->
      eval_name E (Var x) v
  | eval_name_app E E' t0 t1 t2 v :
      eval_name E t1 (E', Abs t0) ->
      eval_name (Cat E [:: t2] E') t0 v ->
      eval_name E (App t1 t2) v
  | eval_name_abs E t0 :
      eval_name E (Abs t0) (E, Abs t0)
  | eval_name_let E ts t v :
      eval_name (Mut ts E) t v ->
      eval_name E (Let ts t) v
  | eval_name_ctor E c ts :
      eval_name E (Cons c ts) (E, Cons c ts)
  | eval_name_case E E' c i t t0 ts pts v :
      eval_name E t (E', Cons c ts) ->
      (forall d, nth d pts i = (c, size ts, t0)) ->
      (forall j d t0, nth d pts j = (c, size ts, t0) -> i <= j) ->
      eval_name (Cat E' ts E) t0 v ->
      eval_name E (Case t pts) v.

CoInductive diverge_name : env -> term -> Prop :=
  | diverge_name_var E E' t x :
      eget E x = Some (E', t) ->
      diverge_name E' t ->
      diverge_name E (Var x)
  | diverge_name_appL E t1 t2 :
      diverge_name E t1 ->
      diverge_name E (App t1 t2)
  | diverge_name_beta E E' t0 t1 t2 :
      eval_name E t1 (E', Abs t0) ->
      diverge_name (Cat E [:: t2] E') t0 ->
      diverge_name E (App t1 t2)
  | diverge_name_let E ts t :
      diverge_name (Mut ts E) t ->
      diverge_name E (Let ts t)
  | diverge_name_case E t pts :
      diverge_name E t ->
      diverge_name E (Case t pts)
  | diverge_name_casematch E E' c i t t0 ts pts :
      eval_name E t (E', Cons c ts) ->
      (forall d, nth d pts i = (c, size ts, t0)) ->
      (forall j d t0, nth d pts j = (c, size ts, t0) -> i <= j) ->
      diverge_name (Cat E' ts E) t0 ->
      diverge_name E (Case t pts).

Inductive corr_term (R : nat -> nat -> Prop) H : nat -> term -> term -> Prop :=
  | corr_term_loc n x l :
      n <= x ->
      R l (x - n) ->
      corr_term R H n (Loc l) (Var x)
  | corr_term_var n x :
      x < n ->
      corr_term R H n (Var x) (Var x)
  | corr_term_abs n t t' :
      corr_term R H n.+1 t t' ->
      corr_term R H n (Abs t) (Abs t')
  | corr_term_app n t1 t1' t2 t2' :
      corr_term R H n t1 t1' ->
      corr_term R H n t2 t2' ->
      corr_term R H n (App t1 t2) (App t1' t2')
  | corr_term_let n t t' ts ts' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term R H (size ts + n)
          (nth d ts x) (nth d ts' x) ) ->
      corr_term R H (size ts + n) t t' ->
      corr_term R H n (Let ts t) (Let ts' t')
  | corr_term_vcons n c ls ts ts' :
      size ls = size ts' ->
      ( forall x, x < size ls -> forall d,
        nth None H (nth d ls x) = Some (ts x) ) ->
      ( forall x, x < size ls -> forall d,
        corr_term R H n (rename (addn n) (ts x)) (nth d ts' x) ) ->
      corr_term R H n (VCons c ls) (Cons c ts')
  | corr_term_cons n c ts ts' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term R H n (nth d ts x) (nth d ts' x) ) ->
      corr_term R H n (Cons c ts) (Cons c ts')
  | corr_term_case n t t' pts pts' :
      corr_term R H n t t' ->
      size pts = size pts' ->
      ( forall x d, (nth d pts x).1 = (nth d pts' x).1 ) ->
      ( forall x, x < size pts -> forall d,
        corr_term R H ((nth d pts x).1.2 + n)
          (nth d pts x).2 (nth d pts' x).2 ) ->
      corr_term R H n (Case t pts) (Case t' pts').

CoInductive corr_heap H : (nat -> nat -> Prop) -> env -> Prop :=
  | corr_heap_fold (R : nat -> nat -> Prop) E :
      ( forall l x, R l x ->
        exists t1, nth None H l = Some t1 /\
        exists E' t2, eget E x = Some (E', t2) /\
        exists R', corr_heap H R' E' /\ corr_term R' H 0 t1 t2 ) ->
      corr_heap H R E.

Lemma corr_heap_unfold R H E :
  corr_heap H R E ->
  forall l x, R l x ->
  exists t1, nth None H l = Some t1 /\
  exists E' t2, eget E x = Some (E', t2) /\
  exists R', corr_heap H R' E' /\ corr_term R' H 0 t1 t2.
Proof. by inversion 1. Qed.

Hint Constructors eval_name diverge_name corr_term corr_heap.

Lemma corr_term_impl :
  forall R H n t t',
  corr_term R H n t t' ->
  forall (R' : _ -> _ -> Prop) H',
  (forall l t, R l t -> R' l t) ->
  (forall l t, nth None H l = Some t -> nth None H' l = Some t) ->
  corr_term R' H' n t t'.
Proof. induction 1; eauto. Qed.

Lemma corr_term_subst (R R' : _ -> _ -> Prop) f H H' :
  ( forall l t, nth None H l = Some t -> nth None H' l = Some (f t) ) ->
  forall n t t',
  corr_term R H n t t' ->
  forall s m,
  m <= n ->
  ( forall x, x < m -> s x = Var x ) ->
  ( forall x, m <= x -> x < n ->
    exists l, s x = Loc l /\ R' l (x - m) ) ->
  ( forall l x, n <= x -> R l (x - n) -> R' l (x - m) ) ->
  ( forall t, rename (addn m) (f t) = subst s (rename (addn n) t) ) ->
  corr_term R' H' m (subst s t) t'.
Proof.
  have Hvar_impl : forall n s m,
    (forall x, x < m -> s x = Var x) ->
    (forall x, x < n + m -> upn s n x = Var x).
  { move => n ? ? Hs x ?.
    rewrite (eq_upn _ Var) => [ | ? ].
    - exact: upn_Var.
    - apply: Hs.
      by rewrite -(ltn_add2l n) subnKC. }
  have Hloc_impl : forall ts s n m,
    ( forall x, m <= x -> x < n ->
      exists l, s x = Loc l /\ R' l (x - m) ) ->
    ( forall x, ts + m <= x -> x < ts + n ->
      exists l, upn s ts x = Loc l /\ R' l (x - (ts + m)) ).
  { move => ts ? n m Hloc x ? ?.
    have Hleq := leq_trans (leq_addr m _).
    rewrite subnDA upn_unfold ltnNge Hleq => //=.
    move: (Hloc (x - ts)) => [ | | ? [ -> ? /= ] ];
    [ rewrite -(leq_add2l ts) subnKC
    | rewrite -(ltn_add2l ts) subnKC | ]; eauto. }
  have HR_impl: forall ts (R R' : nat -> _) m n,
    (forall l x, n <= x -> R l (x - n) -> R' l (x - m)) ->
    (forall l x, ts + n <= x -> R l (x - (ts + n)) -> R' l (x - (ts + m))).
  { move => ts ? ? ? n HR ? ? ?.
    rewrite !subnDA. apply: HR.
    rewrite -(leq_add2l ts) subnKC => //.
    exact: (leq_trans (leq_addr n _)). }
  have Hnth_impl : forall ts s n m,
    ( forall t, rename (addn m) (f t) = subst s (rename (addn n) t) ) ->
    ( forall t, rename (addn (ts + m)) (f t) = subst (upn s ts) (rename (addn (ts + n)) t) ).
  { move => ts ? n m Hnth ?.
    rewrite (eq_rename _ (addn (ts + m)) (addn ts \o addn m)) => [ | ? /= ].
    - rewrite -rename_rename_comp Hnth !rename_subst_comp !subst_rename_comp.
      apply: eq_subst => ?.
      by rewrite /funcomp upn_unfold ltnNge -(addnA ts n) leq_addr addKn.
    - by rewrite addnA. }
  induction 2 => ? m Hleq Hvar Hloc HR Hnth /=; eauto using leq_trans.
  - case (leqP m x) => Hge.
    + move: (Hloc _ Hge H1) => [ ? [ -> ? ] ]. eauto.
    + rewrite Hvar; eauto.
  - constructor.
    apply: IHcorr_term.
    + exact: Hleq.
    + exact: (Hvar_impl 1).
    + exact: (Hloc_impl 1).
    + exact: (HR_impl 1).
    + exact: (Hnth_impl 1).
  - ( constructor; rewrite size_map ) => // [ x ? d | ];
    [ rewrite (nth_map d) => //; apply: H3 => // | apply: IHcorr_term ];
    solve [ by rewrite leq_add2l | exact: Hvar_impl | exact: Hloc_impl | exact: HR_impl | exact: Hnth_impl ].
  - apply: (corr_term_vcons _ _ _ _ _ (f \o ts)) => // ? Hlt d.
    + apply: H0. exact: H2.
    + rewrite Hnth. exact: H4.
  - constructor; rewrite ?size_map => // ? ? d.
    rewrite (nth_map d) => //.
    apply: H3; eauto.
  - ( constructor; rewrite ?size_map ) => [ | | x d | ? ? d ]; eauto.
    + case (leqP (size pts) x) => ?.
      * by rewrite !nth_default ?size_map -?H2.
      * by rewrite -H3 (nth_map d).
    + rewrite !(nth_map d) => //.
      apply: H5 => //=.
      * by rewrite leq_add2l.
      * exact: Hvar_impl.
      * exact: Hloc_impl.
      * exact: HR_impl.
      * exact: Hnth_impl.
Qed.

Lemma corr_heap_impl :
  forall H R E,
  corr_heap H R E ->
  forall (R' : nat -> nat -> Prop) H',
  (forall l x, R' l x -> R l x) ->
  (forall l t, nth None H l = Some t -> nth None H' l = Some t) ->
  corr_heap H' R' E.
Proof.
  cofix corr_heap_impl.
  inversion 1.
  subst => ? ? HR Hext.
  constructor => ? ? /HR /H1 [ ? [ /Hext -> [ ? [ ? [ -> [ ? [ ? ? ] ] ] ] ] ] ].
  repeat (eexists; eauto).
  apply: corr_term_impl; eauto.
Qed.

Corollary corr_heap_catL H Hd R E :
  corr_heap H R E ->
  corr_heap (H ++ Hd) R E.
Proof.
  move => /corr_heap_impl.
  apply => // l.
  by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_rconsL H R E o :
  corr_heap H R E ->
  corr_heap (rcons H o) R E.
Proof. by rewrite -cats1 => /corr_heap_catL. Qed.
  
Lemma corr_heap_union H R R' E :
  corr_heap H R E ->
  corr_heap H R' E ->
  corr_heap H (fun l t => R l t \/ R' l t) E.
Proof.
  inversion 1. subst.
  inversion 1. subst.
  constructor => ? ? [ /H1 | /H3 ]; eauto.
Qed.

Lemma corr_heap_catR H R E E' ts :
  corr_heap H R E ->
  corr_heap H (fun l x => size ts <= x /\ R l (x - size ts)) (Cat E' ts E).
Proof.
  inversion 1. subst.
  constructor => ? ? [ ? /H1 [ ? [ -> /= [ ? [ ? [ -> [ ? [ ? ? ] ] ] ] ] ] ] ].
  rewrite nth_default ?size_map => //.
  repeat (eexists; eauto).
Qed.

Lemma corr_heap_mutR H R E ts :
  corr_heap H R E ->
  corr_heap H (fun l x => size ts <= x /\ R l (x - size ts)) (Mut ts E).
Proof.
  inversion 1. subst.
  constructor => ? ? [ ? /H1 [ ? [ -> /= [ ? [ ? [ -> [ ? [ ? ? ] ] ] ] ] ] ] ].
  rewrite nth_default ?size_map => //.
  repeat (eexists; eauto).
Qed.

Theorem eval_name_sound H H' t1 v1 :
  Heaps.eval_name H t1 H' v1 ->
  forall R E t2,
  corr_heap H R E ->
  corr_term R H 0 t1 t2 ->
  exists R' E' v2,
  eval_name E t2 (E', v2) /\
  corr_heap H' R' E' /\
  corr_term R' H' 0 v1 v2.
Proof.
  induction 1; inversion 1; inversion 1; subst.
  - move: subn0 H10 => -> /H3 [ ? [ ] ].
    rewrite H0 => [ ]. inversion 1.
    subst => [ [ ? [ ? [ ? [ ? [ Hheap Hterm ] ] ] ] ] ].
    move: (IHeval_name _ _ _ Hheap Hterm) => [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H0 H8) => [ R' [ E' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm : corr_term
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0) (rcons H' (Some t2)) 0
      (subst (scons (Loc (size H')) Var) t0) t'.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H5 _ _ _ _ _ _ _) =>
      [ l | | | [ | ? ] ? ? /= | ? [ | ? ] /= | ? ] //; eauto.
      - by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ].
      - by rewrite subst_rename_comp ?(eq_rename _ _ id) ?(eq_subst _ _ Var) ?rename_id ?subst_id. }
    have Hheap : corr_heap (rcons H' (Some t2))
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0)
      (Cat E [:: t2'] E').
    { apply: corr_heap_union.
      - apply: corr_heap_rconsL.
        by refine (corr_heap_catR _ _ _ _ [:: _] _).
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 (eexists; eauto).
        + apply: corr_heap_rconsL.
          refine (corr_heap_impl _ _ _ _ _ _ _ (Heaps.eval_name_heap _ _ _ _ _)); eauto.
        + (apply: corr_term_impl; eauto 2) =>
            l ? /(Heaps.eval_name_heap _ _ _ _ H0_).
          by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ Hheap Hterm) =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm : corr_term (fun l x =>
      size ts <= x /\ R l (x - size ts) \/
      x < size ts /\ l = size H + x)
      (H ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts) 0
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t) t'.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H12 _ _ _ _ _ _ _) =>
      [ l | | // | ? ? | ? ? | ? ]; eauto.
      - by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
      - rewrite addn0 subn0 => ?.
        rewrite nth_scat nth_mkseq => /=; eauto.
      - rewrite addn0 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    have Hheap : corr_heap
      (H ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l x =>
        size ts <= x /\ R l (x - size ts) \/
        x < size ts /\ l = size H + x)
      (Mut ts' E).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mutR.
          apply: corr_heap_catL. eauto.
        + move: H8 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        refine (corr_term_subst _ _ id _ _ _ _ _ _ (H10 _ _ _) _ _ _ _ _ _ _) =>
        [ l | | | // | ? ? | ? ? | ? ]; eauto.
        + by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
        + rewrite addn0 subn0 => ?.
          rewrite nth_scat nth_mkseq => /=; eauto.
        + rewrite addn0 subn0 => ?. eauto.
        + rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
          by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    move: (IHeval_name _ _ _ Hheap Hterm) =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - do 4 (eexists; eauto). split.
    + refine (corr_heap_impl _ _ _ H0 _ _ (fun _ _ H => H) _) => l.
      by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
    + econstructor; rewrite size_mkseq => // x ? d.
      * rewrite nth_cat nth_mkseq => //.
        by rewrite ltnNge leq_addr addKn (nth_map (Var 0)).
      * rewrite (eq_rename _ _ id) ?rename_id ?(set_nth_default d) => //.
        refine (corr_term_impl _ _ _ _ _ (H10 _ _ _) _ _ (fun _ _ H => H) _) => // l.
        by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
  - move: (IHeval_name1 _ _ _ H2 H9) => [ R' [ E' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H0 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H8). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i))  -H12 H0 H7 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts' j = (c, size ts', t1) -> i <= j => [ j d | ].
    { move: (H1 j d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) -!H12 H7 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm' : corr_term
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x) H' 0
      (subst (scat (map Loc ls) Var) t0) (nth (0, 0, Var 0) pts' i).2.
    { refine (corr_term_subst _ _ id _ _ (Heaps.eval_name_heap _ _ _ _ H0_) _ _ _ _ _ _ (leq0n _) _ _ _ _) =>
      [ | // | ? ? ? | ? ? ? | ? ].
      - move: addn0 H0 (H14 _ Hlt (0, 0, Var 0)) => -> -> /=. apply.
      - rewrite subn0 nth_scat (nth_map 0); eauto.
      - rewrite subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?addKn ?leq_addr. }
    have Hheap' : corr_heap H'
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x)
      (Cat E' ts' E).
    { apply: corr_heap_union.
      + rewrite H7.
        apply: corr_heap_catR.
        refine (corr_heap_impl _ _ _ _ _ _ (fun _ _ H => H)
          (Heaps.eval_name_heap _ _ _ _ _)); eauto.
      + constructor => ? ? [ Hlt' -> ] /=.
        move: (H15 _ Hlt').
        rewrite (eq_rename _ _ id) ?rename_id ?H11 ?(nth_map (Var 0)) -?H7 => //=.
        repeat (eexists; eauto). }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_name_sound :
  forall H t1,
  Heaps.diverge_name H t1 ->
  forall R E t2,
  corr_heap H R E ->
  corr_term R H 0 t1 t2 ->
  diverge_name E t2.
Proof.
  cofix diverge_name_sound.
  inversion 1; inversion 1; inversion 1; subst.
  - move: subn0 H14 => -> /H7 [ ? [ ] ].
    rewrite H2. inversion 1. subst => [ [ ? [ ? [ ? [ ? [ ? ?] ] ] ] ] ].
    apply: diverge_name_var; eauto.
  - apply: diverge_name_appL. eauto.
  - move: (eval_name_sound _ _ _ _ H2 _ _ _ H6 H14) => [ R' [ E' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have ? : corr_term
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0) (rcons H' (Some t3)) 0
      (subst (scons (Loc (size H')) Var) t0) t'.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H5 _ _ _ _ _ _ _) =>
      [ l | | | [ | ? ] ? ? /= | ? [ | ? ] /= | ? ] //; eauto.
      - by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ].
      - by rewrite subst_rename_comp ?(eq_rename _ _ id) ?(eq_subst _ _ Var) ?rename_id ?subst_id. }
    have Hheap : corr_heap (rcons H' (Some t3))
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0)
      (Cat E [:: t2'] E').
    { apply: corr_heap_union.
      - apply: corr_heap_rconsL.
        by refine (corr_heap_catR _ _ _ _ [:: _] _).
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 (eexists; eauto).
        + apply: corr_heap_rconsL.
          refine (corr_heap_impl _ _ _ _ _ _ _ (Heaps.eval_name_heap _ _ _ _ _)); eauto.
        + (apply: corr_term_impl; eauto 2) =>
            l ? /(Heaps.eval_name_heap _ _ _ _ H2).
          by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    apply: diverge_name_beta; eauto.
  - have Hterm : corr_term (fun l x =>
      size ts <= x /\ R l (x - size ts) \/
      x < size ts /\ l = size H + x)
      (H ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts) 0
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t) t'.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H16 _ _ _ _ _ _ _) =>
      [ l | | // | ? ? | ? ? | ? ]; eauto.
      - by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
      - rewrite addn0 subn0 => ?.
        rewrite nth_scat nth_mkseq => /=; eauto.
      - rewrite addn0 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    have Hheap : corr_heap
      (H ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l x =>
        size ts <= x /\ R l (x - size ts) \/
        x < size ts /\ l = size H + x)
      (Mut ts' E).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mutR.
          apply: corr_heap_catL. eauto.
        + move: H12 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        refine (corr_term_subst _ _ id _ _ _ _ _ _ (H14 _ _ _) _ _ _ _ _ _ _) =>
        [ l | | | // | ? ? | ? ? | ? ]; eauto.
        + by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
        + rewrite addn0 subn0 => ?.
          rewrite nth_scat nth_mkseq => /=; eauto.
        + rewrite addn0 subn0 => ?. eauto.
        + rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
          by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    apply: diverge_name_let. eauto.
  - apply: diverge_name_case. eauto.
  - move: (eval_name_sound _ _ _ _ H2 _ _ _ H8 H15) =>
      [ R' [ E' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H3 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H10). }
    have ? : forall d, nth d pts' i = (c, size ts', (nth (0, 0, Var 0) pts' i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts' i))  -H18 H3 H7 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts' j = (c, size ts', t1) -> i <= j => [ j d | ].
    { move: (H4 j d).
      rewrite
        (surjective_pairing (nth d pts j))
        (surjective_pairing (nth d pts' j)) -!H18 H7 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm' : corr_term
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x) H' 0
      (subst (scat (map Loc ls) Var) t0) (nth (0, 0, Var 0) pts' i).2.
    { refine (corr_term_subst _ _ id _ _ (Heaps.eval_name_heap _ _ _ _ H2) _ _ _ _ _ _ (leq0n _) _ _ _ _) =>
      [ | // | ? ? ? | ? ? ? | ? ].
      - move: addn0 H3 (H20 _ Hlt (0, 0, Var 0)) => -> -> /=. apply.
      - rewrite subn0 nth_scat (nth_map 0); eauto.
      - rewrite subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?addKn ?leq_addr. }
    have Hheap' : corr_heap H'
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x)
      (Cat E' ts' E).
    { apply: corr_heap_union.
      + rewrite H7.
        apply: corr_heap_catR.
        refine (corr_heap_impl _ _ _ _ _ _ (fun _ _ H => H)
          (Heaps.eval_name_heap _ _ _ _ _)); eauto.
      + constructor => ? ? [ Hlt' -> ] /=.
        move: (H14 _ Hlt').
        rewrite (eq_rename _ _ id) ?rename_id ?H11 ?(nth_map (Var 0)) -?H7 => //=.
        repeat (eexists; eauto). }
    apply: diverge_name_casematch; eauto.
Qed.

Theorem eval_name_complete E t2 c :
  eval_name E t2 c ->
  forall R H t1,
  corr_heap H R E ->
  corr_term R H 0 t1 t2 ->
  exists R' H' v1,
  Heaps.eval_name H t1 H' v1 /\
  corr_heap H' R' c.1 /\
  corr_term R' H' 0 v1 c.2.
Proof.
  induction 1; inversion 1; inversion 1; subst.
  - move: subn0 H11 => -> /H3 [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H. inversion 1. subst => [ [ ? [ Hheap Hterm ] ] ].
    move: (IHeval_name _ _ _ Hheap Hterm) => [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - by [].
  - move: (IHeval_name1 _ _ _ H2 H11) => /= [ R' [ H' [ ? [ Hcbn [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm : corr_term
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0) (rcons H' (Some t5)) 0
      (subst (scons (Loc (size H')) Var) t) t0.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H8 _ _ _ _ _ _ _) =>
      [ l | | | [ | ? ] ? ? /= | ? [ | ? ] /= | ? ] //; eauto.
      - by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ].
      - by rewrite subst_rename_comp ?(eq_rename _ _ id) ?(eq_subst _ _ Var) ?rename_id ?subst_id. }
    have Hheap : corr_heap (rcons H' (Some t5))
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0)
      (Cat E [:: t2] E').
    { apply: corr_heap_union.
      - apply: corr_heap_rconsL.
        by refine (corr_heap_catR _ _ _ _ [:: _] _).
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 (eexists; eauto).
        + apply: corr_heap_rconsL.
          refine (corr_heap_impl _ _ _ _ _ _ _ (Heaps.eval_name_heap _ _ _ _ _)); eauto.
        + (apply: corr_term_impl; eauto 2) =>
            l ? /(Heaps.eval_name_heap _ _ _ _ Hcbn).
          by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ Hheap Hterm) => [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm : corr_term (fun l x =>
      size ts0 <= x /\ R l (x - size ts0) \/
      x < size ts0 /\ l = size H0 + x)
      (H0 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0) 0
      (subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var) t0) t.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H12 _ _ _ _ _ _ _) =>
      [ l | | // | ? ? | ? ? | ? ]; eauto.
      - by move: nth_cat (leqP (size H0) l) => -> [ /(nth_default _) -> | ].
      - rewrite addn0 subn0 => ?.
        rewrite nth_scat nth_mkseq => /=; eauto.
      - rewrite addn0 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    have Hheap : corr_heap
      (H0 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0)
      (fun l x =>
        size ts0 <= x /\ R l (x - size ts0) \/
        x < size ts0 /\ l = size H0 + x)
      (Mut ts E).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mutR.
          apply: corr_heap_catL. eauto.
        + move: H8 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        refine (corr_term_subst _ _ id _ _ _ _ _ _ (H11 _ _ _) _ _ _ _ _ _ _) =>
        [ l | | | // | ? ? | ? ? | ? ]; eauto.
        + by move: nth_cat (leqP (size H0) l) => -> [ /(nth_default _) -> | ].
        + rewrite addn0 subn0 => ?.
          rewrite nth_scat nth_mkseq => /=; eauto.
        + rewrite addn0 subn0 => ?. eauto.
        + rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
          by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    move: (IHeval_name _ _ _ Hheap Hterm) =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - do 4 (eexists; eauto). split.
    + refine (corr_heap_impl _ _ _ H0 _ _ (fun _ _ H => H) _) => l.
      by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
    + econstructor; rewrite size_mkseq => // x ? d.
      * rewrite nth_cat nth_mkseq => //.
        by rewrite ltnNge leq_addr addKn (nth_map (Var 0)).
      * rewrite (eq_rename _ _ id) ?rename_id ?(set_nth_default d) => //.
        refine (corr_term_impl _ _ _ _ _ (H10 _ _ _) _ _ (fun _ _ H => H) _) => // l.
        by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
  - move: (IHeval_name1 _ _ _ H4 H11) => [ R' [ H' [ ? [ Hcbn [ ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1; inversion 2. subst.
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H0 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H9). }
    have ? : forall d, nth d pts0 i = (c, size ls, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i))  H15 H0 H17 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts0 j = (c, size ls, t1) -> i <= j => [ j d | ].
    { move: (H1 j d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) !H15 H17 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm' : corr_term
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x) H' 0
      (subst (scat (map Loc ls) Var) (nth (0, 0, Var 0) pts0 i).2) t0.
    { refine (corr_term_subst _ _ id _ _ (Heaps.eval_name_heap _ _ _ _ Hcbn) _ _ _ _ _ _ (leq0n _) _ _ _ _) =>
      [ | // | ? ? ? | ? ? ? | ? ].
      - move: H12 Hlt => <- /H16 /(_ (0, 0, Var 0)).
        rewrite addn0 H15 H0 => /=. apply.
      - rewrite H17 subn0 nth_scat (nth_map 0); eauto.
      - rewrite H17 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?H17 ?addKn ?leq_addr. }
    have Hheap' : corr_heap H'
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x)
      (Cat E' ts E).
    { apply: corr_heap_union.
      + rewrite H17.
        apply: corr_heap_catR.
        refine (corr_heap_impl _ _ _ _ _ _ (fun _ _ H => H)
          (Heaps.eval_name_heap _ _ _ _ _)); eauto.
      + constructor => ? ? [ Hlt' -> ] /=.
        move: (H19 _ Hlt').
        rewrite (eq_rename _ _ id) ?rename_id ?H18 ?(nth_map (Var 0)) -?H17 => //=.
        repeat (eexists; eauto). }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_name_complete :
  forall E t2,
  diverge_name E t2 ->
  forall R H t1,
  corr_heap H R E ->
  corr_term R H 0 t1 t2 ->
  Heaps.diverge_name H t1.
Proof.
  cofix diverge_name_complete.
  inversion 1; inversion 1; inversion 1; subst.
  - move: subn0 H14 => -> /H6 [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H0. inversion 1. subst => [ [ ? [ ? ? ] ] ].
    apply: Heaps.diverge_name_loc; eauto.
  - by [].
  - apply: Heaps.diverge_name_appL. eauto.
  - move: (eval_name_complete _ _ _ H0 _ _ _ H5 H14) => [ R' [ H' [ ? [ Hcbn [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm : corr_term
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0) (rcons H' (Some t6)) 0
      (subst (scons (Loc (size H')) Var) t) t0.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H8 _ _ _ _ _ _ _) =>
      [ l | | | [ | ? ] ? ? /= | ? [ | ? ] /= | ? ] //; eauto.
      - by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ].
      - by rewrite subst_rename_comp ?(eq_rename _ _ id) ?(eq_subst _ _ Var) ?rename_id ?subst_id. }
    have Hheap : corr_heap (rcons H' (Some t6))
      (fun l x => 0 < x /\ R' l (x - 1) \/ l = size H' /\ x = 0)
      (Cat E [:: t3] E').
    { apply: corr_heap_union.
      - apply: corr_heap_rconsL.
        by refine (corr_heap_catR _ _ _ _ [:: _] _).
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 (eexists; eauto).
        + apply: corr_heap_rconsL.
          refine (corr_heap_impl _ _ _ _ _ _ _ (Heaps.eval_name_heap _ _ _ _ _)); eauto.
        + (apply: corr_term_impl; eauto 2) =>
            l ? /(Heaps.eval_name_heap _ _ _ _ Hcbn).
          by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    apply: Heaps.diverge_name_beta; eauto.
  - have Hterm : corr_term (fun l x =>
      size ts0 <= x /\ R l (x - size ts0) \/
      x < size ts0 /\ l = size H3 + x)
      (H3 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H3)) (size ts0)) Var)) ts0) 0
      (subst (scat (mkseq (Loc \o addn (size H3)) (size ts0)) Var) t0) t.
    { refine (corr_term_subst _ _ id _ _ _ _ _ _ H15 _ _ _ _ _ _ _) =>
      [ l | | // | ? ? | ? ? | ? ]; eauto.
      - by move: nth_cat (leqP (size H3) l) => -> [ /(nth_default _) -> | ].
      - rewrite addn0 subn0 => ?.
        rewrite nth_scat nth_mkseq => /=; eauto.
      - rewrite addn0 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    have Hheap : corr_heap
      (H3 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H3)) (size ts0)) Var)) ts0)
      (fun l x =>
        size ts0 <= x /\ R l (x - size ts0) \/
        x < size ts0 /\ l = size H3 + x)
      (Mut ts E).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mutR.
          apply: corr_heap_catL. eauto.
        + move: H11 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        refine (corr_term_subst _ _ id _ _ _ _ _ _ (H14 _ _ _) _ _ _ _ _ _ _) =>
        [ l | | | // | ? ? | ? ? | ? ]; eauto.
        + by move: nth_cat (leqP (size H3) l) => -> [ /(nth_default _) -> | ].
        + rewrite addn0 subn0 => ?.
          rewrite nth_scat nth_mkseq => /=; eauto.
        + rewrite addn0 subn0 => ?. eauto.
        + rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
          by rewrite nth_scat nth_default size_mkseq addn0 ?addKn ?leq_addr. }
    apply: Heaps.diverge_name_let; eauto.
  - apply: Heaps.diverge_name_case. eauto.
  - move: (eval_name_complete _ _ _ H0 _ _ _ H7 H14) => [ R' [ H' [ ? [ Hcbn [ ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1; inversion 2. subst.
    have Hlt : i < size pts.
    { move: (leqP (size pts) i) (H1 (c.+1, 0, Var 0)) =>
        [ /(nth_default _) -> | // ].
      inversion 1.
      by move: (PeanoNat.Nat.neq_succ_diag_l _ H9). }
    have ? : forall d, nth d pts0 i = (c, size ls, (nth (0, 0, Var 0) pts0 i).2) => [ d | ].
    { rewrite (surjective_pairing (nth d pts0 i))  H18 H1 H16 => /=.
      do 2 f_equal. apply: set_nth_default. congruence. }
    have ? : forall j d t1, nth d pts0 j = (c, size ls, t1) -> i <= j => [ j d | ].
    { move: (H2 j d).
      rewrite
        (surjective_pairing (nth d pts0 j))
        (surjective_pairing (nth d pts j)) !H18 H16 => Hcontra.
      inversion 1. subst.
      apply: Hcontra. f_equal. eauto. }
    have Hterm' : corr_term
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x) H' 0
      (subst (scat (map Loc ls) Var) (nth (0, 0, Var 0) pts0 i).2) t0.
    { refine (corr_term_subst _ _ id _ _ (Heaps.eval_name_heap _ _ _ _ Hcbn) _ _ _ _ _ _ (leq0n _) _ _ _ _) =>
      [ | // | ? ? ? | ? ? ? | ? ].
      - move: H15 Hlt => <- /H19 /(_ (0, 0, Var 0)).
        rewrite addn0 H18 H1 => /=. apply.
      - rewrite H16 subn0 nth_scat (nth_map 0); eauto.
      - rewrite H16 subn0. eauto.
      - rewrite (eq_rename _ _ id) ?rename_id ?subst_rename_comp ?(eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map ?H16 ?addKn ?leq_addr. }
    have Hheap' : corr_heap H'
      (fun l x => size ls <= x /\ R l (x - size ls) \/
        x < size ls /\ l = nth 0 ls x)
      (Cat E' ts E).
    { apply: corr_heap_union.
      + rewrite H16.
        apply: corr_heap_catR.
        refine (corr_heap_impl _ _ _ _ _ _ (fun _ _ H => H)
          (Heaps.eval_name_heap _ _ _ _ _)); eauto.
      + constructor => ? ? [ Hlt' -> ] /=.
        move: (H20 _ Hlt').
        rewrite (eq_rename _ _ id) ?rename_id ?H17 ?(nth_map (Var 0)) -?H16 => //=.
        repeat (eexists; eauto). }
    apply: Heaps.diverge_name_casematch; eauto.
Qed.
