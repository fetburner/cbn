From mathcomp Require Import all_ssreflect.
Require Import Util.

Definition cons := nat.

Inductive term : Type :=
  | Var of nat
  | Loc of nat
  | Abs of term
  | App of term & term
  | Let of seq term & term
  | VCons of cons & seq nat
  | Cons of cons & seq term
  | Case of term & seq (cons * nat * term).

(* まず，まともな帰納法の原理を得る *)

Definition term_rect'
  (P : term -> Type)
  (HVar : forall x, P (Var x))
  (HLoc : forall l, P (Loc l))
  (HAbs : forall t, P t -> P (Abs t))
  (HApp : forall t1, P t1 -> forall t2, P t2 -> P (App t1 t2))
  (HLet : forall ts, foldr (fun t => prod (P t)) unit ts -> forall t, P t -> P (Let ts t))
  (HVCons : forall c ls, P (VCons c ls))
  (HCons : forall c ts, foldr (fun t => prod (P t)) unit ts -> P (Cons c ts))
  (HCase : forall t, P t -> forall pts, foldr (fun pt => prod (P pt.2)) unit pts -> P (Case t pts)) :=
  fix term_ind t :=
    match t as t0 return P t0 with
    | Var _ => HVar _
    | Loc _ => HLoc _
    | Abs t => HAbs _ (term_ind t)
    | App t1 t2 => HApp _ (term_ind t1) _ (term_ind t2)
    | Let ts t => HLet _ ((fix term_ind' ts :=
        match ts as ts0 return foldr (fun t => prod (P t)) unit ts0 with
        | nil => tt
        | t :: ts => pair (term_ind t) (term_ind' ts)
        end) ts) _ (term_ind t)
    | VCons _ _ => HVCons _ _
    | Cons _ ts => HCons _ _ ((fix term_ind' ts :=
        match ts as ts0 return foldr (fun t => prod (P t)) unit ts0 with
        | nil => tt
        | t :: ts => pair (term_ind t) (term_ind' ts)
        end) ts)
    | Case t pts => HCase _ (term_ind t) _ ((fix term_ind' pts :=
        match pts as pts0 return foldr (fun pt => prod (P pt.2)) unit pts0 with
        | nil => tt
        | (_, _, t) :: ts => pair (term_ind t) (term_ind' ts)
        end) pts)
    end.

Lemma sumbool_cast {A B C D : Prop} :
  (A -> C) ->
  (B -> D) ->
  { A } + { B } ->
  { C } + { D }.
Proof. by move => HL HR [ /HL | /HR ] ?; [ left | right ]. Qed.

Definition term_eq_dec : forall (t t' : term), { t = t' } + { t <> t' }.
Proof.
  refine (fix term_eq_dec t t' :=
    match t, t' return { t = t' } + { t <> t' } with
    | Var x, Var y => sumbool_cast _ _ (PeanoNat.Nat.eq_dec x y)
    | Loc l, Loc l' => sumbool_cast _ _ (PeanoNat.Nat.eq_dec l l')
    | Abs t, Abs t' => sumbool_cast _ _ (term_eq_dec t t')
    | App t11 t12, App t21 t22 =>
        sumbool_cast _ _
          (Sumbool.sumbool_and _ _ _ _
             (term_eq_dec t11 t21) (term_eq_dec t12 t22))
    | Let t11s t12, Let t21s t22 =>
        sumbool_cast _ _
          (Sumbool.sumbool_and _ _ _ _
            (List.list_eq_dec term_eq_dec t11s t21s)
            (term_eq_dec t12 t22))
    | VCons c ls, VCons c' ls' =>
        sumbool_cast _ _
          (Sumbool.sumbool_and _ _ _ _
            (PeanoNat.Nat.eq_dec c c')
            (List.list_eq_dec PeanoNat.Nat.eq_dec ls ls'))
    | Cons c ts, Cons c' ts' =>
        sumbool_cast _ _
          (Sumbool.sumbool_and _ _ _ _
            (PeanoNat.Nat.eq_dec c c')
            (List.list_eq_dec term_eq_dec ts ts'))
    | Case t pts, Case t' pts' =>
        sumbool_cast _ _
          (Sumbool.sumbool_and _ _ _ _
            (term_eq_dec t t')
            (List.list_eq_dec (fun pt pt' =>
              match pt, pt' with
              | ((c, n), t), ((c', n'), t') =>
                  sumbool_cast _ _
                    (Sumbool.sumbool_and _ _ _ _
                      (PeanoNat.Nat.eq_dec c c')
                      (Sumbool.sumbool_and _ _ _ _
                        (PeanoNat.Nat.eq_dec n n')
                        (term_eq_dec t t')))
              end) pts pts'))
    | _, _ => right _
    end);
  repeat match goal with
  | |- _ /\ _ -> _ => move => [ ]
  | |- _ \/ _ -> _ => move => [ ]
  | |- _ = _ -> _ => move => ->
  | |- _ <> _ -> _ => move => ?
  | |- _ <> _ => inversion 1
  end; eauto.
Defined.

Lemma term_eqP : Equality.axiom term_eq_dec.
Proof. move => t t'. by case (term_eq_dec t t') => ?; [ left | right ]. Qed.

Definition term_eqMixin := EqMixin term_eqP.
Canonical term_eqType := Eval hnf in EqType _ term_eqMixin.

Definition term_ind'
  (P : term -> Prop)
  (HVar : forall x, P (Var x))
  (HLoc : forall x, P (Loc x))
  (HAbs : forall t, P t -> P (Abs t))
  (HApp : forall t1, P t1 -> forall t2, P t2 -> P (App t1 t2))
  (HLet : forall ts, { in ts, forall t, P t } -> forall t, P t -> P (Let ts t))
  (HVCons : forall c ls, P (VCons c ls))
  (HCons : forall c ts, { in ts, forall t, P t } -> P (Cons c ts))
  (HCase : forall t, P t ->
    forall pts, (forall c n t, (c, n, t) \in pts -> P t) -> P (Case t pts))
  : forall t, P t.
Proof.
  elim /term_rect' => [ | | | | ts IHts | | ? ts IHts | ? ? pts IHpts ] //=.
  - apply: HLet.
    elim: ts IHts => /= [ ? ? | ? ? IHts [ ? ? ] ? ].
    + by rewrite in_nil.
    + rewrite in_cons => /orP [ /eqP -> // | ].
      exact: IHts.
  - apply: HCons.
    elim: ts IHts => /= [ ? ? | ? ? IHts [ ? ? ] ? ].
    + by rewrite in_nil.
    + rewrite in_cons => /orP [ /eqP -> // | ].
      exact: IHts.
  - apply: HCase => //.
    elim: pts IHpts => /= [ ? ? ? ? | [ [ ? ? ] ? ] ? IHpts /= [ ? ? ] ? ? ? ].
    + by rewrite in_nil.
    + rewrite in_cons => /orP [ /andP /= [ ? /eqP -> ] // | ].
      exact: IHpts.
Qed.

(* シフトや代入の定義と，それらについての補題を証明する *)

Fixpoint rename_term r t :=
  match t with
  | Loc l => Loc l
  | Var x => Var (r x)
  | Abs t => Abs (rename_term (upren r) t)
  | App t1 t2 => App (rename_term r t1) (rename_term r t2)
  | Let ts t =>
      let r' := upnren r (size ts) in
      Let (map (rename_term r') ts) (rename_term r' t)
  | VCons c ls => VCons c ls
  | Cons c ts => Cons c (map (rename_term r) ts)
  | Case t pts =>
      Case (rename_term r t)
        (map (fun pt => (pt.1, rename_term (upnren r (pt.1.2)) pt.2)) pts)
  end.

Program Instance RenameTerm : Rename term :=
  { Var := Var; rename := rename_term }.
Next Obligation.
  elim /term_ind' : t r r' H => /=;
  intros; f_equal; eauto using eq_upren, eq_upnren.
  - by apply /eq_in_map => ? /H; eauto using eq_upnren.
  - by apply /eq_in_map => ? /H; eauto using eq_upnren.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using eq_upnren.
Qed.

Program Instance RenameLemmasTerm : RenameLemmas term.
Next Obligation.
  induction t using term_ind' => /=; f_equal;
  eauto using rename_id_upren, rename_id_upnren.
  - apply map_id_in => ? /H. eauto using rename_id_upnren.
  - apply map_id_in => ? /H. eauto using rename_id_upnren.
  - apply: map_id_in => [ [ [ ? ? ] ? ] /= /H ? ].
    f_equal. eauto using rename_id_upnren.
Qed.
Next Obligation.
  elim /term_ind' : t r r' => /=; intros; f_equal; rewrite ?size_map -?map_comp;
  eauto using rename_rename_comp_upren, rename_rename_comp_upnren.
  - apply /eq_in_map => ? /H.
    eauto using rename_rename_comp_upnren.
  - apply /eq_in_map => ? /H.
    eauto using rename_rename_comp_upnren.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using rename_rename_comp_upnren.
Qed.

Fixpoint subst_term s t :=
  match t with
  | Var x => s x
  | Loc l => Loc l
  | Abs t => Abs (subst_term (up s) t)
  | App t1 t2 => App (subst_term s t1) (subst_term s t2)
  | Let ts t =>
      let s' := upn s (size ts) in
      Let (map (subst_term s') ts) (subst_term s' t)
  | VCons c ls => VCons c ls
  | Cons c ts => Cons c (map (subst_term s) ts)
  | Case t pts =>
      Case (subst_term s t)
        (map (fun pt => (pt.1, subst_term (upn s (pt.1.2)) pt.2)) pts)
  end.

Program Instance SubstTerm : Subst term := { subst := subst_term }.
Next Obligation.
  elim /term_ind' : t s s' H => /=; intros; f_equal;
  eauto using eq_up, eq_upn.
  - apply /eq_in_map => ? /H; eauto using eq_upn.
  - apply /eq_in_map => ? /H; eauto using eq_upn.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using eq_upn.
Qed.

Program Instance SubstLemmasTerm : SubstLemmas term.
Next Obligation.
  elim /term_ind' : t => /=; intros; f_equal;
  eauto using subst_id_up, subst_id_upn.
  - apply: map_id_in => ? /H. eauto using subst_id_upn.
  - apply: map_id_in => ? /H. eauto using subst_id_upn.
  - apply: map_id_in => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using subst_id_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r => /=; intros; f_equal;
  eauto using rename_subst_up, rename_subst_upn.
  - apply /eq_in_map => ? /H. eauto using rename_subst_upn.
  - apply /eq_in_map => ? /H. eauto using rename_subst_upn.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using rename_subst_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r s => /=; intros; f_equal; rewrite ?size_map -?map_comp;
  eauto using subst_rename_comp_up, subst_rename_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using subst_rename_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using subst_rename_comp_upn.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using subst_rename_comp_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r s => /=; intros; f_equal; rewrite ?size_map -?map_comp;
  eauto using rename_subst_comp_up, rename_subst_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using rename_subst_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using rename_subst_comp_upn.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using rename_subst_comp_upn.
Qed.

Program Instance SubstLemmas'Term : SubstLemmas' term.
Next Obligation.
  elim /term_ind' : t s s' => /=; intros; f_equal; rewrite ?size_map -?map_comp;
  eauto using subst_subst_comp_up, subst_subst_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using subst_subst_comp_upn.
  - apply /eq_in_map => ? /H.
    eauto using subst_subst_comp_upn.
  - apply /eq_in_map => [ [ [ ? ? ] ? ] /= /H0 ? ].
    f_equal. eauto using subst_subst_comp_upn.
Qed.
