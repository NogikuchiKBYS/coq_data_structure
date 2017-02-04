Require Import Nat Arith Omega.
Require Sumbool.
Require Import Relations RelationClasses Basics.
Require Import Orders OrdersFacts.

Set Implicit Arguments.

Ltac destruct_first H a := destruct H as [a H].

Ltac rewrite_maxlr_with a b :=
  first [
      ((rewrite (Z.max_l a b) in *) + (rewrite (Z.max_r a b) in *)); [| solve [omega]]
    ].

Ltac rewrite_maxlr_hyp :=
      repeat multimatch reverse goal with
             | [ H : ?P |- _ ] =>
               repeat match  P with
                 context A [Z.max ?x ?y] =>  rewrite_maxlr_with x y
               end
        end.

Ltac rewrite_maxlr_goal :=
  repeat match  goal  with
         | [ |- ?A ]=>
           match  A with
             context B [Z.max ?x ?y] => rewrite_maxlr_with x y
           end
         end.

Ltac rewrite_maxlr := rewrite_maxlr_hyp; rewrite_maxlr_goal.


Module Type AVL.
  Declare Module A : UsualOrderedTypeFull'.
  Module  F := OrderedTypeFacts A.

  Inductive Tree : Type :=
  | leaf : Tree
  | node (value : A.t) (balance : Z) (lc rc : Tree) : Tree.

  Definition balance (t : Tree) :=
    match t with
    | leaf => 0%Z
    | node _ b _ _ => b
    end.

  Inductive TIn : A.t -> Tree -> Prop :=
  | tin_top : forall x c l r, TIn x (node x c l r)
  | tin_left : forall x v c l r, TIn x l -> TIn x (node v c l r)
  | tin_right : forall x v c l r, TIn x r -> TIn x (node v c l r).
  Hint Constructors TIn.

  Lemma tin_child : forall x v c l r, TIn x l \/ TIn x r -> TIn x (node v c l r).
  Proof.
    intros.
    destruct H; auto.
  Qed.
  Hint Resolve tin_child.


  Lemma tin_child_iff : forall x v c l r,
      x = v \/ TIn x l \/ TIn x r <-> TIn x (node v c l r).
  Proof.
    intros.
    split; intro H.
    - repeat destruct H as [H | H]; subst; auto.
    - inversion H; auto.
  Qed.


  Definition TIn_dec : forall (x : A.t) (t : Tree), {TIn x t} + {~TIn x t}.
    refine (fix f (x : A.t) (t : Tree) :=
              match t with
              | leaf  => right _
              | node v d lc rc =>
                if A.eq_dec x v
                then left _
                else if Sumbool.sumbool_or _ _ _ _ (f x lc) (f x rc)
                     then left _
                     else right _
              end).
    - inversion 1.
    - subst.
      constructor.
    - auto.
    - intro Hin.
      inversion Hin; subst; intuition.
  Defined.

  Fixpoint depth  (t : Tree) : Z :=
    match t with
    | leaf => 0
    | node _ _ l r  => 1 + Z.max (depth l) (depth r)
    end.
  Arguments depth _ : simpl nomatch.

  Functional Scheme depth_ind := Induction for depth Sort Prop.
  Lemma depth_positive : forall (t : Tree), (depth t >= 0)%Z.
  Proof.
    intros.
    functional induction (depth t).
    - intuition.
    - destruct (Zmax_spec (depth l) (depth r)); omega.
  Qed.

  Lemma depth_node : forall x c l r, depth (node x c l r) = (1 + Z.max (depth l) (depth r))%Z.
  Proof.
    intros.
    reflexivity.
  Qed.
  Ltac try_decide_depth_node := repeat rewrite depth_node in *; rewrite_maxlr.

  (* has correct balancefactor *)
  Inductive Correct : Tree -> Prop :=
  | c_leaf : Correct (leaf)
  | c_node : forall v c l r,
      Correct l -> Correct r ->
      c = (depth l - depth r)%Z ->
      Correct (node v c l r).
  Derive Inversion_clear correct_node_inv with (forall v c l r, Correct (node v c l r)) Sort Prop.

  Lemma correct_node_iff : forall v c l r,
      Correct (node v c l r) <->
      Correct l /\ Correct r /\ (c = depth l - depth r)%Z.
  Proof.
    intros v c l r.
    split.
    - inversion 1; auto.
    - constructor; intuition.
  Qed.

  Lemma Correct_ind' : forall P : Tree -> Prop,
      P leaf ->
      (forall v l r,
          Correct l -> P l -> Correct r -> P r -> depth l = depth r -> P (node v 0 l r)) ->
      (forall v l r,
          Correct l -> P l -> Correct r -> P r -> (depth l < depth r)%Z -> P (node v (depth l - depth r) l r)) ->
      (forall v l r,
          Correct l -> P l -> Correct r -> P r -> (depth l > depth r)%Z -> P (node v (depth l - depth r) l r)) ->
      forall t, Correct t -> P t.
  Proof.
    intros.
    induction H3; auto.
    subst.
    destruct Z.lt_total with (depth l) (depth r) as [Hc | Hc]; [ | destruct Hc as [Hc | Hc]];
      intuition.
    rewrite Hc.
    rewrite Z.sub_diag.
    auto.
  Qed.

  Inductive Balanced : Tree -> Prop :=
  | bl_lefa : Balanced leaf
  | bl_node : forall v c l r,
      Balanced l -> Balanced r ->
      (Z.abs c <= 1)%Z ->
      Balanced (node v c l r).
  Derive Inversion_clear balanced_node_inv with (forall v c l r, Balanced (node v c l r)) Sort Prop.
  Inductive Valid : Tree -> Prop := valid t : Correct t -> Balanced t -> Valid t.
  Lemma Valid_ind'
     : forall P : Tree -> Prop,
       P leaf ->
       (forall (v : A.t) (c : Z) (l r : Tree),
        Valid l -> P l -> Valid r -> P r -> (Z.abs c <= 1)%Z -> P (node v c l r)) ->
       forall t : Tree, Valid t -> P t.
  Proof.
    intros P Hl Hn t Hv.
    destruct Hv as [t Hc Hb].
    induction Hb; auto.
    inversion_clear Hc.
    apply Hn; auto.
    - constructor; auto.
    - constructor; auto.
  Qed.

  Lemma valid_node_inv
     : forall (v : A.t) (c : Z) (l r : Tree) (P : A.t -> Z -> Tree -> Tree -> Prop),
       (Valid l -> Valid r -> c = (depth l - depth r)%Z ->  (Z.abs c <= 1)%Z -> P v c l r) ->
       Valid (node v c l r) -> P v c l r.
  Proof.
    intros v c l r P H.
    inversion_clear 1.
    inversion_clear H1.
    inversion_clear H2.
    apply H; repeat constructor; intuition.
  Qed.

  Fixpoint flip_rec (t : Tree) : Tree :=
    match t with
    | leaf => leaf
    | node v c l r => node v (-c) (flip_rec r) (flip_rec l)
    end.
  Functional Scheme flip_rec_ind := Induction for flip_rec Sort Prop.

  Lemma flip_rec_depth : forall t, depth (flip_rec t) = depth t.
  Proof.
    intros.
    induction t; simpl; auto.
    repeat rewrite depth_node.
    rewrite Z.max_comm.
    congruence.
  Qed.

  Lemma flip_rec_correct : forall t, Correct (flip_rec t) <-> Correct t.
  Proof.
    intros.
    functional induction (flip_rec t).
    - reflexivity.
    - repeat rewrite correct_node_iff.
      repeat rewrite IHt0.
      repeat rewrite IHt1.
      repeat rewrite flip_rec_depth.
      intuition.
  Qed.

  Lemma flip_rec_balanced : forall t, Balanced (flip_rec t) <-> Balanced t.
  Proof.
    intros.
    functional induction (flip_rec t).
    - reflexivity.
    - split; intro Hb; constructor; inversion Hb using balanced_node_inv; intuition.
      + rewrite Z.abs_opp in *.
        assumption.
      + rewrite Z.abs_opp.
        assumption.
  Qed.

  Lemma flip_rec_valid : forall t, Valid (flip_rec t) <-> Valid t.
  Proof.
    intros.
    split; inversion 1; constructor.
    - rewrite <- flip_rec_correct; auto.
    - rewrite <- flip_rec_balanced; auto.
    - rewrite flip_rec_correct; auto.
    - rewrite flip_rec_balanced; auto.
  Qed.

  Lemma flip_rec_involutive : forall (t : Tree), flip_rec (flip_rec t) = t.
  Proof.
    induction t; simpl; intuition.
    rewrite Z.opp_involutive.
    congruence.
  Qed.

  Lemma flip_rec_in : forall t x, TIn x (flip_rec t) <-> TIn x t.
  Proof.
    intros.
    functional induction (flip_rec t); intuition.
    - inversion_clear H3; auto.
    - inversion_clear H3; auto.
  Qed.

  Definition TForall (P : A.t -> Prop) (t : Tree) : Prop := (forall x, TIn x t -> P x).
  Inductive TForall' : (A.t -> Prop) -> Tree -> Prop :=
  | tforall_leaf : forall P, TForall' P leaf
  | tforall_node : forall P v c l r , TForall' P l -> TForall' P r -> P v -> TForall' P (node v c l r).
  Hint Unfold TForall.

  Lemma TForall_iff  : forall P t, TForall P t <-> TForall' P t.
  Proof.
    intros P t.
    split; intro H.
    - unfold TForall in *.
      induction t; constructor; auto.
    - unfold TForall.
      intro x.
      induction H; inversion 1; auto.
  Qed.

  Lemma flip_TForall : forall P t, TForall P (flip_rec t) <-> TForall P t.
  Proof.
    intros.
    unfold TForall in *.
    split; intro H.
    - intros x Hin.
      apply H.
      rewrite flip_rec_in; auto.
    - intros x Hin.
      apply H.
      rewrite <- flip_rec_in; auto.
  Qed.

  Inductive RelTree (R : relation A.t) : Tree -> Prop :=
  | rt_leaf : RelTree R leaf
  | rt_node : forall v c l r,
      RelTree R l -> RelTree R r ->
      TForall (fun y => R y v) l -> TForall (fun y => R v y) r -> RelTree R (node v c l r).
  Derive Inversion_clear reltree_node_inv with (forall R v c l r, RelTree R (node v c l r))
                                                 Sort Prop.
  Hint Constructors RelTree.
  Definition STree t := RelTree A.lt t.
  Hint Unfold STree.

  Lemma flip_rec_reltree : forall R t, RelTree (flip R) (flip_rec t) <-> RelTree R t.
  Proof.
    intros.
    functional induction (flip_rec t).
    - intuition.
    - split; inversion 1;
        (rewrite flip_TForall in * + rewrite <- flip_TForall in *); intuition.
  Qed.

  Fixpoint search (x : A.t) (t : Tree) : bool :=
    match t with
    | leaf => false
    | node v c l r =>
      match A.compare x v with
      | Eq => true
      | Lt => search x l
      | Gt => search x r
      end
    end.
  Functional Scheme  search_ind := Induction for search Sort Prop.

  Lemma search_spec : forall x t, STree t -> search x t = true <-> TIn x t.
  Proof.
    intros x t.
    functional induction (search x t); intro Hst.
    - split; inversion 1.
    - split; auto.
      rewrite F.compare_eq_iff in e0; subst.
      constructor.
    - rewrite F.compare_lt_iff in e0.
      inversion Hst as [| v' c l' r' Hsl Hsr_ Hlt Hgt]; subst.
      rewrite IHb; auto.
      split; auto.
      inversion 1; subst; auto; try F.order.
      specialize (Hgt _ H2). simpl in Hgt.
      F.order.
    - rewrite F.compare_gt_iff in e0.
      inversion Hst as [| v' c l' r' Hsl Hsr_ Hlt Hgt]; subst.
      rewrite IHb; auto.
      split; auto.
      inversion 1; subst; auto; try F.order.
      specialize (Hlt _ H2). simpl in Hlt.
      F.order.
  Qed.

  Definition AVL t := Valid t /\ STree t.
  Hint Unfold AVL.

  Definition rrotate_help_comp (x y : Z) : Z * Z :=
    (if Z_lt_le_dec 0 y
     then if Z_lt_le_dec (x - 1 - y) 0 then (x - 2, x - 1 - y) else (y - 1, x - 1 - y)
     else if Z_lt_le_dec (x - 1) 0 then (x + y - 2, x - 1) else (y - 1, x - 1)
    )%Z.
  Arguments rrotate_help_comp _ _ : simpl nomatch.
  Functional Scheme rrotate_help_comp_ind := Induction for rrotate_help_comp Sort Prop.
  Lemma rrotate_help_comp_ind'
    : (forall (x y : Z) (P : Z * Z -> Prop),
          (forall (Hy : 0 < y) (Hx : x - 1 - y < 0), P (x - 2, x - 1 - y)) ->
          (forall (Hy : 0 < y) (Hx : 0 <= x - 1 - y), P (y - 1, x - 1 - y)) ->
          (forall (Hy : y <= 0) (Hx : x - 1 < 0), P (x + y - 2, x - 1)) ->
          (forall (Hy : y <= 0) (Hx : 0 <= x - 1), P (y - 1, x - 1)) ->
          P (rrotate_help_comp x y))%Z.
  Proof.
    intros.
    functional induction (rrotate_help_comp x y); auto.
  Qed.


  Definition rrotate_help v c lv lc ll lr r :=
    let (cx, cy) := rrotate_help_comp c lc in
    node lv cx ll (node v cy lr r).

  Lemma rrotate_help_rel (R : relation A.t) `{Tr : Transitive _ R} : forall v c lv lc ll lr r,
      RelTree R (node v c (node lv lc ll lr) r) -> RelTree R (rrotate_help v c lv lc ll lr r).
  Proof.
    intros.
    unfold rrotate_help.
    destruct rrotate_help_comp as [cx cy].
    inversion H as [| v' c' l' r' Hsl Hsr Hlt Hgt]; subst.
    inversion Hsl as [| lv' lc' ll' lr' Hsll Hslr Hllt Hlgt]; subst.
    constructor; auto.
    intro x.
    inversion 1; eauto.
  Qed.

  Lemma correct_child_depth_l : forall v c l r,
      (Correct (node v c l r) -> 0 <= c ->
       depth l = depth (node v c l r) - 1 /\ depth r = depth (node v c l r) - 1 - c)%Z.
  Proof.
    intros v c l r Hc Hlt.
    inversion Hc as [| ?v ?c ?l ?r Hcl Hcr Hceq]; subst; try discriminate.
    remember (depth (node _ _ _ _)) as d.
    rewrite depth_equation in Heqd.
    rewrite Z.max_l in Heqd; try omega.
  Qed.

  Lemma correct_child_depth_r : forall v c l r,
      (Correct (node v c l r) -> c <= 0 ->
       depth l = depth (node v c l r) - 1 + c /\ depth r = depth (node v c l r) - 1)%Z.
  Proof.
    intros v c l r Hc Hlt.
    inversion Hc as [| ?v ?c ?l ?r Hcl Hcr Hceq]; subst; try discriminate.
    remember (depth (node _ _ _ _)) as d.
    rewrite depth_equation in Heqd.
    rewrite Z.max_r in Heqd; try omega.
  Qed.

  Lemma valid_depth_case : forall v c l r,
      Valid (node v c l r) ->
      (c = 0 /\ depth l = depth r /\ depth (node v c l r) = depth l + 1)%Z \/
      (c = 1 /\ depth l = depth r + 1 /\ depth (node v c l r) = depth l + 1)%Z \/
      (c = -1 /\ depth l = depth r - 1 /\ depth (node v c l r) = depth l + 2)%Z.
  Proof.
    assert (forall (P Q R : Prop), P -> (P -> Q) -> (P -> Q -> R) -> P /\ Q /\ R) as and3_help.
    - intros.
      intuition.
    - intros.
      inversion_clear H as [?t Hc Hb].
      rewrite correct_node_iff in Hc.
      repeat apply proj2 in Hc.
      inversion Hb using balanced_node_inv; clear Hb.
      intros Hbl Hbr Habs.
      rewrite depth_node.
      destruct (Z.abs_spec c) as [Habs' | Habs']; rewrite_maxlr; omega.
  Qed.

  Ltac solve_correct_child_depth a b c :=
    first [
        destruct (correct_child_depth_l a) as [b c]; [solve[omega]|] |
        destruct (correct_child_depth_r a) as [b c]; [solve[omega]|]
      ].


  Lemma rrotate_help_correct : forall v c lv lc ll lr r,
      (0 <= c)%Z ->
      Correct (node v c (node lv lc ll lr) r) ->
      Correct (rrotate_help v c lv lc ll lr r).
  Proof.
    intros v c lv lc ll lr r.
    intros Hc Hcor.
    unfold rrotate_help.
    solve_correct_child_depth Hcor H1 H2.
    rewrite correct_node_iff in Hcor.
    functional induction (rrotate_help_comp c lc) using rrotate_help_comp_ind'.
    - destruct Hcor as [Hcorl Hcor]; destruct Hcor as [Hcorr Hdep1].
      solve_correct_child_depth Hcorl H3 H4.
      rewrite correct_node_iff in Hcorl.
      repeat constructor; intuition.
      try_decide_depth_node; omega.
    - destruct Hcor as [Hcorl Hcor]; destruct Hcor as [Hcorr Hdep1].
      solve_correct_child_depth Hcorl H3 H4.
      rewrite correct_node_iff in Hcorl.
      repeat constructor; intuition.
      try_decide_depth_node; omega.
    - destruct Hcor as [Hcorl Hcor]; destruct Hcor as [Hcorr Hdep1].
      solve_correct_child_depth Hcorl H3 H4.
      rewrite correct_node_iff in Hcorl.
      repeat constructor; intuition.
      try_decide_depth_node; omega.
    - destruct Hcor as [Hcorl Hcor]; destruct Hcor as [Hcorr Hdep1].
      solve_correct_child_depth Hcorl H3 H4.
      rewrite correct_node_iff in Hcorl.
      repeat constructor; intuition.
      try_decide_depth_node; omega.
  Qed.

  Definition lrotate_help v c l rv rc rl rr :=
    match (rrotate_help v (-c)%Z rv (-rc)%Z rr rl l) with
    | node v' c' l' (node rv' rc' rl' rr') => node v' (-c') (node rv' (-rc')%Z rr' rl') l'
    | _ => leaf
    end.
  Functional Scheme lrotate_help_ind := Induction for lrotate_help Sort Prop.

  Lemma lrotate_help_ind' : forall (v : A.t) (c : Z) (l : Tree) (rv : A.t) (rc : Z) (rl rr : Tree) (P : Tree -> Prop),
      (forall (v' : A.t) (c' : Z) (l' rc0 : Tree),
          rrotate_help v (- c) rv (- rc) rr rl l = node v' c' l' rc0 ->
          forall (rv' : A.t) (rc' : Z) (rl' rr' : Tree),
            rc0 = node rv' rc' rl' rr' -> P (node v' (- c') (node rv' (- rc') rr' rl') l')) ->
      P (lrotate_help v c l rv rc rl rr).
  Proof.
    intros.
    functional induction (lrotate_help v c l rv rc rl rr); eauto.
    - unfold rrotate_help in e.
      destruct (rrotate_help_comp (-c) (-rc))%Z.
      discriminate.
    - unfold rrotate_help in e.
      destruct (rrotate_help_comp (-c) (-rc))%Z.
      discriminate.
  Qed.

  Lemma lrotate_help_correct : forall v c l rv rc rl rr,
      (c <= 0)%Z ->
      Correct (node v c l (node rv rc rl rr)) ->
      Correct (lrotate_help v c l rv rc rl rr).
  Proof.
    intros.
    functional induction (lrotate_help v c l rv rc rl rr) using lrotate_help_ind'.
    cut (Correct (rrotate_help v (- c) rv (-rc) rr rl l)).
    - intro Hcor.
      rewrite H1 in Hcor.
      repeat rewrite correct_node_iff in Hcor.
      repeat constructor; intuition.
      rewrite depth_node in *.
      rewrite Z.max_comm.
      omega.
    - apply rrotate_help_correct; try omega.
      repeat rewrite correct_node_iff in H0.
      repeat constructor; intuition.
      rewrite depth_node in *.
      rewrite Z.max_comm.
      omega.
  Qed.

  Lemma lrotate_help_rel (R : relation A.t) `{Tr : Transitive _ R} : forall  v c l rv rc rl rr,
      RelTree R (node v c l (node rv rc rl rr)) ->
      RelTree R (lrotate_help v c l rv rc rl rr).
  Proof.
    intros.
    functional induction (lrotate_help v c l rv rc rl rr) using lrotate_help_ind'.
    unfold rrotate_help in H0.
    destruct (rrotate_help_comp _ _ ) as [a b].
    inversion H0; subst; clear H0.
    inversion H using reltree_node_inv; intros HRrr HRrl Hlt Hgt.
    inversion HRrl using reltree_node_inv; intros HRrl' HRl' Hlt' Hgt'.
    repeat constructor; auto.
    intro x.
    inversion 1; eauto.
  Qed.

  Definition rrotate t : Tree :=
    match t with
    | node v c (node lv lc ll lr) r => rrotate_help v c lv lc ll lr r
    | _  => t
    end.
  Arguments rrotate t : simpl nomatch.
  Functional Scheme rrotate_ind := Induction for rrotate Sort Prop.
  Lemma rrotate_reltree (R : relation A.t) `{Tr : Transitive _ R} : forall t, RelTree R t -> RelTree R (rrotate t).
  Proof. intros. functional induction (rrotate t); eauto using rrotate_help_rel. Qed.

  Lemma rrotate_in : forall t x, TIn x (rrotate t) <-> TIn x t.
  Proof.
    intros.
    functional induction (rrotate t); try solve [intuition].
    unfold rrotate_help.
    destruct rrotate_help_comp as [cx cy].
    repeat rewrite <- tin_child_iff.
    intuition; auto.
  Qed.

  Definition lrotate t : Tree :=
    match t with
    | node v c l (node rv rc rl rr) => lrotate_help v c l rv rc rl rr
    | _  => t
    end.
  Arguments lrotate t : simpl nomatch.
  Functional Scheme lrotate_ind := Induction for lrotate Sort Prop.
  Lemma lrotate_reltree (R : relation A.t) `{Tr : Transitive _ R} : forall t, RelTree R t -> RelTree R (lrotate t).
  Proof. intros. functional induction (lrotate t); eauto using lrotate_help_rel. Qed.


  Lemma lrotate_flip_eq : forall t, lrotate t = flip_rec (rrotate (flip_rec t)).
  Proof.
    intros.
    induction t; simpl; auto.
    unfold lrotate, rrotate.
    destruct t2; simpl.
    - rewrite Z.opp_involutive, flip_rec_involutive.
      reflexivity.
    - unfold lrotate_help.
      unfold rrotate_help.
      destruct (rrotate_help_comp _ _) as [cx cy].
      simpl.
      repeat rewrite flip_rec_involutive.
      reflexivity.
  Qed.
  Lemma lrotate_in : forall t x, TIn x (lrotate t) <-> TIn x t.
  Proof.
    intros.
    rewrite lrotate_flip_eq.
    rewrite flip_rec_in.
    rewrite rrotate_in.
    rewrite flip_rec_in.
    reflexivity.
  Qed.

  Definition rrot_balance v c l r :=
    if (Z_lt_ge_dec (balance l) 0)%Z then rrotate (node v c (lrotate l) r) else rrotate (node v c l r).

  Lemma rrot_balance_reltree R `{Tr : Transitive A.t R} : forall v c l r,
      RelTree R (node v c l r) -> RelTree R (rrot_balance v c l r).
  Proof.
    intros.
    unfold rrot_balance.
    destruct Z_lt_ge_dec.
    - destruct l as[| lv lc ll lr].
      + simpl in l0.
        discriminate.
      + simpl in l0.
        apply rrotate_reltree; auto.
        inversion_clear H as [|?v ?c ?l ?r Hsl Hsr Hlt Hgt]; subst.
        inversion Hsl as [|?v ?c ?l ?r Hsl' Hsr' Hlt' Hgt']; subst.
        constructor; eauto using lrotate_reltree.
        intro x.
        rewrite lrotate_in.
        eauto.
    - apply rrotate_reltree; auto.
  Qed.

  Lemma rrotate_balance_depth_single :
    forall v l r,
      (balance l = 1)%Z -> Valid l -> Valid r -> Correct (node v 2 l r) ->
      Valid (rrot_balance v 2 l r) /\
      depth (rrot_balance v 2 l r) = (depth (node v 2 l r) - 1)%Z.
  Proof.
    intros v l r Hball HVl HVr HCt.
    inversion_clear HVl as [?t HCl HBl].
    inversion_clear HVr as [?t HCr HBr].
    destruct l as [| lv lc ll lr]; simpl in Hball; try discriminate.
    subst.
    unfold rrot_balance.
    simpl.
    inversion HCl using correct_node_inv; intros HCll HClr Hlceq.
    inversion HBl using balanced_node_inv; intros HBll HBlr Hlcabs.
    unfold rrotate. unfold rrotate_help.
    simpl.
    assert (depth lr = depth r) as Heq. {
      repeat rewrite correct_node_iff in HCt.
      try_decide_depth_node; omega.
    }
    split.
    - repeat constructor; simpl; eauto; try omega.
      try_decide_depth_node; omega.
    - try_decide_depth_node; omega.
  Qed.

  Lemma rrotate_balance_depth_double :
    forall v l r, (balance l = -1)%Z -> Valid l -> Valid r -> Correct (node v 2 l r) ->
                  Valid (rrot_balance v 2 l r) /\
                  depth (rrot_balance v 2 l r) = (depth (node v 2 l r) - 1)%Z.
  Proof.
    intros v l r Hball HVl HVr HCt.
    inversion_clear HVl as [?t HCl HBl].
    inversion_clear HVr as [?t HCr HBr].
    inversion HCt using correct_node_inv; clear HCt.
    intros _ _ Hdept.
    destruct l as [| lv lc ll lr]; simpl in Hball; try discriminate.
    subst.
    inversion HBl using balanced_node_inv; clear HBl.
    intros HBll HBlr _.
    inversion HCl using correct_node_inv; clear HCl.
    intros HCll HClr Hdepl.
    set (depth_positive ll) as Hpos; clearbody Hpos.
    destruct lr as [| lrv lrc lrl lrr]; simpl in Hdepl; try omega.
    inversion HBlr using balanced_node_inv.
    intros HBlrl HBlrr Hlrcabs.
    inversion HClr using correct_node_inv.
    intros HClrl HClrr Hdeplr.
    set (valid_depth_case (valid HClr HBlr)) as Hd; clearbody Hd; repeat destruct Hd as [Hd | Hd].
    - destruct_first Hd Hlrc.
      destruct Hd as [Hd1 Hd2].
      subst.
      unfold rrot_balance, rrotate_help; simpl.
      unfold rrotate_help; simpl.
      repeat rewrite depth_node in Hdept; rewrite_maxlr.
      rewrite Hlrc in *.
      simpl.
      unfold rrotate_help; simpl.
      try_decide_depth_node.
      repeat constructor; eauto; try solve [omega | simpl; omega].
      try_decide_depth_node; omega.
    - destruct_first Hd Hlrc.
      destruct Hd as [Hd1 Hd2].
      subst.
      unfold rrot_balance; simpl.
      repeat unfold rrotate_help; simpl.
      repeat rewrite depth_node in Hdept; rewrite_maxlr.
      rewrite Hlrc in *.
      simpl.
      unfold rrotate_help; simpl.
      try_decide_depth_node.
      repeat constructor; eauto; try solve [omega | simpl; omega].
      try_decide_depth_node; omega.
    - destruct_first Hd Hlrc.
      destruct Hd as [Hd1 Hd2].
      subst.
      unfold rrot_balance; simpl.
      repeat unfold rrotate_help; simpl.
      repeat rewrite depth_node in Hdept; rewrite_maxlr.
      rewrite Hlrc in *.
      simpl.
      unfold rrotate_help; simpl.
      try_decide_depth_node.
      repeat constructor; eauto; try solve [omega | simpl; omega].
      try_decide_depth_node; omega.
  Qed.

  Lemma rrotate_balance_depth :
    forall v l r, Valid l -> Valid r ->
                  (balance l <> 0)%Z ->
                  Correct (node v 2 l r) ->
                  Valid (rrot_balance v 2 l r) /\
                  depth (rrot_balance v 2 l r) = (depth (node v 2 l r) - 1)%Z.
  Proof.
    intros.
    cut (balance l = -1 \/ balance l = 1)%Z.
    - intro Hp.
      destruct Hp; eauto using rrotate_balance_depth_single, rrotate_balance_depth_double.
    - destruct l as [| lv lc ll lr]; inversion H; simpl in *; try omega; subst.
      apply valid_depth_case in H.
      intuition.
  Qed.

  Definition lrot_balance v c l r :=
    if (Z_gt_le_dec (balance r) 0)%Z then lrotate (node v c l (rrotate r)) else lrotate (node v c l r).

  Lemma lrot_balance_reltree R `{Tr : Transitive A.t R} : forall v c l r, RelTree R (node v c l r) -> RelTree R (lrot_balance v c l r).
  Proof.
    intros.
    unfold lrot_balance.
    destruct Z_gt_le_dec.
    - destruct r as[| rv rc rl rr].
      + simpl in g.
        discriminate.
      + simpl in g.
        apply lrotate_reltree; auto.
        inversion_clear H as [|?v ?c ?l ?r Hsl Hsr Hlt Hgt]; subst.
        inversion Hsr as [|?v ?c ?l ?r Hsl' Hsr' Hlt' Hgt']; subst.
        constructor; eauto using rrotate_reltree.
        intro x.
        rewrite rrotate_in.
        auto.
    - apply lrotate_reltree; auto.
  Qed.

  Lemma lrotate_balance_flip_eq : forall v l r,
      lrot_balance v (-2) l r = flip_rec (rrot_balance v 2 (flip_rec r) (flip_rec l)).
  Proof.
    intros.
    destruct r as [| rv rc rl rr]; simpl; auto.
    - unfold lrot_balance; simpl.
      rewrite flip_rec_involutive.
      reflexivity.
    - unfold lrot_balance, rrot_balance.
      simpl.
      destruct Z_gt_le_dec, Z_lt_ge_dec; try omega.
      + rewrite lrotate_flip_eq.
        simpl.
        f_equal.
        rewrite lrotate_flip_eq.
        simpl.
        repeat f_equal; eauto using flip_rec_involutive.
        omega.
      + unfold lrotate_help.
        simpl.
        unfold rrotate_help.
        destruct rrotate_help_comp as [cx cy].
        simpl.
        repeat rewrite flip_rec_involutive.
        reflexivity.
  Qed.
  Lemma rrotate_balance_flip_eq : forall v l r,
      rrot_balance v 2 l r = flip_rec (lrot_balance v (-2) (flip_rec r) (flip_rec l)).
  Proof.
    intros.
    rewrite lrotate_balance_flip_eq.
    repeat rewrite flip_rec_involutive.
    reflexivity.
  Qed.

  Lemma lrotate_balance_depth :
    forall v l r, Valid l -> Valid r -> Correct (node v (-2) l r) ->
                  (balance r <> 0)%Z ->
                  Valid (lrot_balance v (-2) l r) /\
                  depth (lrot_balance v (-2) l r) = (depth (node v (-2) l r) - 1)%Z.
  Proof.
    intros.
    rewrite lrotate_balance_flip_eq.
    rewrite flip_rec_valid.
    rewrite flip_rec_depth.
    replace (depth (node v (-2)%Z l r)) with (depth (node v 2 (flip_rec r) (flip_rec l))).
    - apply rrotate_balance_depth.
      + rewrite flip_rec_valid; assumption.
      + rewrite flip_rec_valid; assumption.
      + destruct r; simpl in *; omega.
      + rewrite <- flip_rec_correct in H1.
        assumption.
    - repeat rewrite depth_node.
      repeat rewrite flip_rec_depth.
      rewrite Z.max_comm.
      reflexivity.
  Qed.

  Definition balance_node v c l r :=
    if (Z.abs c <=? 1)%Z
    then (node v c l r, negb (c =? 0)%Z)
    else if (0 <=? c)%Z
         then (rrot_balance v 2 l r, false)
         else (lrot_balance v (-2) l r, false).

  Functional Scheme balance_node_ind := Induction for balance_node Sort Prop.
  (*
    match c with
    | Z0 => (node v c l r, false)
    | 1%Z => (node v c l r, true)
    | 2%Z => (rrot_balance v 2 l r, false)
    | (-1)%Z => (node v c l r, true)
    | (-2)%Z => (lrot_balance v (-2) l r, false)
    | _ => (node v c l r, true)
    end.
   *)
  Lemma balance_node_flip_eq : forall v c l r,
      balance_node v c l r = let (t, b) := balance_node v (-c) (flip_rec r) (flip_rec l) in (flip_rec t, b).
  Proof.
    assert (forall (x : Z), (x =? 0) = (-x =? 0))%Z as neg_zero. {
      intros.
      case_eq (x =? 0)%Z.
      - rewrite Z.eqb_eq.
        intro; subst.
        reflexivity.
      - rewrite Z.eqb_neq.
        intros.
        apply eq_sym.
        rewrite Z.eqb_neq.
        omega.
    }

    intros.
    unfold balance_node.
    rewrite Z.abs_opp.
    case_eq (Z.abs c <=? 1)%Z.
    - rewrite neg_zero.
      simpl.
      repeat rewrite flip_rec_involutive.
      rewrite Z.opp_involutive.
      reflexivity.
    - case_eq (0 <=? c)%Z; case_eq (0 <=? -c)%Z;
        repeat rewrite Z.leb_le; repeat rewrite Z.leb_gt; intros.
      + exfalso.
        cut (c = 0)%Z; try omega.
        intro; subst.
        simpl in *.
        omega.
      + rewrite rrotate_balance_flip_eq.
        reflexivity.
      + rewrite lrotate_balance_flip_eq.
        reflexivity.
      + omega.
  Qed.
  Lemma balance_node_in : forall v c l r x, TIn x (fst (balance_node v c l r)) <->
                                            TIn x (node v c l r).
  Proof.
    intros.
    functional induction (balance_node v c l r); simpl; try solve [intuition].
    - unfold rrot_balance.
      destruct Z_lt_ge_dec.
      + rewrite rrotate_in.
        repeat rewrite <- tin_child_iff.
        rewrite lrotate_in.
        reflexivity.
      +  rewrite rrotate_in.
         repeat rewrite <- tin_child_iff.
         reflexivity.
    - unfold lrot_balance.
      destruct Z_gt_le_dec.
      + rewrite lrotate_in.
        repeat rewrite <- tin_child_iff.
        rewrite rrotate_in.
        reflexivity.
      +  rewrite lrotate_in.
         repeat rewrite <- tin_child_iff.
         reflexivity.
  Qed.

  Lemma balance_node_reltree R `{Tr : Transitive A.t R} : forall v c l r,
      RelTree R (node v c l r) -> RelTree R (fst (balance_node v c l r)).
  Proof.
    intros.
    functional induction (balance_node v c l r); try solve [intuition].
    - apply rrot_balance_reltree; auto.
      inversion H; constructor; auto.
    - apply  lrot_balance_reltree; auto.
      inversion H; constructor; auto.
  Qed.

  Fixpoint insert' (cmp : A.t -> A.t -> comparison) (t : Tree) (x : A.t) : (Tree * bool) :=
    match t with
    | leaf => (node x 0%Z leaf leaf, true)
    | node v c l r =>
      match cmp x v with
      | Eq => (t, false)
      | Lt => let (l', grow) := insert' cmp l x in
              if grow then balance_node v (c + 1)%Z l' r else (node v c l' r, false)
      | Gt => let (r', grow) := insert' cmp r x in
              if grow then balance_node v (c - 1)%Z l r' else (node v c l r', false)
      end
    end.
  Functional Scheme insert'_ind := Induction for insert' Sort Prop.

  Lemma flip_rec_insert' : forall t x,
      let (t', grow) := insert' (fun x y => (CompOpp (A.compare x y))) (flip_rec t) x in
      (flip_rec t', grow) = insert' A.compare t x.
  Proof.
    intros t x.
    induction t as [| v c l IHl r IHr].
    - reflexivity.
    - simpl.
      destruct (insert' _ (flip_rec l) x) as [l' lg].
      destruct (insert' _ (flip_rec r) x) as [r' rg].
      rewrite <- IHl, <- IHr.
      case A.compare; simpl.
      + repeat rewrite flip_rec_involutive.
        repeat rewrite Z.opp_involutive.
        reflexivity.
      + destruct lg.
        * rewrite balance_node_flip_eq.
          replace (- (-c -1))%Z with (c + 1)%Z; try omega.
          rewrite flip_rec_involutive.
          destruct balance_node.
          rewrite flip_rec_involutive.
          reflexivity.
        * simpl.
          repeat rewrite flip_rec_involutive.
          rewrite Z.opp_involutive.
          reflexivity.
      + destruct rg.
        * rewrite balance_node_flip_eq.
          replace (- (- c + 1))%Z with (c - 1)%Z; try omega.
          rewrite flip_rec_involutive.
          destruct balance_node.
          rewrite flip_rec_involutive.
          reflexivity.
        * simpl.
          repeat rewrite flip_rec_involutive.
          rewrite Z.opp_involutive.
          reflexivity.
  Qed.


  Definition insert t x := fst (insert' A.compare t x).

  Lemma insert_in : forall cmp t x y,
      (forall x y, cmp x y = Eq <-> x = y) ->
      TIn y (fst(insert' cmp t x)) <-> x = y \/ TIn y t.
  Proof.
    intros cmp t x y Hspec.
    functional induction (insert' cmp t x); simpl.
    - rewrite <- tin_child_iff.
      intuition.
    - rewrite Hspec in e0; subst.
      rewrite <- tin_child_iff.
      intuition.
    - rewrite balance_node_in.
      repeat rewrite <- tin_child_iff in *.
      rewrite e1 in *.
      intuition.
    - repeat rewrite <- tin_child_iff in *.
      rewrite e1 in *.
      intuition.
    - rewrite balance_node_in.
      repeat rewrite <- tin_child_iff in *.
      rewrite e1 in *.
      intuition.
    - repeat rewrite <- tin_child_iff in *.
      rewrite e1 in *.
      intuition.
  Qed.

  Lemma insert_reltree  : forall t x,
      STree t -> STree (fst (insert' A.compare t x)).
  Proof.
    destruct A.lt_strorder.
    intros t x.
    functional induction (insert' A.compare t x); intro H; try solve [intuition].
    - repeat constructor.
      + rewrite TForall_iff; constructor.
      + rewrite TForall_iff; constructor.
    - rewrite F.compare_lt_iff in e0.
      apply balance_node_reltree; auto.
      rewrite e1 in IHp.
      simpl in IHp.
      inversion_clear H.
      constructor; intuition.
      intros y Hin.
      fold (fst (l', true)) in Hin.
      rewrite <- e1 in Hin.
      rewrite insert_in in Hin; eauto using F.compare_eq_iff.
      destruct Hin; subst; auto.
    - rewrite F.compare_lt_iff in e0.
      inversion_clear H.
      constructor; intuition.
      + rewrite e1 in H.
        assumption.
      + intros y Hin.
        fold (fst (l', false)) in Hin.
        rewrite <- e1 in Hin.
        rewrite insert_in in Hin; eauto using F.compare_eq_iff.
        destruct Hin; subst; auto.
    - rewrite F.compare_gt_iff in e0.
      apply balance_node_reltree; auto.
      rewrite e1 in IHp.
      simpl in IHp.
      inversion_clear H.
      constructor; intuition.
      intros y Hin.
      fold (fst (r', true)) in Hin.
      rewrite <- e1 in Hin.
      rewrite insert_in in Hin; eauto using F.compare_eq_iff.
      destruct Hin; subst; auto.
    - rewrite F.compare_gt_iff in e0.
      inversion_clear H.
      constructor; intuition.
      + rewrite e1 in H.
        assumption.
      + intros y Hin.
        fold (fst (r', false)) in Hin.
        rewrite <- e1 in Hin.
        rewrite insert_in in Hin; eauto using F.compare_eq_iff.
        destruct Hin; subst; auto.
  Qed.

  Lemma insert_not_leaf : forall cmp t x, fst (insert' cmp t x) <> leaf.
  Proof.
    assert (forall t, rrotate t = leaf -> t = leaf) as Hrrot. {
      intro t.
      functional induction (rrotate t); auto.
      unfold rrotate_help.
      destruct rrotate_help_comp.
      discriminate.
    }
    assert (forall t, lrotate t = leaf -> t = leaf) as Hlrot. {
      intros.
      cut (rrotate (flip_rec t) = leaf).
      - intro Hl.
        apply Hrrot in Hl.
        destruct t; try discriminate.
        reflexivity.
      - rewrite lrotate_flip_eq in H.
        destruct rrotate; try discriminate.
        reflexivity.
    }
    assert (forall v n l r, lrot_balance v n l r <> leaf) as Hlrb. {
      intros.
      unfold lrot_balance.
      destruct Z_gt_le_dec; intro Heq.
      - apply Hlrot in Heq. discriminate.
      - apply Hlrot in Heq. discriminate.
    }

    assert (forall v n l r, rrot_balance v n l r <> leaf) as Hrrb. {
      intros.
      unfold rrot_balance.
      destruct Z_lt_ge_dec; intro Heq.
      - apply Hrrot in Heq. discriminate.
      - apply Hrrot in Heq. discriminate.
    }


    intros.
    functional induction (insert' cmp t x); simpl; try discriminate.
    - unfold balance_node.
      destruct Z.leb; try discriminate.
      simpl.
      destruct Z.leb; simpl.
      + intuition.
        eapply Hrrb; eauto.
      + intuition.
        eapply Hlrb; eauto.
    - unfold balance_node.
      destruct Z.leb; try discriminate.
      simpl.
      destruct Z.leb; simpl.
      + intuition.
        eapply Hrrb; eauto.
      + intuition.
        eapply Hlrb; eauto.
  Qed.

  Lemma insert_depth : forall t x,
      Valid t ->
      let (t', grow) := insert' A.compare t x in
      Valid t' /\
      if grow then (depth t' = depth t + 1 /\ (t = leaf \/ balance t' <> 0))%Z else depth t' = depth t.
  Proof.
    intros t x HVt.
    functional induction (insert' A.compare t x); intuition.
    {
      repeat constructor; intuition.
    }
    {
      rewrite e1 in IHp.
      inversion HVt using valid_node_inv. intros HVl HVr Hdept Habst.
      specialize (IHp  HVl).
      functional induction (balance_node v (c0 + 1) l' r).
      inversion_clear HVl as [?t HCl HBl].
      inversion_clear HVr as [?t HCr HBr].
      - destruct IHp as [IHV IHp]; destruct IHp as [IHdep IHor].
        inversion_clear IHV as [?t IHC IHB].
        set (valid_depth_case HVt) as Hcaset.
        repeat destruct Hcaset as [Hcaset | Hcaset];
          destruct_first Hcaset Heqc; rewrite Heqc in *; clear Heqc; simpl.
        + cut (Valid (node v 1 l' r)).
          * try_decide_depth_node. intuition.
          * repeat constructor; intuition.
        + rewrite Z.leb_le in e.
          exfalso. intuition.
        + cut (Valid (node v 0 l' r)).
          * try_decide_depth_node; intuition.
          * repeat constructor; intuition.
      - destruct IHp as [IHV IHp]; destruct IHp as [IHdep IHor].
        rewrite Z.leb_le  in e2.
        rewrite Z.abs_eq in e; auto.
        rewrite Z.leb_gt in e.
        set (valid_depth_case HVt) as Hcaset.
        repeat destruct Hcaset as [Hcaset | Hcaset];
          destruct_first Hcaset Heqc; rewrite Heqc in *; clear Heqc; simpl; try omega.
        clear e e2 Habst.
        set rrotate_balance_depth as Hrrot; clearbody Hrrot.
        specialize (Hrrot v l' r).
        destruct Hrrot as [Hx Hy]; auto.
        + destruct IHor; auto.
          subst; simpl in *.
          set (depth_positive r); omega.
        + constructor; auto; try omega.
          * inversion IHV; auto.
          * inversion HVr; auto.
        + split; auto.
          rewrite Hy.
          repeat rewrite depth_node; rewrite_maxlr.
          omega.
      - exfalso.
        rewrite Z.leb_gt  in e, e2.
        rewrite Z.abs_neq in e, Habst; try omega.
    }
    {
      destruct l' as [| lv lc ll lr].
      - exfalso.
        apply (insert_not_leaf A.compare l x).
        rewrite e1; reflexivity.
      - rewrite e1 in IHp.
        inversion HVt using valid_node_inv.
        intros HVl HVr Hdept Habst.
        specialize (IHp HVl).
        destruct IHp as [HVl' Hdep].
        inversion HVl' using valid_node_inv.
        intros HVll HVlr Hdepl' Habsl'.
        inversion_clear HVll. inversion_clear HVlr.
        inversion_clear HVl. inversion_clear HVr.
        repeat constructor; intuition.
    }
    {
      rewrite e1 in IHp.
      inversion HVt using valid_node_inv. intros HVl HVr Hdept Habst.
      repeat rewrite depth_node.
      rewrite (proj2 (IHp HVl)).
      reflexivity.
    }
    {
      rewrite e1 in IHp.
      inversion HVt using valid_node_inv. intros HVl HVr Hdept Habst.
      specialize (IHp HVr).
      functional induction (balance_node v (c0 - 1) l r').
      inversion_clear HVl as [?t HCl HBl].
      inversion_clear HVr as [?t HCr HBr].
      - destruct IHp as [IHV IHp]; destruct IHp as [IHdep IHor].
        inversion_clear IHV as [?t IHC IHB].
        set (valid_depth_case HVt) as Hcaset.
        repeat destruct Hcaset as [Hcaset | Hcaset];
          destruct_first Hcaset Heqc; rewrite Heqc in *; clear Heqc; simpl.
        + cut (Valid (node v (-1) l r')).
          * rewrite depth_node. rewrite_maxlr. intuition.
          * repeat constructor; intuition.
        + cut (Valid (node v 0 l r')).
          * rewrite depth_node. rewrite_maxlr. intuition.
          * repeat constructor; intuition.
        + rewrite Z.leb_le in e.
          exfalso. intuition.
      - exfalso.
        rewrite Z.leb_gt in e.
        rewrite Z.leb_le  in  e2.
        rewrite Z.abs_eq in e, Habst; try omega.
      - destruct IHp as [IHV IHp]; destruct IHp as [IHdep IHor].
        rewrite Z.leb_gt in e, e2.
        rewrite Z.abs_neq in e; try omega.
        set (valid_depth_case HVt) as Hcaset.
        repeat destruct Hcaset as [Hcaset | Hcaset];
          destruct_first Hcaset Heqc; rewrite Heqc in *; clear Heqc; simpl; try omega.
        clear e e2 Habst.
        set lrotate_balance_depth as Hlrot; clearbody Hlrot.
        specialize (Hlrot v l r').
        destruct Hlrot as [Hx Hy]; auto.
        + constructor; auto; try omega.
          * inversion HVl; auto.
          * inversion IHV; auto.
        + destruct IHor; auto.
          subst; simpl in *.
          set (depth_positive l); omega.
        + split; auto.
          rewrite Hy.
          rewrite depth_node. rewrite_maxlr.
          rewrite depth_node. rewrite_maxlr.
          omega.
    }
    {
      destruct r' as [| rv rc rl rr].
      - exfalso.
        apply (insert_not_leaf A.compare r x).
        rewrite e1; reflexivity.
      - rewrite e1 in IHp.
        inversion HVt using valid_node_inv.
        intros HVl HVr Hdept Habst.
        specialize (IHp HVr).
        destruct IHp as [HVr' Hdep].
        inversion HVr' using valid_node_inv.
        intros HVrl HVrr Hdepr' Habsr'.
        inversion_clear HVrl. inversion_clear HVrr.
        inversion_clear HVl. inversion_clear HVr.
        repeat constructor; intuition.
    }
    {
      rewrite e1 in IHp.
      inversion HVt using valid_node_inv. intros HVl HVr Hdept Habst.
      repeat rewrite depth_node.
      rewrite (proj2 (IHp HVr)).
      reflexivity.
    }
  Qed.

  Theorem insert_spec_in : forall t x y, TIn y (insert t x) <-> x = y \/ TIn y t.
  Proof.
    unfold insert.
    intros.
    apply insert_in.
    clear.
    set (A.compare_spec) as Hspec; clearbody Hspec.
    intros.
    specialize (Hspec x y).
    inversion Hspec; intuition; subst; try solve [discriminate | F.order].
  Qed.

  Theorem insert_spec_avl : forall t x, AVL t -> AVL (insert t x).
  Proof.
    intros.
    inversion_clear H as [HV HST].
    constructor.
    - set (insert_depth x HV) as Hd; clearbody Hd.
      unfold insert.
      destruct (insert' A.compare t x); intuition.
    - unfold insert.
      apply insert_reltree.
      auto.
  Qed.
End AVL.
