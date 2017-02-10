Require Import SetoidClass Orders OrdersFacts Nat.
Require Import Program.
Set Implicit Arguments.

Module Def.
  Declare Module A : UsualOrderedTypeFull.
  Module  F := OrderedTypeFacts A.
  Ltac lt_discriminate := solve [
                              exfalso;
                              (eapply StrictOrder_Irreflexive) + (eapply StrictOrder_Asymmetric);
                              eauto using A.lt_strorder
                            ].

  Inductive Color := B | R.
        
  Inductive Tree : Type :=
  | leaf : Tree
  | node (v : A.t) (c : Color) (l r : Tree) : Tree.

  Inductive In : A.t -> Tree -> Prop :=
  | in_top : forall v c l r, In v (node v c l r)
  | in_ltree : forall x v c l r (Inl : In x l), In x (node v c l r)
  | in_rtree : forall x v c l r (Inr : In x r), In x (node v c l r).
  Hint Constructors In.
  Lemma in_node_iff : forall x v c l r, In x (node v c l r) <-> x = v \/ In x l \/ In x r.
  Proof.
    intros.
    split; inversion 1; subst; intuition.
  Qed.
  Definition Forall (P : A.t -> Prop) (t : Tree) := forall x, In x t -> P x.
  Hint Unfold Forall.
  Lemma Forall_leaf : forall P, Forall P leaf.
  Proof.
    intros.
    intro.
    inversion 1.
  Qed.
  Hint Resolve Forall_leaf.
  
  Definition color t := match t with
                        | leaf => B
                        | node _ c _ _  => c
                        end.
  
  Lemma color_red_inv : forall t (P : Tree -> Prop),
      (forall v l r , t = node v R l r -> P t) -> color t = R -> P t.
  Proof.
    intros t p H Hc.
    destruct t; simpl in Hc; try discriminate.
    subst.
    specialize (H v t1 t2).
    auto.
  Qed.
  
  
  Inductive BlackCount : Tree -> nat -> Prop :=
  | bc_leaf : BlackCount leaf 0
  | bc_bnode : forall v l r n 
                      (Bl : BlackCount l n) (Br : BlackCount r n),
      BlackCount (node v B l r) (S n)
  | bc_rnode : forall v l r n
                      (Bl : BlackCount l n) (Br : BlackCount r n)
                      (Cl : color l = B) (Cr : color r = B),
      BlackCount (node v R l r) n.
  Hint Constructors BlackCount.

  Derive Inversion_clear bc_node_inv with (forall v c l r n, BlackCount (node v c l r) n) Sort Prop.
  Derive Inversion_clear bc_black_inv with (forall v l r n, BlackCount (node v B l r) n) Sort Prop.
  Derive Inversion_clear bc_red_inv with (forall v l r n, BlackCount (node v R l r) n) Sort Prop.

  
  Inductive Balanced : Tree -> Prop :=
  | balanced n t : BlackCount t n -> Balanced t.
  Hint Constructors Balanced.

  Lemma blackcount_uniq : forall t n m, BlackCount t n -> BlackCount t m -> n = m.
  Proof.
    intros t.
    induction t; intros n m Hn Hm.
    - inversion Hn; inversion Hm.
      reflexivity.
    - inversion Hn; inversion Hm; subst; try discriminate; auto.
  Qed.
  
  Inductive RelTree (Rel : relation A.t) : Tree -> Prop :=
  | rel_leaf : RelTree Rel leaf
  | rel_node v c l r 
             (Rl : RelTree Rel l) (Rr : RelTree Rel r)
             (L : Forall (fun x => Rel x v) l)
             (G : Forall (fun x => Rel v x) r) : RelTree Rel (node v c l r).
  Hint Constructors RelTree.

  Lemma rel_color_irr : forall R c c' v l r, RelTree R (node v c l r) -> RelTree R (node v c' l r).
  Proof.
    intros.
    inversion H; subst.
    auto.
  Qed.
  Hint Immediate rel_color_irr.

  Inductive ValidRBT : Tree -> Prop :=
  | validrbt t : RelTree A.lt t -> Balanced t -> color t = B -> ValidRBT t.
  Hint Constructors ValidRBT.
End Def.

Module BasicOps.
  Declare Module A : UsualOrderedTypeFull.
  Export Def.

  Fixpoint flipt t :=
    match t with
    | leaf => leaf
    | node v c l r => node v c (flipt r) (flipt l)
    end.
  Functional Scheme flipt_ind := Induction for flipt Sort Prop.

  Lemma flipt_involutive : forall t, flipt (flipt t) = t.
  Proof.
    induction t; simpl; eauto.
    rewrite IHt1, IHt2.
    reflexivity.
  Qed.
  Hint Rewrite flipt_involutive : flipt_rewrite.


  Lemma flipt_color : forall t, color (flipt t) = color t.
  Proof.
    intros.
    destruct t; reflexivity.
  Qed.
  Hint Rewrite flipt_color : flip_rewrite.

  Lemma flipt_in : forall x t, In x (flipt t) <-> In x t.
  Proof.
    intros.
    induction t; split; intro H; inversion H; subst; simpl; eauto.
    - rewrite IHt2 in *; auto.
    - rewrite IHt1 in *; auto.
    - rewrite <- IHt1 in *; auto.
    - rewrite <- IHt2 in *; auto.
  Qed.
  Hint Rewrite flipt_in : flip_rewrite.
  Hint Resolve -> flipt_in.
  Hint Resolve <- flipt_in.

  Lemma flipt_bc : forall t n, BlackCount (flipt t) n <->  BlackCount t n.
  Proof.
    intros t.
    induction t; intro n.
    - simpl.
      reflexivity.
    - simpl.
      split; intro H; inversion H; subst.
      + constructor.
        * rewrite <- IHt1; auto.
        * rewrite <- IHt2; auto.
      + constructor.
        * rewrite <- IHt1; auto.
        * rewrite <- IHt2; auto.
        * autorewrite with flip_rewrite in *; auto.
        * autorewrite with flip_rewrite in *; auto.
      + constructor.
        * rewrite IHt2; auto.
        * rewrite IHt1; auto.
      + constructor.
        * rewrite IHt2; auto.
        * rewrite IHt1; auto.
        * autorewrite with flip_rewrite in *; auto.
        * autorewrite with flip_rewrite in *; auto.
  Qed.
  Hint Rewrite flipt_bc : flip_rewrite.
  Hint Resolve -> flipt_bc.
  Hint Resolve <- flipt_bc.
  

  Lemma flipt_balanced : forall t, Balanced (flipt t) <-> Balanced t.
  Proof.
    intros.
    split; intro H; inversion H; subst.
    - rewrite flipt_bc in *.
      eauto.
    - rewrite <- flipt_bc in *.
      eauto.
  Qed.
  Hint Rewrite flipt_balanced : flip_rewrite.
  Hint Resolve -> flipt_balanced.
  Hint Resolve <- flipt_balanced.

  Lemma flipt_rel : forall Rel t, RelTree (flip Rel) (flipt t) <-> RelTree Rel t.
  Proof.
    intros.
    induction t; split; inversion 1; subst; simpl in *; eauto.
    - rewrite IHt1, IHt2 in *.
      constructor; auto.
      + repeat  intro.
        apply G; auto.
      + repeat  intro.
        apply L; auto.
    - rewrite <- IHt1, <- IHt2 in *.
      constructor; auto.
      + repeat intro.
        apply G.
        auto.
      + repeat intro.
        apply L.
        auto.
  Qed.
  
  Definition rrot (t : Tree) :=
    match t with
    | leaf => t
    | node v c l r =>
      match l with
      | leaf => t
      | node lv lc ll lr => node lv lc ll (node v c lr r)
      end
    end.
  Functional Scheme rrot_ind := Induction for rrot Sort Prop.
  
  Definition lrot (t : Tree) :=
    match t with
    | leaf => t
    | node v c l r =>
      match r with
      | leaf => t
      | node rv rc rl rr => node rv rc (node v c l rl) rr
      end
    end.
  Functional Scheme lrot_ind := Induction for lrot Sort Prop.
  
  Lemma flipt_rrot : forall t, flipt (lrot (flipt t)) = rrot t.
  Proof.
    intros t.
    functional induction (rrot t); auto; simpl.
    - rewrite flipt_involutive; reflexivity.
    - repeat rewrite flipt_involutive; reflexivity.
  Qed.

  Lemma flipt_lrot : forall t, flipt (rrot (flipt t)) = lrot t.
  Proof.
    intros.
    rewrite <- flipt_rrot.
    repeat rewrite flipt_involutive; reflexivity.
  Qed.

  Lemma rrot_in : forall x t, In x (rrot t) <-> In x t.
  Proof.
    intros x t.
    functional induction (rrot t); split; inversion 1; auto; subst.
    - inversion Inr; auto.
    - inversion Inl; auto.
  Qed.
  
  Lemma lrot_in : forall x t, In x (lrot t) <-> In x t.
  Proof.
    intros.
    rewrite <- flipt_lrot.
    rewrite flipt_in, rrot_in, flipt_in.
    reflexivity.
  Qed.

  Lemma rrot_rel : forall Rel `{Transitive A.t Rel} t, RelTree Rel t -> RelTree Rel (rrot t).
  Proof.
    intros Rel Htr t HRt.
    functional induction (rrot t); auto.
    inversion_clear HRt; subst.
    inversion_clear Rl; subst.
    constructor; auto.
    intros x Hin.
    inversion_clear Hin; subst; auto.
    apply Htr with v; auto.
  Qed.

  Lemma lrot_rel : forall Rel `{Transitive A.t Rel} t, RelTree Rel t -> RelTree Rel (lrot t).
  Proof.
    intros Rel Htr t HRt.
    functional induction (lrot t); auto.
    inversion_clear HRt; subst.
    inversion_clear Rr; subst.
    constructor; auto.
    intros x Hin.
    inversion_clear Hin; subst; auto.
    apply Htr with v; auto.
  Qed.
End BasicOps.

Module Balance.
  Declare Module A : UsualOrderedTypeFull.
  Import BasicOps.

  Definition paint cp cc t :=
    match t with
    | node v _ (node lv _ ll lr) (node rv _ rl rr) => node v cp (node lv cc ll lr) (node rv cc rl rr)
    | _ => t
    end.
  Functional Scheme paint_ind := Induction for paint Sort Prop.
    
  Lemma paint_in : forall x t cp cc, In x (paint cp cc t) <-> In x t.
  Proof.
    intros.
    functional induction (paint cp cc t); intuition.
    - inversion_clear H; auto; subst.
      + inversion_clear Inl; auto.
      + inversion_clear Inr; auto.
    - inversion_clear H; auto; subst.
      + inversion_clear Inl; auto.
      + inversion_clear Inr; auto.
  Qed.

  Lemma paint_rel : forall Rel t cp cc, RelTree Rel t  -> RelTree Rel (paint cp cc t).
  Proof.
    intros Rel t cp cc HR.
    functional induction (paint cp cc t); auto.
    inversion_clear HR; subst.
    inversion_clear Rl; inversion_clear Rr.
    repeat constructor; auto.
    - intros x Hin.
      apply L.
      inversion Hin; auto.
    - intros x Hin.
      apply G.
      inversion Hin; auto.
  Qed.

  Lemma flipt_paint : forall t cp cc, paint cp cc (flipt t) = flipt (paint cp cc t).
  Proof.
    intros.
    functional induction (paint cp cc t); trivial.
    destruct r; simpl paint; auto.
  Qed.
  
  Definition balance_ll t := paint B R (rrot t).

  Lemma balance_ll_in : forall x t, In x (balance_ll t) <-> In x t.
  Proof.
    intros.
    unfold balance_ll.
    rewrite paint_in.
    rewrite rrot_in.
    reflexivity.
  Qed.

  Lemma balance_ll_rel : forall Rel `{Transitive A.t Rel} t,
      RelTree Rel t -> RelTree Rel (balance_ll t).
  Proof.
    intros Rel Tr t HR.
    unfold balance_ll.
    apply paint_rel.
    apply rrot_rel; auto.
  Qed.

  Definition Black t n := color t = B /\ BlackCount t n.
  
  Lemma balance_ll_balanced : forall
      v lv llv lll llr lr r n,
      Black lll n -> Black llr n -> Black lr n -> Black r n ->
      Black (balance_ll (node v B
                              (node lv R 
                                    (node llv R lll llr)
                                    lr)
                              r)) (S n).
  Proof.
    intros until n.
    intros HBlll HBllr HBlr HBr.
    simpl.
    unfold Black.
    split; auto.
    unfold Black in *.
    repeat constructor; intuition.
  Qed.

  Definition balance_lr t :=
    match t with
    | leaf => leaf
    | node v c l r => paint B R (rrot (node v c (lrot l) r))
    end.
  
  
  Lemma balance_lr_in : forall x t, In x (balance_lr t) <-> In x t.
  Proof.
    intros.
    destruct t; try reflexivity.
    unfold balance_lr.
    rewrite paint_in, rrot_in.
    rewrite in_node_iff, lrot_in.
    rewrite in_node_iff; reflexivity.
  Qed.
  

  Lemma balance_lr_rel : forall Rel `{Transitive A.t Rel} t,
      RelTree Rel t -> RelTree Rel (balance_lr t).
  Proof.
    intros Rel Tr t HR.
    destruct t; trivial.
    apply paint_rel.
    apply rrot_rel; auto.
    inversion_clear HR.
    constructor; auto.
    - apply lrot_rel; auto.
    - intros x Hin.
      apply L.
      apply lrot_in.
      assumption.
  Qed.

  Lemma balance_lr_balanced : forall v lv ll lrv lrl lrr r n,
      Black ll n -> Black lrl n -> Black lrr n -> Black r n ->
      Black
        (balance_lr (node v B
                          (node lv R 
                                ll
                                (node lrv R lrl lrr)
                          ) r)) (S n).
  Proof.
    intros until n.
    intros HBll HBlrl HBlrr HBr.
    split; auto.
    unfold Black in *.
    repeat constructor; intuition.
  Qed.

  Definition balance_rr t := paint B R (lrot t).
  Definition balance_rl t :=
    match t with
    | leaf => leaf
    | node v c l r => paint B R (lrot (node v c l (rrot r)))
    end.

  Lemma flipt_balance_rr : forall t, flipt (balance_rr (flipt t)) = balance_ll t.
  Proof.
    intros.
    unfold balance_rr, balance_ll.
    rewrite <- flipt_paint.
    rewrite flipt_rrot.
    reflexivity.
  Qed.

  Lemma flipt_balance_rl : forall t, flipt (balance_rl (flipt t)) = balance_lr t.
  Proof.
    intros.
    destruct t; trivial.
    rewrite (flipt_equation (node v c t1 t2)).
    unfold balance_rl, balance_lr.
    rewrite <- flipt_paint.
    rewrite <- flipt_lrot.
    rewrite flipt_involutive.
    rewrite flipt_equation.
    repeat rewrite flipt_involutive.
    rewrite flipt_lrot.
    reflexivity.
  Qed.


  Lemma balance_rl_in : forall x t, In x (balance_rl t) <-> In x t.
  Proof.
    intros.
    unfold balance_rl.
    destruct t.
    - reflexivity.
    - rewrite paint_in, lrot_in.
      rewrite in_node_iff, rrot_in.
      intuition; subst; auto.
      inversion H; auto.
  Qed.
  Lemma balance_rr_in : forall x t, In x (balance_rr t) <-> In x t.
  Proof.
    intros.
    unfold balance_rr.
    destruct t.
    - reflexivity.
    - rewrite paint_in, lrot_in.
      reflexivity.
  Qed.


  Lemma balance_rl_rel : forall Rel `{Transitive A.t Rel} t,
      RelTree Rel t -> RelTree Rel (balance_rl t).
  Proof.
    intros Rel Tr t HR.
    destruct t; trivial.
    apply paint_rel.
    apply lrot_rel; auto.
    inversion_clear HR.
    constructor; auto.
    - apply rrot_rel; auto.
    - intros x Hin.
      apply G.
      apply rrot_in.
      assumption.
  Qed.
  
  
  Lemma balance_rr_rel : forall Rel `{Transitive A.t Rel} t,
      RelTree Rel t -> RelTree Rel (balance_rr t).
  Proof.
    intros Rel Tr t HR.
    unfold balance_rr.
    apply paint_rel.
    apply lrot_rel; auto.
  Qed.

  Inductive InsertResult := Ok | Inserted | Collapsed.

  Inductive SemiBalanced : Tree -> nat -> Prop :=
  | sb_l v l r n (BL : BlackCount l n)  (BR : BlackCount r n)
         (HLRed : color l = R) (HRBlack : color r = B) : SemiBalanced (node v R l r) n
  | sb_r v l r n (BL : BlackCount l n)  (BR : BlackCount r n)
         (HLBlack : color l = B) (HRRed : color r = R) : SemiBalanced (node v R l r) n.
  Hint Constructors SemiBalanced.
  
  Definition left_balance v l r :=
    match color r with
    | R => (paint R B (node v R l r), Inserted)
    | B => match l with
           | node lv R ll lr =>
             match color ll with
             | R => (balance_ll (node v B l r), Ok)
             | B => (balance_lr (node v B l r), Ok)
             end
           | _ => (node v B l r, Collapsed) (* shouldn't reach *)
           end
    end.
  Functional Scheme left_balance_ind := Induction for left_balance Sort Prop.

  Definition right_balance v l r :=
    match color l with
    | R => (paint R B (node v R l r), Inserted)
    | B => match r with
           | node rv R rl rr =>
             match color rr with
             | R => (balance_rr (node v B l r), Ok)
             | B => (balance_rl (node v B l r), Ok)
             end
           | _ => (node v B l r, Collapsed) (* shouldn't reach *)
           end
    end.
  Functional Scheme right_balance_ind := Induction for right_balance Sort Prop.

  Lemma left_balance_in :
    forall c v l r x, In x (node v c l r) <-> In x (fst (left_balance v l r)).
  Proof.
    intros.
    functional induction (left_balance v l r); unfold fst.
    - split; inversion 1; eauto.
    - split; inversion 1; eauto.
    - rewrite balance_lr_in.
      split; inversion 1; eauto.
    - rewrite balance_ll_in.
      split; inversion 1; eauto.
    - rewrite paint_in.
      split; inversion 1; eauto.
  Qed.

  
  Lemma right_balance_in :
    forall c v l r x, In x (node v c l r) <-> In x (fst (right_balance v l r)).
  Proof.
    intros.
    functional induction (right_balance v l r); unfold fst.
    - split; inversion 1; eauto.
    - split; inversion 1; eauto.
    - rewrite balance_rl_in.
      split; inversion 1; eauto.
    - rewrite balance_rr_in.
      split; inversion 1; eauto.
    - rewrite paint_in.
      split; inversion 1; eauto.
  Qed.


  Lemma left_balance_rel : forall Rel `{Transitive A.t Rel} c v l r,
      RelTree Rel (node v c l r) -> RelTree Rel (fst (left_balance v l r)).
  Proof.
    intros.
    functional induction (left_balance v l r); unfold fst;
      eauto using balance_lr_rel, balance_ll_rel, paint_rel.
  Qed.
  Lemma right_balance_rel : forall Rel `{Transitive A.t Rel} c v l r,
      RelTree Rel (node v c l r) -> RelTree Rel (fst (right_balance v l r)).
  Proof.
    intros.
    functional induction (right_balance v l r); unfold fst;
      eauto using balance_rl_rel, balance_rr_rel, paint_rel.
  Qed.
  
  

  Fixpoint insert' (x : A.t) (t : Tree) : (Tree * InsertResult) :=
    match t with
    | leaf => (node x R leaf leaf, Inserted)
    | node v c l r =>
      match A.compare x v with
      | Eq => (t, Ok)
      | Lt => match insert' x l with
              | (l', Ok) => (node v c l' r, Ok)
              | (l', Inserted) =>
                match c with
                | R => (node v c l' r, Collapsed)
                | B => (node v c l' r, Ok)
                end
              | (l', Collapsed) => left_balance v l' r
              end
      | Gt => match insert' x r with
              | (r', Ok) => (node v c l r', Ok)
              | (r', Inserted) =>
                match c with
                | R => (node v c l r', Collapsed)
                | B => (node v c l r', Ok)
                end
              | (r', Collapsed) => right_balance v l r'
             end
      end
    end.
  Functional Scheme insert'_ind := Induction for insert' Sort Prop.
  
  Lemma insert'_in : forall a x t, In a (fst (insert' x t)) <-> a = x \/ In a t.
  Proof.
    intros a x t.
    induction t; [| case_eq (A.compare x v); intro Hcmp]; simpl.
    - split; inversion 1; subst; intuition.
    - rewrite Hcmp.
      simpl.
      rewrite F.compare_eq_iff in Hcmp. subst.
      split; inversion 1; subst; intuition.
    - rewrite Hcmp.
      cut (In a (node v c (fst (insert' x t1)) t2) <-> a = x \/ In a (node v c t1 t2)).
      + intro Hiff.
        rewrite <- Hiff.
        destruct (insert' x t1) as [l' i].
        destruct i; try reflexivity.
        * destruct c; reflexivity.
        * rewrite left_balance_in.
          reflexivity.
      + repeat rewrite in_node_iff.
        rewrite IHt1.
        intuition.
    - rewrite Hcmp.
      cut (In a (node v c t1 (fst (insert' x t2))) <-> a = x \/ In a (node v c t1 t2)).
      + intro Hiff.
        rewrite <- Hiff.
        destruct (insert' x t2) as [r' i].
        destruct i; try reflexivity.
        * destruct c; reflexivity.
        * rewrite right_balance_in.
          reflexivity.
      + repeat rewrite in_node_iff.
        rewrite IHt2.
        intuition.
  Qed.

  Lemma insert'_in2 : forall a x t t' i, insert' x t = (t', i) ->
                                         (In a t' <-> a = x \/ In a t).
  Proof.
    intros.
    rewrite <- insert'_in.
    rewrite H.
    unfold fst.
    reflexivity.
  Qed.
  
  Lemma insert'_rel : forall  x t,
      RelTree A.lt t -> RelTree A.lt (fst (insert' x t)).
  Proof.
    intros x t HR.
    induction t; try solve [simpl; auto].
    rewrite insert'_equation.
    case_eq (A.compare x v); intro Hcmp; inversion Hcmp;
      try rewrite F.compare_lt_iff in *;
      try rewrite F.compare_eq_iff in *;
        try rewrite F.compare_gt_iff in *.
    - auto.
    - cut (RelTree A.lt (node v c (fst (insert' x t1)) t2)).
      + intro H.
        destruct (insert' x t1) as [l' i].
        simpl in *.
        destruct i; [|destruct c|]; auto.
        apply left_balance_rel with c; auto.
        apply A.lt_strorder.
      + inversion_clear HR. intuition.
        constructor; auto.
        intro a.
        rewrite insert'_in.
        inversion 1; subst; auto.
    - cut (RelTree A.lt (node v c t1 (fst (insert' x t2)))).
      + intro H.
        destruct (insert' x t2) as [r' i].
        simpl in *.
        destruct i; [|destruct c|]; auto.
        apply right_balance_rel with c; auto.
        apply A.lt_strorder.
      + inversion_clear HR. intuition.
        constructor; auto.
        intro a.
        rewrite insert'_in.
        inversion 1; subst; auto.
  Qed.  
  
  Lemma insert'_spec : forall x t n, BlackCount t n ->
      match insert' x t with
      | (t', Ok) => BlackCount t' n /\ color t = color t'
      | (t', Inserted) => BlackCount t' n /\ color t = B /\ color t' = R
      | (t', Collapsed) => SemiBalanced t' n /\ color t = R
      end.
  Proof.
    intros x t.
    functional induction (insert' x t); intros n HBC; auto.
    - split; auto.
      rewrite e1 in IHp.
      inversion HBC using bc_node_inv.
      + intros m HBl HBr.
        edestruct IHp as [HBl' Hcl']; eauto.
      + intros HBl HBr Hcl Hcr.
        edestruct IHp as [HBl' Hcl']; eauto.
        constructor; auto.
        congruence.
    - split; auto.
      rewrite e1 in IHp.
      inversion HBC using bc_black_inv.
      intros m HBl HBr.
      edestruct IHp as [HBl' Hcl']; eauto.
    - rewrite e1 in IHp.
      inversion HBC using bc_red_inv.
      intros HBl HBr Hcl Hcr.
      edestruct IHp as [HBl' Hcl']; eauto.
      intuition.
    - rewrite e1 in IHp.
      assert (c = B); subst. {
        destruct c; auto.
        inversion HBC using bc_red_inv.
        intros HBl HBr Hcl Hcr.
        edestruct IHp as [Hbl' Hcl']; eauto; congruence.
      }
      inversion HBC using bc_black_inv.
      intros m HBl HBr.
      edestruct IHp as [Hbl' _]; eauto.

      functional induction (left_balance v l' r);
        inversion_clear  Hbl' as [lv' ll' lr' m'| lv' ll' lr' m']; try congruence.
      + inversion HRRed using color_red_inv; intros; subst.
        inversion BR; subst.
        repeat constructor; intuition.
      + inversion HLRed using color_red_inv; intros; subst.
        inversion BL; subst.
        repeat constructor; intuition.
      + inversion e using color_red_inv; intros; subst.
        inversion HBr; subst.
        repeat constructor; intuition.
      + inversion e using color_red_inv; intros; subst.
        inversion HBr.
        repeat constructor; intuition.
    - split; auto.
      rewrite e1 in IHp.
      inversion HBC using bc_node_inv.
      + intros m HBl HBr.
        edestruct IHp as [HBl' Hcl']; eauto.
      + intros HBl HBr Hcl Hcr.
        edestruct IHp as [HBl' Hcl']; eauto.
        constructor; auto.
        congruence.
    - split; auto.
      rewrite e1 in IHp.
      inversion HBC using bc_black_inv.
      intros m HBl HBr.
      edestruct IHp as [HBl' Hcl']; eauto.
    - rewrite e1 in IHp.
      inversion HBC using bc_red_inv.
      intros HBl HBr Hcl Hcr.
      edestruct IHp as [HBl' Hcl']; eauto.
      intuition.
    - rewrite e1 in IHp.
      assert (c = B); subst. {
        destruct c; auto.
        inversion HBC using bc_red_inv.
        intros HBl HBr Hcl Hcr.
        edestruct IHp as [Hbl' Hcl']; eauto; congruence.
      }
      inversion HBC using bc_black_inv.
      intros m HBl HBr.
      edestruct IHp as [Hbr' _]; eauto.
      functional induction (right_balance v l r');
        inversion_clear  Hbr' as [rv' rl' rr' m'| rv' rl' rr' m']; try congruence.
      + inversion HLRed using color_red_inv; intros; subst.
        inversion BL; subst.
        repeat constructor; intuition.
      + inversion HRRed using color_red_inv; intros; subst.
        inversion BR; subst.
        repeat constructor; intuition.
      + inversion e using color_red_inv; intros; subst.
        inversion HBl; subst.
        repeat constructor; intuition.
      + inversion e using color_red_inv; intros; subst.
        inversion HBl.
        repeat constructor; intuition.
  Qed.

  Lemma insert'_not_leaf : forall x t i, insert' x t <> (leaf, i).
  Proof.
    intros.
    cut (In x (fst (insert' x t))).
    - intro H.
      intro Heq.
      rewrite Heq in H.
      simpl in H.
      inversion H.
    - rewrite insert'_in.
      auto.
  Qed.
  
  Definition insert x t := let (t', _) := insert' x t in
                           match t' with
                           | leaf => leaf
                           | node v _ l r => node v B l r
                           end.
  Theorem insert_in : forall a x t, In a (insert x t) <-> a = x \/ In a t.
  Proof.
    intros.
    rewrite <- insert'_in.
    remember (insert x t) as t'.

    unfold insert in Heqt'.
    destruct (insert' x t) as [t'' i].
    simpl.
    destruct t'' as [| v c l r]; subst.
    - reflexivity.
    - split; inversion 1; eauto.
  Qed.

  Theorem insert_rbt :
    forall x t, ValidRBT t -> ValidRBT (insert x t).
  Proof.
    intros x t HV.
    inversion_clear  HV as [t' HR HB HC].
    constructor.
    - unfold insert.
      remember (insert' x t) as p.
      destruct p as [t' i].
      destruct t' as [| v c l r]; auto.
      apply rel_color_irr with c.
      fold (fst (node v c l r, i)).
      rewrite Heqp.
      apply insert'_rel.
      auto.
    - inversion_clear HB as [n ?t HBC].
      remember (insert x t) as t'.
      unfold insert in Heqt'.
      set (insert'_spec x HBC) as Hspec. clearbody Hspec.
      case_eq (insert' x t).
      intros t'' i Heqinsert'.
      rewrite Heqinsert' in *.
      case_eq i; intro Hcase; rewrite Hcase in *.
      + replace t' with t''.
        * apply (@balanced n).
          intuition.
        * rewrite HC in *.
          apply proj2 in Hspec.
          destruct t'' as [| v c l r]; auto.
          simpl in Hspec.
          congruence.
      + apply (@balanced (S n)).
        destruct t'' as  [| v c l r].
        * simpl in Hspec.
          intuition. discriminate.
        * subst.
          destruct Hspec as [HBC' Hcl].
          destruct Hcl as [_ Hcl].
          simpl in Hcl. subst.
          inversion HBC'; subst.
          constructor; auto.
      + destruct Hspec.
        congruence.
    - unfold insert.
      destruct (insert' x t) as [t' _].
      destruct t'; auto.
  Qed.    
