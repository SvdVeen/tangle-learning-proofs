theory Attractors
  imports Main ParityGames
begin

chapter \<open>Attractors\<close>
section \<open>Attractors for Arbitrary Players\<close>
(** We first define attractors in the context player_paritygame so we can prove properties for any
    player. *)
context player_paritygame begin
(** A maximal attractor for a target set. *)
inductive_set player_attractor :: "'v set \<Rightarrow> 'v set" for X where
  base: "x \<in> X \<Longrightarrow> x \<in> player_attractor X"
| own: "\<lbrakk> x \<in> V\<^sub>\<alpha>-X; (x,y)\<in>E; y\<in>player_attractor X \<rbrakk> \<Longrightarrow> x \<in> player_attractor X"
| opponent: "\<lbrakk> x\<in>V\<^sub>\<beta>-X; \<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>player_attractor X \<rbrakk> \<Longrightarrow> x \<in> player_attractor X"

(** The target set X is a subset of its maximal attractor. *)
lemma player_attractor_subset[simp]: "X \<subseteq> player_attractor X"
  by (auto intro: base)

(** Every node not part of the maximal attractor still has at least one successor. *)
lemma notin_player_attractor_succ: "\<lbrakk>v\<in>V; v \<notin> player_attractor X\<rbrakk> \<Longrightarrow> E `` {v} - player_attractor X \<noteq> {}"
  using player_attractor.simps succ V\<^sub>\<alpha>_subset by fast

(** A player's attractor is maximal; no player nodes have a successor in the attractor. *)
lemma player_attractor_max_player: "\<lbrakk>v\<in>V\<^sub>\<alpha>; v \<notin> player_attractor X\<rbrakk> \<Longrightarrow> \<forall>w \<in> E `` {v}. w \<notin> player_attractor X"
  using player_attractor.simps by fast

(** An opponent's attractor is maximal: no opponent nodes have a successor in the attractor. *)
lemma player_attractor_max_opponent: "\<lbrakk>v\<in>V\<^sub>\<beta>; v \<notin> player_attractor X\<rbrakk> \<Longrightarrow> \<exists>w \<in> E `` {v}. w \<notin> player_attractor X"
  using player_attractor.simps by fast

context
  fixes X :: "'v set"
begin
(** To prove important properties of attractors, we need to reason with ranks. *)
  fun nodes_in_rank :: "nat \<Rightarrow> 'v set" where
    "nodes_in_rank 0 = X"
  | "nodes_in_rank (Suc n) =
     nodes_in_rank n
     \<union> { x | x y. x\<in>V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>nodes_in_rank n }
     \<union> { x. x\<in>V\<^sub>\<beta> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>nodes_in_rank n) }"

  (** nodes_in_rank is monotonous. *)
  lemma nodes_in_rank_mono: "n\<le>m \<Longrightarrow> nodes_in_rank n \<subseteq> nodes_in_rank m"
    apply (induction m)
    by (auto simp: le_Suc_eq)

  (** X is a subset of nodes_in_rank. *)
  lemma nodes_in_rank_subset: "X \<subseteq> nodes_in_rank n"
    using nodes_in_rank.simps(1) nodes_in_rank_mono by blast

  (** nodes_in_rank is a subset of the maximal attractor. *)
  lemma nodes_in_rank_ss_player_attractor: "nodes_in_rank n \<subseteq> player_attractor X"
    apply (induction n)
    by (auto intro: player_attractor.intros)

  (** There is a rank that contains all nodes in the maximal attractor. *)
  lemma player_attractor_ss_nodes_in_rank: "x\<in>player_attractor X \<Longrightarrow> (\<exists>n. x\<in>nodes_in_rank n)"
  proof (induction rule: player_attractor.induct)
    case (base x) thus ?case using nodes_in_rank.simps(1) by fast
  next
    case (own x y) thus ?case using nodes_in_rank.simps(2) by blast
  next
    case (opponent x)
    define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> nodes_in_rank n"
    define n_max where "n_max \<equiv> MAX y\<in>E``{x}. n_of_y y"
    have FIN: "finite (n_of_y ` E `` {x})" by auto

    have n_of_y: "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank (n_of_y y)" for y
      unfolding n_of_y_def using opponent.IH by (auto intro: someI)

    have "(x,y)\<in>E \<Longrightarrow> (\<exists>i\<le>n_max. y\<in>nodes_in_rank i)" for y
      using Max_ge[OF FIN] n_of_y unfolding n_max_def by blast
    hence "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank n_max" for y
      using nodes_in_rank_mono by auto
    thus ?case
      apply (rule_tac exI[where x="Suc n_max"])
      using opponent.hyps by simp
  qed

  (** The maximal attractor is the union of all ranks. *)
  lemma player_attractor_eq_nodes_in_rank: "player_attractor X = \<Union>(nodes_in_rank`UNIV)"
    using player_attractor_ss_nodes_in_rank nodes_in_rank_ss_player_attractor by auto

  (** All edges in a rank n lead to at most the same rank. *)
  lemma nodes_in_rank_edges_same: "\<lbrakk>x \<in> nodes_in_rank n; x \<notin> X; (x, y) \<in> E; x \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y \<in> nodes_in_rank n"
    apply (induction n) by auto

  (** All edges in a rank n lead to a lower rank. *)
  lemma nodes_in_rank_edges_lower: "\<lbrakk>x \<in> nodes_in_rank (Suc n); x \<notin> X; (x,y) \<in> E; x \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y \<in> nodes_in_rank n"
    apply (induction n arbitrary: x) by auto

  (** There exists a strategy for nodes_in_rank that forces all plays in the rank to go to X. *)
  lemma nodes_in_rank_forces_X: "\<exists>\<sigma>.
    strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = (nodes_in_rank n - X) \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> nodes_in_rank n
    \<and> (\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_subgraph V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))
    \<and> (\<forall>x\<in>nodes_in_rank n. \<forall>xs z. path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z \<and> n<length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
  proof (induction n)
    case 0 thus ?case
      apply (rule_tac exI[where x=Map.empty])
      apply (intro conjI; simp)
        subgoal using nodes_in_rank_edges_same by blast
        subgoal using origin_in_path by fastforce
      done

  next
    case (Suc n)
    from Suc.IH obtain \<sigma> where
      strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
      dom_\<sigma>: "dom \<sigma> = (nodes_in_rank n - X) \<inter> V\<^sub>\<alpha>" and
      ran_\<sigma>: "ran \<sigma> \<subseteq> nodes_in_rank n" and
      closed_\<sigma>: "(\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_subgraph V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))" and
      forces_\<sigma>: "\<And>x xs z. \<lbrakk>x\<in>nodes_in_rank n; path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z; n < length xs\<rbrakk> \<Longrightarrow> set xs \<inter> X \<noteq> {}"
      by blast

    define new_player_nodes where "new_player_nodes = (nodes_in_rank (Suc n) - nodes_in_rank n) \<inter> V\<^sub>\<alpha>"
    define target where "target = (\<lambda>x. SOME x'. x'\<in>nodes_in_rank n \<and> (x,x')\<in>E)"

    {
      fix x
      assume "x\<in>new_player_nodes"
      hence "target x\<in>nodes_in_rank n" "(x,target x)\<in>E"
        unfolding new_player_nodes_def
        apply simp_all
        using some_eq_imp[of _ "target x"]
        unfolding target_def by blast+
    } note target=this

    have target_eq: "x\<in>new_player_nodes \<longleftrightarrow> (x\<in>nodes_in_rank (Suc n) \<and> x\<in>V\<^sub>\<alpha> \<and> x\<notin>nodes_in_rank n \<and> target x\<in>nodes_in_rank n\<and> (x,target x)\<in>E)" for x
      unfolding new_player_nodes_def
      apply (rule iffI; simp)
      using some_eq_imp[of _ "target x"]
      unfolding target_def by blast+

    define \<sigma>' where "\<sigma>' = (\<lambda>x. if x \<in> new_player_nodes then Some (target x) else \<sigma> x)"
    show ?case
    proof (intro exI[where x=\<sigma>'] conjI allI ballI impI; (elim conjE)?)
      show "strategy_of V\<^sub>\<alpha> \<sigma>'"
        using strat_\<sigma>
        unfolding \<sigma>'_def strategy_of_def E_of_strat_def
        apply (safe; simp split: if_splits)
        using target_eq by blast+

      show "dom \<sigma>' = (nodes_in_rank (Suc n) - X) \<inter> V\<^sub>\<alpha>"
        unfolding \<sigma>'_def
        using dom_\<sigma>
        apply (safe; simp add: new_player_nodes_def split: if_splits)
        using nodes_in_rank_subset by fastforce+

      have "\<forall>x y. \<sigma>' x = Some y \<longrightarrow> y \<in> nodes_in_rank (Suc n)"
      proof (intro allI; rule impI)
        fix x y
        assume \<sigma>'_x_to_y: "\<sigma>' x = Some y"
        consider "x \<in> new_player_nodes" | "x \<notin> new_player_nodes" by blast
        thus "y \<in> nodes_in_rank (Suc n)" proof cases
          case 1 with \<sigma>'_x_to_y show ?thesis
            unfolding \<sigma>'_def
            apply (simp split: if_splits)
            using target by blast
        next
          case 2 with \<sigma>'_x_to_y ran_\<sigma> show ?thesis
            unfolding \<sigma>'_def
            by (simp add: ranI subsetD split: if_splits)
        qed
      qed
      thus "ran \<sigma>' \<subseteq> nodes_in_rank (Suc n)"
        unfolding ran_def by blast

      {
        fix n' x' y'
        assume "x' \<in> nodes_in_rank n' - X" "y' \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>' `` {x'}"
        thus "y' \<in> nodes_in_rank n'"
          using closed_\<sigma> nodes_in_rank_mono
          unfolding \<sigma>'_def induced_subgraph_def E_of_strat_def
          apply (simp split: if_splits)
          apply (simp add: target_eq)
          by (meson in_mono nle_le)
      } note closed_\<sigma>'=this

      {
        fix x xs z
        assume "x\<in>nodes_in_rank n"
          and "path (induced_subgraph V\<^sub>\<alpha> \<sigma>') x xs z"
          and "X \<inter> set xs = {}"
        hence "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z"
        proof (induction xs arbitrary: x)
          case Nil thus ?case by fastforce
        next
          case (Cons a xs')

          from Cons(3) have a_is_x[simp]: "a=x" by simp
          with Cons obtain x' where x'_edge: "(x,x') \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>'"
            and x'_path_\<sigma>': "path (induced_subgraph V\<^sub>\<alpha> \<sigma>')  x' xs' z" by auto

          from x'_edge closed_\<sigma>' have "x' \<in> nodes_in_rank n"
            using Cons.prems(1) Cons.prems(3) by auto
          from Cons.IH[OF this x'_path_\<sigma>'] Cons.prems have x'_path_\<sigma>:
            "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x' xs' z" by simp

          from Cons.prems(1) x'_edge have "(x,x') \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>"
            unfolding \<sigma>'_def new_player_nodes_def induced_subgraph_def E_of_strat_def
            by simp
          thus ?case using x'_path_\<sigma> by auto
        qed
      } note xfer_lower_rank_path = this

      {
        fix x xs z
        assume
          X_IN_SUCN: "x \<in> nodes_in_rank (Suc n)"
          and PATH': "path (induced_subgraph V\<^sub>\<alpha> \<sigma>') x xs z"
          and LEN: "Suc n < length xs"

        from X_IN_SUCN consider
          (already_in) "x\<in>nodes_in_rank n"
          | (our_node) "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<alpha>" "(x,target x)\<in>E" "target x\<in>nodes_in_rank n"
          | (opponent_node) "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<beta>" "\<forall>y\<in>E``{x}. y\<in>nodes_in_rank n"
          apply simp
          using IntI X_IN_SUCN new_player_nodes_def target_eq by blast
        thus "set xs \<inter> X \<noteq> {}"
        proof cases
          case already_in thus ?thesis
            using Suc_lessD PATH' LEN forces_\<sigma> xfer_lower_rank_path by fast

        next
          case our_node
          hence "(x,x')\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>' \<Longrightarrow> x'=target x" for x'
            unfolding induced_subgraph_def E_of_strat_def \<sigma>'_def
            using X_IN_SUCN
            by (auto split: if_splits simp: target_eq)
          then obtain xs' where xs': "xs=x#xs'" "path (induced_subgraph V\<^sub>\<alpha> \<sigma>') (target x) xs' z"
            using LEN PATH'
            by (cases xs) auto

          show "set xs \<inter> X \<noteq> {}"
          proof
            assume XS_dj_X: "set xs \<inter> X = {}"
            from xfer_lower_rank_path[OF _ xs'(2)] XS_dj_X xs'(1) \<open>target x \<in> nodes_in_rank n\<close>
            have "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) (target x) xs' z" by auto
            from forces_\<sigma>[OF _ this] LEN \<open>target x \<in> nodes_in_rank n\<close> xs'(1) XS_dj_X show False by auto
          qed
        next
          case opponent_node

          then obtain xs' y where xs': "xs=x#xs'" "path (induced_subgraph V\<^sub>\<alpha> \<sigma>') y xs' z" "y\<in>nodes_in_rank n"
            using LEN PATH'
            by (cases xs) auto

          show "set xs \<inter> X \<noteq> {}"
          proof
            assume XS_dj_X: "set xs \<inter> X = {}"
            from xfer_lower_rank_path[OF _ xs'(2)] XS_dj_X xs'(1,3)
            have "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) y xs' z" by auto
            from forces_\<sigma>[OF _ this] LEN \<open>y \<in> nodes_in_rank n\<close> xs'(1) XS_dj_X show False by auto
          qed
        qed
      }
    qed
  qed (** End of proof nodes_in_rank_forces_X. *)
end (** End of context with fixed X. *)

(** nodes_in_rank is a subset of all of the target set in V. *)
lemma nodes_in_rank_ss: "nodes_in_rank X n \<subseteq> X \<union> V"
  apply (induction n)
  using V\<^sub>\<alpha>_subset by auto

(** If the target set is finite, so is nodes_in_rank. *)
lemma nodes_in_rank_finite[simp, intro!]: "finite X \<Longrightarrow> finite (nodes_in_rank X n)"
  using fin_V finite_Un[of X V] finite_subset[OF nodes_in_rank_ss, of X n] by simp

(** The maximal attractor is a subset of all of the target set in V. *)
lemma player_attractor_ss: "player_attractor X \<subseteq> X \<union> V"
  using player_attractor_ss_nodes_in_rank nodes_in_rank_ss by blast

lemma finite_union_nat_range_bound:
  fixes f :: "nat \<Rightarrow> 'a set"
  assumes FIN: "finite (\<Union>(range f))"
  assumes MONO: "\<And>n n'. n\<le>n' \<Longrightarrow> f n \<subseteq> f n'"
  shows "\<exists>n. \<Union>(range f) = f n"
proof -
  obtain n where "\<Union>(range f) = \<Union>{f i | i . i\<le>n}"
  proof -
    from finite_subset_image[OF finite_UnionD[OF FIN] order_refl]
    obtain C where 1: "finite C" "range f = f`C" by auto
    then obtain n where "C \<subseteq> {0..n}"
      by (meson atLeastAtMost_iff finite_nat_set_iff_bounded_le subset_eq zero_le)
    with 1 have "range f = f`{0..n}" by auto
    thus thesis by (force intro!: that[of n])
  qed
  also have "\<dots> = f n"
    using MONO
    by auto
  finally show ?thesis ..
qed

(** The attractor minus its target set is always finite. *)
lemma finite_player_attractor: "finite (player_attractor X - X)"
  using player_attractor_ss[of X] Diff_subset_conv[of "player_attractor X" X V] rev_finite_subset[OF fin_V]
  by simp

(** There exists a maximum rank that is equal to the maximal attractor. *)
lemma player_attractor_max_rank_eq: "\<exists>n. player_attractor X = nodes_in_rank X n"
proof -
  have 1: "\<Union>(range (nodes_in_rank X)) - X = \<Union>(range (\<lambda>x. nodes_in_rank X x - X))" by auto

  have "\<exists>n. player_attractor X - X = nodes_in_rank X n - X"
    using finite_player_attractor
    unfolding player_attractor_eq_nodes_in_rank
    apply (subst 1)
    apply (rule finite_union_nat_range_bound)
    apply simp
    by (simp add: Diff_mono nodes_in_rank_mono)

  thus ?thesis
    using player_attractor_subset[of X] nodes_in_rank_subset[of X] Diff_partition[of X "player_attractor X"]
    by blast
qed

(** There exists a strategy for the maximal attractor that forces all plays in it to go to X. *)
lemma player_attractor_attracts: "\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = (player_attractor X - X) \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> player_attractor X \<and>
  (\<forall>v\<in>player_attractor X - X. \<forall>v'. (v,v') \<in> (induced_subgraph V\<^sub>\<alpha> \<sigma>) \<longrightarrow> v' \<in> player_attractor X) \<and>
  (\<forall>v\<in>player_attractor X. \<forall>xs. lasso_from_node' (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
proof -
  obtain n where attr_x_rank_n: "player_attractor X = nodes_in_rank X n"
    using player_attractor_max_rank_eq by blast

  from nodes_in_rank_forces_X[of X n] obtain \<sigma> where
    strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    dom_\<sigma>: "dom \<sigma> = (nodes_in_rank X n - X) \<inter> V\<^sub>\<alpha>" and
    ran_\<sigma>: "ran \<sigma> \<subseteq> nodes_in_rank X n" and
    closed_\<sigma>: "(\<forall>n'. \<forall>x'\<in>nodes_in_rank X n' - X. \<forall>y'\<in>induced_subgraph V\<^sub>\<alpha> \<sigma> `` {x'}. y' \<in> nodes_in_rank X n')" and
    forces_\<sigma>: "(\<forall>x\<in>nodes_in_rank X n. \<forall>xs z. path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z \<and> n < length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
    by blast

  show ?thesis
  proof (rule exI[where x=\<sigma>]; intro conjI ballI impI allI)
    show "strategy_of V\<^sub>\<alpha> \<sigma>" by fact
    from dom_\<sigma> attr_x_rank_n show "dom \<sigma> = (player_attractor X - X) \<inter> V\<^sub>\<alpha>" by simp
    from ran_\<sigma> attr_x_rank_n show "ran \<sigma> \<subseteq> player_attractor X" by simp

    fix v v'
    assume v_in_attr_min_X: "v \<in> player_attractor X - X" and
           edge_in_subgame: "(v,v') \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>"
    with closed_\<sigma> show "v' \<in> player_attractor X"
      using attr_x_rank_n by fastforce

  next
    fix v xs
    assume v_in_attr: "v \<in> player_attractor X"
       and lasso_v_xs: "lasso_from_node' (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs"

    from v_in_attr attr_x_rank_n have v_in_rank_n: "v \<in> nodes_in_rank X n" by simp

    from lasso'_extend_any_length[OF lasso_v_xs]
    obtain xs' where
      len_xs': "n < length xs'" and
      set_xs'_eq: "set xs = set xs'" and
      lasso_xs': "lasso_from_node' (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs'"
      by blast

    from lasso'_impl_path[OF lasso_xs']
    obtain v' where "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs' v'" by blast

    hence "set xs' \<inter> X \<noteq> {}" using forces_\<sigma> v_in_rank_n len_xs' by blast
    with set_xs'_eq show "set xs \<inter> X \<noteq> {}" by simp
  qed
qed
end (** End of context player_paritygame. *)


(** We put our definitions for players' attractors in player_paritygame into the context of the
    general paritygame with specified players. *)
section \<open>Attractors for Specific Players\<close>
context paritygame begin

(** An attractor for a specific player. *)
fun attractor where
  "attractor EVEN = P0.player_attractor"
| "attractor ODD = P1.player_attractor"

(** The target set X is a subset of an attractor. *)
lemma attractor_subset: "X \<subseteq> attractor \<alpha> X"
  using P0.player_attractor_subset P1.player_attractor_subset by (cases \<alpha>) auto

(** If the target set is part of the graph, so is the attractor. *)
lemma attractor_subset_graph: "X \<subseteq> V \<Longrightarrow> attractor \<alpha> X \<subseteq> V"
  using P0.player_attractor_ss P1.player_attractor_ss by (cases \<alpha>; simp) blast+

(** If a node is not in the attractor, then they have a successor in the graph with the attractor
    removed from it. *)
lemma notin_attractor_succ: "\<lbrakk>v \<in> V ; v \<notin> attractor \<alpha> X\<rbrakk> \<Longrightarrow> E `` {v} - attractor \<alpha> X \<noteq> {}"
  using P0.notin_player_attractor_succ P1.notin_player_attractor_succ by (cases \<alpha>) auto

(** The attractor is maximal for the player; all player nodes not in the attractor have no successors
    in it. *)
lemma attractor_max_player: "\<lbrakk>v \<in> V_player \<alpha>; v \<notin> attractor \<alpha> X\<rbrakk> \<Longrightarrow> \<forall>w \<in> E `` {v}. w \<notin> attractor \<alpha> X"
  using P0.player_attractor_max_player P1.player_attractor_max_player by (cases \<alpha>) auto

(** The attractor is maximal for the opponent: all opponent nodes not in the attractor have at least
    one successor that is also not in the attractor. *)
lemma attractor_max_opponent: "\<lbrakk>v \<in> V_opponent \<alpha>; v \<notin> attractor \<alpha> X\<rbrakk> \<Longrightarrow> \<exists>w \<in> E `` {v}. w \<notin> attractor \<alpha> X"
  using P0.player_attractor_max_opponent P1.player_attractor_max_opponent V\<^sub>1_def V\<^sub>0_in_V by (cases \<alpha>) auto

(** The player has a strategy that forces all plays in the attractor to move to the target. *)
lemma attractor_attracts: "\<exists>\<sigma>. strategy_of (V_player \<alpha>) \<sigma> \<and>
    dom \<sigma> = (attractor \<alpha> X - X) \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> attractor \<alpha> X \<and>
    (\<forall>v\<in>attractor \<alpha> X - X. \<forall>v'. (v,v') \<in> induced_subgraph (V_player \<alpha>) \<sigma> \<longrightarrow> v' \<in> attractor \<alpha> X) \<and>
    (\<forall>v\<in>attractor \<alpha> X. \<forall>xs. lasso_from_node' (induced_subgraph (V_player \<alpha>) \<sigma>) v xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
    using P0.player_attractor_attracts P1.player_attractor_attracts by (cases \<alpha>) auto
end (** End of context paritygame. *)

end
