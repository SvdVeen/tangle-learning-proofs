theory TangleAttractors
  imports Main Tangles
begin
chapter \<open>Tangle Attractors\<close>
section \<open>Tangle Attractors for Arbitrary Players\<close>
context player_paritygame begin
  (** We fix the set of known tangles T. *)
context
  fixes T :: "'v set set"
  assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
  assumes fin_T: "finite T"
begin

context
  fixes A :: "'v set"
begin
subsection \<open>Tangle Attractors as an Inductive Predicate\<close>
(** Van Dijk defines a tangle attractor as an extension of the regular attractor. We define an
    inductive predicate for a step of the attractor construction, which also constructs the strategy.
    There are three cases:
    own:
    All vertices belonging to the player that have a successor in the previous step are added to the
    attractor. The strategy is updated with an edge from it to that successor.

    opponent:
    All vertices belonging to the opponent that have only successors in the previous step are added
    to the attractor. The strategy remains the same.

    escape:
    Every non-empty tangle belonging to the player in the set of known tangles that has escapes into
    the previous step is added in its entirety to the attractor. For ease of proof we limit this to
    only use attractors that are not already entirely inside the existing attractor. The strategy
    is updated with the tangle strategy, but we omit the target set A from its domain. *)
inductive tangle_attractor_step :: "'v set \<times> 'v strat \<Rightarrow> 'v set \<times> 'v strat \<Rightarrow> bool" where
  own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-X; (x,y) \<in> E; y \<in> X\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (insert x X,\<sigma>(x\<mapsto>y))"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-X; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> X\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (insert x X,\<sigma>)"
| escape: "\<lbrakk>t \<in> T; t-X \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> X;
            player_tangle_strat t \<sigma>'\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (X\<union>t,(\<sigma>' |` (t-A)) ++ \<sigma>)"

lemmas tangle_attractor_step_induct[consumes 1, case_names own opponent_escape] =
  tangle_attractor_step.induct[
    of "(S,\<sigma>)" "(S',\<sigma>')" for S \<sigma> S' \<sigma>',
    where P="\<lambda>(a,b) (c,d). P a b c d" for P,
    unfolded split]

(** The tangle attractor step is monotonous with respect to the set of vertices in the attracted
    region. *)
lemma tangle_attractor_step_mono: "tangle_attractor_step S S' \<Longrightarrow> fst S \<subset> fst S'"
  by (induction rule: tangle_attractor_step.induct) auto

(** The tangle attractor step's result is always in the union of the original attractor set and V.
    This means that attractors to regions in V will be entirely in V. *)
lemma tangle_attractor_step_ss: "tangle_attractor_step S S' \<Longrightarrow> fst S' \<subseteq> (fst S \<union> V)"
  apply (induction rule: tangle_attractor_step.induct)
  subgoal using V\<^sub>\<alpha>_subset by auto
  subgoal by simp
  subgoal using tangles_T player_tangle_in_V by auto
  done

(* If the original region is finite, then the region obtained in one step of the tangle attractor
   is also finite. *)
lemma fin_tangle_attractor_step: "tangle_attractor_step S S' \<Longrightarrow> finite (fst S) \<Longrightarrow> finite (fst S')"
  using finite_subset[OF tangle_attractor_step_ss] by blast

(** We define an invariant for the properties of the constructed strategy in tangle_attractor_step. *)
definition tangle_attractor_strat_I :: "'v set \<times> 'v strat \<Rightarrow> bool" where
  "tangle_attractor_strat_I \<equiv> \<lambda>(S,\<sigma>).
   strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A) \<and> ran \<sigma> \<subseteq> S \<and>
   induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S \<and>
   (\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"

(** The invariant is true for the initial state of the tangle attractor. *)
lemma tangle_attractor_strat_I_base: "tangle_attractor_strat_I (A,Map.empty)"
  unfolding tangle_attractor_strat_I_def using origin_in_lasso by fastforce

(** The step preserves the invariant, so long as A was part of state S. *)
lemma tangle_attractor_strat_I_step:
  "tangle_attractor_step S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_strat_I S
   \<Longrightarrow> tangle_attractor_strat_I S'"
proof (induction rule: tangle_attractor_step.induct)
  case (own x S y \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
          \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
    unfolding tangle_attractor_strat_I_def by blast+
  let ?S' = "insert x S"
  let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"

  from \<sigma>_strat own.hyps(1,2) have \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> ?\<sigma>'"
    unfolding strategy_of_def E_of_strat_def by (auto split: if_splits)

  moreover from \<sigma>_dom own.hyps(1) own.prems(1) have \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (?S' - A)"
    by auto

  moreover from \<sigma>_ran own.hyps(3) have \<sigma>'_ran: "ran ?\<sigma>' \<subseteq> ?S'"
    by (auto simp: ran_def)

  moreover from \<sigma>_closed \<sigma>_ran own.hyps(1) have \<sigma>'_closed_S: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (S-A) \<subseteq> S"
    unfolding induced_subgraph_def E_of_strat_def
    by (auto split: if_splits simp: ranI)
  with own.hyps(1,3) have \<sigma>'_closed: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (?S'-A) \<subseteq> ?S'"
    using ind_subgraph_to_strategy by fastforce

  moreover have \<sigma>'_forces_A_or_wins:
    "\<forall>x\<in>?S'. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') x xs ys
          \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_S': "v \<in> ?S'" and lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v xs ys"
    from lasso_v_xs_ys obtain v' where
      cycle_v'_ys: "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v' ys"
      unfolding lasso_from_node_def by auto

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_S' have v_in_S'_min_A: "v \<in> insert x S - A"
        using origin_in_lasso[OF lasso_v_xs_ys] by blast

      from lasso_from_node_partially_closed_sets[OF this \<sigma>'_closed xs_no_A ys_no_A lasso_v_xs_ys]
      have ys_in_S'_min_A: "set ys \<subseteq> ?S' - A" by simp
      hence y_in_S'_min_A: "v' \<in> ?S' - A"
        using origin_in_cycle[OF cycle_v'_ys] by auto

      consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
      hence "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys \<and> v'\<in>S" proof cases
        case ys_has_x
        from own.hyps(1,2) obtain ys' where
          cycle_y_ys': "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') y ys'" and
          sets_eq: "set ys' = set ys" and
          y_in_ys': "y \<in> set ys'"
          using cycle_intermediate_node[OF cycle_v'_ys ys_has_x]
          apply clarsimp
          subgoal for vs'
            using cycle_D[of "induced_subgraph V\<^sub>\<alpha> ?\<sigma>'" x vs']
            using ind_subgraph_to_strategy by fastforce
          done

        from own.hyps(3) sets_eq y_in_ys' ys_no_A have "y \<in> S-A" by blast
        from cycle_partially_closed_set[OF this \<sigma>'_closed_S cycle_y_ys'] sets_eq ys_no_A
        have "set ys \<subseteq> S - A" by simp
        with ys_has_x own.hyps(1) show ?thesis by blast
      next
        case ys_no_x
        from own.hyps(1) have subset:
          "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' \<inter> (S-A)\<times>(S-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
          unfolding induced_subgraph_def E_of_strat_def
          by (auto split: if_splits)

        from ys_no_x ys_in_S'_min_A have ys_in_S_min_A: "set ys \<subseteq> S-A" by blast
        from subgraph_cycle[OF subset cycle_restr_V[OF cycle_v'_ys this]]
        have cycle_\<sigma>_v'_ys: " cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' ys " .

        with ys_in_S_min_A have v'_in_S_min_A: "v' \<in> S-A"
          using origin_in_cycle by fast

        with cycle_\<sigma>_v'_ys show ?thesis by (simp add: cycle_iff_lasso)
      qed
      with \<sigma>_forces_A_or_wins ys_no_A show ?thesis by fastforce
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed

  ultimately show ?case
    unfolding tangle_attractor_strat_I_def by blast

next
  case (opponent x S \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
          \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
    unfolding tangle_attractor_strat_I_def by blast+
  let ?S' = "insert x S"

  from \<sigma>_closed_S opponent.hyps(2) have \<sigma>_closed_S': "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (?S'-A) \<subseteq> ?S'"
    by auto

  have \<sigma>_forces_A_or_wins':
    "\<forall>x\<in>?S'. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_S': "v \<in> insert x S" and
      lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs ys"
    from lasso_v_xs_ys obtain v' where
      cycle_v'_ys: "cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' ys"
      unfolding lasso_from_node_def by blast

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_S' have "v \<in> insert x S - A"
        using origin_in_lasso[OF lasso_v_xs_ys] by blast

      from lasso_from_node_partially_closed_sets[OF this \<sigma>_closed_S' xs_no_A ys_no_A lasso_v_xs_ys]
      have ys_in_S'_min_A: "set ys \<subseteq> insert x S - A" by simp
      hence v'_in_S'_min_A: "v' \<in> insert x S - A"
        using origin_in_cycle[OF cycle_v'_ys] by blast

      consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
      hence "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys \<and> v' \<in> S" proof cases
        case ys_has_x
        from opponent.hyps(1,2) obtain y ys' where
          x_y_edge: "(x,y) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>" and
          y_in_S: "y \<in> S" and
          cycle_y_ys': "cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) y ys'" and
          sets_eq: "set ys' = set ys" and
          y_in_ys: "y \<in> set ys"
          using cycle_intermediate_node[OF cycle_v'_ys ys_has_x]
          apply clarsimp
          subgoal for vs'
            using cycle_D[of "induced_subgraph V\<^sub>\<alpha> \<sigma>" x vs']
            using ind_subgraph_to_strategy by blast
          done

        from y_in_S y_in_ys ys_no_A have y_in_S_min_A: "y \<in> S-A" by blast
        from cycle_partially_closed_set[OF this \<sigma>_closed_S cycle_y_ys'] sets_eq ys_no_A
        have "set ys \<subseteq> S-A" by auto
        hence "v' \<in> S"
          using origin_in_cycle[OF cycle_v'_ys] by blast

        with cycle_v'_ys show ?thesis by (simp add: cycle_iff_lasso)
      next
        case ys_no_x
        with ys_in_S'_min_A have ys_in_S_min_A: "set ys \<subseteq> S-A" by blast
        with origin_in_cycle[OF cycle_v'_ys] have v'_in_S_min_A: "v' \<in> S-A" by blast
        with cycle_v'_ys show ?thesis by (simp add: cycle_iff_lasso)
      qed

      with \<sigma>_forces_A_or_wins no_A show ?thesis by fastforce
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed

  from \<sigma>_strat \<sigma>_dom \<sigma>_ran \<sigma>_closed_S' \<sigma>_forces_A_or_wins' opponent.hyps(1) show ?case
    unfolding tangle_attractor_strat_I_def by blast

next
  case (escape t S \<sigma>' \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S - A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S - A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    unfolding tangle_attractor_strat_I_def by auto
  let ?\<tau> = "(\<sigma>' |` (t-A)) ++ \<sigma>"
  let ?S' = "S\<union>t"

  from escape.hyps(1) have t_tangle: "player_tangle t" using tangles_T by simp

  from t_tangle have
    t_notempty: "t \<noteq> {}" and
    t_in_V: "t \<subseteq> V"
    using player_tangle_in_V by auto

  let ?t_subgraph = "player_tangle_subgraph t \<sigma>'"
  from escape.hyps(5) have
    \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> \<sigma>'" and
    \<sigma>'_dom: "dom \<sigma>' = t \<inter> V\<^sub>\<alpha>" and
    \<sigma>'_ran: "ran \<sigma>' \<subseteq> t" and
    \<sigma>'_strongly_connected_subgraph: "strongly_connected ?t_subgraph (EV ?t_subgraph)" and
    \<sigma>'_winning: "\<forall>v\<in>t. \<forall>xs. cycle (player_tangle_subgraph t \<sigma>') v xs \<longrightarrow> winning_player xs"
    unfolding player_tangle_strat_def Let_def by auto

  have \<tau>_strat: "strategy_of V\<^sub>\<alpha> ?\<tau>"
  proof -
    from \<sigma>'_strat have "strategy_of V\<^sub>\<alpha> (\<sigma>' |` (t-A))"
      unfolding strategy_of_def E_of_strat_def
      apply (simp; safe)
      subgoal for x y by blast
      subgoal for x y using restrict_in[of x "t-A" \<sigma>'] by fastforce
      done
    from strategy_of_add_same[OF this \<sigma>_strat] show ?thesis by blast
  qed

  from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom ?\<tau> =  V\<^sub>\<alpha> \<inter> (?S' - A)" by auto

  have \<tau>_ran: "ran ?\<tau> \<subseteq> ?S'"
  proof -
    have "ran (\<sigma>' |` (t-A)) \<subseteq> t"
      using subsetD[OF \<sigma>'_ran] ran_restrictD[of _ \<sigma>' "t-A"] ranI by fast
    with \<sigma>_ran show ?thesis
      unfolding ran_def by blast
  qed

  have \<tau>_closed_S: "induced_subgraph V\<^sub>\<alpha> ?\<tau> `` (S-A) \<subseteq> S"
  proof (rule subsetI)
    fix y assume y_succ: "y\<in>induced_subgraph V\<^sub>\<alpha> ?\<tau> `` (S-A)"
    then obtain x where
      x_y_edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> ?\<tau>" and
      x_in_S_min_A: "x\<in>S-A"
      by blast
    consider (in_\<tau>) "x \<in> dom ?\<tau>" | (notin_\<tau>) "x \<notin> dom ?\<tau>" by fast
    thus "y \<in> S" proof cases
      case in_\<tau>
      with \<tau>_dom have x_in_V\<^sub>\<alpha>: "x \<in> V\<^sub>\<alpha>" by simp
      from ind_subgraph_to_strategy[OF x_y_edge x_in_V\<^sub>\<alpha>] have \<tau>_x_y: "?\<tau> x = Some y" .

      from x_in_V\<^sub>\<alpha> \<tau>_x_y \<sigma>_dom \<sigma>_ran x_in_S_min_A show ?thesis
        by (simp add: map_add_dom_app_simps(1) ranI subsetD)
    next
      case notin_\<tau>
      with x_y_edge \<tau>_dom x_in_S_min_A
      have x_y_edge_\<sigma>: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>"
        using ind_subgraph_notin_dom by auto
      with \<sigma>_closed_S x_in_S_min_A show ?thesis by blast
    qed
  qed

  have \<tau>_closed_S': "induced_subgraph V\<^sub>\<alpha> ?\<tau> `` (?S'-A) \<subseteq> ?S'"
  proof (rule subsetI)
    fix y assume y_succ: "y\<in>induced_subgraph V\<^sub>\<alpha> ?\<tau> `` (?S'-A)"
    then obtain x where
      x_y_edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> ?\<tau>" and
      x_in_S'_min_A: "x\<in>?S'-A"
      by blast

    consider (in_\<tau>) "x \<in> dom ?\<tau>" | (notin_\<tau>) "x \<notin> dom ?\<tau>" by fast
    thus "y\<in>?S'" proof cases
      case in_\<tau> with \<tau>_dom \<tau>_ran show ?thesis
        using ind_subgraph_edge_dst[OF x_y_edge] by auto
    next
      case notin_\<tau>
      consider (in_S_min_A) "x \<in> S-A" | (notin_S_min_A) "x \<notin> S-A" by blast
      thus ?thesis proof cases
        case in_S_min_A with x_y_edge \<tau>_closed_S show ?thesis by blast
      next
        case notin_S_min_A
        with x_in_S'_min_A have x_in_t_min_A: "x \<in> t-A" by blast
        thus ?thesis
          apply (cases "y\<in>opponent_escapes t")
          subgoal using escape.hyps(4) by blast
          subgoal unfolding opponent_escapes_def
            using notin_\<tau> \<tau>_dom ind_subgraph_edge_in_E[OF x_y_edge] E_in_V
            by clarsimp blast
          done
      qed
    qed
  qed

  have \<tau>_forces_A_or_wins:
    "\<forall>x\<in>?S'. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<tau>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
  proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_S': "v\<in>?S'" and
      lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<tau>) v xs ys"
    from lasso_v_xs_ys obtain v' where
      cycle_v'_ys: "cycle (induced_subgraph V\<^sub>\<alpha> ?\<tau>) v' ys"
      unfolding lasso_from_node_def by blast

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_S' have "v\<in>?S'-A"
        using origin_in_lasso[OF lasso_v_xs_ys] by blast

      from lasso_from_node_partially_closed_sets[OF this \<tau>_closed_S' xs_no_A ys_no_A lasso_v_xs_ys]
      have ys_in_S'_min_A: "set ys \<subseteq> ?S'-A" by simp
      hence v'_in_S'_min_A: "v' \<in> ?S'-A"
        using origin_in_cycle[OF cycle_v'_ys] by blast

      consider (ys_has_S) "set ys \<inter> S \<noteq> {}" | (ys_no_S) "set ys \<inter> S = {}" by blast
      thus ?thesis proof cases
        (** In this case, the cycle must be entirely contained in S because S is closed under
            \<tau>. That also means it is won because under \<sigma>, all plays that do not go through A
            are winning. *)
        case ys_has_S
        with ys_no_A obtain y ys' where
          y_in_S_min_A: "y \<in> S-A" and
          sets_eq: "set ys' = set ys" and
          ys'_no_A: "set ys' \<inter> A = {}" and
          cycle_y_ys': "cycle (induced_subgraph V\<^sub>\<alpha> ?\<tau>) y ys'"
          using cycle_intermediate_node[OF cycle_v'_ys] by fastforce

        from cycle_partially_closed_set[OF y_in_S_min_A \<tau>_closed_S cycle_y_ys' ys'_no_A] sets_eq
        have ys_in_S_min_A: "set ys \<subseteq> S-A" by blast
        hence v'_in_S: "v' \<in> S" using origin_in_cycle[OF cycle_v'_ys] by blast

        from \<sigma>_dom have subset: "induced_subgraph V\<^sub>\<alpha> ?\<tau> \<inter> (S-A)\<times>(S-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
          unfolding induced_subgraph_def E_of_strat_def by auto

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle_v'_ys ys_in_S_min_A]]
        have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys"
          by (simp add: cycle_iff_loop loop_impl_lasso)

        with \<sigma>_forces_A_or_wins v'_in_S no_A show ?thesis by fastforce
      next
        case ys_no_S
        with ys_in_S'_min_A have ys_in_t_min_S_min_A: "set ys \<subseteq> t-S-A" by blast
        hence v'_in_t: "v'\<in>t" using origin_in_cycle[OF cycle_v'_ys] by blast

        from \<sigma>_ran t_in_V have subset:
          "induced_subgraph V\<^sub>\<alpha> ?\<tau> \<inter> (t-S-A)\<times>(t-S-A) \<subseteq> player_tangle_subgraph t \<sigma>' \<inter> (t-S-A)\<times>(t-S-A)"
          unfolding induced_subgraph_def player_tangle_subgraph_def E_of_strat_def
          using ind_subgraph_edge_dst[of _ _ V\<^sub>\<alpha> \<sigma>] strategy_to_ind_subgraph[of \<sigma> _ _ V\<^sub>\<alpha>]
          by fastforce

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle_v'_ys ys_in_t_min_S_min_A]]
        have "cycle (player_tangle_subgraph t \<sigma>') v' ys" using restr_V_cycle by fast

        with \<sigma>'_winning v'_in_t show ?thesis by blast
      qed
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed

  from \<tau>_strat \<tau>_dom \<tau>_ran \<tau>_closed_S' \<tau>_forces_A_or_wins show ?case
    unfolding tangle_attractor_strat_I_def by blast
qed

(** We will be using the reflexive transitive closure of the step relation for our final definition.
    To prove properties of the final definition, we will therefore need to prove them for the
    reflexive transitive closure first. *)

(** The reflexive transitive closure of steps is monotonous over the obtained region. This is less
    strict than our monotonicity property for the individual steps because of the reflexivity. *)
lemma tangle_attractor_step_rtranclp_mono: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S \<subseteq> fst S'"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal using tangle_attractor_step_mono by blast
  done

(** The reflexive transitive closure of steps yields a subset of the union of the original set with
    V. If we attract to a region in V, then the result will always be in V. *)
lemma tangle_attractor_step_rtranclp_ss: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S' \<subseteq> (fst S \<union> V)"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal using tangle_attractor_step_ss by blast
  done

(** The region in the result of the reflexive transitive closure of steps is finite if the original
    set is finite. *)
lemma fin_tangle_attractor_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> finite (fst S)
  \<Longrightarrow> finite (fst S')"
  using finite_subset[OF tangle_attractor_step_rtranclp_ss] by blast

(** The reflexive transitive closure of the tangle attractor step preserves the strategy invariant. *)
lemma tangle_attractor_step_rtranclp_preserves_I:
  "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_strat_I S
  \<Longrightarrow> tangle_attractor_strat_I S'"
  apply (induction rule: rtranclp_induct; simp)
  using tangle_attractor_step_rtranclp_mono tangle_attractor_strat_I_step subset_trans
  by fast

subsection \<open>Tangle Attractors\<close>
(** Van Dijk's definition for the construction of witness strategies of tangle attractors includes
    assigning a successor in X to each player_owned nodes in A. We define this as a lambda that
    uses the hilbert choice operator to pick some valid successor if it exists. *)
definition A_target :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v option" where
  "A_target X \<equiv> \<lambda>x.
    if x \<in> V\<^sub>\<alpha> \<inter> A \<and> (\<exists>y. y \<in> X \<and> (x,y) \<in> E)
    then
      Some (SOME y. y \<in> X \<and> (x,y) \<in> E)
    else
      None"

(** A_target produces a strategy for the player. *)
lemma A_target_strat: "strategy_of V\<^sub>\<alpha> (A_target X)"
  unfolding A_target_def strategy_of_def E_of_strat_def
  apply (safe; clarsimp split: if_splits)
  subgoal for x using someI2[of "(\<lambda>y. y \<in> X \<and> (x,y) \<in> E)"] by fast
  done

(** The domain of A_target is some subset of the player's node in A. *)
lemma A_target_dom: "dom (A_target X) \<subseteq> V\<^sub>\<alpha> \<inter> A"
  unfolding A_target_def
  by (auto split: if_splits)

(** The range of A_target is in X. *)
lemma A_target_ran: "ran (A_target X) \<subseteq> X"
proof
  fix y assume y_in_range: "y \<in> ran (A_target X)"
  then obtain x where x_to_y: "A_target X x = Some y"
    by (auto simp: ran_def)
  thus "y \<in> X"
    unfolding A_target_def
    using some_eq_imp[of "(\<lambda>v'. v' \<in> X \<and> (x,v') \<in> E)" y]
    by (simp split: if_splits)
qed

(** Every x in A belonging to the player with at least one successor in X is in the domain of
    A_target X *)
lemma A_target_in_dom: "\<lbrakk>x \<in> V\<^sub>\<alpha> \<inter> A; E `` {x} \<inter> X \<noteq> {}\<rbrakk> \<Longrightarrow> x \<in> dom (A_target X)"
  unfolding A_target_def
  apply (simp split!: if_splits)
  using someI[of "(\<lambda>v'. v' \<in> X \<and> (x,v') \<in> E)"] by force

(** We finally get the definition for the attractor as a whole by taking the reflexive transitive
    closure of the steps starting from the target set with an empty strategy. We also limit it to
    only final results by saying it should not be in the domain of the relation; it cannot be
    followed by another step. *)
(*
definition player_tangle_attractor :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "player_tangle_attractor X \<sigma> \<equiv> \<exists>\<sigma>'. tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>') \<and>
    \<not>Domainp tangle_attractor_step (X,\<sigma>') \<and>
    (\<sigma> |` (X-A)) = \<sigma>' \<and>
    (\<forall>v\<in>A. E `` {v} \<inter> X \<noteq> {} \<longrightarrow> \<sigma> v \<in> Some ` (E `` {v} \<inter> X))" *)

(** The whole attractor is obtained by taking the reflexive transitive closure of the steps starting
    from the target set with an empty strategy. We limit it to only include final results by saying
    it should not be in the domain of the relation; it cannot be followed by another step. We also
    have to assign a target for all nodes in A that have a successor in X, as per Van Dijk's
    definition of the construction of the witness strategy. *)
definition player_tangle_attractor :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "player_tangle_attractor X \<sigma> \<equiv> \<exists>\<sigma>'. tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>') \<and>
    \<not>Domainp tangle_attractor_step (X,\<sigma>') \<and> \<sigma> = \<sigma>' ++ A_target X"

(** The attracted region always contais A due to the monotonicity of the steps. *)
lemma player_tangle_attractor_contains_A:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> A \<subseteq> X"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_mono
  by fastforce

(** This auxiliary lemma is used to show that the invariant has been preserved for \<sigma>, and that
    \<sigma> is constructed from \<sigma>' and A_target. *)
lemma player_tangle_attractor_I_aux:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> \<exists>\<sigma>'. tangle_attractor_strat_I (X,\<sigma>') \<and> \<sigma> = \<sigma>' ++ A_target X"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_preserves_I[OF _ _ tangle_attractor_strat_I_base]
  by auto

(** If we have a tangle-attracted region X and witness strategy \<sigma>, then that is a strategy for the
    player. *)
lemma player_tangle_attractor_strat_of_V\<^sub>\<alpha>:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>"
  using player_tangle_attractor_I_aux[of X \<sigma>] A_target_strat[of X]
  unfolding tangle_attractor_strat_I_def
  by fastforce

(** If we have a tangle-attracted region X and witness strategy \<sigma>, then the domain of \<sigma> is some
    subset of all player-owned nodes in X. *)
lemma player_tangle_attractor_strat_dom:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] player_tangle_attractor_contains_A[of X \<sigma>]
        A_target_dom[of X]
  unfolding tangle_attractor_strat_I_def
  by auto

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then the range of \<sigma> is in X.*)
lemma player_tangle_attractor_strat_ran:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> ran \<sigma> \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] A_target_ran[of X]
  unfolding tangle_attractor_strat_I_def
  by (auto simp: ran_def)

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then the induced subgraph of \<sigma>
    is partially closed in X, excluding A. *)
lemma player_tangle_attractor_strat_partially_closed:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X-A) \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>]
  unfolding tangle_attractor_strat_I_def A_target_def induced_subgraph_def E_of_strat_def
  by auto

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, and X is a closed region, then
    the induced subgraph of \<sigma> is also closed in X. This is a somewhat trivial property, but nice to
    have. *)
lemma closed_player_tangle_attractor_strat_closed:
  "\<lbrakk>player_tangle_attractor X \<sigma>; E `` X \<subseteq> X\<rbrakk> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` X \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] ind_subgraph[of V\<^sub>\<alpha> \<sigma>]
  unfolding tangle_attractor_strat_I_def
  by fast

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then all plays in X restricted
    by \<sigma> either lead to A or are won by the player. *)
lemma player_tangle_attractor_strat_forces_A_or_wins:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> \<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
    \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
proof (intro ballI allI impI)
  fix x xs ys
  assume attr: "player_tangle_attractor X \<sigma>" and
    x_in_X: "x \<in> X" and lasso: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys"
  (** We need the domain of \<sigma>', the fact that \<sigma>' forces all plays to go to A or be won by the player,
      and the composition of \<sigma>. *)
  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' :: "'v strat" where
    \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
    \<sigma>'_forces_A_or_wins: "\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>') x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" and
    \<sigma>_comp: "\<sigma> = \<sigma>' ++ A_target X"
    unfolding tangle_attractor_strat_I_def
    by blast
  (** From the domain of \<sigma>', and the way \<sigma> is composed, we can say that \<sigma> restricted to X minus A
      is equal to \<sigma>'. *)
  from \<sigma>'_dom \<sigma>_comp have \<sigma>_extends_\<sigma>': "\<sigma> |` (X-A) = \<sigma>'"
    using A_target_dom[of X]
    apply (simp add: restrict_map_def)
    using map_add_dom_app_simps(3)[of _ "A_target X" \<sigma>']
    by fastforce
  (** Therefore, the induced subgraphs of \<sigma> and \<sigma>' are equal in the graph restricted to X minus A. *)
  hence restricted_graphs_equal:
    "(induced_subgraph V\<^sub>\<alpha> \<sigma>) \<inter> (X-A) \<times> X = (induced_subgraph V\<^sub>\<alpha> \<sigma>') \<inter> (X-A) \<times> X"
    unfolding induced_subgraph_def E_of_strat_def by auto
  (** ys is not empty, and we have a path from x to y and a path from y to y. We can also say that
      y is included at the start of ys'. *)
  from lasso have ys_notempty: "ys \<noteq> []" by auto
  from lasso obtain y where
    path_x_xs_y: "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs y" and
    path_y_ys_y: "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) y ys y"
    using lasso_from_node_paths[of "induced_subgraph V\<^sub>\<alpha> \<sigma>"] by auto
  with ys_notempty have y_in_ys: "\<exists>ys'. ys = (y#ys')"
    using path_D[of _ y ys y] by blast
  (** Now we attach these paths to form a single path. *)
  define zs where "zs=xs@ys"
  with path_x_xs_y path_y_ys_y have path_x_zs_y: "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x zs y"
    by auto
  (** Using this lemma, we know that this path either needs to intersect with A, or it exists
      withing the area without A. *)
  from player_tangle_attractor_strat_partially_closed[OF attr]
  have \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X - A) \<subseteq> X" .
  have A_in_zs_or_path: "A \<inter> set zs \<noteq> {} \<or> path (induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (X-A) \<times> X) x zs y"
    using simulate_closed_path[OF \<sigma>_closed x_in_X path_x_zs_y] by blast
  (** If we assume that there is no A in zs we should have a winning path. *)
  have "A \<inter> set zs = {} \<Longrightarrow> winning_player ys"
  proof -
    assume no_A_in_zs: "A \<inter> set zs = {}"
    (** Because A is not in ZS, we have a path that stays in the region minus A. *)
    with A_in_zs_or_path have "path (induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (X-A) \<times> X) x zs y" by simp
    (** This path also exists in the graph of \<sigma>'. *)
    with restricted_graphs_equal have "path (induced_subgraph V\<^sub>\<alpha> \<sigma>' \<inter> (X-A) \<times> X) x zs y" by simp
    hence "path (induced_subgraph V\<^sub>\<alpha> \<sigma>') x zs y" using path_inter(1) by fastforce
    (** Now, we can say that the original lasso existed in the graph of \<sigma>' too.*)
    with y_in_ys ys_notempty have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>') x xs ys"
      using lasso_from_node_paths
      unfolding zs_def by fastforce
    (** Because this lasso does not intersect with A, the loop is won by the player by the
        property of \<sigma>' we obtained from the invariant. *)
    with \<sigma>'_forces_A_or_wins x_in_X no_A_in_zs show ?thesis
      unfolding zs_def by blast
  qed
  (** Since not intersecting with A means the loop is won by the player, we have proven our lemma. *)
  thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    unfolding zs_def by fast
qed

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then \<sigma> is a strategy for the
    player, its domain is a subset of all player-owned nodes in X, its range is in X, the induced
    subgraph of \<sigma> is partially closed in X (excluding A), and all plays starting in X restricted by
    \<sigma> either go to A or are won by the player. *)
lemma player_tangle_attractor_strat:
  "player_tangle_attractor X \<sigma> \<Longrightarrow>
   strategy_of V\<^sub>\<alpha> \<sigma> \<and>
   dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> X \<and>
   ran \<sigma> \<subseteq> X \<and>
   induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X-A) \<subseteq> X \<and>
   (\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  using player_tangle_attractor_strat_of_V\<^sub>\<alpha>[of X \<sigma>]
    player_tangle_attractor_strat_dom[of X \<sigma>]
    player_tangle_attractor_strat_ran[of X \<sigma>]
    player_tangle_attractor_strat_partially_closed[of X \<sigma>]
    player_tangle_attractor_strat_forces_A_or_wins[of X \<sigma>]
  by fast

(** If we have an attracted region X and a witness strategy \<sigma>, and a player-owned node in A that has
    at least one successor in X, then that x is in the domain of \<sigma>. This is because it was given one
    by A_target X.*)
lemma player_tangle_attractor_strat_in_dom_A:
  "\<lbrakk>player_tangle_attractor X \<sigma>; x\<in>V\<^sub>\<alpha> \<inter> A; E `` {x} \<inter> X \<noteq> {}\<rbrakk> \<Longrightarrow> x \<in> dom \<sigma>"
  using player_tangle_attractor_I_aux[of X \<sigma>] A_target_in_dom[of x X]
  unfolding tangle_attractor_strat_I_def
  by auto

(** If we have an attracted region X and a witness strategy \<sigma>, and a player-owned node in X minus A,
    then that x is in the domain of \<sigma>. This is due to the invariant on \<sigma>'. *)
lemma player_tangle_attractor_strat_in_dom_not_A:
  "\<lbrakk>player_tangle_attractor X \<sigma>; x \<in> V\<^sub>\<alpha> \<inter> (X-A)\<rbrakk> \<Longrightarrow> x \<in> dom \<sigma>"
  using player_tangle_attractor_I_aux[of X \<sigma>]
  unfolding tangle_attractor_strat_I_def
  by (clarsimp simp: domD)

(** The (inverse) reflexive transitive closure of the tangle attractor step is a well-founded
    relation. *)
lemma tangle_attractor_step_wf: "wfP (tangle_attractor_step\<inverse>\<inverse>)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image (finite_psubset) (\<lambda>(s,\<sigma>). V - s)"]; clarsimp)
  subgoal for S' \<sigma>' S \<sigma>
    apply (erule tangle_attractor_step.cases)
    subgoal using V\<^sub>\<alpha>_subset by blast
    subgoal by auto
    subgoal using player_tangle_in_V tangles_T by blast
    done
  done

(** A wellfounded relation terminates. *)
lemma wf_rel_terminates: "wfP R\<inverse>\<inverse> \<Longrightarrow> \<exists>X' \<sigma>'. R\<^sup>*\<^sup>* S (X',\<sigma>') \<and> \<not> Domainp R (X', \<sigma>')"
  unfolding wfP_def
  apply (induction S rule: wf_induct_rule)
  subgoal for x apply (cases "Domainp R x"; clarsimp)
    subgoal using converse_rtranclp_into_rtranclp[of R] by blast
    subgoal using surj_pair[of x] by blast
    done
  done

(** There always exists a tangle attractor. *)
lemma player_tangle_attractor_exists: "\<exists>X \<sigma>. player_tangle_attractor X \<sigma>"
proof -
  from wf_rel_terminates[OF tangle_attractor_step_wf] obtain X \<sigma>' where
    step_rtrancl: "tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X, \<sigma>')" and
    no_further_steps: "\<not>Domainp tangle_attractor_step (X, \<sigma>')" by blast

  from tangle_attractor_step_rtranclp_preserves_I[OF step_rtrancl _ tangle_attractor_strat_I_base]
  have \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> X-A"
    unfolding tangle_attractor_strat_I_def by auto

  define target where "target \<equiv> \<lambda>x. SOME x'. (x,x') \<in> E \<and> x' \<in> X"
  define \<sigma> where "\<sigma> \<equiv> \<lambda>x. if x \<in> A then Some (target x) else \<sigma>' x"
  from \<sigma>'_dom have \<sigma>_in_\<sigma>'_dom_is_\<sigma>': "\<sigma> |` (X-A) = \<sigma>'"
    unfolding \<sigma>_def restrict_map_def by fastforce

  have A_succs_in_X:
    "\<forall>v\<in>A. E `` {v} \<inter> X \<noteq> {} \<longrightarrow> \<sigma> v \<in> Some ` (E `` {v} \<inter> X)"
    unfolding \<sigma>_def
    apply (clarsimp split: if_splits)
    subgoal for x using some_eq_imp[of _ "target x"]
      unfolding target_def by auto
    done

  from step_rtrancl no_further_steps \<sigma>_in_\<sigma>'_dom_is_\<sigma>' A_succs_in_X
  show ?thesis
    unfolding player_tangle_attractor_def by blast
qed

(** Every node that is not in a tangle attractor still has successors outside of that attractor. *)
lemma notin_player_tangle_attractor_succ:
  "\<lbrakk>player_tangle_attractor X \<sigma>; v \<in> V; v \<notin> X\<rbrakk> \<Longrightarrow> E `` {v} - X \<noteq> {}"
proof
  assume attr: "player_tangle_attractor X \<sigma>" and
         v_in_V: "v \<in> V" and
         v_notin_X: "v \<notin> X" and
         no_succs_outside_X: "E `` {v} - X = {}"
  (** We need to unfold the definition of the attractor so we can use it for our induction later. *)
  from attr obtain \<sigma>' where
    attr_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>')" and
    attr_step_result: "\<not>Domainp tangle_attractor_step (X,\<sigma>')"
    unfolding player_tangle_attractor_def by auto

  (** By our definition of a parity game, there must be successors to v. Furthermore, because we
      have the assumption that there are no successors outside of X, all of them must be in X.
      This also means that there exists at least one successor in X, which we will need for the case
      that v belongs to the player. *)
  from succ[OF v_in_V] have v_succ: "E `` {v} \<noteq> {}" .
  with no_succs_outside_X v_in_V have all_succs_in_X: "\<forall>v'. (v,v') \<in> E \<longrightarrow> v' \<in> X" by blast
  with v_succ have some_succ_in_X: "\<exists>v'. (v,v') \<in> E \<and> v' \<in> X" by blast

  (** Now we have two cases: v belongs to the player, and v belongs to the opponent.
      If v belongs to the player, and it has a successor in X, then it should be part of X by
      the definition of our tangle attractor.
      Likewise, if v belongs to the opponent, and all of its successors are in X, then it should
      be part of X by the definition of the tangle attractor.
      We have the assumption that v is not a part of X, so we have a contradiction, completing
      our proof. *)
  from v_in_V consider (v_player) "v \<in> V\<^sub>\<alpha>" | (v_opp) "v \<in> V\<^sub>\<beta>" by blast
  thus "False"
    using attr_step_rtranclp attr_step_result v_notin_X
    apply cases
    subgoal apply (induction rule: converse_rtranclp_induct)
      using some_succ_in_X by (auto intro: tangle_attractor_step.own)
    subgoal apply (induction rule: converse_rtranclp_induct)
      using all_succs_in_X by (auto intro: tangle_attractor_step.opponent)
    done
qed

(** The target of a tangle attractor is part of the attracted region. *)
lemma target_in_player_tangle_attractor: "player_tangle_attractor X \<sigma> \<Longrightarrow> A \<subseteq> X"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_mono by fastforce

(** An attracted region is a subset of the union of its target and V. This means that if the target
    is in V, the attracted region is entirely in V. *)
lemma player_tangle_attractor_ss: "player_tangle_attractor X \<sigma> \<Longrightarrow> X \<subseteq> A \<union> V"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_ss by fastforce

(** If the target of the attractor is finite, so is the attracted region. *)
lemma player_tangle_attractor_finite: "player_tangle_attractor X \<sigma> \<Longrightarrow> finite A \<Longrightarrow> finite X"
  using finite_subset[OF player_tangle_attractor_ss] by blast
end (** End of context with fixed A *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor, i.e. TAttr(A) = A.
    This definition is now clearly wrong - it needs changing! *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> \<forall>\<sigma>. \<nexists>S'. tangle_attractor_step A (A,\<sigma>) S'" (** player_tangle_attractor A A Map.empty" *)

(** Tangle attracted regions cannot be extended further with the tangle attractor. *)
lemma attractor_no_extension:
  "player_tangle_attractor A X \<sigma> \<Longrightarrow> \<nexists>S'. tangle_attractor_step A (X,\<sigma>) S'"
  unfolding player_tangle_attractor_def sorry

end (** End of context with fixed T *)

end (** End of context player_paritygame *)

section \<open>Tangle Attractors for Specific Players\<close>
context paritygame begin

fun tangle_attractor :: "player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_attractor EVEN T = P0.player_tangle_attractor {t\<in>T. tangle EVEN t}"
| "tangle_attractor ODD T = P1.player_tangle_attractor {t\<in>T. tangle ODD t}"

lemma tangle_attractor_exists:
  assumes fin_T: "finite T"
  shows "\<exists>X \<sigma>. tangle_attractor \<alpha> T A X \<sigma>"
  using assms P0.player_tangle_attractor_exists P1.player_tangle_attractor_exists
  by (cases \<alpha>; simp)

lemma notin_tangle_attractor_succ:
  assumes fin_T: "finite T"
  shows "\<lbrakk>tangle_attractor \<alpha> T A X \<sigma>; v \<in> V; v \<notin> X\<rbrakk> \<Longrightarrow> E `` {v}-X \<noteq> {}"
  using assms
  using P0.notin_player_tangle_attractor_succ[of "{t\<in>T. tangle EVEN t}"]
  using P1.notin_player_tangle_attractor_succ[of "{t\<in>T. tangle ODD t}"]
  by (cases \<alpha>; simp)

lemma target_in_tangle_attractor:
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> A \<subseteq> X"
  using assms
  using P0.target_in_player_tangle_attractor[of "{t\<in>T. tangle EVEN t}"]
  using P1.target_in_player_tangle_attractor[of "{t\<in>T. tangle ODD t}"]
  by (cases \<alpha>; simp)

lemma tangle_attractor_ss:
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> X \<subseteq> A \<union> V"
  using assms
  using P0.player_tangle_attractor_ss[of "{t\<in>T. tangle EVEN t}"]
  using P1.player_tangle_attractor_ss[of "{t\<in>T. tangle ODD t}"]
  by (cases \<alpha>; simp)

lemma tangle_attractor_strat:
  assumes "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow>
    strategy_of_player \<alpha> \<sigma> \<and>
    dom \<sigma> \<subseteq> V_player \<alpha> \<inter> X \<and>
    ran \<sigma> \<subseteq> X \<and>
    induced_subgraph (V_player \<alpha>) \<sigma> `` (X-A) \<subseteq> X \<and>
    (\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph (V_player \<alpha>) \<sigma>) x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys)"
  unfolding strategy_of_player_def
  using assms
  using P0.player_tangle_attractor_strat[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_strat[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp add: V\<^sub>1_def)

lemma tangle_attractor_strat_in_dom_A:
  assumes "finite T"
  shows "\<lbrakk>tangle_attractor \<alpha> T A X \<sigma>; x \<in> V_player \<alpha> \<inter> A; E `` {x} \<inter> X \<noteq> {}\<rbrakk> \<Longrightarrow> x \<in> dom \<sigma>"
  using assms
  using P0.player_tangle_attractor_strat_in_dom_A[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_strat_in_dom_A[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)

lemma tangle_attractor_strat_in_dom_not_A:
  assumes "finite T"
  shows "\<lbrakk>tangle_attractor \<alpha> T A X \<sigma>; x \<in> V_player \<alpha> \<inter> (X-A)\<rbrakk> \<Longrightarrow> x \<in> dom \<sigma>"
  using assms
  using P0.player_tangle_attractor_strat_in_dom_not_A[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_strat_in_dom_not_A[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)

lemma tangle_attractor_finite:
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> finite A \<Longrightarrow> finite X"
  using assms
  using P0.player_tangle_attractor_finite[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_finite[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)

(** If you remove a tangle attractor from the game, the resulting graph is a valid subgame. *)
lemma remove_tangle_attractor_subgame:
  assumes fin_T: "finite T"
  assumes tangle_attractor: "tangle_attractor \<alpha> T A X \<sigma>"
  shows "paritygame (Restr E (V-X)) (V-X) (V\<^sub>0-X)"
proof (unfold_locales)
  show "Restr E (V-X) \<subseteq> (V-X)\<times>(V-X)" by blast
  show "finite (V-X)" by simp
  show "V\<^sub>0-X \<subseteq> V-X" using V\<^sub>0_in_V by blast
  show "\<And>v. v \<in> V-X \<Longrightarrow> Restr E (V-X) `` {v} \<noteq> {}"
  proof -
    fix v
    assume v_in_V_min_X: "v \<in> V-X"
    hence v_in_V: "v\<in>V" by simp
    from v_in_V_min_X have "v \<notin> X" by simp
    with notin_tangle_attractor_succ[OF fin_T tangle_attractor v_in_V]
    have "E `` {v} - X \<noteq> {}" by simp
    then obtain w where w: "(v,w) \<in> E \<and> w \<in> V-X" using E_in_V by blast
    with v_in_V_min_X have "(v,w) \<in> Restr E (V-X)" using E_in_V by blast
    then show "Restr E (V-X) `` {v} \<noteq> {}" by blast
  qed
qed


subsection \<open>\<alpha>-maximal regions\<close>
fun \<alpha>_max :: "player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> bool" where
  "\<alpha>_max EVEN = P0.player_\<alpha>_max"
| "\<alpha>_max ODD = P1.player_\<alpha>_max"
end (** End of context paritygame *)

end
