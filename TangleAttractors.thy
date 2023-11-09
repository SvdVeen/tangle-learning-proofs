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

subsection \<open>Tangle Attractors as an Inductive Predicate\<close>
context
  fixes A :: "'v set"
begin

inductive tangle_attractor_step :: "'v set \<times> 'v strat \<Rightarrow> 'v set \<times> 'v strat \<Rightarrow> bool" where
  own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (insert x S,\<sigma>(x\<mapsto>y))"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (insert x S,\<sigma>)"
| escape: "\<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
            player_tangle_strat t \<sigma>'\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (S\<union>t,(\<sigma>' |` (t-A)) ++ \<sigma>)"

lemma tangle_attractor_step_mono: "tangle_attractor_step S S' \<Longrightarrow> fst S \<subset> fst S'"
  by (induction rule: tangle_attractor_step.induct) auto

lemma tangle_attractor_step_rtranclp_mono: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S \<subseteq> fst S'"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal using tangle_attractor_step_mono by blast
  done

lemma tangle_attractor_step_ss: "tangle_attractor_step S S' \<Longrightarrow> fst S' \<subseteq> (fst S \<union> V)"
  apply (induction rule: tangle_attractor_step.induct)
  subgoal using V\<^sub>\<alpha>_subset by auto
  subgoal by simp
  subgoal using tangles_T player_tangle_in_V by auto
  done

lemma tangle_attractor_step_rtranclp_ss: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S' \<subseteq> (fst S \<union> V)"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal using tangle_attractor_step_ss by blast
  done

lemma fin_tangle_attractor_step: "tangle_attractor_step S S' \<Longrightarrow> finite (fst S) \<Longrightarrow> finite (fst S')"
  using finite_subset[OF tangle_attractor_step_ss] by blast

lemma fin_tangle_attractor_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> finite (fst S) \<Longrightarrow> finite (fst S')"
  using finite_subset[OF tangle_attractor_step_rtranclp_ss] by blast

definition tangle_attractor_step_I :: "'v set \<times> 'v strat \<Rightarrow> bool" where
  "tangle_attractor_step_I \<equiv> \<lambda>(S,\<sigma>).
   strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A) \<and> ran \<sigma> \<subseteq> S \<and>
   induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S \<and>
   (\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"

lemma tangle_attractor_step_I_base: "tangle_attractor_step_I (A,Map.empty)"
  unfolding tangle_attractor_step_I_def using origin_in_lasso by fastforce

lemma tangle_attractor_step_I_step:
  "tangle_attractor_step S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_step_I S
   \<Longrightarrow> tangle_attractor_step_I S'"
proof (induction rule: tangle_attractor_step.induct)
  case (own x S y \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
          \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
    unfolding tangle_attractor_step_I_def by blast+
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
    unfolding tangle_attractor_step_I_def by blast

next
  case (opponent x S \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
          \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
    unfolding tangle_attractor_step_I_def by blast+
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
    unfolding tangle_attractor_step_I_def by blast

next
  case (escape t S \<sigma>' \<sigma>)
  hence \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S - A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S - A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    unfolding tangle_attractor_step_I_def by auto
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
    unfolding tangle_attractor_step_I_def by blast
qed

lemma tangle_attractor_step_rtranclp_I:
  "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_step_I S \<Longrightarrow> tangle_attractor_step_I S'"
  apply (induction rule: rtranclp_induct; simp)
  using tangle_attractor_step_rtranclp_mono tangle_attractor_step_I_step subset_trans
  by fast

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

lemma tangle_attractor_step_rtranclp_induct[consumes 1, case_names base own opponent escape]:
  assumes tangle_attractor_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* S S'"
  assumes base: "P S"
  assumes own: "\<And>x S y \<sigma>. \<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S; P (S,\<sigma>)\<rbrakk> \<Longrightarrow> P (insert x S,\<sigma>(x\<mapsto>y))"
  assumes opponent: "\<And>x S \<sigma>. \<lbrakk>x \<in> V\<^sub>\<beta>-S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S; P (S,\<sigma>)\<rbrakk> \<Longrightarrow> P (insert x S,\<sigma>)"
  assumes escape: "\<And>t S \<sigma>' \<sigma>. \<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
                   player_tangle_strat t \<sigma>'; P (S,\<sigma>)\<rbrakk> \<Longrightarrow> P (S\<union>t, \<sigma>' |` (t-A) ++ \<sigma>)"
  shows "P S'"
  using tangle_attractor_step_rtranclp base
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl S)
  thus ?case by simp
next
  case (rtrancl_into_rtrancl S S' S'')
  from this(2) this(3)[OF this(4)]
  show ?case
    apply (induction rule: tangle_attractor_step.induct)
    subgoal using own by simp
    subgoal using opponent by simp
    subgoal using escape by simp
    done
qed

(** Correctness check for the induction lemma *)
lemma "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> finite (fst S) \<Longrightarrow> finite (fst S')"
  apply (induction rule: tangle_attractor_step_rtranclp_induct)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using tangles_T fin_player_tangle by simp
  done

definition player_tangle_attractor :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "player_tangle_attractor X \<sigma> \<equiv> tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>)"

lemma player_tangle_attractor_induct[consumes 1, case_names base own opponent escape]:
  assumes attr: "player_tangle_attractor X \<sigma>"
  assumes base: "P A Map.empty"
  assumes own: "\<And>x S y \<sigma>. \<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S; P S \<sigma>\<rbrakk> \<Longrightarrow> P (insert x S) (\<sigma>(x\<mapsto>y))"
  assumes opponent: "\<And>x S \<sigma>. \<lbrakk>x \<in> V\<^sub>\<beta> - S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S; P S \<sigma>\<rbrakk> \<Longrightarrow> P (insert x S) \<sigma>"
  assumes escape: "\<And>t S \<sigma>' \<sigma>. \<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
                   player_tangle_strat t \<sigma>'; P S \<sigma>\<rbrakk> \<Longrightarrow> P (S\<union>t) (\<sigma>' |` (t-A) ++ \<sigma>)"
  shows "P X \<sigma>"
proof -
  define P' :: "'v set \<times> 'v strat \<Rightarrow> bool" where "P' \<equiv> \<lambda>(a,b). P a b"
  hence base': "P' (A,Map.empty)" and
        own': "\<And>x S y \<sigma>. \<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S; P' (S,\<sigma>)\<rbrakk> \<Longrightarrow> P' (insert x S,\<sigma>(x\<mapsto>y))" and
        opponent': "\<And>x S \<sigma>. \<lbrakk>x \<in> V\<^sub>\<beta>-S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S; P' (S,\<sigma>)\<rbrakk> \<Longrightarrow> P' (insert x S,\<sigma>)" and
        escape': "\<And>t S \<sigma>' \<sigma>. \<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
                  player_tangle_strat t \<sigma>'; P' (S,\<sigma>)\<rbrakk> \<Longrightarrow> P' (S\<union>t,\<sigma>' |` (t-A) ++ \<sigma>)"
    using base own opponent escape by auto
  from attr base'
  have "P' (X,\<sigma>)"
    unfolding player_tangle_attractor_def
    apply (induction rule: tangle_attractor_step_rtranclp_induct)
    using own' opponent' escape' by auto
  thus ?thesis
    unfolding P'_def by simp
qed

lemma A_in_player_tangle_attractor: "player_tangle_attractor U \<sigma> \<Longrightarrow> A \<subseteq> U"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_mono by fastforce

lemma player_tangle_attractor_ss: "player_tangle_attractor U \<sigma> \<Longrightarrow> U \<subseteq> A \<union> V"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_ss by fastforce

lemma fin_player_tangle_attractor: "player_tangle_attractor U \<sigma> \<Longrightarrow> finite A \<Longrightarrow> finite U"
  using finite_subset[OF player_tangle_attractor_ss] by blast

lemma player_tangle_attractor_strat: "player_tangle_attractor U \<sigma> \<Longrightarrow>
      strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (U-A) \<and> ran \<sigma> \<subseteq> U \<and>
      induced_subgraph V\<^sub>\<alpha> \<sigma> `` (U-A) \<subseteq> U \<and>
      (\<forall>x\<in>U. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
        \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  using tangle_attractor_step_I_base tangle_attractor_step_rtranclp_I
  unfolding player_tangle_attractor_def tangle_attractor_step_I_def
  by clarsimp
end (** End of context with fixed A *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor. *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> player_tangle_attractor A A Map.empty"

lemma attracted_region_is_player_\<alpha>_max: "player_tangle_attractor A U \<sigma> \<Longrightarrow> player_\<alpha>_max U"
  unfolding player_\<alpha>_max_def
  apply (induction rule: player_tangle_attractor_induct)
  subgoal unfolding player_tangle_attractor_def by blast
  subgoal unfolding player_tangle_attractor_def by blast
  subgoal unfolding player_tangle_attractor_def by blast
  subgoal unfolding player_tangle_attractor_def by blast
  done

end (** End of context with fixed T *)

(** We need this version of the induction lemma so we can supply the properties of T without losing
    our case names. *)
lemma player_tangle_attractor_induct'[consumes 3, case_names base own opponent escape]:
  assumes attr: "player_tangle_attractor T A X \<sigma>"
  assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
  assumes fin_T: "finite T"
  assumes base: "P A Map.empty"
  assumes own: "\<And>x S y \<sigma>. \<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S; P S \<sigma>\<rbrakk> \<Longrightarrow> P (insert x S) (\<sigma>(x\<mapsto>y))"
  assumes opponent: "\<And>x S \<sigma>. \<lbrakk>x \<in> V\<^sub>\<beta> - S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S; P S \<sigma>\<rbrakk> \<Longrightarrow> P (insert x S) \<sigma>"
  assumes escape: "\<And>t S \<sigma>' \<sigma>. \<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
                   player_tangle_strat t \<sigma>'; P S \<sigma>\<rbrakk> \<Longrightarrow> P (S\<union>t) (\<sigma>' |` (t-A) ++ \<sigma>)"
  shows "P X \<sigma>"
  using player_tangle_attractor_induct[OF tangles_T fin_T attr] base own opponent escape by blast

end (** End of context player_paritygame *)

section \<open>Tangle Attractors for Specific Players\<close>
context paritygame begin

fun tangle_attractor :: "player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_attractor EVEN = P0.player_tangle_attractor"
| "tangle_attractor ODD = P1.player_tangle_attractor"

lemma A_in_tangle_attractor:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A U \<sigma> \<Longrightarrow> A \<subseteq> U"
  using assms P0.A_in_player_tangle_attractor P1.A_in_player_tangle_attractor
  by (cases \<alpha>; simp)

lemma tangle_attractor_ss:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A U \<sigma> \<Longrightarrow> U \<subseteq> A \<union> V"
  using assms P0.player_tangle_attractor_ss P1.player_tangle_attractor_ss
  by (cases \<alpha>; simp)

lemma tangle_attractor_strat:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A U \<sigma> \<Longrightarrow>
         strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = V_player \<alpha> \<inter> (U-A) \<and> ran \<sigma> \<subseteq> U \<and>
         induced_subgraph (V_player \<alpha>) \<sigma> `` (U-A) \<subseteq> U \<and>
         (\<forall>x\<in>U. \<forall>xs ys. lasso_from_node (induced_subgraph (V_player \<alpha>) \<sigma>) x xs ys
            \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys)"
  unfolding strategy_of_player_def
  using assms P0.player_tangle_attractor_strat P1.player_tangle_attractor_strat
  by (cases \<alpha>; simp add: V\<^sub>1_def)

subsection \<open>\<alpha>-maximal regions\<close>
fun \<alpha>_max :: "player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> bool" where
  "\<alpha>_max EVEN = P0.player_\<alpha>_max"
| "\<alpha>_max ODD = P1.player_\<alpha>_max"
end (** End of context paritygame *)

end
