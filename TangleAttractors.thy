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
subsection \<open>Tangle Attractors as Inductive Sets\<close>
inductive_set player_tangle_attractor :: "'v set \<Rightarrow> 'v set" for A where
  base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor A"
| own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y) \<in> E; y \<in> player_tangle_attractor A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor A"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> player_tangle_attractor A\<rbrakk>
              \<Longrightarrow> x \<in> player_tangle_attractor A"
| escape: "\<lbrakk>x \<in> t; t \<in> T; t \<inter> A = {}; opponent_escapes t \<noteq> {};
            \<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> player_tangle_attractor A\<rbrakk>
            \<Longrightarrow> x \<in> player_tangle_attractor A"

lemma A_in_player_tangle_attractor: "A \<subseteq> player_tangle_attractor A"
  using player_tangle_attractor.base by fast

subsection \<open>Tangle Attractors as an Inductive Predicate\<close>
context
  fixes A :: "'v set"
begin
inductive attractor_step :: "'v set \<Rightarrow> 'v set \<Rightarrow> bool" where
  own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S\<rbrakk> \<Longrightarrow> attractor_step S (insert x S)"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S\<rbrakk> \<Longrightarrow> attractor_step S (insert x S)"
| escape: "\<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S\<rbrakk>
              \<Longrightarrow> attractor_step S (S \<union> t)"

definition player_tangle_attractor_I :: "'v set \<Rightarrow> bool" where
  "player_tangle_attractor_I S \<equiv> \<exists>\<sigma>.
      strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A) \<and> ran \<sigma> \<subseteq> S
    \<and> induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S
    \<and> (\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
        \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"

lemma attractor_step_mono: "attractor_step S S' \<Longrightarrow> S \<subset> S'"
  by (induction rule: attractor_step.induct) auto

lemma attractor_step_in_S_Un_V: "attractor_step S S' \<Longrightarrow> S' \<subseteq> S \<union> V"
  apply (induction rule: attractor_step.induct)
    subgoal using V\<^sub>\<alpha>_subset by auto
    subgoal by fast
    subgoal using tangles_T player_tangle_in_V by blast
  done

lemma attractor_step_in_V: "attractor_step S S' \<Longrightarrow> S \<subseteq> V \<Longrightarrow> S' \<subseteq> V"
  using attractor_step_in_S_Un_V by blast

lemma "attractor_step S S' \<Longrightarrow> V-S' \<subseteq> V-S"
  using attractor_step_mono by blast

lemma "attractor_step S S' \<Longrightarrow> S \<subseteq> V \<Longrightarrow> V-S' \<subset> V-S"
  using attractor_step_mono attractor_step_in_V by blast

lemma player_tangle_attractor_I_base:
  "player_tangle_attractor_I A"
  unfolding player_tangle_attractor_I_def
  apply (rule exI[where x="Map.empty"]; intro conjI; simp)
  using origin_in_lasso by fastforce

lemma player_tangle_attractor_I_step:
  "attractor_step S S' \<Longrightarrow> A\<subseteq>S \<Longrightarrow> player_tangle_attractor_I S \<Longrightarrow> player_tangle_attractor_I S'"
proof (induction rule: attractor_step.induct)
  case (own x S y)
  from own.prems obtain \<sigma> where
    \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "(\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
        \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
    unfolding player_tangle_attractor_I_def
    by auto

  from own.hyps(1,2) have new_strat: "strategy_of V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])"
    using strategy_of_add_same[OF \<sigma>_strat strategy_of_map_assign] by blast

  from own.hyps(1) own.prems(1) \<sigma>_dom have new_dom: "dom (\<sigma> ++ [x\<mapsto>y]) = V\<^sub>\<alpha> \<inter> (insert x S - A)"
    by auto

  from own.hyps(3) \<sigma>_ran have new_ran: "ran (\<sigma> ++ [x\<mapsto>y]) \<subseteq> (insert x S)"
    unfolding ran_def by auto

  from \<sigma>_closed \<sigma>_ran own.hyps(1)
  have new_closed_S: "induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y]) `` (S-A) \<subseteq> S"
    unfolding induced_subgraph_def E_of_strat_def
    by (auto split: if_splits simp: ranI)
  with own.hyps(1,3) have new_closed:
    "induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y]) `` (insert x S - A) \<subseteq> insert x S"
    using ind_subgraph_to_strategy[of _ _ V\<^sub>\<alpha> "\<sigma> ++ [x\<mapsto>y]"] by fastforce

  have new_forces_A_or_wins:
    "\<forall>v\<in>insert x S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])) v xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
  proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_S': "v \<in> insert x S" and
           lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])) v xs ys"
    from lasso_v_xs_ys obtain v' where
      cycle_v'_ys: "cycle (induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])) v' ys"
      unfolding lasso_from_node_def by auto

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_S' have v_in_S'_min_A: "v \<in> insert x S - A"
        using origin_in_lasso[OF lasso_v_xs_ys] by blast

      from lasso_from_node_partially_closed_sets[OF this new_closed xs_no_A ys_no_A lasso_v_xs_ys]
      have ys_in_S'_min_A: "set ys \<subseteq> insert x S - A" by simp
      hence y_in_S'_min_A: "v' \<in> insert x S - A"
        using origin_in_cycle[OF cycle_v'_ys] by auto

      consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
      hence "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys \<and> v'\<in>S" proof cases
        case ys_has_x
        from own.hyps(1,2) obtain ys' where
          cycle_y_ys': "cycle (induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])) y ys'" and
          sets_eq: "set ys' = set ys" and
          y_in_ys': "y \<in> set ys'"
          using cycle_intermediate_node[OF cycle_v'_ys ys_has_x]
          apply clarsimp
          subgoal for vs'
            using cycle_D[of "induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y])" x vs']
            using ind_subgraph_to_strategy by fastforce
          done

        from own.hyps(3) sets_eq y_in_ys' ys_no_A have "y \<in> S-A" by blast
        from cycle_partially_closed_set[OF this new_closed_S cycle_y_ys'] sets_eq ys_no_A
        have "set ys \<subseteq> S - A" by simp
        with ys_has_x own.hyps(1) show ?thesis by blast
      next
        case ys_no_x
        from own.hyps(1) have subset:
          "induced_subgraph V\<^sub>\<alpha> (\<sigma> ++ [x\<mapsto>y]) \<inter> (S-A)\<times>(S-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
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

  show ?case
    unfolding player_tangle_attractor_I_def
    apply (rule exI[where x="\<sigma> ++ [x\<mapsto>y]"]; intro conjI)
      subgoal using new_strat .
      subgoal using new_dom .
      subgoal using new_ran .
      subgoal using new_closed .
      subgoal using new_forces_A_or_wins .
    done

next
  case (opponent x S)
  from opponent.prems obtain \<sigma> where
    \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "(\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
        \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
    unfolding player_tangle_attractor_I_def
    by auto

  have \<sigma>_closed_S': "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (insert x S - A) \<subseteq> insert x S"
    using \<sigma>_closed_S opponent.hyps(2) by auto

  have \<sigma>_forces_A_or_wins_S':
    "\<forall>x\<in>insert x S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
    \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
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

  show ?case
    unfolding player_tangle_attractor_I_def
    apply (rule exI[where x="\<sigma>"]; intro conjI)
      subgoal using \<sigma>_strat .
      subgoal using \<sigma>_dom opponent.hyps(1) by force
      subgoal using \<sigma>_ran by auto
      subgoal using \<sigma>_closed_S' .
      subgoal using \<sigma>_forces_A_or_wins_S' .
    done

next
  case (escape t S)
  from escape.prems obtain \<sigma> where
    \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (S - A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> S" and
    \<sigma>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S - A) \<subseteq> S" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    unfolding player_tangle_attractor_I_def by auto

  from escape.hyps(1) have t_tangle: "player_tangle t" using tangles_T by simp

  from t_tangle have
    t_notempty: "t \<noteq> {}" and
    t_in_V: "t \<subseteq> V"
    using player_tangle_in_V by auto

  from t_tangle obtain \<sigma>' where
   \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> \<sigma>'" and
   \<sigma>'_dom: "dom \<sigma>' = t \<inter> V\<^sub>\<alpha>" and
   \<sigma>'_ran: "ran \<sigma>' \<subseteq> t" and
   \<sigma>'_strongly_connected_subgraph: "strongly_connected (player_tangle_subgraph t \<sigma>')" and
   \<sigma>'_winning: "\<forall>v\<in>t. \<forall>xs. cycle (player_tangle_subgraph t \<sigma>') v xs \<longrightarrow> winning_player xs"
    unfolding player_tangle_def is_player_tangle_strat_def Let_def by auto

  define \<tau> where "\<tau> = (\<sigma>' |` (t-A)) ++ \<sigma>"
  have \<tau>_strat: "strategy_of V\<^sub>\<alpha> \<tau>"
  proof -
    from \<sigma>'_strat have "strategy_of V\<^sub>\<alpha> (\<sigma>' |` (t-A))"
      unfolding strategy_of_def E_of_strat_def
      apply (simp; safe)
        subgoal for x y by blast
        subgoal for x y using restrict_in[of x "t-A" \<sigma>'] by fastforce
      done
      from strategy_of_add_same[OF this \<sigma>_strat] show ?thesis
        unfolding \<tau>_def by blast
  qed

  from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom \<tau> =  V\<^sub>\<alpha> \<inter> (S \<union> t - A)"
    unfolding \<tau>_def by auto

  have \<tau>_ran: "ran \<tau> \<subseteq> S\<union>t"
  proof -
    have "ran (\<sigma>' |` (t-A)) \<subseteq> t"
      using subsetD[OF \<sigma>'_ran] ran_restrictD[of _ \<sigma>' "t-A"] ranI by fast
    with \<sigma>_ran show ?thesis
      unfolding \<tau>_def ran_def by blast
  qed

  have \<tau>_closed_S: "induced_subgraph V\<^sub>\<alpha> \<tau> `` (S-A) \<subseteq> S"
  proof (rule subsetI)
    fix y assume y_succ: "y\<in>induced_subgraph V\<^sub>\<alpha> \<tau> `` (S-A)"
    then obtain x where
      x_y_edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<tau>" and
      x_in_S_min_A: "x\<in>S-A"
      by blast
    consider (in_\<tau>) "x \<in> dom \<tau>" | (notin_\<tau>) "x \<notin> dom \<tau>" by blast
    thus "y \<in> S" proof cases
      case in_\<tau>
      with \<tau>_dom have x_in_V\<^sub>\<alpha>: "x \<in> V\<^sub>\<alpha>" by simp
      from ind_subgraph_to_strategy[OF x_y_edge x_in_V\<^sub>\<alpha>] have \<tau>_x_y: "\<tau> x = Some y" .

      from x_in_V\<^sub>\<alpha> \<tau>_x_y \<sigma>_dom \<sigma>_ran x_in_S_min_A show ?thesis
        unfolding \<tau>_def by (simp add: map_add_dom_app_simps(1) ranI subsetD)
    next
      case notin_\<tau>
      with x_y_edge \<tau>_dom x_in_S_min_A
      have x_y_edge_\<sigma>: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>"
        using ind_subgraph_notin_dom by auto
      with \<sigma>_closed_S x_in_S_min_A show ?thesis by blast
    qed
  qed

  have \<tau>_closed_S': "induced_subgraph V\<^sub>\<alpha> \<tau> `` (S\<union>t-A) \<subseteq> S\<union>t"
  proof (rule subsetI)
    fix y assume y_succ: "y\<in>induced_subgraph V\<^sub>\<alpha> \<tau> `` (S\<union>t-A)"
    then obtain x where
      x_y_edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<tau>" and
      x_in_S'_min_A: "x\<in>S\<union>t-A"
      by blast

    consider (in_\<tau>) "x \<in> dom \<tau>" | (notin_\<tau>) "x \<notin> dom \<tau>" by blast
    thus "y\<in>S\<union>t" proof cases
      case in_\<tau> with \<tau>_dom \<tau>_ran show ?thesis
        using ind_subgraph_edge_dst[OF x_y_edge] by blast
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
              by blast
          done
      qed
    qed
  qed

  have \<tau>_forces_A_or_wins:
    "\<forall>x\<in>S \<union> t. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<tau>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
  proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_S': "v\<in>S\<union>t" and
           lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<tau>) v xs ys"
    from lasso_v_xs_ys obtain v' where
      cycle_v'_ys: "cycle (induced_subgraph V\<^sub>\<alpha> \<tau>) v' ys"
      unfolding lasso_from_node_def by blast

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_S' have "v\<in>(S\<union>t)-A"
        using origin_in_lasso[OF lasso_v_xs_ys] by blast

      from lasso_from_node_partially_closed_sets[OF this \<tau>_closed_S' xs_no_A ys_no_A lasso_v_xs_ys]
      have ys_in_S'_min_A: "set ys \<subseteq> (S\<union>t)-A" by simp
      hence v'_in_S'_min_A: "v' \<in> (S\<union>t)-A"
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
          cycle_y_ys': "cycle (induced_subgraph V\<^sub>\<alpha> \<tau>) y ys'"
          using cycle_intermediate_node[OF cycle_v'_ys] by fastforce

        from cycle_partially_closed_set[OF y_in_S_min_A \<tau>_closed_S cycle_y_ys' ys'_no_A] sets_eq
        have ys_in_S_min_A: "set ys \<subseteq> S-A" by blast
        hence v'_in_S: "v' \<in> S" using origin_in_cycle[OF cycle_v'_ys] by blast

        from \<sigma>_dom have subset: "induced_subgraph V\<^sub>\<alpha> \<tau> \<inter> (S-A)\<times>(S-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
          unfolding \<tau>_def induced_subgraph_def E_of_strat_def by auto

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle_v'_ys ys_in_S_min_A]]
        have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys"
          by (simp add: cycle_iff_loop loop_impl_lasso)

        with \<sigma>_forces_A_or_wins v'_in_S no_A show ?thesis by fastforce
      next
        case ys_no_S
        with ys_in_S'_min_A have ys_in_t_min_S_min_A: "set ys \<subseteq> t-S-A" by blast
        hence v'_in_t: "v'\<in>t" using origin_in_cycle[OF cycle_v'_ys] by blast

        from \<sigma>_ran t_in_V have subset:
          "induced_subgraph V\<^sub>\<alpha> \<tau> \<inter> (t-S-A)\<times>(t-S-A) \<subseteq> player_tangle_subgraph t \<sigma>' \<inter> (t-S-A)\<times>(t-S-A)"
          unfolding \<tau>_def induced_subgraph_def player_tangle_subgraph_def E_of_strat_def
          using ind_subgraph_edge_dst[of _ _ V\<^sub>\<alpha> \<sigma>] strategy_to_ind_subgraph[of \<sigma> _ _ V\<^sub>\<alpha>]
          by fastforce

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle_v'_ys ys_in_t_min_S_min_A]]
        have "cycle (player_tangle_subgraph t \<sigma>') v' ys" using restr_V_cycle by fast

        with \<sigma>'_winning v'_in_t show ?thesis by blast
      qed
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed

  show ?case
    unfolding player_tangle_attractor_I_def
    apply (rule exI[where x="\<tau>"]; intro conjI)
      subgoal using \<tau>_strat .
      subgoal using \<tau>_dom .
      subgoal using \<tau>_ran .
      subgoal using \<tau>_closed_S' .
      subgoal using \<tau>_forces_A_or_wins .
    done
qed

definition is_player_tangle_attractor :: "'v set \<Rightarrow> bool" where
  "is_player_tangle_attractor \<equiv> attractor_step\<^sup>*\<^sup>* A"

lemma attractor_step_rtranclp_subset: "attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> S \<subseteq> S'"
  apply (induction rule: rtranclp_induct)
  using attractor_step_mono by blast+

lemma attractor_step_rtrancl:
  "attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> A \<subseteq> S \<Longrightarrow> player_tangle_attractor_I S \<Longrightarrow> player_tangle_attractor_I S'"
  apply (induction rule: rtranclp_induct; simp)
  using attractor_step_rtranclp_subset player_tangle_attractor_I_step by fast
end (** End of context with fixed A *)

lemma "is_player_tangle_attractor A S \<Longrightarrow> player_tangle_attractor_I A S"
  unfolding is_player_tangle_attractor_def
  using player_tangle_attractor_I_base attractor_step_rtrancl by blast

lemma "is_player_tangle_attractor A (player_tangle_attractor A)"
  unfolding is_player_tangle_attractor_def
  sorry ,xxx sorry (** I do not know how to prove this right now. *)
end (** End of context with fixed T *)
end (** End of context player_paritygame *)

end
