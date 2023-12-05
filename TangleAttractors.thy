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

lemmas tangle_attractor_step_induct[consumes 1, case_names own opponent escape] =
  tangle_attractor_step.induct[
    of "(X,\<sigma>)" "(X',\<sigma>')" for X \<sigma> X' \<sigma>',
    where P="\<lambda>(a,b) (c,d). P a b c d" for P,
    unfolded split]
(** The tangle attractor step is monotonous with respect to the set of vertices in the attracted
    region. *)
lemma tangle_attractor_step_mono: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X \<subset> X'"
  by (induction rule: tangle_attractor_step_induct) auto

(** The tangle attractor step's result is always in the union of the original attractor set and V.
    This means that attractors to regions in V will be entirely in V. *)
lemma tangle_attractor_step_ss: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X' \<subseteq> (X\<union>V)"
  apply (induction rule: tangle_attractor_step_induct)
  subgoal using V\<^sub>\<alpha>_subset by auto
  subgoal by simp
  subgoal using tangles_T player_tangle_in_V by auto
  done

(* If the original region is finite, then the region obtained in one step of the tangle attractor
   is also finite. *)
lemma fin_tangle_attractor_step:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); finite X\<rbrakk> \<Longrightarrow> finite X'"
  using finite_subset[OF tangle_attractor_step_ss] by blast

(** We define an invariant for the properties of the constructed strategy in tangle_attractor_step. *)
definition tangle_attractor_step_I :: "'v set \<times> 'v strat \<Rightarrow> bool" where
  "tangle_attractor_step_I \<equiv> \<lambda>(X,\<sigma>). A \<subseteq> X \<and>
   strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A) \<and> ran \<sigma> \<subseteq> X \<and>
   induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X-A) \<subseteq> X \<and>
   (\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"

(** The invariant is true for the initial state of the tangle attractor. *)
lemma tangle_attractor_step_I_base: "tangle_attractor_step_I (A,Map.empty)"
  unfolding tangle_attractor_step_I_def split using origin_in_lasso by fastforce

lemma tangle_attractor_step_strat_of_V\<^sub>\<alpha>:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
   \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>'"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal unfolding strategy_of_def E_of_strat_def by (auto split: if_splits)
  subgoal by fast
  subgoal unfolding player_tangle_strat_def strategy_of_def E_of_strat_def
    apply (safe; clarsimp split: if_splits simp: restrict_map_def) by blast+
  done

lemma tangle_attractor_step_dom:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  unfolding player_tangle_strat_def by auto

lemma tangle_attractor_step_ran:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> ran \<sigma>' \<subseteq> X'"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal by fastforce
  subgoal by blast
  subgoal for t using ran_restrictD[of _ _ "t-A"] unfolding player_tangle_strat_def ran_def by fast
  done

lemma tangle_attractor_step_closed:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma>' `` (X'-A) \<subseteq> X'"
  unfolding tangle_attractor_step_I_def split
proof (induction rule: tangle_attractor_step_induct)
  case (own x X y \<sigma>) thus ?case
    unfolding induced_subgraph_def E_of_strat_def
    by (auto split: if_splits simp: in_mono ranI)
next
  case (opponent x X \<sigma>) thus ?case by auto
next
  case (escape t X \<sigma>' \<sigma>)
  hence dom: "dom (\<sigma>' |` (t - A) ++ \<sigma>) = V\<^sub>\<alpha> \<inter> (t \<union> X - A)" and
  \<sigma>_ran: "ran \<sigma> \<subseteq> X" and \<sigma>'_ran: "ran \<sigma>' \<subseteq> t" and
  \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X - A) \<subseteq> X"
    unfolding player_tangle_strat_def by auto
  from \<sigma>_ran \<sigma>'_ran have ran: "ran (\<sigma>' |` (t - A) ++ \<sigma>) \<subseteq> (t \<union> X)"
    using ran_restrictD
    unfolding ran_def by fast
  show ?case proof (rule subsetI)
    fix y assume y_in_succs: "y \<in> induced_subgraph V\<^sub>\<alpha> (\<sigma>' |` (t - A) ++ \<sigma>) `` (X \<union> t - A)"
    then obtain x where
      edge: "(x,y) \<in> induced_subgraph V\<^sub>\<alpha> (\<sigma>' |` (t - A) ++ \<sigma>)" and
      x_in_X_t_min_A: "x \<in> X \<union> t -A" by blast
    consider (in_dom) "x \<in> dom (\<sigma>' |` (t - A) ++ \<sigma>)" | (notin_dom) "x \<notin> dom (\<sigma>' |` (t - A) ++ \<sigma>)" by fast
    thus "y \<in> X \<union> t" proof cases
      case in_dom
      with dom have "x \<in> V\<^sub>\<alpha>" by simp
      with ran show ?thesis using edge ind_subgraph_edge_dst by fastforce
    next
      case notin_dom
      with edge dom x_in_X_t_min_A have edge_\<sigma>: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>"
        using ind_subgraph_notin_dom by auto
      consider (in_X_min_A) "x \<in> X-A" | (notin_X_min_A) "x \<notin> X-A" by blast
      thus ?thesis proof cases
        case in_X_min_A with edge_\<sigma> \<sigma>_closed show ?thesis by blast
      next
        case notin_X_min_A
      with x_in_X_t_min_A have "x \<in> t-A" by blast
      thus ?thesis
        apply (cases "y \<in> opponent_escapes t")
        subgoal using \<open>opponent_escapes t \<subseteq> X\<close> by blast
        subgoal unfolding opponent_escapes_def
          using notin_dom dom ind_subgraph_edge_in_E[OF edge] E_in_V
          by clarsimp blast
        done
      qed
    qed
  qed
qed

(** This reuses proofs from the previous lemmas. Either I merge them again, or rephrase my lemmas
    so they can reuse one another somehow. *)
lemma tangle_attractor_step_forces_A_or_wins:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> (\<forall>x\<in>X'. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>') x xs ys
        \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
  unfolding tangle_attractor_step_I_def split
proof (induction rule: tangle_attractor_step_induct)
  case (own x X y \<sigma>)
  let ?X' = "insert x X"
  let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
  from own have \<sigma>_forces_A_or_wins:
    "\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  from own have \<sigma>'_closed_X: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (X-A) \<subseteq> X"
    unfolding induced_subgraph_def E_of_strat_def
    by (auto split: if_splits simp: ranI)
  with own.hyps(1,3) have \<sigma>'_closed: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (?X'-A) \<subseteq> ?X'"
    using ind_subgraph_to_strategy by fastforce
  show ?case proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_X': "v \<in> ?X'" and lasso: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v xs ys"
    from lasso obtain v' where
      cycle: "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v' ys"
      unfolding lasso_from_node_def by auto

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_X' have v_in_X'_min_A: "v \<in> ?X' - A"
        using origin_in_lasso[OF lasso] by blast

      from lasso_from_node_partially_closed_sets[OF this \<sigma>'_closed xs_no_A ys_no_A lasso]
      have ys_in_X'_min_A: "set ys \<subseteq> ?X' - A" by simp
      hence y_in_X'_min_A: "v' \<in> ?X' - A"
        using origin_in_cycle[OF cycle] by auto

      consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
      hence "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys \<and> v'\<in>X" proof cases
        case ys_has_x
        from own.hyps(1,2) obtain ys' where
          cycle': "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') y ys'" and
          sets_eq: "set ys' = set ys" and
          y_in_ys': "y \<in> set ys'"
          using cycle_intermediate_node[OF cycle ys_has_x]
          apply clarsimp
          subgoal for vs'
            using cycle_D[of "induced_subgraph V\<^sub>\<alpha> ?\<sigma>'" x vs']
            using ind_subgraph_to_strategy by fastforce
          done

        from own.hyps(3) sets_eq y_in_ys' ys_no_A have "y \<in> X-A" by blast
        from cycle_partially_closed_set[OF this \<sigma>'_closed_X cycle'] sets_eq ys_no_A
        have "set ys \<subseteq> X-A" by simp
        with ys_has_x own.hyps(1) show ?thesis by blast
      next
        case ys_no_x
        from own.hyps(1) have subset:
          "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' \<inter> (X-A)\<times>(X-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
          unfolding induced_subgraph_def E_of_strat_def
          by (auto split: if_splits)

        from ys_no_x ys_in_X'_min_A have ys_in_X_min_A: "set ys \<subseteq> X-A" by blast
        from subgraph_cycle[OF subset cycle_restr_V[OF cycle this]]
        have cycle_\<sigma>: " cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' ys " .

        with ys_in_X_min_A have "v' \<in> X-A"
          using origin_in_cycle by fast
        with cycle_\<sigma> show ?thesis by (simp add: cycle_iff_lasso)
      qed
      with \<sigma>_forces_A_or_wins ys_no_A show ?thesis by fastforce
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed
next
  case (opponent x X \<sigma>)
  let ?X' = "insert x X"

  from opponent have \<sigma>_closed_X: " induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X - A) \<subseteq> X" by blast
  with opponent.hyps(2) have \<sigma>_closed_X': "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (?X'-A) \<subseteq> ?X'" by auto
  from opponent have \<sigma>_forces_A_or_wins:
    "\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys" by simp

  show ?case proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_X': "v \<in> ?X'" and lasso: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs ys"
    from lasso obtain v' where
      cycle: "cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' ys"
      unfolding lasso_from_node_def by blast

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_X' have "v \<in> ?X' - A"
        using origin_in_lasso[OF lasso] by blast

      from lasso_from_node_partially_closed_sets[OF this \<sigma>_closed_X' xs_no_A ys_no_A lasso]
      have ys_in_X'_min_A: "set ys \<subseteq> ?X'-A" by simp
      hence v'_in_X'_min_A: "v' \<in> ?X'-A"
        using origin_in_cycle[OF cycle] by blast

      consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
      hence "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys \<and> v' \<in> X" proof cases
        case ys_has_x
        from opponent.hyps(1,2) obtain y ys' where
          x_y_edge: "(x,y) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>" and
          y_in_X: "y \<in> X" and
          cycle': "cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) y ys'" and
          sets_eq: "set ys' = set ys" and
          y_in_ys: "y \<in> set ys"
          using cycle_intermediate_node[OF cycle ys_has_x]
          apply clarsimp
          subgoal for vs'
            using cycle_D[of "induced_subgraph V\<^sub>\<alpha> \<sigma>" x vs']
            using ind_subgraph_to_strategy by blast
          done

        from y_in_X y_in_ys ys_no_A have y_in_S_min_A: "y \<in> X-A" by blast
        from cycle_partially_closed_set[OF this \<sigma>_closed_X cycle'] sets_eq ys_no_A
        have "set ys \<subseteq> X-A" by auto
        hence "v' \<in> X"
          using origin_in_cycle[OF cycle] by blast

        with cycle show ?thesis by (simp add: cycle_iff_lasso)
      next
        case ys_no_x
        with ys_in_X'_min_A have ys_in_S_min_A: "set ys \<subseteq> X-A" by blast
        with origin_in_cycle[OF cycle] have v'_in_S_min_A: "v' \<in> X-A" by blast
        with cycle show ?thesis by (simp add: cycle_iff_lasso)
      qed

      with \<sigma>_forces_A_or_wins no_A show ?thesis by fastforce
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed
next
  case (escape t X \<tau> \<sigma>)
  let ?X' = "X \<union> t"
  let ?\<sigma>' = "(\<tau> |` (t - A) ++ \<sigma>)"

  from escape have \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X - A)" and \<tau>_dom: "dom \<tau> = t \<inter> V\<^sub>\<alpha>" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> X" and t_in_V: "t \<subseteq> V" and
    \<sigma>_closed_X: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X - A) \<subseteq> X" and
    \<tau>_winning: "\<forall>v\<in>t. \<forall>xs. cycle (player_tangle_subgraph t \<tau>) v xs \<longrightarrow> winning_player xs" and
    \<sigma>_forces_A_or_wins:
      "\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
        \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    unfolding player_tangle_strat_def Let_def
    using player_tangle_in_V tangles_T by auto
  from \<sigma>_dom \<tau>_dom have \<sigma>'_dom: "dom ?\<sigma>' =  V\<^sub>\<alpha> \<inter> (?X'-A)" by auto

  from escape have \<sigma>'_ran: "ran ?\<sigma>' \<subseteq> ?X'"
    unfolding player_tangle_strat_def
    using ran_restrictD
    unfolding ran_def by fast

  have \<sigma>'_closed_X: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (X-A) \<subseteq> X"
  proof (rule subsetI)
    fix y assume "y\<in>induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (X-A)"
    then obtain x where
      edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> ?\<sigma>'" and
      x_in_X_min_A: "x\<in>X-A"
      by blast
    consider (in_dom) "x \<in> dom ?\<sigma>'" | (notin_dom) "x \<notin> dom ?\<sigma>'" by fast
    thus "y \<in> X" proof cases
      case in_dom
      with \<sigma>'_dom have x_in_V\<^sub>\<alpha>: "x \<in> V\<^sub>\<alpha>" by simp
      with \<sigma>_closed_X edge x_in_X_min_A \<sigma>_dom
      show ?thesis
        using ind_subgraph_edge_in_E ind_subgraph_to_strategy[OF edge \<open>x\<in>V\<^sub>\<alpha>\<close>]
          strategy_to_ind_subgraph
        by blast
    next
      case notin_dom
      with edge \<sigma>'_dom x_in_X_min_A
      have "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>"
        using ind_subgraph_notin_dom by auto
      with \<sigma>_closed_X x_in_X_min_A show ?thesis by blast
    qed
  qed

  have \<sigma>'_closed_X': "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (?X'-A) \<subseteq> ?X'"
  proof (rule subsetI)
    fix y assume "y\<in>induced_subgraph V\<^sub>\<alpha> ?\<sigma>' `` (?X'-A)"
    then obtain x where
      edge: "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> ?\<sigma>'" and
      x_in_X'_min_A: "x\<in>?X'-A"
      by blast

    consider (in_dom) "x \<in> dom ?\<sigma>'" | (notin_dom) "x \<notin> dom ?\<sigma>'" by fast
    thus "y\<in>?X'" proof cases
      case in_dom with \<sigma>'_dom \<sigma>'_ran show ?thesis
        using ind_subgraph_edge_dst[OF edge] by auto
    next
      case notin_dom
      consider (in_X_min_A) "x \<in> X-A" | (notin_X_min_A) "x \<notin> X-A" by blast
      thus ?thesis proof cases
        case in_X_min_A with edge \<sigma>'_closed_X show ?thesis by blast
      next
        case notin_X_min_A
        with x_in_X'_min_A have x_in_t_min_A: "x \<in> t-A" by blast
        thus ?thesis
          apply (cases "y\<in>opponent_escapes t")
          subgoal using escape.hyps(4) by blast
          subgoal unfolding opponent_escapes_def
            using notin_dom \<sigma>'_dom ind_subgraph_edge_in_E[OF edge] E_in_V
            by clarsimp blast
          done
      qed
    qed
  qed

  show ?case proof (intro ballI allI impI)
    fix v xs ys
    assume v_in_X': "v\<in>?X'" and lasso: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v xs ys"
    from lasso obtain v' where
      cycle: "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') v' ys"
      unfolding lasso_from_node_def by blast

    have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
    proof -
      assume no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with v_in_X' have "v\<in>?X'-A"
        using origin_in_lasso[OF lasso] by blast

      from lasso_from_node_partially_closed_sets[OF this \<sigma>'_closed_X' xs_no_A ys_no_A lasso]
      have ys_in_X'_min_A: "set ys \<subseteq> ?X'-A" by simp
      hence v'_in_X'_min_A: "v' \<in> ?X'-A"
        using origin_in_cycle[OF cycle] by blast

      consider (ys_has_X) "set ys \<inter> X \<noteq> {}" | (ys_no_X) "set ys \<inter> X = {}" by blast
      thus ?thesis proof cases
        (** In this case, the cycle must be entirely contained in X because X is closed under
            \<sigma>'. That also means it is won because under \<sigma>, all plays that do not go through A
            are winning. *)
        case ys_has_X
        with ys_no_A obtain y ys' where
          y_in_X_min_A: "y \<in> X-A" and
          sets_eq: "set ys' = set ys" and
          ys'_no_A: "set ys' \<inter> A = {}" and
          cycle': "cycle (induced_subgraph V\<^sub>\<alpha> ?\<sigma>') y ys'"
          using cycle_intermediate_node[OF cycle] by fastforce

        from cycle_partially_closed_set[OF y_in_X_min_A \<sigma>'_closed_X cycle' ys'_no_A] sets_eq
        have ys_in_X_min_A: "set ys \<subseteq> X-A" by blast
        hence v'_in_X: "v' \<in> X" using origin_in_cycle[OF cycle] by blast

        from \<sigma>_dom have subset: "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' \<inter> (X-A)\<times>(X-A) \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
          unfolding induced_subgraph_def E_of_strat_def by auto

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle ys_in_X_min_A]]
        have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v' [] ys"
          by (simp add: cycle_iff_loop loop_impl_lasso)

        with \<sigma>_forces_A_or_wins v'_in_X no_A show ?thesis by fastforce
      next
        case ys_no_X
        with ys_in_X'_min_A have ys_in_t_min_X_min_A: "set ys \<subseteq> t-X-A" by blast
        hence v'_in_t: "v'\<in>t" using origin_in_cycle[OF cycle] by blast

        from \<sigma>_ran t_in_V have subset:
          "induced_subgraph V\<^sub>\<alpha> ?\<sigma>' \<inter> (t-X-A)\<times>(t-X-A) \<subseteq> player_tangle_subgraph t \<tau> \<inter> (t-X-A)\<times>(t-X-A)"
          unfolding induced_subgraph_def player_tangle_subgraph_def E_of_strat_def
          using ind_subgraph_edge_dst[of _ _ V\<^sub>\<alpha> \<sigma>] strategy_to_ind_subgraph[of \<sigma> _ _ V\<^sub>\<alpha>]
          by fastforce

        from subgraph_cycle[OF subset cycle_restr_V[OF cycle ys_in_t_min_X_min_A]]
        have "cycle (player_tangle_subgraph t \<tau>) v' ys" using restr_V_cycle by fast

        with \<tau>_winning v'_in_t show ?thesis by blast
      qed
    qed
    thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
  qed
qed

(** The step preserves the invariant. *)
lemma tangle_attractor_step_I_preserved:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> tangle_attractor_step_I (X',\<sigma>')"
  using tangle_attractor_step_strat_of_V\<^sub>\<alpha>[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_dom[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_ran[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_closed[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_forces_A_or_wins[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_mono[of X \<sigma> X' \<sigma>']
  unfolding tangle_attractor_step_I_def
  by simp blast

(** We will be using the reflexive transitive closure of the step relation for our final definition.
    To prove properties of the final definition, we will therefore need to prove them for the
    reflexive transitive closure first. *)

(** The reflexive transitive closure of steps is monotonous over the obtained region. This is less
    strict than our monotonicity property for the individual steps because of the reflexivity. *)
lemma tangle_attractor_step_rtranclp_mono: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S \<subseteq> fst S'"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal for y z using tangle_attractor_step_mono[of "fst y" "snd y" "fst z" "snd z"] by simp
  done

(** The reflexive transitive closure of steps yields a subset of the union of the original set with
    V. If we attract to a region in V, then the result will always be in V. *)
lemma tangle_attractor_step_rtranclp_ss: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> fst S' \<subseteq> (fst S \<union> V)"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal for y z using tangle_attractor_step_ss[of "fst y" "snd y" "fst z" "snd z"] by auto
  done

(** The region in the result of the reflexive transitive closure of steps is finite if the original
    set is finite. *)
lemma fin_tangle_attractor_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> finite (fst S)
  \<Longrightarrow> finite (fst S')"
  using finite_subset[OF tangle_attractor_step_rtranclp_ss] by blast

(** The reflexive transitive closure of the tangle attractor step preserves the strategy invariant. *)
lemma tangle_attractor_step_rtranclp_preserves_I:
  "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_step_I S
  \<Longrightarrow> tangle_attractor_step_I S'"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal for y z using tangle_attractor_step_I_preserved[of "fst y" "snd y" "fst z" "snd z"] by force
  done

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
  "player_tangle_attractor X \<sigma> \<Longrightarrow> \<exists>\<sigma>'. tangle_attractor_step_I (X,\<sigma>') \<and> \<sigma> = \<sigma>' ++ A_target X"
  unfolding player_tangle_attractor_def
  using tangle_attractor_step_rtranclp_preserves_I[OF _ _ tangle_attractor_step_I_base]
  by auto

(** If we have a tangle-attracted region X and witness strategy \<sigma>, then that is a strategy for the
    player. *)
lemma player_tangle_attractor_strat_of_V\<^sub>\<alpha>:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>"
  using player_tangle_attractor_I_aux[of X \<sigma>] A_target_strat[of X]
  unfolding tangle_attractor_step_I_def
  by fastforce

(** If we have a tangle-attracted region X and witness strategy \<sigma>, then the domain of \<sigma> is some
    subset of all player-owned nodes in X. *)
lemma player_tangle_attractor_strat_dom:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] player_tangle_attractor_contains_A[of X \<sigma>]
        A_target_dom[of X]
  unfolding tangle_attractor_step_I_def
  by auto

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then the range of \<sigma> is in X.*)
lemma player_tangle_attractor_strat_ran:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> ran \<sigma> \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] A_target_ran[of X]
  unfolding tangle_attractor_step_I_def
  by (auto simp: ran_def)

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then the induced subgraph of \<sigma>
    is partially closed in X, excluding A. *)
lemma player_tangle_attractor_strat_partially_closed:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X-A) \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>]
  unfolding tangle_attractor_step_I_def A_target_def induced_subgraph_def E_of_strat_def
  by auto

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, and X is a closed region, then
    the induced subgraph of \<sigma> is also closed in X. This is a somewhat trivial property, but nice to
    have. *)
lemma closed_player_tangle_attractor_strat_closed:
  "\<lbrakk>player_tangle_attractor X \<sigma>; E `` X \<subseteq> X\<rbrakk> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` X \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] ind_subgraph[of V\<^sub>\<alpha> \<sigma>]
  unfolding tangle_attractor_step_I_def
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
    unfolding tangle_attractor_step_I_def
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
  unfolding tangle_attractor_step_I_def
  by auto

(** If we have an attracted region X and a witness strategy \<sigma>, and a player-owned node in X minus A,
    then that x is in the domain of \<sigma>. This is due to the invariant on \<sigma>'. *)
lemma player_tangle_attractor_strat_in_dom_not_A:
  "\<lbrakk>player_tangle_attractor X \<sigma>; x \<in> V\<^sub>\<alpha> \<inter> (X-A)\<rbrakk> \<Longrightarrow> x \<in> dom \<sigma>"
  using player_tangle_attractor_I_aux[of X \<sigma>]
  unfolding tangle_attractor_step_I_def
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

  from tangle_attractor_step_rtranclp_preserves_I[OF step_rtrancl _ tangle_attractor_step_I_base]
  have \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> X-A"
    unfolding tangle_attractor_step_I_def by auto

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
lemma player_tangle_attractor_finite: "\<lbrakk>player_tangle_attractor X \<sigma>; finite A\<rbrakk> \<Longrightarrow> finite X"
  using finite_subset[OF player_tangle_attractor_ss] by blast

  (**tangle_attractor_step.induct[
    of "(X,\<sigma>)" "(X',\<sigma>')" for X \<sigma> X' \<sigma>',
    where P="\<lambda>(a,b) (c,d). P a b c d" for P,
    unfolded split]*)

lemmas tangle_attractor_step_rtranclp_induct[consumes 1, case_names base step] =
  rtranclp_induct[
    of "tangle_attractor_step" "(X,\<sigma>)" "(X',\<sigma>')" for X \<sigma> X' \<sigma>',
    where P="\<lambda>(a,b). P a b" for P,
    unfolded split]

lemma test: "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>');
        \<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom \<sigma>) \<sigma>) x xs x'\<rbrakk>
        \<Longrightarrow> \<forall>x\<in>X'. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom \<sigma>') \<sigma>') x xs x'"
proof (induction rule: tangle_attractor_step_induct)
  case (own x X y \<sigma>)
  hence "Restr (induced_subgraph (dom \<sigma>) \<sigma>) X = Restr (induced_subgraph (dom (\<sigma>(x\<mapsto>y))) (\<sigma>(x\<mapsto>y))) X"
    unfolding induced_subgraph_def E_of_strat_def
    by (auto split: if_splits)
  show ?case proof (intro ballI)
    fix v assume "v \<in> insert x X"
    consider (v_is_x) "v = x" | (v_not_x) "v \<noteq> x" by blast
    thus "\<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom (\<sigma>(x \<mapsto> y))) (\<sigma>(x \<mapsto> y))) v xs x'"
    proof cases
      case v_is_x
      then show ?thesis sorry
    next
      case v_not_x
      show ?thesis
    qed
  qed
next
  case (opponent x X \<sigma>)
  then show ?case sorry
next
  case (escape t X \<sigma>' \<sigma>)
  then show ?case sorry
qed

lemma "player_tangle_attractor X \<sigma> \<Longrightarrow> \<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom \<sigma>) \<sigma>) x xs x'"
proof -
  assume attr: "player_tangle_attractor X \<sigma>"
  then obtain \<sigma>' where
    rtranclp_\<sigma>': "tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>')"
    unfolding player_tangle_attractor_def by blast
  then have "\<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom \<sigma>') \<sigma>') x xs x'"
  proof (induction rule: tangle_attractor_step_rtranclp_induct)
    case base thus ?case
      apply (intro ballI)
      subgoal for x apply (rule bexI[where x=x])
        subgoal apply (rule exI[where x="[]"]) by simp
        subgoal by simp
        done
      done
  next
    case (step y z)
    then obtain X \<sigma> X' \<sigma>' where "y = (X,\<sigma>)" "z = (X',\<sigma>')" by fastforce
    with step have step_y_z: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" by blast
    from step \<open>y=(X,\<sigma>)\<close> have paths_to_A_X:
      "\<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph (dom \<sigma>) \<sigma>) x xs x'" by blast
    from step_y_z paths_to_A_X show ?case
      using test[of X \<sigma> X' \<sigma>'] \<open>z = (X',\<sigma>')\<close> by blast
  qed
  show ?thesis
qed
end (** End of context with fixed A *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor, i.e. TAttr(A) = A.
    This definition is now clearly wrong - it needs changing! *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> \<forall>\<sigma>. \<nexists>S'. tangle_attractor_step A (A,\<sigma>) S'"

(** A tangle_attracted region cannot be extended further, meaning it is \<alpha>-maximal. *)
lemma player_tangle_attractor_is_\<alpha>_max:
  "player_tangle_attractor A X \<sigma> \<Longrightarrow> player_\<alpha>_max X"
proof -
  (** We cannot take any further steps from the attracted region. *)
  assume attr: "player_tangle_attractor A X \<sigma>"
  then obtain \<sigma>' where "\<not> Domainp (tangle_attractor_step A) (X, \<sigma>')"
    unfolding player_tangle_attractor_def by blast
  (** That means there are no player-owned nodes that can play to it, no opponent nodes that must
      play to it, and no tangles that escape to it. *)
  hence "(\<nexists>x y. x \<in> V\<^sub>\<alpha>-X \<and> (x,y) \<in> E \<and> y \<in> X) \<and>
     (\<nexists>x. x \<in> V\<^sub>\<beta>-X \<and> (\<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> X)) \<and>
     (\<nexists>t \<tau>. t \<in> T \<and> t-X \<noteq> {} \<and> opponent_escapes t \<noteq> {} \<and> opponent_escapes t \<subseteq> X \<and>
      player_tangle_strat t \<tau>)"
    apply (safe)
    subgoal for x y using own[of x X y] by blast
    subgoal for x using opponent[of x X] by blast
    subgoal for t \<tau> using escape[of t X \<tau>] by blast
    done
  (** This means there are no extensions possible for X using such nodes, therefore X is \<alpha>-maximal. *)
  thus ?thesis
    unfolding player_\<alpha>_max_def
    apply clarsimp
    subgoal for \<tau> X' \<tau>' using tangle_attractor_step.simps[of X "(X,\<tau>)" "(X',\<tau>')"] by blast
    done
qed
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
  using P0.notin_player_tangle_attractor_succ[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.notin_player_tangle_attractor_succ[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)

lemma target_in_tangle_attractor:
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> A \<subseteq> X"
  using assms
  using P0.target_in_player_tangle_attractor[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.target_in_player_tangle_attractor[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)

lemma tangle_attractor_ss:
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> X \<subseteq> A \<union> V"
  using assms
  using P0.player_tangle_attractor_ss[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_ss[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
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
  "\<alpha>_max EVEN T = P0.player_\<alpha>_max {t\<in>T. tangle EVEN t}"
| "\<alpha>_max ODD T = P1.player_\<alpha>_max {t\<in>T. tangle ODD t}"

lemma tangle_attractor_is_\<alpha>_max:
  assumes "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> \<alpha>_max \<alpha> T X"
  using assms
  using P0.player_tangle_attractor_is_\<alpha>_max[of "{t\<in>T. tangle EVEN t}" A X \<sigma>]
  using P1.player_tangle_attractor_is_\<alpha>_max[of "{t\<in>T. tangle ODD t}" A X \<sigma>]
  by (cases \<alpha>; simp)
end (** End of context paritygame *)

end
