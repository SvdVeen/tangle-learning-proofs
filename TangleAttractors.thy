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
    player:
    All vertices belonging to the player that have a successor in the previous step are added to the
    attractor. The strategy is updated with an edge from it to that successor.

    opponent:
    All vertices belonging to the opponent that have only successors in the previous step are added
    to the attractor. The strategy remains the same.

    tangle:
    Every non-empty tangle belonging to the player in the set of known tangles that has escapes into
    the previous step is added in its entirety to the attractor. For ease of proof we limit this to
    only use attractors that are not already entirely inside the existing attractor. The strategy
    is updated with the tangle strategy, but we omit the target set A from its domain. *)
inductive tangle_attractor_step :: "'v set \<times> 'v strat \<Rightarrow> 'v set \<times> 'v strat \<Rightarrow> bool" where
  player: "\<lbrakk>x \<in> V\<^sub>\<alpha>-X; (x,y) \<in> E; y \<in> X\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (insert x X,\<sigma>(x\<mapsto>y))"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-X; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> X\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (insert x X,\<sigma>)"
| tangle: "\<lbrakk>t \<in> T; t-X \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> X;
            player_tangle_strat t \<sigma>'\<rbrakk> \<Longrightarrow> tangle_attractor_step (X,\<sigma>) (X\<union>t,(\<sigma>' |` (t-A)) ++ \<sigma>)"

(** The standard induction rule does not work with explicit pairs in lemmas. This custom rule
    lets us use them. *)
lemmas tangle_attractor_step_induct[consumes 1, case_names player opponent tangle] =
  tangle_attractor_step.induct[
    of "(X,\<sigma>)" "(X',\<sigma>')" for X \<sigma> X' \<sigma>',
    where P="\<lambda>(a,b) (c,d). P a b c d" for P,
    unfolded split]

(** The tangle attractor step is monotonous with respect to the set of vertices in the attracted
    region. *)
lemma tangle_attractor_step_mono:
  "tangle_attractor_step (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X \<subset> X'"
  by (induction rule: tangle_attractor_step_induct) auto

(** The reflexive transitive closure of steps is monotonous over the obtained region. This is less
    strict than our monotonicity property for the individual steps because of the reflexivity. *)
lemma tangle_attractor_step_rtranclp_mono:
  "tangle_attractor_step\<^sup>*\<^sup>* (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X \<subseteq> X'"
  apply (induction rule: rtranclp_induct2)
  using tangle_attractor_step_mono by blast+

(** The tangle attractor step's result is always in the union of the original attractor set and V.
    This means that attractors to regions in V will be entirely in V. *)
lemma tangle_attractor_step_ss: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X' \<subseteq> X \<union> V"
  apply (induction rule: tangle_attractor_step_induct)
  subgoal using V\<^sub>\<alpha>_subset by auto
  subgoal by simp
  subgoal using tangles_T player_tangle_in_V by auto
  done

(** The reflexive transitive closure of steps yields a subset of the union of the original set with
    V. If we attract to a region in V, then the result will always be in V. *)
lemma tangle_attractor_step_rtranclp_ss:
  "tangle_attractor_step\<^sup>*\<^sup>* (X,\<sigma>) (X',\<sigma>') \<Longrightarrow> X' \<subseteq> X \<union> V"
  apply (induction rule: rtranclp_induct2)
  using tangle_attractor_step_ss by blast+

(* If the original region is finite, then the region obtained in one step of the tangle attractor
   is also finite. *)
lemma fin_tangle_attractor_step:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); finite X\<rbrakk> \<Longrightarrow> finite X'"
  using finite_subset[OF tangle_attractor_step_ss] by blast

(** The region in the result of the reflexive transitive closure of steps is finite if the original
    set is finite. *)
lemma fin_tangle_attractor_step_rtranclp:
  "\<lbrakk>tangle_attractor_step\<^sup>*\<^sup>* (X,\<sigma>) (X',\<sigma>'); finite X\<rbrakk> \<Longrightarrow> finite X'"
  apply (induction rule: rtranclp_induct2)
  using fin_tangle_attractor_step by blast+

subsubsection \<open>Invariant\<close>
(** We define an invariant for the properties of the constructed strategy in tangle_attractor_step. *)
definition tangle_attractor_step_I :: "'v set \<times> 'v strat \<Rightarrow> bool" where
  "tangle_attractor_step_I \<equiv> \<lambda>(X,\<sigma>).
   A \<subseteq> X \<and>
   strategy_of V\<^sub>\<alpha> \<sigma> \<and>
   dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A) \<and>
   ran \<sigma> \<subseteq> X \<and>
   induced_subgraph \<sigma> `` (X-A) \<subseteq> X \<and>
   (\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)) \<and>
   (\<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs x')"

(** The invariant holds for the initial state of the tangle attractor. *)
lemma tangle_attractor_step_I_base: "tangle_attractor_step_I (A,Map.empty)"
  unfolding tangle_attractor_step_I_def split
  apply (clarsimp; intro conjI ballI)
  subgoal for x using origin_in_lasso[of _ x] by blast
  subgoal for x using path.simps(1)[of _ x x] by blast
  done

(** If our invariant holds for a previous state, then the strategy obtained in a step is a strategy
    for the player. *)
lemma tangle_attractor_step_strat_of_V\<^sub>\<alpha>:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>'"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal unfolding strategy_of_def E_of_strat_def by (auto split: if_splits)
  subgoal by fast
  subgoal
    unfolding player_tangle_strat_def strategy_of_def E_of_strat_def restrict_map_def
    apply (safe; clarsimp split: if_splits) by blast+
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
  subgoal for t using ran_restrictD[of _ _ "t-A"]
    unfolding player_tangle_strat_def ran_def by fast
  done

lemma tangle_attractor_step_closed_X:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal unfolding induced_subgraph_def E_of_strat_def
    by (clarsimp split: if_splits) blast
  subgoal by auto
  subgoal unfolding induced_subgraph_def E_of_strat_def
    using ind_subgraph_notin_dom by clarsimp blast
  done

lemma tangle_attractor_step_closed_X':
    "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)" "ran \<sigma>' \<subseteq> X'" "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
    using tangle_attractor_step_dom tangle_attractor_step_ran tangle_attractor_step_closed_X
    by auto
  from step invar this show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>) thus ?case
      unfolding induced_subgraph_def E_of_strat_def by auto
  next
    case (opponent x X \<sigma>) thus ?case by auto
  next
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X \<union> t"
    let ?\<sigma>' = "(\<tau> |` (t - A) ++ \<sigma>)"
    from tangle have
      escapes_in_X: "opponent_escapes t \<subseteq> X" and
      \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (?X' - A)" and
      \<sigma>'_ran: "ran ?\<sigma>' \<subseteq> ?X'" and
      \<sigma>'_closed_X: "induced_subgraph (\<tau> |` (t - A) ++ \<sigma>) `` (X - A) \<subseteq> X" by blast+
    show ?case proof (rule subsetI; clarify)
      fix y x
      assume x_in_X': "x \<in> ?X'" and x_notin_A: "x \<notin> A" and y_notin_t: "y \<notin> t" and
        edge: "(x,y) \<in> induced_subgraph ?\<sigma>'"

      consider (x_in_X) "x \<in> X" | (x_notin_X) "x \<notin> X" by blast
      thus "y \<in> X" proof cases
        case x_in_X with x_notin_A edge \<sigma>'_closed_X show ?thesis by auto
      next
        case x_notin_X
        with x_in_X' have x_in_t: "x \<in> t" by blast
        consider (player) "x \<in> V\<^sub>\<alpha>" | (opponent) "x \<notin> V\<^sub>\<alpha>" by blast
        thus ?thesis proof cases
          case player
          with x_in_X' x_notin_A edge y_notin_t \<sigma>'_dom \<sigma>'_ran
          show ?thesis
            using ind_subgraph_edge_dst[of x y ?\<sigma>'] by auto
        next
          case opponent
          with y_notin_t edge x_in_t have "y \<in> opponent_escapes t"
            unfolding opponent_escapes_def
            apply (simp)
            apply (rule exI[where x=x])
            using ind_subgraph[of ?\<sigma>'] E_in_V by blast
          with escapes_in_X show ?thesis by blast
        qed
      qed
    qed
  qed
qed

lemma tangle_attractor_step_forces_A_or_wins:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> (\<forall>x\<in>X'. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
        \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)" "ran \<sigma>' \<subseteq> X'"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X" "induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
  using tangle_attractor_step_dom tangle_attractor_step_ran
  using tangle_attractor_step_closed_X tangle_attractor_step_closed_X' by auto
  from step invar this show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    from player have \<sigma>_forces_A_or_wins:
      "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma> x xs ys
        \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
    from player have \<sigma>'_closed_X: "?G\<sigma>' `` (X-A) \<subseteq> X" by blast
    from player have \<sigma>'_closed_X': "?G\<sigma>' `` (?X'-A) \<subseteq> ?X'" by blast

    show ?case proof (intro ballI allI impI)
      fix v xs ys
      assume v_in_X': "v \<in> ?X'" and lasso: "lasso ?G\<sigma>' v xs ys"
      from lasso obtain v' where
        cycle: "cycle ?G\<sigma>' v' ys"
        unfolding lasso_def by auto

      have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
      proof -
        assume no_A: "set (xs@ys) \<inter> A = {}"
        hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
        with v_in_X' have v_in_X'_min_A: "v \<in> ?X' - A"
          using origin_in_lasso[OF lasso] by blast

        from lasso_partially_closed_sets[OF this \<sigma>'_closed_X' xs_no_A ys_no_A lasso]
        have ys_in_X'_min_A: "set ys \<subseteq> ?X' - A" by simp
        hence y_in_X'_min_A: "v' \<in> ?X' - A"
          using origin_in_cycle[OF cycle] by auto

        consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
        hence "lasso ?G\<sigma> v' [] ys \<and> v'\<in>X" proof cases
          case ys_has_x
          from player.hyps(1,2) obtain ys' where
            cycle': "cycle ?G\<sigma>' y ys'" and
            sets_eq: "set ys' = set ys" and
            y_in_ys': "y \<in> set ys'"
            using cycle_intermediate_node[OF cycle ys_has_x]
            apply clarsimp
            subgoal for vs'
              using cycle_D[of ?G\<sigma>' x vs']
              using ind_subgraph_to_strategy by fastforce
            done

          from player.hyps(3) sets_eq y_in_ys' ys_no_A have "y \<in> X-A" by blast
          from cycle_partially_closed_set[OF this \<sigma>'_closed_X cycle'] sets_eq ys_no_A
          have "set ys \<subseteq> X-A" by simp
          with ys_has_x player.hyps(1) show ?thesis by blast
        next
          case ys_no_x
          from player.hyps(1) have subset:
            "Restr ?G\<sigma>' (X-A) \<subseteq> ?G\<sigma>"
            unfolding induced_subgraph_def E_of_strat_def
            by (auto split: if_splits)

          from ys_no_x ys_in_X'_min_A have ys_in_X_min_A: "set ys \<subseteq> X-A" by blast
          from subgraph_cycle[OF subset cycle_restr_V[OF cycle this]]
          have cycle_\<sigma>: " cycle ?G\<sigma> v' ys " .

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
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    from opponent have \<sigma>_closed_X: "?G\<sigma> `` (X - A) \<subseteq> X" by blast
    with opponent have \<sigma>_closed_X': "?G\<sigma> `` (?X'-A) \<subseteq> ?X'" by blast
    from opponent have \<sigma>_forces_A_or_wins:
      "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma> x xs ys
        \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys" by simp

    show ?case proof (intro ballI allI impI)
      fix v xs ys
      assume v_in_X': "v \<in> ?X'" and lasso: "lasso ?G\<sigma> v xs ys"
      from lasso obtain v' where cycle: "cycle ?G\<sigma> v' ys"
        unfolding lasso_def by blast

      have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
      proof -
        assume no_A: "set (xs@ys) \<inter> A = {}"
        hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
        with v_in_X' have "v \<in> ?X' - A"
          using origin_in_lasso[OF lasso] by blast

        from lasso_partially_closed_sets[OF this \<sigma>_closed_X' xs_no_A ys_no_A lasso]
        have ys_in_X'_min_A: "set ys \<subseteq> ?X'-A" by simp
        hence v'_in_X'_min_A: "v' \<in> ?X'-A"
          using origin_in_cycle[OF cycle] by blast

        consider (ys_has_x) "x \<in> set ys" | (ys_no_x) "x \<notin> set ys" by blast
        hence "lasso ?G\<sigma> v' [] ys \<and> v' \<in> X" proof cases
          case ys_has_x
          from opponent.hyps(1,2) obtain y ys' where
            x_y_edge: "(x,y) \<in> induced_subgraph \<sigma>" and
            y_in_X: "y \<in> X" and
            cycle': "cycle ?G\<sigma> y ys'" and
            sets_eq: "set ys' = set ys" and
            y_in_ys: "y \<in> set ys"
            using cycle_intermediate_node[OF cycle ys_has_x]
            apply clarsimp
            subgoal for vs'
              using cycle_D[of ?G\<sigma> x vs']
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
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X \<union> t"
    let ?\<sigma>' = "(\<tau> |` (t - A) ++ \<sigma>)"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    let ?Gt = "player_tangle_subgraph t \<tau>"
    from tangle have \<sigma>'_closed_X: "?G\<sigma>' `` (X-A) \<subseteq> X" by blast
    from tangle have \<sigma>'_closed_X': "?G\<sigma>' `` (?X'-A) \<subseteq> ?X'" by blast
    from tangle have \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (X \<union> t - A)" by blast
    from tangle have \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" by blast
    from tangle have \<sigma>_ran: "ran \<sigma> \<subseteq> X" by blast
    from tangle have \<sigma>_forces_A_or_wins:
        "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma> x xs ys
          \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
    from tangle have t_in_V: "t \<subseteq> V"
      using player_tangle_in_V[of t] tangles_T by auto
    from tangle have \<tau>_winning:
      "\<forall>v\<in>t. \<forall>xs. cycle ?Gt v xs \<longrightarrow> winning_player xs"
      unfolding player_tangle_strat_def Let_def by auto


    show ?case proof (intro ballI allI impI)
      fix v xs ys
      assume v_in_X': "v\<in>?X'" and lasso: "lasso ?G\<sigma>' v xs ys"
      from lasso obtain v' where cycle: "cycle ?G\<sigma>' v' ys"
        unfolding lasso_def by blast

      have "set (xs@ys) \<inter> A = {} \<Longrightarrow> winning_player ys"
      proof -
        assume no_A: "set (xs@ys) \<inter> A = {}"
        hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
        with v_in_X' have "v\<in>?X'-A"
          using origin_in_lasso[OF lasso] by blast

        from lasso_partially_closed_sets[OF this \<sigma>'_closed_X' xs_no_A ys_no_A lasso]
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
            cycle': "cycle ?G\<sigma>' y ys'"
            using cycle_intermediate_node[OF cycle] by fastforce

          from cycle_partially_closed_set[OF y_in_X_min_A \<sigma>'_closed_X cycle' ys'_no_A] sets_eq
          have ys_in_X_min_A: "set ys \<subseteq> X-A" by blast
          hence v'_in_X: "v' \<in> X" using origin_in_cycle[OF cycle] by blast

          from \<sigma>_dom have subset: "Restr ?G\<sigma>' (X-A) \<subseteq> ?G\<sigma>"
            unfolding induced_subgraph_def E_of_strat_def by auto

          from subgraph_cycle[OF subset cycle_restr_V[OF cycle ys_in_X_min_A]]
          have "lasso ?G\<sigma> v' [] ys"
            by (simp add: cycle_iff_loop loop_impl_lasso)

          with \<sigma>_forces_A_or_wins v'_in_X no_A show ?thesis by fastforce
        next
          case ys_no_X
          with ys_in_X'_min_A have ys_in_t_min_X_min_A: "set ys \<subseteq> t-X-A" by blast
          hence v'_in_t: "v'\<in>t" using origin_in_cycle[OF cycle] by blast

          from \<sigma>'_dom \<sigma>_dom t_in_V have subset:
            "Restr ?G\<sigma>' (t-X-A) \<subseteq> Restr ?Gt (t-X-A)"
            unfolding induced_subgraph_def player_tangle_subgraph_def E_of_strat_def
            by auto

          from subgraph_cycle[OF subset cycle_restr_V[OF cycle ys_in_t_min_X_min_A]]
          have "cycle ?Gt v' ys" using restr_V_cycle by fast

          with \<tau>_winning v'_in_t show ?thesis by blast
        qed
      qed
      thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" by blast
    qed
  qed
qed

lemma tangle_attractor_step_path_X_to_A:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs x'"
proof-
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and invar: "tangle_attractor_step_I (X,\<sigma>)"

  (** If we have two strategies where one is closed and gives a path from any x in X to a y in A,
      and the subgraph X is the same under both strategies, then this path also exists under the
      other strategy.
      This auxiliary lemma will be reused for both the own and escape cases. *)
  {
    fix X :: "'v set"
    fix \<sigma> \<sigma>' :: "'v strat"
    assume \<sigma>_closed: "induced_subgraph \<sigma> `` (X-A) \<subseteq> X"
    assume restr_graphs_eq: "Restr (induced_subgraph \<sigma>') X = Restr (induced_subgraph \<sigma>) X"
    assume path_ex: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y"

    have "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs y"
    proof (rule ballI)
      fix x assume x_in_X: "x \<in> X"
      (** For some x in X, consider the case where x is already in A, and the case where it is not. *)
      consider (x_in_A) "x \<in> A" | (x_notin_A) "x \<notin> A" by blast
      thus "\<exists>y' \<in> A. \<exists>xs. path (induced_subgraph \<sigma>') x xs y'" proof cases
        (** If x is already in A, then an empty path will take us to A: we are already there. *)
        case x_in_A
        show ?thesis
          apply (rule bexI[where x=x])
          subgoal apply (rule exI[where x="[]"]) by simp
          subgoal using x_in_A by simp
          done
      next
        (* If x is not in A, then we should have a path from x to some y in A using strategy, which
           also exists under \<sigma>'. *)
        case x_notin_A
        with x_in_X have x_in_X_min_A: "x\<in>X-A" by simp
        (** First, we get y and the path xs from x to y. *)
        from x_in_X path_ex obtain y xs where
          y'_in_A: "y \<in> A" and
          path_x_y: "path (induced_subgraph \<sigma>) x xs y" and
          A_notin_xs: "set xs \<inter> A = {}"
          using shortest_subpath_to_target_region[of _ x] by blast
        (** Because x is not in A and \<sigma> is closed, the whole path stays in X. *)
        from path_partially_closed_set[OF x_in_X_min_A \<sigma>_closed path_x_y A_notin_xs]
        have xs_in_X: "set xs \<subseteq> X" by blast
        from path_partially_closed_dest[OF x_in_X_min_A \<sigma>_closed path_x_y A_notin_xs]
        have y_in_X: "y \<in> X" .
        (** Therefore, the path exists in the graph of \<sigma> restricted to X *)
        from path_restr_V[OF path_x_y xs_in_X y_in_X]
        have path_restr_x_y: "path (Restr (induced_subgraph \<sigma>) X) x xs y" .
        (** Since the graphs of \<sigma> and \<sigma>' are equal when restricted to X, the path also exists under
            \<sigma>'. *)
        from restr_graphs_eq path_restr_x_y have path_x_y_\<sigma>': "path (induced_subgraph \<sigma>') x xs y"
          using path_inter(1) by metis
        (** Therefore, we can use the path xs from x to y under \<sigma>' as our witness. *)
        show ?thesis
          apply (rule bexI[where x=y])
          subgoal apply (rule exI[where x=xs]) using path_x_y_\<sigma>' by simp
          subgoal using y'_in_A by simp
          done
      qed
    qed
  } note X_path_to_A = this

  from step invar have
    "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)" "ran \<sigma>' \<subseteq> X'"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X" "induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
  using tangle_attractor_step_dom tangle_attractor_step_ran
  using tangle_attractor_step_closed_X tangle_attractor_step_closed_X' by auto

  with step invar show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
    (** We know that \<sigma> is partially closed, and that we can get a path from any x in X to some x'
        in A. *)
    from player have
      \<sigma>_closed: "induced_subgraph \<sigma> `` (X - A) \<subseteq> X" and
      path_ex: "\<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs x'"
      by blast+
    (** We show that the graphs of \<sigma> and \<sigma>' are equal when restricted to X. *)
    from \<open>x\<in>V\<^sub>\<alpha>-X\<close> have "Restr (induced_subgraph ?\<sigma>') X = Restr (induced_subgraph \<sigma>) X"
      unfolding induced_subgraph_def E_of_strat_def
      by (auto split: if_splits)
    (** From our earlier auxiliary lemma and these properties, it follows that the thesis holds for
        this case. *)
    from X_path_to_A[OF \<sigma>_closed this path_ex] show ?case by blast
  next
    (** The thesis holds trivially for the opponent case because the strategy has not changed. *)
    case (opponent x X \<sigma>) thus ?case by blast
  next
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X\<union>t"
    let ?\<sigma>' = "\<tau> |` (t - A) ++ \<sigma>"
    (** We know the domains of \<sigma> and \<sigma>', that \<sigma> is partially closed, and that we can get a path from
        any x in X to some x' in A. *)
    from tangle have
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" and
      \<sigma>'_dom: "dom ?\<sigma>' =  V\<^sub>\<alpha> \<inter> (X \<union> t - A)" and
      \<sigma>_closed: "induced_subgraph \<sigma> `` (X-A) \<subseteq> X" and
      path_ex: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y"
      by blast+
    (** Using the domains of \<sigma> and \<sigma>', we can see that the two subgraphs are equal in X. *)
    from \<sigma>_dom \<sigma>'_dom
    have "Restr (induced_subgraph ?\<sigma>') X = Restr (induced_subgraph \<sigma>) X"
      unfolding induced_subgraph_def E_of_strat_def by auto
    (** From our earlier auxiliary proof and these properties, it follows that the thesis holds for
        this case as well. *)
    from X_path_to_A[OF \<sigma>_closed this path_ex] show ?case by blast
  qed
qed

lemma tangle_attractor_step_path_X'_to_A:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>X'. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs x'"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)" "ran \<sigma>' \<subseteq> X'"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X" "induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
    "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs y"
  using tangle_attractor_step_dom tangle_attractor_step_ran
  using tangle_attractor_step_closed_X tangle_attractor_step_closed_X'
  using tangle_attractor_step_path_X_to_A by auto

  with step invar show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    (** We can take a path from successor y to some z in A if we start with x, and prepend x to
        that path. If we start in X, then we already know that we can get a path to A. *)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
    (** We know we can get a path to A under \<sigma>' from any node in X. *)
    from player have X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs y" by blast

    show ?case proof (rule ballI)
      fix x' assume x'_in_X': "x' \<in> ?X'"
      (** We must consider whether we start in X, or with x itself. *)
      then consider (x'_in_X) "x' \<in> X" | (x'_is_x) "x' = x"  by blast
      thus "\<exists>y'\<in>A. \<exists>xs. path (induced_subgraph ?\<sigma>') x' xs y'" proof cases
        (** If we start in X, then we already know we can get a path to A. *)
        case x'_in_X with X_path_to_A show ?thesis by blast
      next
        (** If we start with x, then we can take a path to A from y. *)
        case x'_is_x
        from \<open>y\<in>X\<close> X_path_to_A obtain ys z where
          z_in_A: "z \<in> A" and path_y_z: "path (induced_subgraph ?\<sigma>') y ys z " by blast
        (** Now we can prepend x to the path from y to get our path from x to A. *)
        with x'_is_x \<open>(x,y) \<in> E\<close> have path_x'_z: "path (induced_subgraph ?\<sigma>') x' (x'#ys) z"
          using path.simps(2)[of "induced_subgraph ?\<sigma>'" x' x' ys z] strategy_to_ind_subgraph
          by force
        (** This path from x to A is our witness for the thesis statement. *)
        show ?thesis
          apply (rule bexI[where x=z])
          subgoal apply (rule exI[where x="x'#ys"]) using path_x'_z by blast
          subgoal using z_in_A by simp
          done
      qed
    qed
  next
    (** We can take a path from any successor y of x that leads to A, and prepend x to complete the
        path from x to A. Otherwise, if we start in X, we already know we can get a path to A. *)
    case (opponent x X \<sigma>)
    let ?X' = "insert x X"
    (** We know the domain of \<sigma>, and that we can get a path from any x in X to A. *)
    from opponent have
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X - A)" and
      X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y"
      by blast+
    show ?case proof (rule ballI)
      fix x' assume x'_in_X': "x' \<in> ?X'"
      (** We must consider whether we start in X, or with x itself. *)
      then consider (x'_in_X) "x' \<in> X" | (x'_is_x) "x' = x" by blast
      thus "\<exists>y'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x' xs y'" proof cases
        (** If we start in X, we already know we can get a path to A. *)
        case x'_in_X with X_path_to_A show ?thesis by blast
      next
        case x'_is_x
        (** If we start with x, we can take any successor y of x, which will be in X. *)
        with \<open>x\<in>V-V\<^sub>\<alpha>-X\<close> \<open>\<forall>y. (x, y) \<in> E \<longrightarrow> y \<in> X\<close> obtain y where
          edge: "(x',y) \<in> E" and y_in_X: "y \<in> X"
          using succ by auto
        (** We can now get a path from y to some z in A. *)
        from y_in_X X_path_to_A obtain ys z where
          z_in_A: "z \<in> A" and path_y_z: "path (induced_subgraph \<sigma>) y ys z " by blast
        (** Next, we prepend x to this path, completing our path from x to A. *)
        with x'_is_x edge \<sigma>_dom \<open>x\<in>V-V\<^sub>\<alpha>-X\<close> have path_x'_z: "path (induced_subgraph \<sigma>) x' (x'#ys) z"
          using path.simps(2)[of "induced_subgraph \<sigma>" x' x' ys z] ind_subgraph_notin_dom[of x' y \<sigma>]
          by blast
        (** This path from x to A serves as our witness for the thesis statement. *)
        show ?thesis
          apply (rule bexI[where x=z])
          subgoal apply (rule exI[where x="x'#ys"]) using path_x'_z by blast
          subgoal using z_in_A by simp
          done
      qed
    qed
  next
    (** t is strongly connected, so there is a path to an opponent node that escapes to a y in X.
        From any x in t, get a path to an escape y in X, then get the path from that y to A, and
        glue the two paths together to get a path from x to A. *)
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X\<union>t"
    let ?\<sigma>' = "\<tau> |` (t - A) ++ \<sigma>"

    from tangle have
      A_in_X: "A\<subseteq>X" and
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X - A)" and
      \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (X \<union> t - A)" and
      X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs y"
      by blast+

    show ?case proof (rule ballI)
      fix x assume x_in_X': "x \<in> ?X'"
      then consider (x_in_X) "x \<in> X" | (x_in_t_min_X) "x \<in> t-X" by blast
      thus "\<exists>x'\<in>A. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs x'" proof cases
        case x_in_X with X_path_to_A show ?thesis by blast
      next
        case x_in_t_min_X
        with A_in_X have x_in_t_min_X_min_A: "x \<in> t-X-A" by blast

        have "\<exists>y\<in>X. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs y"
        proof -
          from \<open>t \<in> T\<close> tangles_T have t_in_V: "t \<subseteq> V"
            using player_tangle_in_V by blast
          from \<open>player_tangle_strat t \<tau>\<close> have
            \<tau>_dom: "dom \<tau> = t \<inter> V\<^sub>\<alpha>" and \<tau>_ran: "ran \<tau> \<subseteq> t"
            unfolding player_tangle_strat_def by auto

          from \<open>opponent_escapes t \<noteq> {}\<close> \<open>opponent_escapes t \<subseteq> X\<close> obtain y z where
            y_opp_in_t: "y \<in> t \<inter> V\<^sub>\<beta>" and
            z_in_X: "z \<in> X" and
            y_z_edge: "(y,z) \<in> E"
          unfolding opponent_escapes_def by blast

          from \<open>player_tangle_strat t \<tau>\<close>
          have t_connected: "strongly_connected (Restr (induced_subgraph \<tau>) t) t"
            unfolding player_tangle_strat_def Let_def
            by (simp add: player_tangle_subgraph_is_restricted_ind_subgraph[OF t_in_V \<tau>_dom \<tau>_ran])

          from y_opp_in_t x_in_t_min_X t_connected obtain xs where
            path_x_y: "path (Restr (induced_subgraph \<tau>) t) x xs y"
            using strongly_connected_path by blast

          from \<sigma>_dom have subgraph_\<tau>: "Restr (induced_subgraph \<tau>) (t-X) \<subseteq> induced_subgraph ?\<sigma>'"
            unfolding induced_subgraph_def E_of_strat_def
            by (auto simp: map_add_dom_app_simps(3))

          consider (xs_empty) "xs = []" | (xs_notempty) "xs \<noteq> []" by blast
          thus ?thesis proof cases
            case xs_empty
            with path_x_y have x_is_y[simp]: "x=y" by simp
            from y_opp_in_t \<sigma>'_dom have x_notin_dom: "x \<notin> dom ?\<sigma>'" by auto
            from y_z_edge have "(x,z) \<in> E" by simp
            with x_notin_dom have "(x,z) \<in> induced_subgraph ?\<sigma>'"
              using ind_subgraph_notin_dom by blast
            hence path_x_z: "path (induced_subgraph ?\<sigma>') x [x] z" by simp

            show ?thesis
              apply (rule bexI[where x=z])
              using path_x_z z_in_X by blast+
          next
            case xs_notempty
            from restr_V_path[OF path_x_y xs_notempty] have
              xs_in_t: "set xs \<subseteq> t" and
              y_in_t: "y \<in> t"
              by blast+

            {
              fix y xs
              assume y_in_X: "y \<in> X" and xs_notempty: "xs \<noteq> []" and xs_in_t: "set xs \<subseteq> t" and
                no_X_in_xs: "set xs \<inter> X = {}" and
                path_x_y: "path (Restr (induced_subgraph \<tau>) t) x xs y"
              from path_D_rev[OF path_x_y xs_notempty] obtain y' xs' where
                y'_y_edge_\<tau>: "(y',y) \<in> Restr (induced_subgraph \<tau>) t" and
                xs_comp: "xs = xs'@[y']" and
                path_x_y': "path (Restr (induced_subgraph \<tau>) t) x xs' y'"
                by blast
              from xs_comp no_X_in_xs have no_X_in_xs': "set xs' \<inter> X = {}" by simp
              from xs_comp no_X_in_xs xs_in_t have y'_in_t_min_X: "y' \<in> t-X" by simp
              with y'_y_edge_\<tau> \<sigma>_dom have y_y'_edge_\<sigma>': "(y',y) \<in> induced_subgraph ?\<sigma>'"
                unfolding induced_subgraph_def E_of_strat_def
                by (auto simp: map_add_dom_app_simps(3))
              have "\<exists>y'\<in>t-X. \<exists>z'\<in>X. \<exists>xs'.
                set xs' \<inter> X = {} \<and> (y',z') \<in> induced_subgraph (\<tau> |` (t-A) ++ \<sigma>) \<and>
                path (Restr (induced_subgraph \<tau>) t) x xs' y'"
                apply (rule bexI[where x=y'])
                apply (rule bexI[where x=y])
                using no_X_in_xs' y_y'_edge_\<sigma>' path_x_y'  y_in_X  y'_in_t_min_X
                by blast+
            } note aux=this

            consider (no_X_in_xs) "set xs \<inter> X = {}" | (X_in_xs) "set xs \<inter> X \<noteq> {}" by blast
            hence "\<exists>y'\<in>t-X. \<exists>z'\<in>X. \<exists>xs'. set xs' \<inter> X = {} \<and> (y',z') \<in> induced_subgraph ?\<sigma>' \<and>
              path (Restr (induced_subgraph \<tau>) t) x xs' y'"
            proof cases
              case no_X_in_xs
              consider (y_notin_X) "y \<notin> X" | (y_in_X) "y \<in> X" by blast
              thus ?thesis proof cases
                case y_notin_X
                with y_opp_in_t have y_in_t_min_X: "y \<in> t-X" by blast
                from y_opp_in_t \<sigma>'_dom have "y \<notin> dom ?\<sigma>'" by simp
                with y_z_edge have y_z_edge_\<sigma>': "(y,z) \<in> induced_subgraph ?\<sigma>'"
                  using ind_subgraph_notin_dom by blast
                show ?thesis
                  apply (rule bexI[where x=y])
                  apply (rule bexI[where x=z])
                  using y_z_edge_\<sigma>' no_X_in_xs path_x_y z_in_X y_in_t_min_X
                  by blast+
              next
                case y_in_X
                from aux[OF y_in_X xs_notempty xs_in_t no_X_in_xs path_x_y] show ?thesis .
              qed
            next
              case X_in_xs
              from shortest_subpath_to_intersecting_region[OF path_x_y X_in_xs] obtain y' xs' where
                y'_in_X: "y' \<in> X" and
                xs'_no_X: "set xs' \<inter> X = {}" and
                path_x_y': "path (Restr (induced_subgraph \<tau>) t) x xs' y'"
                by blast
              with x_in_t_min_X have xs'_notempty: "xs' \<noteq> []" by force
              from restr_V_path[OF path_x_y' xs'_notempty] have xs'_in_t: "set xs' \<subseteq> t" by blast
              from aux[OF y'_in_X xs'_notempty xs'_in_t xs'_no_X path_x_y']
              show ?thesis by blast
            qed
            then obtain xs' y' z' where
              y'_in_t_min_X: "y' \<in> t-X" and z'_in_X: "z' \<in> X" and xs'_no_X: "set xs' \<inter> X = {}" and
              y'_z'_edge: "(y',z') \<in> induced_subgraph ?\<sigma>'" and
              path_x_y': "path (Restr (induced_subgraph \<tau>) t) x xs' y'"
              by blast

            (** Just repeat what we did before :( *)
            from restr_V_path[OF path_x_y']

            show ?thesis sorry
          qed

          consider (no_X_in_xs) "set xs \<inter> X = {}" | (X_in_xs) "set xs \<inter> X \<noteq> {}" by blast
          thus ?thesis proof cases
            case no_X_in_xs
            consider (xs_empty) "xs = []" | (xs_notempty) "xs \<noteq> []" by blast
            thus ?thesis proof cases
              case xs_empty
              then show ?thesis sorry
            next
              case xs_notempty
              then show ?thesis sorry
            qed

            consider (y_in_X) "y \<in> X" | (y_notin_X) "y \<notin> X" by blast
            thus ?thesis proof cases
              case y_in_X
              from shortest_subpath_to_target_region[OF path_x_y y_in_X] obtain y' xs' where
                y'_in_X: "y' \<in> X" and X_notin_xs': "set xs' \<inter> X = {}" and
                path_x_y': "path (Restr (induced_subgraph \<tau>) t) x xs' y'"
                by blast
              with x_in_t_min_X have xs'_notempty: "xs' \<noteq> []" by force

              from path_D_rev[OF path_x_y' xs'_notempty] obtain x' xs'' where
                x'_y'_edge: "(x',y') \<in> Restr (induced_subgraph \<tau>) t" and
                xs'_comp: "xs' = xs''@[x']" and
                path_x_x': "path (Restr (induced_subgraph \<tau>) t) x xs'' x'"
                by blast
              from xs'_comp X_notin_xs' have "x' \<notin> X" by simp

              from restr_V_path[OF path_x_x'] path_restr_V

              show ?thesis sorry
            next
              case y_notin_X
              then show ?thesis sorry
            qed
          next
            case X_in_xs
            then show ?thesis sorry
          qed
        qed

        from \<open>t \<in> T\<close> tangles_T have t_in_V: "t \<subseteq> V"
          using player_tangle_in_V by blast
        from \<open>player_tangle_strat t \<tau>\<close> have
          \<tau>_dom: "dom \<tau> = t \<inter> V\<^sub>\<alpha>" and \<tau>_ran: "ran \<tau> \<subseteq> t"
          unfolding player_tangle_strat_def by auto

        from \<open>player_tangle_strat t \<tau>\<close>
        have conn: "strongly_connected (Restr (induced_subgraph \<tau>) t) t"
          unfolding player_tangle_strat_def Let_def
          by (simp add: player_tangle_subgraph_is_restricted_ind_subgraph[OF t_in_V \<tau>_dom \<tau>_ran])

        {
          assume no_A_in_t: "t \<inter> A = {}"
          with \<tau>_dom have "\<tau> |` (t-A) = \<tau>"
            unfolding restrict_map_def by fastforce
        } note no_A_\<tau>_same = this

        from \<sigma>_dom have ss: "Restr (induced_subgraph \<tau>) (t-X) \<subseteq> induced_subgraph ?\<sigma>'"
          unfolding induced_subgraph_def E_of_strat_def
          by (auto simp: map_add_dom_app_simps(3))

        from \<open>opponent_escapes t \<noteq> {}\<close> \<open>opponent_escapes t \<subseteq> X\<close> obtain y z where
          y_opp_in_t: "y \<in> t \<inter> V\<^sub>\<beta>" and
          z_in_X: "z \<in> X" and
          y_z_edge: "(y,z) \<in> E"
          unfolding opponent_escapes_def by blast

        with conn x_in_t_min_X obtain xs where
          path_x_y: "path (Restr (induced_subgraph \<tau>) t) x xs y"
          using strongly_connected_path by blast

        consider (no_X_in_xs) "set xs \<inter> X = {}" | (X_in_xs) "set xs \<inter> X \<noteq> {}" by blast
        hence "\<exists>y\<in>X. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs y" proof cases
          case no_X_in_xs
          then show ?thesis sorry
        next
          case X_in_xs
          from shortest_subpath_to_intersecting_region[OF path_x_y this] obtain z' xs' where
            z'_in_X: "z' \<in> X" and
            xs'_no_X: "set xs' \<inter> X = {}" and
            path_x_z': "path (Restr (induced_subgraph \<tau>) t) x xs' z'"
            by blast

          with x_in_t_min_X have xs'_notempty: "xs' \<noteq> []" by force
          from restr_V_path[OF path_x_z' xs'_notempty]
          have "set xs' \<subseteq> t" by simp

          from xs'_notempty path_x_z' obtain y' ys where
            y'_z'_edge: "(y',z') \<in> Restr (induced_subgraph \<tau>) t" and
            xs'_comp: "xs' = ys@[y']" and
            path_x_y': "path (Restr (induced_subgraph \<tau>) t) x ys y'"
            using path_D_rev by fastforce
          with \<open>set xs' \<subseteq> t\<close> xs'_no_X have
            ys_in_t_min_X: "set ys \<subseteq> t-X" and
            y'_in_t_min_X: "y' \<in> t-X"
            by auto

          from path_restr_V[OF path_x_y' ys_in_t_min_X y'_in_t_min_X]
          have "path (Restr (induced_subgraph \<tau>) (t-X)) x ys y'"
            by (auto simp: path_inter(2) Int_assoc Int_left_commute[of "induced_subgraph \<tau>"])
          from subgraph_path[OF ss this] have aaa: "path (induced_subgraph ?\<sigma>') x ys y'" .

          from y'_z'_edge y'_in_t_min_X \<sigma>_dom have "(y',z') \<in> induced_subgraph ?\<sigma>'"
            unfolding induced_subgraph_def E_of_strat_def
            by (auto simp: map_add_dom_app_simps(3))
          with aaa xs'_comp have bbb: "path (induced_subgraph ?\<sigma>') x xs' z'" by simp
          show ?thesis
            apply (rule bexI[where x=z'])
            subgoal apply (rule exI[where x=xs']) using bbb by blast
            subgoal using z'_in_X by simp
            done
        qed

        have "Restr (induced_subgraph \<tau>) t \<subseteq> induced_subgraph \<tau>" by blast
        from subgraph_path[OF this p] have "path (induced_subgraph \<tau>) x xs x'" .
        with \<tau>_dom x'_opp_in_t x'_y_edge have p': "path (induced_subgraph \<tau>) x (xs@[x']) y"
          using ind_subgraph_notin_dom by auto

        consider


        have "\<exists>y\<in>X. \<exists>xs. path (induced_subgraph ?\<sigma>') x xs y"
        proof -
          consider (no_X_in_t) "t \<inter> X = {}" | (X_in_t) "t \<inter> X \<noteq> {}" by blast
          thus ?thesis proof cases
            case no_X_in_t
            then show ?thesis sorry
          next
            case X_in_t
            then show ?thesis sorry
          qed
        qed

        from \<open>opponent_escapes t \<subseteq> X\<close> \<open>opponent_escapes t \<noteq> {}\<close> obtain x' y where
          "x' \<in> t \<inter> V\<^sub>\<beta>" and
          "y \<in> opponent_escapes t" and "y \<in> X" unfolding opponent_escapes_def
          by blast

        show ?thesis sorry
      qed
    qed
  qed
qed

(** The step preserves the invariant. *)
lemma tangle_attractor_step_preserves_I:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> tangle_attractor_step_I (X',\<sigma>')"
  using tangle_attractor_step_mono[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_strat_of_V\<^sub>\<alpha>[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_dom[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_ran[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_closed_X'[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_forces_A_or_wins[of X \<sigma> X' \<sigma>']
  using tangle_attractor_step_path_X'_to_A[of X \<sigma> X' \<sigma>']
  unfolding tangle_attractor_step_I_def split
  by auto

(** The reflexive transitive closure of the tangle attractor step preserves the strategy invariant. *)
lemma tangle_attractor_step_rtranclp_preserves_I:
  "\<lbrakk>tangle_attractor_step\<^sup>*\<^sup>* (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> tangle_attractor_step_I (X',\<sigma>')"
  apply (induction rule: rtranclp_induct2)
  using tangle_attractor_step_preserves_I by blast+

subsection \<open>Tangle Attractors\<close>
(** Van Dijk's definition for the construction of witness strategies of tangle attractors includes
    assigning a successor in X to each player_owned nodes in A. We define this as a lambda that
    uses the Hilbert choice operator to pick some valid successor if it exists. *)
definition A_target :: "'v set \<Rightarrow> 'v strat" where
  "A_target X \<equiv> \<lambda>x.
    if x \<in> V\<^sub>\<alpha> \<inter> A \<and> (\<exists>y. y \<in> X \<and> (x,y) \<in> E)
    then Some (SOME y. y \<in> X \<and> (x,y) \<in> E)
    else None"

(** A_target produces a strategy for the player. *)
lemma A_target_strat: "strategy_of V\<^sub>\<alpha> (A_target X)"
  unfolding A_target_def strategy_of_def E_of_strat_def
  apply (rule conjI; clarsimp split: if_splits)
  using someI2[of "\<lambda>y. y \<in> X \<and> (x,y) \<in> E" for x] by fast

(** The domain of A_target is some subset of the player's node in A. *)
lemma A_target_dom: "dom (A_target X) \<subseteq> V\<^sub>\<alpha> \<inter> A"
  unfolding A_target_def by (auto split: if_splits)

(** The range of A_target is in X. *)
lemma A_target_ran: "ran (A_target X) \<subseteq> X"
  apply (clarsimp simp: A_target_def ran_def)
  using someI_ex[of "\<lambda>y. y \<in> X \<and> (x,y) \<in> E" for x] by blast

(** Every x in A belonging to the player with at least one successor in X is in the domain of
    A_target X *)
lemma A_target_in_dom: "\<lbrakk>x \<in> V\<^sub>\<alpha> \<inter> A; E `` {x} \<inter> X \<noteq> {}\<rbrakk> \<Longrightarrow> x \<in> dom (A_target X)"
  by (clarsimp simp: A_target_def split!: if_splits)

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
  using tangle_attractor_step_rtranclp_preserves_I[OF _ tangle_attractor_step_I_base]
  by blast

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
  "player_tangle_attractor X \<sigma> \<Longrightarrow> induced_subgraph \<sigma> `` (X-A) \<subseteq> X"
proof (rule subsetI; clarify)
  fix x y
  assume attr: "player_tangle_attractor X \<sigma>" and
    x_in_X: "x \<in> X" and x_notin_A: "x \<notin> A" and
    edge: "(x,y) \<in> induced_subgraph \<sigma>"

  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' where
      A_in_X: "A \<subseteq> X" and
      \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
      \<sigma>'_closed: "induced_subgraph \<sigma>' `` (X - A) \<subseteq> X" and
      \<sigma>_comp: "\<sigma> = \<sigma>' ++ A_target X"
      unfolding tangle_attractor_step_I_def
      by blast


  consider (y_in_A) "y \<in> A" | (y_notin_A) "y \<notin> A" by blast
  thus "y \<in> X" proof cases
    case y_in_A with A_in_X show ?thesis by blast
  next
    case y_notin_A
    with x_notin_A edge have "(x,y) \<in> Restr (induced_subgraph \<sigma>) (-A)" by blast
    moreover have "Restr (induced_subgraph \<sigma>) (-A) \<subseteq> induced_subgraph \<sigma>'"
      apply (simp add: \<sigma>_comp)
      unfolding A_target_def induced_subgraph_def E_of_strat_def
      by auto
    ultimately have "(x,y) \<in> induced_subgraph \<sigma>'" by blast
    with x_in_X x_notin_A \<sigma>'_closed show ?thesis by blast
  qed
qed

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, and X is a closed region, then
    the induced subgraph of \<sigma> is also closed in X. This is a somewhat trivial property, but nice to
    have. *)
lemma closed_player_tangle_attractor_strat_closed:
  "\<lbrakk>player_tangle_attractor X \<sigma>; E `` X \<subseteq> X\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` X \<subseteq> X"
  using player_tangle_attractor_I_aux[of X \<sigma>] ind_subgraph[of \<sigma>]
  unfolding tangle_attractor_step_I_def
  by fast

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then all plays in X restricted
    by \<sigma> either lead to A or are won by the player. *)
lemma player_tangle_attractor_strat_forces_A_or_wins:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> \<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>) x xs ys
    \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
proof (intro ballI allI impI)
  fix x xs ys
  assume attr: "player_tangle_attractor X \<sigma>" and
    x_in_X: "x \<in> X" and lasso: "lasso (induced_subgraph \<sigma>) x xs ys"
  (** We need the domain of \<sigma>', the fact that \<sigma>' forces all plays to go to A or be won by the player,
      and the composition of \<sigma>. *)
  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' :: "'v strat" where
    \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
    \<sigma>'_forces_A_or_wins: "\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
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
    "(induced_subgraph \<sigma>) \<inter> (X-A) \<times> X = (induced_subgraph \<sigma>') \<inter> (X-A) \<times> X"
    unfolding induced_subgraph_def E_of_strat_def by auto
  (** ys is not empty, and we have a path from x to y and a path from y to y. We can also say that
      y is included at the start of ys'. *)
  from lasso have ys_notempty: "ys \<noteq> []" by auto
  from lasso obtain y where
    path_x_xs_y: "path (induced_subgraph \<sigma>) x xs y" and
    path_y_ys_y: "path (induced_subgraph \<sigma>) y ys y"
    using lasso_paths[of "induced_subgraph \<sigma>"] by auto
  with ys_notempty have y_in_ys: "\<exists>ys'. ys = (y#ys')"
    using path_D[of _ y ys y] by blast
  (** Now we attach these paths to form a single path. *)
  define zs where "zs=xs@ys"
  with path_x_xs_y path_y_ys_y have path_x_zs_y: "path (induced_subgraph \<sigma>) x zs y"
    by auto
  (** Using this lemma, we know that this path either needs to intersect with A, or it exists
      withing the area without A. *)
  from player_tangle_attractor_strat_partially_closed[OF attr]
  have \<sigma>_closed: "induced_subgraph \<sigma> `` (X - A) \<subseteq> X" .
  have A_in_zs_or_path: "A \<inter> set zs \<noteq> {} \<or> path (induced_subgraph \<sigma> \<inter> (X-A) \<times> X) x zs y"
    using simulate_closed_path[OF \<sigma>_closed x_in_X path_x_zs_y] by blast
  (** If we assume that there is no A in zs we should have a winning path. *)
  have "A \<inter> set zs = {} \<Longrightarrow> winning_player ys"
  proof -
    assume no_A_in_zs: "A \<inter> set zs = {}"
    (** Because A is not in ZS, we have a path that stays in the region minus A. *)
    with A_in_zs_or_path have "path (induced_subgraph \<sigma> \<inter> (X-A) \<times> X) x zs y" by simp
    (** This path also exists in the graph of \<sigma>'. *)
    with restricted_graphs_equal have "path (induced_subgraph \<sigma>' \<inter> (X-A) \<times> X) x zs y" by simp
    hence "path (induced_subgraph \<sigma>') x zs y" using path_inter(1) by fastforce
    (** Now, we can say that the original lasso existed in the graph of \<sigma>' too.*)
    with y_in_ys ys_notempty have "lasso (induced_subgraph \<sigma>') x xs ys"
      using lasso_paths
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
   induced_subgraph \<sigma> `` (X-A) \<subseteq> X \<and>
   (\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>) x xs ys
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
  apply (erule tangle_attractor_step.cases)
  subgoal using V\<^sub>\<alpha>_subset by blast
  subgoal by auto
  subgoal using player_tangle_in_V tangles_T by blast
  done

(** A wellfounded relation terminates. *)
lemma wf_rel_terminates: "wfP R\<inverse>\<inverse> \<Longrightarrow> \<exists>X' \<sigma>'. R\<^sup>*\<^sup>* S (X',\<sigma>') \<and> \<not>Domainp R (X', \<sigma>')"
  unfolding wfP_def
  apply (induction S rule: wf_induct_rule)
  subgoal for x apply (cases "Domainp R x"; clarsimp)
    subgoal using converse_rtranclp_into_rtranclp[of R] by blast
    subgoal using surj_pair[of x] by blast
    done
  done

(** There always exists a tangle attractor. *)
lemma player_tangle_attractor_exists: "\<exists>X \<sigma>. player_tangle_attractor X \<sigma>"
  using wf_rel_terminates[OF tangle_attractor_step_wf]
  unfolding player_tangle_attractor_def by simp

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
      using some_succ_in_X by (auto intro: tangle_attractor_step.player)
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
end (** End of context with fixed A *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor, i.e. TAttr(A) = A.
    This definition is now clearly wrong - it needs changing! *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> \<forall>\<sigma>. \<nexists>S'. tangle_attractor_step A (A,\<sigma>) S'"

(** A tangle_attracted region cannot be extended further, meaning it is \<alpha>-maximal. *)
lemma player_tangle_attractor_is_\<alpha>_max:
  "player_tangle_attractor A X \<sigma> \<Longrightarrow> player_\<alpha>_max X"
  unfolding player_tangle_attractor_def player_\<alpha>_max_def
  by (auto simp: tangle_attractor_step.simps intro: tangle_attractor_step.intros)
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
  using P0.player_tangle_attractor_exists P1.player_tangle_attractor_exists
  by (cases \<alpha>; simp add: fin_T)

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
    induced_subgraph \<sigma> `` (X-A) \<subseteq> X \<and>
    (\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>) x xs ys
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
  shows "valid_subgame (V-X)"
  apply simp
  apply (unfold_locales; clarsimp)
  using notin_tangle_attractor_succ[OF fin_T tangle_attractor] E_in_V by blast


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
