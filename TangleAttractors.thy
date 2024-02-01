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
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>'"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal
    unfolding strategy_of_def E_of_strat_def
    by (auto split: if_splits)
  subgoal by fast
  subgoal
    unfolding player_tangle_strat_def strategy_of_def E_of_strat_def
    by (safe; simp add: restrict_map_def split: if_splits) blast+
  done

(** After each step, \<sigma>' has in its domain all player-nodes in X', except for those in A. *)
lemma tangle_attractor_step_dom:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  unfolding player_tangle_strat_def by auto

(** After each step, the range of \<sigma>' lies in X'. *)
lemma tangle_attractor_step_ran:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> ran \<sigma>' \<subseteq> X'"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal by fastforce
  subgoal by blast
  subgoal for t
    using ran_restrictD[of _ _ "t-A"]
    unfolding player_tangle_strat_def ran_def by fast
  done

(** After each step, X is partially closed in X-A under \<sigma>'. *)
lemma tangle_attractor_step_closed_X:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
  unfolding tangle_attractor_step_I_def split
  apply (induction rule: tangle_attractor_step_induct)
  subgoal for x X y \<sigma>
    using ind_subgraph_add_disjoint[of \<sigma> "[x\<mapsto>y]"]
    by simp blast
  subgoal by blast
  subgoal
    unfolding induced_subgraph_def E_of_strat_def
    using ind_subgraph_notin_dom by simp blast
  done

(** After each step, X' is partially closed in X'-A under \<sigma>'. *)
lemma tangle_attractor_step_closed_X':
    "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and
    invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)" "ran \<sigma>' \<subseteq> X'"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
    using tangle_attractor_step_dom tangle_attractor_step_ran
      tangle_attractor_step_closed_X
    by auto

  from step invar this show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>) thus ?case
      unfolding induced_subgraph_def E_of_strat_def by auto
  next
    case (opponent x X \<sigma>) thus ?case
      unfolding induced_subgraph_def E_of_strat_def by blast
  next
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X \<union> t"
    let ?\<sigma>' = "\<tau> |` (t-A) ++ \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    from tangle have
      escapes_in_X: "opponent_escapes t \<subseteq> X" and
      \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (?X'-A)" and
      \<sigma>'_ran: "ran ?\<sigma>' \<subseteq> ?X'" and
      \<sigma>'_closed_X: "?G\<sigma>' `` (X-A) \<subseteq> X"
      by blast+
    show ?case
      apply clarsimp
      subgoal for y x
        apply (cases "x \<in> X")
        using \<sigma>'_closed_X apply blast
        apply (cases "x \<in> V\<^sub>\<alpha>")
        using \<sigma>'_dom \<sigma>'_ran ind_subgraph_edge_dst[of x y ?\<sigma>'] apply force
        using escapes_in_X opponent_escapes_pre[of y t] by force
      done
  qed
qed

(** After each step, \<sigma>' forces all plays starting in X to go to A or be won by the player. *)
lemma tangle_attractor_step_forces_A_or_wins_X:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> (\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
        \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  unfolding tangle_attractor_step_I_def split
proof (induction rule: tangle_attractor_step_induct)
  case (player x X y \<sigma>)
  hence disj: "dom \<sigma> \<inter> dom [x\<mapsto>y] = {}" by simp
  from player show ?case
    using subgraph_lasso[OF ind_subgraph_add_disjoint(1)[OF disj]]
    by (metis map_add_empty map_add_upd)
next
  case (opponent x X \<sigma>) thus ?case by blast
next
  case (tangle t X \<tau> \<sigma>)
  let ?\<sigma>' = "\<tau> |` (t-A) ++ \<sigma>"
  have subgraph: "induced_subgraph ?\<sigma>' \<subseteq> induced_subgraph \<sigma>"
    unfolding induced_subgraph_def E_of_strat_def by auto
  from tangle show ?case
    using subgraph_lasso[OF subgraph] by fast
qed

(** After each step, \<sigma>' forces all plays that start in X' to go to A or be won by the player. *)
lemma tangle_attractor_step_forces_A_or_wins:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> (\<forall>x\<in>X'. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
        \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and
    invar: "tangle_attractor_step_I (X,\<sigma>)"

  hence props:
    "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
    "induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
    "\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    using tangle_attractor_step_dom
          tangle_attractor_step_closed_X
          tangle_attractor_step_closed_X'
          tangle_attractor_step_forces_A_or_wins_X
    by auto

  (** This auxiliary lemma shows that if we add only a single node to X, the property holds.
      it is used for both the player and opponent cases. *)
  {
    fix X :: "'v set" and x :: 'v
    fix \<sigma> v xs ys
    let ?X' = "insert x X"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    assume x_succs_X: "\<forall>y. (x,y) \<in> ?G\<sigma> \<longrightarrow> y\<in>X"
       and x_notin_X: "x \<notin> X"
       and \<sigma>_closed_X: "?G\<sigma> `` (X-A) \<subseteq> X"
       and \<sigma>_closed_X': "?G\<sigma> `` (?X'-A) \<subseteq> ?X'"
       and \<sigma>_forces_A_or_wins_X:
        "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma> x xs ys
          \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
       and v_in_X': "v \<in> ?X'"
       and lasso: "lasso ?G\<sigma> v xs ys"
       and lasso_no_A: "set (xs@ys) \<inter> A = {}"

    (** Because there is no A in the lasso, the spoke and loop do not have A, and
        v is part of X'-A. *)
    hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
    with v_in_X' have "v \<in> ?X'-A"
      using origin_in_lasso[OF lasso] by blast

    (** We can get the loop of our lasso as a cycle. *)
    from lasso obtain v' where cycle: "cycle ?G\<sigma> v' ys"
      unfolding lasso_def by auto

    (** The cycle does not contain x because then it would have to loop back within the attractor,
        which is not possible without going through A. *)
    have "x \<notin> set ys" proof
      assume "x \<in> set ys"
      (** Because all successors of x are part of X, having x in the cycle means it also has X in
          it. *)
      from x_succs_X have X_in_ys: "set ys \<inter> X \<noteq> {}"
        using cycle_intermediate_node[OF cycle \<open>x\<in>set ys\<close>] cycle_D[of ?G\<sigma> x]
        by (metis disjoint_iff[of "set ys" X])

      (** Since X is partially closed in X-A under \<sigma>, the whole cycle must now be in X. *)
      with cycle ys_no_A \<sigma>_closed_X
      have "set ys \<subseteq> X"
        using cycle_intersects_partially_closed_region[of ?G\<sigma>]
        by blast

      (** This is a contradiction, as x is also in the cycle, and x is not part of X. *)
      with \<open>x\<in>set ys\<close> \<open>x\<notin>X\<close> show False by blast
    qed

    (** ys exists entirely in X'-A because X' is partially closed in X'-A under \<sigma>. *)
    from \<open>v\<in>?X'-A\<close> \<sigma>_closed_X' xs_no_A ys_no_A lasso
    have "set ys \<subseteq> ?X'-A"
      using lasso_partially_closed_sets[of v] by simp

    (** Since x is not part of ys, this means it exists entirely in X. *)
    with \<open>x\<notin>set ys\<close> have "set ys \<subseteq> X" by blast
    hence "v' \<in> X"  using origin_in_cycle[OF cycle] by blast

    (** Our cycle starts in X, and it does not intersect with A, so the cycle is won by the
        player. *)
    with \<sigma>_forces_A_or_wins_X cycle ys_no_A have "winning_player ys"
      using cycle_iff_lasso[of ?G\<sigma> v' ys] by fastforce
  } note add_single_node=this

  from step invar props show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?G\<sigma>' = "induced_subgraph (\<sigma>(x\<mapsto>y))"

    from player have
      "?G\<sigma>' `` (X-A) \<subseteq> X"
      "?G\<sigma>' `` (?X'-A) \<subseteq> ?X'"
      "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma>' x xs ys
        \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
      by blast+

    (** All successors of x under \<sigma>', which in this case is only y, are part of X. *)
    moreover from \<open>y\<in>X\<close> have "\<forall>y. (x,y) \<in> ?G\<sigma>' \<longrightarrow> y \<in> X"
      using ind_subgraph_to_strategy by fastforce

    (** By our auxiliary lemma, the thesis statement holds. *)
    ultimately show ?case using add_single_node by blast
  next
    case (opponent x X \<sigma>)
    let ?X' = "insert x X"
    let ?G\<sigma> = "induced_subgraph \<sigma>"

    from opponent have
      "?G\<sigma> `` (X-A) \<subseteq> X"
      "?G\<sigma> `` (?X'-A) \<subseteq> ?X'"
      "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma> x xs ys
        \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
      by blast+

    (** All successors of x are part of X. *)
    moreover from \<open>\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>X\<close> have
      "\<forall>y. (x,y) \<in> ?G\<sigma> \<longrightarrow> y \<in> X" by simp

    (** By our auxiliary lemma, the thesis statement holds. *)
    ultimately show ?case using add_single_node by blast
  next
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X \<union> t"
    let ?\<sigma>' = "\<tau> |` (t - A) ++ \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    let ?Gt = "player_tangle_subgraph t \<tau>"

    from tangle have
      A_in_X: "A \<subseteq> X" and
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" and
      \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (?X'-A)" and
      \<sigma>'_closed_X: "?G\<sigma>' `` (X-A) \<subseteq> X" and
      \<sigma>'_closed_X': "?G\<sigma>' `` (?X'-A) \<subseteq> ?X'" and
      \<sigma>'_forces_A_or_wins:
        "\<forall>x\<in>X. \<forall>xs ys. lasso ?G\<sigma>' x xs ys
          \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys"
      by blast+

    from tangle have "t \<subseteq> V"
      using player_tangle_in_V tangles_T by auto
    from tangle have \<tau>_winning:
      "\<forall>v\<in>t. \<forall>xs. cycle ?Gt v xs \<longrightarrow> winning_player xs"
      unfolding player_tangle_strat_def Let_def by auto

    {
      fix v xs ys
      assume v_in_X': "v \<in> ?X'"
         and lasso: "lasso ?G\<sigma>' v xs ys"
         and lasso_no_A: "set (xs@ys) \<inter> A = {}"
      hence xs_no_A: "set xs \<inter> A = {}" and ys_no_A: "set ys \<inter> A = {}" by auto
      with \<open>v\<in>?X'\<close> have "v \<in> ?X'-A"
        using origin_in_lasso[OF lasso] by blast
      from lasso obtain v' where cycle: "cycle ?G\<sigma>' v' ys"
        unfolding lasso_def by auto

      consider (ys_has_X) "set ys \<inter> X \<noteq> {}" | (ys_no_X) "set ys \<inter> X = {}" by blast
      hence "winning_player ys" proof cases
        (** The cycle is entirely contained within X, as it is closed under \<sigma>'.
            Since lassos starting in X are won, this cycle is also won. *)
        case ys_has_X
        with cycle ys_no_A \<sigma>'_closed_X have "set ys \<subseteq> X"
          using cycle_intersects_partially_closed_region[of ?G\<sigma>'] by blast
        hence "v' \<in> X" using origin_in_cycle[OF cycle] by blast

        with \<sigma>'_forces_A_or_wins cycle ys_no_A show ?thesis
          using cycle_iff_lasso[of ?G\<sigma>' v' ys] by fastforce
      next
        (** The cycle is part of the tangle t, so it is won. *)
        case ys_no_X
        from \<open>v\<in>?X'-A\<close> \<sigma>'_closed_X' xs_no_A ys_no_A lasso
        have "set ys \<subseteq> ?X'-A"
          using lasso_partially_closed_sets[of v] by simp
        with ys_no_X have "set ys \<subseteq> t-X" by blast
        hence "v'\<in>t" using origin_in_cycle[OF cycle] by blast

        from \<sigma>'_dom \<sigma>_dom \<open>t\<subseteq>V\<close> \<open>A\<subseteq>X\<close> have subset:
          "Restr ?G\<sigma>' (t-X) \<subseteq> ?Gt"
          unfolding induced_subgraph_def player_tangle_subgraph_def E_of_strat_def
          by auto
        from subgraph_cycle[OF subset cycle_restr_V[OF cycle \<open>set ys\<subseteq>t-X\<close>]]
        have "cycle ?Gt v' ys" by fast

        with \<tau>_winning \<open>v'\<in>t\<close> show ?thesis by blast
      qed
    }
    thus ?case by blast
  qed
qed

(** After every step, we can reach a node in A from any node in X under \<sigma>'. *)
lemma tangle_attractor_step_path_X_to_A:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs x'"
proof-
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and
    invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)"
    using tangle_attractor_step_dom by auto

  (** If we have two strategies where one is closed and gives a path from any x in X to a y in A,
      and the subgraph X is the same under both strategies, then this path also exists under the
      other strategy. *)
  {
    fix X :: "'v set" and \<sigma> \<sigma>' :: "'v strat"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    let ?G\<sigma>' = "induced_subgraph \<sigma>'"
    assume \<sigma>_closed: "?G\<sigma> `` (X-A) \<subseteq> X"
       and restr_subgraph: "Restr ?G\<sigma> X \<subseteq> ?G\<sigma>'"
       and path_ex: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y"

    have "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma>' x xs y"
    proof (rule ballI)
      fix x assume x_in_X: "x \<in> X"
      (** For some x in X, consider the case where x is already in A, and the case where it is not. *)
      consider (x_in_A) "x \<in> A" | (x_notin_A) "x \<notin> A" by blast
      thus "\<exists>y\<in>A. \<exists>xs. path ?G\<sigma>' x xs y" proof cases
        (** If x is already in A, then an empty path will take us to A: we are already there. *)
        case x_in_A
        show ?thesis
          apply (rule bexI[where x=x])
          apply (rule exI[where x="[]"])
          using x_in_A by auto
      next
        (* If x is not in A, then we should have a path from x to some y in A using strategy, which
           also exists under \<sigma>'. *)
        case x_notin_A
        with \<open>x\<in>X\<close> have "x\<in>X-A" by simp
        from \<open>x\<in>X\<close> path_ex obtain xs y where
          y_in_A: "y \<in> A" and
          xs_no_A: "set xs \<inter> A = {}" and
          path: "path ?G\<sigma> x xs y"
          using shortest_subpath_to_region[of ?G\<sigma>] by metis
        (** Because x is not in A and \<sigma> is closed, the whole path stays in X. *)
        from path_partially_closed[OF \<open>x\<in>X-A\<close> \<sigma>_closed path xs_no_A]
        have xs_in_X: "set xs \<subseteq> X" and "y \<in> X" by blast+
        (** Therefore, the path exists in the graph of \<sigma> restricted to X *)
        from path_restr_V[OF path xs_in_X \<open>y\<in>X\<close>]
        have "path ?G\<sigma>' x xs y"
          using subgraph_path[OF restr_subgraph] by simp
        (** Therefore, we can use the path xs from x to y under \<sigma>' as our witness. *)
        with \<open>y\<in>A\<close> show ?thesis by blast
      qed
    qed
  } note X_path_to_A = this

  from step invar dom show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"

    (** We know that \<sigma> is partially closed, and that we can get a path from any x in X to some x'
        in A. *)
    from player have
      \<sigma>_closed: "?G\<sigma> `` (X-A) \<subseteq> X" and
      path_ex: "\<forall>x\<in>X. \<exists>x'\<in>A. \<exists>xs. path ?G\<sigma> x xs x'"
      by blast+

    (** We show that the graphs of \<sigma> and \<sigma>' are equal when restricted to X. *)
    from \<open>x\<in>V\<^sub>\<alpha>-X\<close> have "Restr ?G\<sigma> X \<subseteq> ?G\<sigma>'"
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
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"

    (** We know the domains of \<sigma> and \<sigma>', that \<sigma> is partially closed, and that we can get a path from
        any x in X to some x' in A. *)
    from tangle have
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" and
      \<sigma>'_dom: "dom ?\<sigma>' =  V\<^sub>\<alpha> \<inter> (?X'-A)" and
      \<sigma>_closed: "?G\<sigma> `` (X-A) \<subseteq> X" and
      path_ex: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y"
      by blast+

    (** Using the domains of \<sigma> and \<sigma>', we can see that the two subgraphs are equal in X. *)
    from \<sigma>_dom \<sigma>'_dom have "Restr ?G\<sigma> X \<subseteq> ?G\<sigma>'"
      unfolding induced_subgraph_def E_of_strat_def by auto

    (** From our earlier auxiliary proof and these properties, it follows that the thesis holds for
        this case as well. *)
    from X_path_to_A[OF \<sigma>_closed this path_ex] show ?case by blast
  qed
qed

(** After each step, we can reach a node in A from any node in X' under \<sigma>'. *)
lemma tangle_attractor_step_path_to_A:
  "\<lbrakk>tangle_attractor_step (X,\<sigma>) (X',\<sigma>'); tangle_attractor_step_I (X,\<sigma>)\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>X'. \<exists>x'\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs x'"
proof -
  assume step: "tangle_attractor_step (X,\<sigma>) (X',\<sigma>')" and
    invar: "tangle_attractor_step_I (X,\<sigma>)"
  hence props:
    "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X'-A)"
    "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X"
    "induced_subgraph \<sigma>' `` (X'-A) \<subseteq> X'"
    "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs y"
    using tangle_attractor_step_dom
          tangle_attractor_step_closed_X
          tangle_attractor_step_closed_X'
          tangle_attractor_step_path_X_to_A
    by auto

  (** If we have a y in X that can be reached from some x under a strategy \<sigma>, and we can reach a
      node in A from anywhere in X, then we can combine the two paths to get a path from that x to
      some node in A. *)
  {
    fix X :: "'v set" and x y :: 'v and \<sigma> xs
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    assume y_in_X: "y \<in> X"
       and path_y: "path ?G\<sigma> x xs y"
       and path_ex: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y"
    then obtain z ys where
      "z\<in>A" "path ?G\<sigma> y ys z" by blast
    with path_y have "path ?G\<sigma> x (xs@ys) z" by auto
    with \<open>z\<in>A\<close> have "\<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y" by blast
  } note append_path_to_A=this

  from step invar props show ?thesis
    unfolding tangle_attractor_step_I_def split
  proof (induction rule: tangle_attractor_step_induct)
    (** We can take a path from successor y to some z in A if we start with x, and prepend x to
        that path. If we start in X, then we already know that we can get a path to A. *)
    case (player x X y \<sigma>)
    let ?X' = "insert x X"
    let ?\<sigma>' = "\<sigma>(x\<mapsto>y)"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    (** We know we can get a path to A under \<sigma>' from any node in X. *)
    from player have X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma>' x xs y" by blast

    show ?case proof (rule ballI)
      fix x' assume x'_in_X': "x' \<in> ?X'"
      (** We must consider whether we start in X, or with x itself. *)
      then consider (x'_in_X) "x' \<in> X" | (x'_is_x) "x' = x"  by blast
      thus "\<exists>y'\<in>A. \<exists>xs. path ?G\<sigma>' x' xs y'" proof cases
        (** If we start in X, then we already know we can get a path to A. *)
        case x'_in_X with X_path_to_A show ?thesis by blast
      next
        (** If we start with x, then we can take a path to A from y and add x to the start of that
            path. *)
        case x'_is_x
        with player have "path ?G\<sigma>' x [x] y"
          using strategy_to_ind_subgraph[of ?\<sigma>' x y] by simp
        with X_path_to_A x'_is_x \<open>y\<in>X\<close> show ?thesis
          using append_path_to_A by blast
      qed
    qed
  next
    (** We can take a path from any successor y of x that leads to A, and prepend x to complete the
        path from x to A. Otherwise, if we start in X, we already know we can get a path to A. *)
    case (opponent x X \<sigma>)
    let ?X' = "insert x X"
    let ?G\<sigma> = "induced_subgraph \<sigma>"
    (** We know the domain of \<sigma>, and that we can get a path from any x in X to A. *)
    from opponent have
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" and
      X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y"
      by blast+

    show ?case proof (rule ballI)
      fix x' assume x'_in_X': "x' \<in> ?X'"
      (** We must consider whether we start in X, or with x itself. *)
      then consider (x'_in_X) "x' \<in> X" | (x'_is_x) "x' = x" by blast
      thus "\<exists>y'\<in>A. \<exists>xs. path ?G\<sigma> x' xs y'" proof cases
        (** If we start in X, we already know we can get a path to A. *)
        case x'_in_X with X_path_to_A show ?thesis by blast
      next
        case x'_is_x
        (** If we start with x, we can take any successor y of x, which will be in X. *)
        with \<open>x\<in>V\<^sub>\<beta>-X\<close> \<open>\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>X\<close> obtain y where
          "(x,y) \<in> E" "y \<in> X"
          using succ by auto
        with \<open>x\<in>V\<^sub>\<beta>-X\<close> \<sigma>_dom have "path ?G\<sigma> x [x] y"
          using ind_subgraph_notin_dom[of x y \<sigma>] by force
        with X_path_to_A x'_is_x \<open>y\<in>X\<close> show ?thesis
          using append_path_to_A by blast
      qed
    qed
  next
    (** t is strongly connected, so there is a path to an opponent node that escapes to a y in X.
        From any x in t, get a path to an escape y in X, then get the path from that y to A, and
        glue the two paths together to get a path from x to A. *)
    case (tangle t X \<tau> \<sigma>)
    let ?X' = "X\<union>t"
    let ?\<sigma>' = "\<tau> |` (t-A) ++ \<sigma>"
    let ?G\<tau> = "induced_subgraph \<tau>"
    let ?G\<sigma>' = "induced_subgraph ?\<sigma>'"
    from tangle have
      \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A)" and
      \<sigma>'_dom: "dom ?\<sigma>' = V\<^sub>\<alpha> \<inter> (X \<union> t-A)" and
      X_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path ?G\<sigma>' x xs y"
      by blast+

    show ?case proof (rule ballI)
      fix x assume x_in_X': "x \<in> ?X'"
      then consider (x_in_X) "x \<in> X" | (x_in_t_min_X) "x \<in> t-X" by blast
      thus "\<exists>x'\<in>A. \<exists>xs. path ?G\<sigma>' x xs x'" proof cases
        case x_in_X with X_path_to_A show ?thesis by blast
      next
        case x_in_t_min_X
        from \<open>t\<in>T\<close> tangles_T have "t \<subseteq> V"
          using player_tangle_in_V by blast
        with \<open>player_tangle_strat t \<tau>\<close> have
          \<tau>_dom: "dom \<tau> = t \<inter> V\<^sub>\<alpha>" and
          \<tau>_ran: "ran \<tau> \<subseteq> t" and
          t_connected: "strongly_connected (Restr ?G\<tau> t) t"
          unfolding player_tangle_strat_def Let_def
          by (auto simp: player_tangle_subgraph_is_restricted_ind_subgraph)

        from \<sigma>_dom have subgraph_\<tau>: "Restr ?G\<tau> (t-X) \<subseteq> ?G\<sigma>'"
          unfolding induced_subgraph_def E_of_strat_def
          by (auto simp: map_add_dom_app_simps(3))

        {
          fix xs z
          assume z_in_X: "z \<in> X"
             and xs_notempty: "xs \<noteq> []"
             and xs_no_X: "set xs \<inter> X = {}"
             and path: "path (Restr ?G\<tau> t) x xs z"

          then obtain xs' y where
            xs_comp: "xs = xs' @ [y]" and
            xs'_no_X: "set xs' \<inter> X = {}" and
            y_notin_X: "y \<notin> X" and
            y_in_xs: "y \<in> set xs" and
            edge: "(y,z) \<in> ?G\<tau>" and
            path_y: "path ?G\<tau> x xs' y"
            using path_D_rev[OF path xs_notempty] path_inter(1)
            by force

          from restr_V_path[OF path xs_notempty]
               y_in_xs \<open>y\<notin>X\<close> xs_comp xs'_no_X
          have "set xs' \<subseteq> t-X" "y \<in> t-X"
            by auto

          from path_restr_V[OF path_y this]
          have path_1: "path ?G\<sigma>' x xs' y"
            using subgraph_path[OF subgraph_\<tau>] by blast

          from y_notin_X edge \<sigma>_dom \<tau>_dom
          have path_2: "path ?G\<sigma>' y [y] z"
            unfolding induced_subgraph_def E_of_strat_def
            by (auto simp: map_add_dom_app_simps(3))

          from path_1 path_2 xs_comp have "path ?G\<sigma>' x xs z" by simp
        } note path_no_X=this

        from \<open>opponent_escapes t \<noteq> {}\<close> \<open>opponent_escapes t \<subseteq> X\<close> obtain y z where
          y_opp_in_t: "y \<in> t \<inter> V\<^sub>\<beta>" and
          z_in_X: "z \<in> X" and
          y_z_edge: "(y,z) \<in> E"
          unfolding opponent_escapes_def by blast
        with \<sigma>'_dom have y_z_edge_G\<sigma>': "(y,z)\<in>?G\<sigma>'"
          by (simp add: ind_subgraph_notin_dom)

        from y_opp_in_t x_in_t_min_X t_connected obtain xs where
          path_x_y: "path (Restr ?G\<tau> t) x xs y"
          using strongly_connected_path by blast

        consider (X_in_xs) "set xs \<inter> X \<noteq> {}" | (X_notin_xs) "set xs \<inter> X = {}" by blast
        thus ?thesis proof cases
          case X_in_xs
          obtain xs' y' where
            y'_in_X: "y' \<in> X" and
            xs'_no_X: "set xs' \<inter> X = {}" and
            path_x_y': "path (Restr ?G\<tau> t) x xs' y'"
            using shortest_subpath_to_region[OF path_x_y X_in_xs] by blast
          with x_in_t_min_X have "xs' \<noteq> []" by force

          from path_no_X[OF y'_in_X \<open>xs'\<noteq>[]\<close> xs'_no_X path_x_y']
            y'_in_X X_path_to_A
          show ?thesis using append_path_to_A by blast
        next
          case X_notin_xs
          consider (xs_empty) "xs = []" | (xs_notempty) "xs \<noteq> []" by blast
          thus ?thesis proof cases
            case xs_empty
            with path_x_y y_z_edge_G\<sigma>'
            have x_z_edge_G\<sigma>': "path ?G\<sigma>' x [x] z" by auto
            with z_in_X X_path_to_A show ?thesis
              using append_path_to_A by blast
          next
            case xs_notempty
            consider (y_in_X) "y \<in> X" | (y_notin_X) "y \<notin> X" by blast
            thus ?thesis proof cases
              case y_in_X
              with path_no_X[OF this xs_notempty X_notin_xs path_x_y]
                X_path_to_A
              show ?thesis using append_path_to_A by blast
            next
              case y_notin_X
              with y_opp_in_t have "y \<in> t-X" by blast

              from restr_V_path[OF path_x_y xs_notempty] X_notin_xs
              have "set xs \<subseteq> t-X" by blast

              from path_x_y have "path ?G\<tau> x xs y"
                using path_inter(1) by fast
              from path_restr_V[OF this \<open>set xs\<subseteq>t-X\<close> \<open>y\<in>t-X\<close>]
                subgraph_path[OF subgraph_\<tau>]
              have "path ?G\<sigma>' x xs y" by simp

              with \<open>(y,z)\<in>?G\<sigma>'\<close> have "path ?G\<sigma>' x (xs@[y]) z" by simp
              with \<open>z\<in>X\<close> X_path_to_A show ?thesis
                using append_path_to_A by blast
            qed
          qed
        qed
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
  using tangle_attractor_step_path_to_A[of X \<sigma> X' \<sigma>']
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

(** If A is not part of the domain of a strategy, then the subgraph of it with A_target added
    is a subgraph of the subgraph of that strategy. *)
lemma add_A_target_A_notin_dom:
  assumes "dom \<sigma> \<inter> A = {}"
  shows "induced_subgraph (\<sigma> ++ A_target X) \<subseteq> induced_subgraph \<sigma>"
    and "Restr (induced_subgraph \<sigma>) (-A) \<subseteq> induced_subgraph (\<sigma> ++ A_target X)"
  unfolding induced_subgraph_def E_of_strat_def A_target_def
  using assms by (auto split: if_splits simp: map_add_Some_iff)

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

(** The attracted region always contains A due to the monotonicity of the steps. *)
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
  using tangle_attractor_step_rtranclp_preserves_I tangle_attractor_step_I_base
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
proof -
  assume attr: "player_tangle_attractor X \<sigma>"
  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' where
    \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
    \<sigma>'_closed: "induced_subgraph \<sigma>' `` (X-A) \<subseteq> X" and
    \<sigma>_comp: "\<sigma> = \<sigma>' ++ A_target X"
    unfolding tangle_attractor_step_I_def
    by blast
  thus ?thesis
    using add_A_target_A_notin_dom[of \<sigma>' X] by blast
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
proof -
  assume attr: "player_tangle_attractor X \<sigma>"
  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' :: "'v strat" where
    \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
    \<sigma>'_forces_A_or_wins: "\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>') x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" and
    \<sigma>_comp: "\<sigma> = \<sigma>' ++ A_target X"
    unfolding tangle_attractor_step_I_def
    by blast
  thus ?thesis
    using subgraph_lasso[OF add_A_target_A_notin_dom(1)[of \<sigma>' X]]
    by blast
qed

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, there always exists a path from
    any node in X to A. *)
lemma player_tangle_attractor_strat_path_to_A:
  "player_tangle_attractor X \<sigma> \<Longrightarrow> \<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y"
proof (rule ballI)
  fix x
  assume attr: "player_tangle_attractor X \<sigma>" and x_in_X: "x\<in>X"
  from player_tangle_attractor_I_aux[OF attr] obtain \<sigma>' :: "'v strat" where
    \<sigma>'_dom: "dom \<sigma>' = V\<^sub>\<alpha> \<inter> (X-A)" and
    \<sigma>'_path_to_A: "\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>') x xs y" and
    \<sigma>_comp: "\<sigma> = \<sigma>' ++ A_target X"
    unfolding tangle_attractor_step_I_def
    by blast
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?G\<sigma>' = "induced_subgraph \<sigma>'"

  consider (x_in_A) "x\<in>A" | (x_notin_A) "x\<notin>A" by blast
  thus "\<exists>y\<in>A. \<exists>xs. path ?G\<sigma> x xs y" proof cases
    case x_in_A show ?thesis
      apply (rule bexI[where x=x])
      apply (rule exI[where x="[]"])
      using x_in_A by auto
  next
    case x_notin_A
    from x_in_X \<sigma>'_path_to_A obtain xs y where
      y_in_A: "y\<in>A" and
      xs_no_A: "set xs \<subseteq> -A" and
      path: "path ?G\<sigma>' x xs y"
      using shortest_subpath_to_region[of ?G\<sigma>' x]
      by (metis inf_shunt)
    from path xs_no_A \<open>x\<notin>A\<close> \<open>y\<in>A\<close> have "xs \<noteq> []" by force

    from path obtain xs' y' where
        edge: "(y',y) \<in> ?G\<sigma>'" and
        xs_comp: "xs = xs'@[y']" and
        path': "path ?G\<sigma>' x xs' y'"
        using path_D_rev[OF path \<open>xs\<noteq>[]\<close>] by blast
    with xs_no_A have "set xs' \<subseteq> -A" "y' \<in> -A" by auto

    from path_restr_V[OF path' this] \<sigma>'_dom \<sigma>_comp
    have "path ?G\<sigma> x xs' y'"
      using subgraph_path[OF add_A_target_A_notin_dom(2)[of \<sigma>' X]]
      by blast

    moreover from edge \<open>y'\<in>-A\<close> \<sigma>_comp have "(y',y) \<in> ?G\<sigma>"
      unfolding induced_subgraph_def E_of_strat_def A_target_def
      by (auto simp: map_add_Some_iff)

    ultimately have "path ?G\<sigma> x xs y"
      using xs_comp by auto

    with \<open>y\<in>A\<close> show ?thesis by blast
  qed
qed

(** If we have a tangle-attracted region X and a witness strategy \<sigma>, then \<sigma> is a strategy for the
    player, its domain is a subset of all player-owned nodes in X, its range is in X, the induced
    subgraph of \<sigma> is partially closed in X (excluding A), all plays starting in X restricted by
    \<sigma> either go to A or are won by the player, and there exists a path from all nodes in X to A. *)
lemma player_tangle_attractor_strat:
  "player_tangle_attractor X \<sigma> \<Longrightarrow>
   strategy_of V\<^sub>\<alpha> \<sigma> \<and>
   dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> X \<and>
   ran \<sigma> \<subseteq> X \<and>
   induced_subgraph \<sigma> `` (X-A) \<subseteq> X \<and>
   (\<forall>x\<in>X. \<forall>xs ys. lasso (induced_subgraph \<sigma>) x xs ys
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys) \<and>
   (\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y)"
  using player_tangle_attractor_strat_of_V\<^sub>\<alpha>[of X \<sigma>]
        player_tangle_attractor_strat_dom[of X \<sigma>]
        player_tangle_attractor_strat_ran[of X \<sigma>]
        player_tangle_attractor_strat_partially_closed[of X \<sigma>]
        player_tangle_attractor_strat_forces_A_or_wins[of X \<sigma>]
        player_tangle_attractor_strat_path_to_A[of X \<sigma>]
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
      \<longrightarrow> set (xs@ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys) \<and>
    (\<forall>x\<in>X. \<exists>y\<in>A. \<exists>xs. path (induced_subgraph \<sigma>) x xs y)"
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
