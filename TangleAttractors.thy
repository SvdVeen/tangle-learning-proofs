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
  own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-S; (x,y) \<in> E; y \<in> S\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (insert x S,\<sigma>(x\<mapsto>y))"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-S; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> S\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (insert x S,\<sigma>)"
| escape: "\<lbrakk>t \<in> T; t-S \<noteq> {}; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> S;
            player_tangle_strat t \<sigma>'\<rbrakk> \<Longrightarrow> tangle_attractor_step (S,\<sigma>) (S\<union>t,(\<sigma>' |` (t-A)) ++ \<sigma>)"

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


subsection \<open>Tangle Attractors\<close>
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


(** We finally get the definition for the attractor as a whole by taking the reflexive transitive
    closure of the steps starting from the target set with an empty strategy. We also limit it to
    only final results by saying it should not be in the domain of the relation; it cannot be
    followed by another step. *)
definition player_tangle_attractor :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "player_tangle_attractor X \<sigma> \<equiv> tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>) \<and>
    \<not>Domainp tangle_attractor_step (X,\<sigma>)"

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
  using wf_rel_terminates[OF tangle_attractor_step_wf]
  unfolding player_tangle_attractor_def .

(** Every node that is not in a tangle attractor still has successors outside of that attractor. *)
lemma notin_player_tangle_attractor_succ:
  "\<lbrakk>player_tangle_attractor X \<sigma>; v \<in> V; v \<notin> X\<rbrakk> \<Longrightarrow> E `` {v} - X \<noteq> {}"
proof
  assume attr: "player_tangle_attractor X \<sigma>" and
         v_in_V: "v \<in> V" and
         v_notin_X: "v \<notin> X" and
         no_succs_outside_X: "E `` {v} - X = {}"
  (** We need to unfold the definition of the attractor so we can use it for our induction later. *)
  from attr have
    attr_step_rtranclp: "tangle_attractor_step\<^sup>*\<^sup>* (A,Map.empty) (X,\<sigma>)" and
    attr_step_result: "\<not>Domainp tangle_attractor_step (X,\<sigma>)"
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
lemma fin_player_tangle_attractor: "player_tangle_attractor X \<sigma> \<Longrightarrow> finite A \<Longrightarrow> finite X"
  using finite_subset[OF player_tangle_attractor_ss] by blast


subsubsection \<open>An Induction Rule for Tangle Attractors\<close>
(** We want to define an induction rule for tangle attractors. To achieve this, we start with
    an induction rule for the reflexive transitive closure of the tangle_attractor_step. *)
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

(** We can now use this rule to make an induction rule for the tangle attractor itself.
    This rule is internal, because it still depends on the assumptions of the context it is in. *)
lemma player_tangle_attractor_induct_internal[consumes 1, case_names base own opponent escape]:
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
  from attr have " tangle_attractor_step\<^sup>*\<^sup>* (A, \<lambda>x. None) (X, \<sigma>)"
    unfolding player_tangle_attractor_def by blast
  from this base' have "P' (X,\<sigma>)"
    apply (induction rule: tangle_attractor_step_rtranclp_induct)
    using own' opponent' escape' by auto
  thus ?thesis
    unfolding P'_def by simp
qed

subsection \<open>Tangle Attractor Strategies\<close>
definition tangle_attractor_strat_I :: "'v set \<times> 'v strat \<Rightarrow> bool" where
  "tangle_attractor_strat_I \<equiv> \<lambda>(S,\<sigma>).
   strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (S-A) \<and> ran \<sigma> \<subseteq> S \<and>
   induced_subgraph V\<^sub>\<alpha> \<sigma> `` (S-A) \<subseteq> S \<and>
   (\<forall>x\<in>S. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"

lemma tangle_attractor_strat_I_base: "tangle_attractor_strat_I (A,Map.empty)"
  unfolding tangle_attractor_strat_I_def using origin_in_lasso by fastforce

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

(** The reflexive transitive closure of the tangle attractor step preserves the strategy invariant. *)
lemma tangle_attractor_step_rtranclp_preserves_I:
  "tangle_attractor_step\<^sup>*\<^sup>* S S' \<Longrightarrow> A \<subseteq> fst S \<Longrightarrow> tangle_attractor_strat_I S
  \<Longrightarrow> tangle_attractor_strat_I S'"
  apply (induction rule: rtranclp_induct; simp)
  using tangle_attractor_step_rtranclp_mono tangle_attractor_strat_I_step subset_trans
  by fast

(** The tangle attractor strategy belongs to the player, goes from V\<^sub>\<alpha>-A to X, is closed in X, and
    forces all plays starting within it to either move to A, or be won by the player. *)
lemma player_tangle_attractor_strat: "player_tangle_attractor X \<sigma> \<Longrightarrow>
  strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (X-A) \<and> ran \<sigma> \<subseteq> X \<and>
  induced_subgraph V\<^sub>\<alpha> \<sigma> `` (X-A) \<subseteq> X \<and>
  (\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
    \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
  using tangle_attractor_strat_I_base tangle_attractor_step_rtranclp_preserves_I
  unfolding player_tangle_attractor_def tangle_attractor_strat_I_def
  by clarsimp

find_theorems wf
term lfp
term mono
thm wfP_induct_rule[OF tangle_attractor_step_wf]
find_theorems mono
find_theorems rtranclp Domainp
lemma "\<lbrakk>tangle_attractor_step\<^sup>*\<^sup>* S S'; \<not>Domainp tangle_attractor_step S'; tangle_attractor_step\<^sup>*\<^sup>* S S''; \<not>Domainp tangle_attractor_step S''\<rbrakk> \<Longrightarrow> fst S' = fst S''"
  sorry, xxx sorry
term "(tangle_attractor_step\<^sup>*\<^sup>* S)"
lemma "\<not>Domainp tangle_attractor_step\<^sup>*\<^sup>* S \<Longrightarrow> \<nexists>S'. tangle_attractor_step S S'"
  by blast

lemma a: "\<lbrakk>P\<^sup>*\<^sup>* A B; A\<noteq>B\<rbrakk> \<Longrightarrow> Rangep P B"
  by (auto intro: rtranclp.cases)

lemma b: "\<lbrakk>P\<^sup>*\<^sup>* A B; A\<noteq>B\<rbrakk> \<Longrightarrow> Domainp P A"
  by (auto intro: converse_rtranclpE)

lemma c: "\<lbrakk>\<not>Domainp P A; B\<noteq>A\<rbrakk> \<Longrightarrow> \<not>P\<^sup>*\<^sup>* A B"
  by (auto intro: converse_rtranclpE)

lemma tangle_attractor_step_set_comp: "tangle_attractor_step S S' \<Longrightarrow> fst S' \<subseteq>
  (fst S
   \<union> {x | x y. x \<in> V\<^sub>\<alpha>-fst S \<and> (x,y) \<in> E \<and> y \<in> fst S}
   \<union> {x. x \<in> V\<^sub>\<beta>-fst S \<and> (\<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> fst S)}
   \<union> \<Union>{t. t \<in> T \<and> t - fst S \<noteq> {} \<and> opponent_escapes t \<noteq> {} \<and> opponent_escapes t \<subseteq> fst S})"
  by (induction rule: tangle_attractor_step.induct) auto

lemma tangle_attractor_step_set_membership: "\<lbrakk>tangle_attractor_step S S'; v \<in> fst S'\<rbrakk> \<Longrightarrow>
  v \<in> fst S \<or>
  (v \<in> V\<^sub>\<alpha>-fst S \<and> (\<exists>y. (v, y) \<in> E \<and> y \<in> fst S)) \<or>
  (v \<in> V\<^sub>\<beta>-fst S \<and> (\<forall>y. (v, y) \<in> E \<longrightarrow> y \<in> fst S)) \<or>
  (\<exists>t. v \<in> t \<and> t \<in> T \<and> t-fst S \<noteq> {} \<and> opponent_escapes t \<noteq> {} \<and> opponent_escapes t \<subseteq> fst S)"
  using tangle_attractor_step_set_comp[of S S'] by blast

lemma tangle_attractor_step_set_cases:
  assumes "tangle_attractor_step S S'"
  assumes "v \<in> fst S'"
  obtains (base) "v \<in> fst S"
        | (own) "v \<in> V\<^sub>\<alpha>-fst S \<and> (\<exists>y. (v, y) \<in> E \<and> y \<in> fst S)"
        | (opponent)"v \<in> V\<^sub>\<beta>-fst S \<and> (\<forall>y. (v, y) \<in> E \<longrightarrow> y \<in> fst S)"
        | (escape)"(\<exists>t. v \<in> t \<and> t \<in> T \<and> t-fst S \<noteq> {} \<and> opponent_escapes t \<noteq> {} \<and> opponent_escapes t \<subseteq> fst S)"
  using tangle_attractor_step_set_membership[OF assms] by blast
end (** End of context with fixed A *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor, i.e. TAttr(A) = A.
    This definition is now clearly wrong - it needs changing! *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> \<forall>\<sigma>. \<nexists>S'. tangle_attractor_step A (A,\<sigma>) S'" (** player_tangle_attractor A A Map.empty" *)


subsection \<open>\<alpha>-maximal Regions\<close>
(** A region is \<alpha>-maximal if it equals its tangle attractor, i.e. TAttr(A) = A.
    This definition is now clearly wrong - it needs changing! *)
definition player_\<alpha>_max :: "'v set \<Rightarrow> bool" where
  "player_\<alpha>_max A \<equiv> \<forall>\<sigma>. \<nexists>S'. tangle_attractor_step A (A,\<sigma>) S'" (** player_tangle_attractor A A Map.empty" *)

(** Tangle attracted regions cannot be extended further with the tangle attractor. *)
lemma attractor_no_extension:
  "player_tangle_attractor A X \<sigma> \<Longrightarrow> \<nexists>S'. tangle_attractor_step A (X,\<sigma>) S'"
  unfolding player_tangle_attractor_def by blast

lemma attractor_no_extension':
  "player_tangle_attractor A X \<sigma> \<Longrightarrow> \<nexists>S'. tangle_attractor_step X (X,Map.empty) S'"
  unfolding player_tangle_attractor_def
  apply (erule conjE)
  apply (induction rule: rtranclp_induct)
  sorry

end (** End of context with fixed T *)

(** We need this version of the induction lemma so we can supply the properties of T without losing
    our case names. *)
lemmas player_tangle_attractor_induct[consumes 3, case_names base own opponent escape] =
  player_tangle_attractor_induct_internal

end (** End of context player_paritygame *)

section \<open>Tangle Attractors for Specific Players\<close>
context paritygame begin

fun tangle_attractor :: "player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_attractor EVEN = P0.player_tangle_attractor"
| "tangle_attractor ODD = P1.player_tangle_attractor"

lemma tangle_attractor_exists:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "\<exists>X \<sigma>. tangle_attractor \<alpha> T A X \<sigma>"
  using assms P0.player_tangle_attractor_exists P1.player_tangle_attractor_exists
  by (cases \<alpha>; simp)

lemma notin_tangle_attractor_succ:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "\<lbrakk>tangle_attractor \<alpha> T A X \<sigma>; v \<in> V; v \<notin> X\<rbrakk> \<Longrightarrow> E `` {v}-X \<noteq> {}"
  using assms P0.notin_player_tangle_attractor_succ P1.notin_player_tangle_attractor_succ
  by(cases \<alpha>; simp)

lemma target_in_tangle_attractor:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> A \<subseteq> X"
  using assms P0.target_in_player_tangle_attractor P1.target_in_player_tangle_attractor
  by (cases \<alpha>; simp)

lemma tangle_attractor_ss:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> X \<subseteq> A \<union> V"
  using assms P0.player_tangle_attractor_ss P1.player_tangle_attractor_ss
  by (cases \<alpha>; simp)

lemma tangle_attractor_strat:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow>
         strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = V_player \<alpha> \<inter> (X-A) \<and> ran \<sigma> \<subseteq> X \<and>
         induced_subgraph (V_player \<alpha>) \<sigma> `` (X-A) \<subseteq> X \<and>
         (\<forall>x\<in>X. \<forall>xs ys. lasso_from_node (induced_subgraph (V_player \<alpha>) \<sigma>) x xs ys
            \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys)"
  unfolding strategy_of_player_def
  using assms P0.player_tangle_attractor_strat P1.player_tangle_attractor_strat
  by (cases \<alpha>; simp add: V\<^sub>1_def)

lemma fin_tangle_attractor:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  shows "tangle_attractor \<alpha> T A X \<sigma> \<Longrightarrow> finite A \<Longrightarrow> finite X"
  using assms P0.fin_player_tangle_attractor P1.fin_player_tangle_attractor
  by (cases \<alpha>; simp)

(** If you remove a tangle attractor from the game, the resulting graph is a valid subgame. *)
lemma remove_tangle_attractor_subgame:
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  assumes tangle_attractor: "tangle_attractor \<alpha> T A X \<sigma>"
  shows "paritygame (Restr E (V-X)) (V-X) (V\<^sub>0-X)"
proof (unfold_locales)
  show " Restr E (V-X) \<subseteq> (V-X)\<times>(V-X)" by blast
  show "finite (V-X)" by simp
  show "V\<^sub>0-X \<subseteq> V-X" using V\<^sub>0_in_V by blast
  show "\<And>v. v \<in> V-X \<Longrightarrow> Restr E (V-X) `` {v} \<noteq> {}"
  proof -
    fix v
    assume v_in_V_min_X: "v \<in> V-X"
    hence v_in_V: "v\<in>V" by simp
    from v_in_V_min_X have "v \<notin> X" by simp
    with notin_tangle_attractor_succ[OF tangles_T fin_T tangle_attractor v_in_V]
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
