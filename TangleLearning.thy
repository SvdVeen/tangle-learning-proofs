theory TangleLearning
imports Main Tangles TangleAttractors
begin

context player_paritygame begin
(** Van Dijk's lemmata. Naming, descriptions will be improved later *)

(** Lemma 2:
    all plays bound by the tangle attractor strategy \<sigma> that stay in that tangle attractor
    to a region consisting only of vertices of the highest priority, won by \<alpha>, are won by \<alpha>. *)
lemma van_dijk_2_player:
  assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
  assumes fin_T: "finite T"
  assumes R_in_V: "R \<subseteq> V"
  assumes top_pr_p: "p = pr_set R"
  assumes winning_p: "winningP p"
  assumes A_def: "A = {v. v\<in>R \<and> pr v = p}"
  assumes \<sigma>_attr_strat: "player_tangle_attractor_strat T \<sigma> A"
  shows "\<forall>v\<in>player_tangle_attractor T A.
                \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (player_tangle_attractor T A \<times> player_tangle_attractor T A)) v xs ys \<longrightarrow> winning_player ys"
proof (intro ballI allI impI)
  let ?Z = "player_tangle_attractor T A"
  let ?restr_subgraph = "induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (?Z \<times> ?Z)"
  fix v xs ys
  assume v_in_Z: "v \<in> ?Z" and
         lasso_restr_Z_v_xs_ys: "lasso_from_node ?restr_subgraph v xs ys"

  from tangles_T fin_T \<sigma>_attr_strat have
    \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (?Z - A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> ?Z" and
    \<sigma>_closed: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (?Z - A) \<subseteq> ?Z" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>?Z. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
      \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
    by (simp add: player_tangle_attractor_strat_def)+

  from restr_V_lasso[OF lasso_restr_Z_v_xs_ys]
  have xs_in_Z: "set xs \<subseteq> ?Z" and
       ys_in_Z: "set ys \<subseteq> ?Z" and
       lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs ys"
    by blast+

  show "winning_player ys" proof(rule ccontr)
    assume not_winning: "winning_opponent ys"
    with \<sigma>_forces_A_or_wins lasso_v_xs_ys v_in_Z
    have A_in_xs_ys: "set (xs@ys) \<inter> A \<noteq> {}" by blast

    consider "set ys \<inter> A \<noteq> {}" | "set ys \<inter> A = {}" by blast
    hence "winning_player ys" proof cases
      case 1
      (** Because A consists of nodes of the highest priority in R, it should always have
          the winning priority, but this current lemma formulation does not specify that the
          tangle attractor remains in R.
          Possible solution: forget about R, take the highest priority in V instead.
          For an actual proof of the algorithm, we just need to limit to a subgame R.
          See below! *)
      then show ?thesis sorry
    next
      case 2
      from lasso_from_node_loop[OF lasso_v_xs_ys] obtain y where
         lasso_y_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) y [] ys" and
         y_in_ys: "y \<in> set ys" by blast
      with ys_in_Z have y_in_Z: "y \<in> ?Z" by blast

      with \<sigma>_forces_A_or_wins lasso_y_ys 2 show ?thesis by auto
    qed

    show "False" sorry
  qed
qed

lemma van_dijk_2_player':
  assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
  assumes fin_T: "finite T"
  assumes winning_top_p: "winningP (pr_set V)"
  assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
  assumes \<sigma>_attr_strat: "player_tangle_attractor_strat T \<sigma> A"
  shows "\<forall>v\<in>player_tangle_attractor T A.
          \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (player_tangle_attractor T A \<times> player_tangle_attractor T A)) v xs ys
            \<longrightarrow> winning_player ys"
proof (intro ballI allI impI)
  let ?Z = "player_tangle_attractor T A"
  from player_tangle_attractor_ss[OF tangles_T fin_T, of A] A_def
  have Z_in_V: "?Z \<subseteq> V" by blast
  let ?restr_subgraph = "induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> (?Z \<times> ?Z)"

  fix v xs ys
  assume v_in_Z: "v \<in> ?Z" and
         lasso_restr_Z_v_xs_ys: "lasso_from_node ?restr_subgraph v xs ys"

  from restr_V_lasso[OF lasso_restr_Z_v_xs_ys] have
    ys_in_Z: "set ys \<subseteq> ?Z" and
    lasso_v_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs ys"
    by blast+
  with Z_in_V have ys_in_V: "set ys \<subseteq> V" by simp

  from lasso_from_node_loop[OF lasso_v_xs_ys] obtain y where
    lasso_y_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) y [] ys" and
    y_in_ys: "y \<in> set ys" and
    ys_notempty: "ys \<noteq> []"
    by fastforce
  with ys_in_Z have y_in_Z: "y \<in> ?Z" by blast

  consider (A_in_ys) "set ys \<inter> A \<noteq> {}" | (A_notin_ys) "set ys \<inter> A = {}" by blast
  thus "winning_player ys" proof cases
    case A_in_ys

    have "top_pr ys = pr_set V" proof (rule antisym)
      from top_pr_le_pr_set_V[OF ys_in_V ys_notempty]
      show "top_pr ys \<le> pr_set V" .
    next
      from A_in_ys A_def ys_in_V show "pr_set V \<le> top_pr ys"
        unfolding top_pr_def
        using Max_ge[OF finite_surj[OF fin_V image_mono[OF ys_in_V, of pr]]]
        by fastforce
    qed

    with winning_top_p show ?thesis by simp
  next
    case A_notin_ys
    with tangles_T fin_T \<sigma>_attr_strat y_in_Z lasso_y_ys
    show ?thesis by (auto simp: player_tangle_attractor_strat_def)
  qed
qed

lemma van_dijk_7_player:
  assumes t_tangle: "player_tangle t"
  shows "opponent_escapes t = {} \<longleftrightarrow> player_winning_region t"
  using assms no_escapes_closed_opponent closed_player_tangle_is_winning_region
  by safe (auto simp: player_winning_region_def)

end (** End of context player_paritygame *)

context paritygame begin

(** Future proof still needs to show that this is limited to a region R, which is a subgame. *)
lemma van_dijk_2':
  assumes tangles_T: "\<forall>t\<in>T. tangle \<alpha> t"
  assumes fin_T: "finite T"
  assumes winning_top_p: "player_winningP \<alpha> (pr_set V)"
  assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
  assumes \<sigma>_attr_strat: "tangle_attractor_strat \<alpha> T \<sigma> A"
  shows "\<forall>v\<in>tangle_attractor \<alpha> T A.
          \<forall>xs ys. lasso_from_node (induced_subgraph (V_player \<alpha>) \<sigma> \<inter> (tangle_attractor \<alpha> T A \<times> tangle_attractor \<alpha> T A)) v xs ys
            \<longrightarrow> player_wins_list \<alpha> ys"
  using assms P0.van_dijk_2_player' P1.van_dijk_2_player'
  by (cases \<alpha>; simp)

lemma van_dijk_7:
  assumes "tangle \<alpha> t"
  shows "escapes \<alpha> t = {} \<longleftrightarrow> winning_region \<alpha> t"
  using assms P0.van_dijk_7_player P1.van_dijk_7_player
  by (cases \<alpha>; simp)

end (** End of context paritygame *)

end
