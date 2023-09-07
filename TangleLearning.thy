theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>
section \<open>Tangle Definitions\<close>

context paritygame begin

(** As defined by Van Dijk:
    A p-tangle is a nonempty set of vertices U \<subseteq> V with p = pr(U),
    for which player \<alpha> \<equiv>\<^sub>2 p has a strategy \<sigma>: U\<^sub>\<alpha> \<rightarrow> U, such that the graph (U,E'),
    with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and player \<alpha> wins all cycles in (U,E').*)
(** Maybe this needs moving to player_paritygame, but maybe not *)
definition p_tangle :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "p_tangle p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (prio ` U) \<and>
  (let \<alpha> = player_wins_prio p in (
    \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  ))))"

(** A definition of a p-tangle using induced subgraphs, making it easier to work with *)
definition p_tangle' :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "p_tangle' p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (prio ` U) \<and>
  (let \<alpha> = player_wins_prio p in (
    \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = induced_subgraph (U \<inter> V_player \<alpha>) \<sigma> \<inter> (U\<times>U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  ))))"

lemma ind_subgraph_int: "\<lbrakk>dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> U; ran \<sigma> \<subseteq> U\<rbrakk>
  \<Longrightarrow> E \<inter> (((U-V\<^sub>\<alpha>) \<times> U) \<union> E_of_strat \<sigma>) = induced_subgraph (U \<inter> V\<^sub>\<alpha>) \<sigma> \<inter> (U\<times>U)"
  apply (subst ind_subgraph_in_V)
  apply safe
  subgoal using E_in_V by blast
  subgoal using E_in_V by blast
  subgoal unfolding E_of_strat_def by blast
  subgoal unfolding E_of_strat_def using ranI by fast
  done

lemma V_opponent_player_int: "U \<subseteq> V \<Longrightarrow> U \<inter> V_opponent \<alpha> = U - V_player \<alpha>"
  using V\<^sub>1_def by (cases \<alpha>) auto

lemma p_tangles_eq: "p_tangle p U = p_tangle' p U"
  unfolding p_tangle_def p_tangle'_def Let_def strategy_of_player_def strategy_of_def
  apply (rule; clarsimp)
  subgoal for \<sigma>
    apply (rule exI[where x="\<sigma>"]; simp; intro conjI ballI allI)
    using ind_subgraph_int[of \<sigma> "V_player (player_wins_prio  (Max (prio ` U)))" U]
    using V_opponent_player_int[of U "player_wins_prio  (Max (prio ` U))"]
    using Int_commute[of U] Un_commute subset_refl by metis+
  subgoal for \<sigma>
    apply (rule exI[where x="\<sigma>"]; simp; intro conjI ballI allI)
    using ind_subgraph_int[of \<sigma> "V_player (player_wins_prio  (Max (prio ` U)))" U]
    using V_opponent_player_int[of U "player_wins_prio  (Max (prio ` U))"]
    using Int_commute[of U] Un_commute subset_refl by metis+
  done

(** TODO: adapt winning region to p-dominion *)
lemma "p_tangle p U \<Longrightarrow> \<forall>v \<in> U \<inter> V_opponent (player_wins_prio p). E `` {v} \<subseteq> U \<Longrightarrow> winning_region (player_wins_prio p) U"
proof -
  assume p_tangle: "p_tangle p U"
  assume no_opponent_escapes: "\<forall>v \<in> U \<inter> V_opponent (player_wins_prio p). E `` {v} \<subseteq> U"
  from p_tangle have U_in_V: "U \<subseteq> V" unfolding p_tangle_def by simp

  let ?\<alpha> = "player_wins_prio p"
  from p_tangle obtain \<sigma> where
      \<sigma>_strat: "strategy_of_player ?\<alpha> \<sigma>"
  and \<sigma>_dom: "dom \<sigma> = U \<inter> V_player ?\<alpha>"
  and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
  and \<sigma>_conn: "strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
  and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U)) v xs
    \<longrightarrow> player_wins_list ?\<alpha> xs"
    unfolding p_tangle_def Let_def by blast

  have \<sigma>_subgraph_closed: "induced_subgraph (dom \<sigma>) \<sigma> `` U \<subseteq> U"
  proof -
    from ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran, of "dom \<sigma>"] no_opponent_escapes
         V_opponent_player_int[OF U_in_V, of ?\<alpha>]
    have "\<forall>v \<in> U. \<forall>v'. (v,v') \<in> induced_subgraph (dom \<sigma>) \<sigma> \<longrightarrow> v' \<in> U"
      by (simp add: \<sigma>_dom)
    thus ?thesis by blast
  qed

  show "winning_region (player_wins_prio p) U"
    unfolding winning_region_strat
    apply (rule conjI)
    using U_in_V apply simp
    apply (rule exI[where x="\<sigma>"]; intro conjI)
    subgoal using \<sigma>_strat by simp
    subgoal using \<sigma>_dom by force
    subgoal using \<sigma>_ran by simp
    subgoal proof (rule ballI; rule allI; rule impI)
      fix v ys
      assume v_in_U: "v \<in> U" and cycle_w_ys: "cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v ys"
      from cycle_from_node_closed_set[OF v_in_U \<sigma>_subgraph_closed cycle_w_ys]
      have ys_in_U: "set ys \<subseteq> U" .

      from cycle_w_ys ys_in_U obtain y where
          cycle_y_ys: "cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) y ys"
      and y_in_U: "y \<in> U"
        unfolding cycle_from_node_def
        using origin_in_cycle_node by fastforce

      have "induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U) \<subseteq> (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
        apply (subst \<sigma>_dom; simp; rule conjI)
        subgoal using ind_subgraph[of "U \<inter> V_player ?\<alpha>"] by blast
        subgoal apply (subst V_opponent_player_int[OF U_in_V])
          unfolding induced_subgraph_def by fast
        done
      from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
      show "player_wins_list ?\<alpha> ys" by simp
    qed
    subgoal using no_opponent_escapes by simp
    done
qed

(** Tom's observations *)
(** 1: A p-tangle from which the opponent cannot leave is a p-dominion  *)
corollary tangle_obs_1: "\<lbrakk>p_tangle p U; E `` (U \<inter> V_opponent (player_wins_prio p)) \<subseteq> U\<rbrakk> \<Longrightarrow> p_dominion (player_wins_prio p) p U"
proof -
  let ?\<alpha> = "player_wins_prio p"

  assume p_tangle: "p_tangle p U"
  assume no_opponent_escapes: "E `` (U \<inter> V_opponent ?\<alpha>) \<subseteq> U"
  from p_tangle have U_in_V: "U \<subseteq> V" unfolding p_tangle_def by simp
  from p_tangle have p_max: "p = Max (prio ` U)" unfolding p_tangle_def by simp

  from p_tangle obtain \<sigma> where
      \<sigma>_strat: "strategy_of_player ?\<alpha> \<sigma>"
  and \<sigma>_dom: "dom \<sigma> = U \<inter> V_player ?\<alpha>"
  and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
  and \<sigma>_conn: "strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
  and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U)) v xs
    \<longrightarrow> player_wins_list ?\<alpha> xs"
    unfolding p_tangle_def Let_def by blast

  have \<sigma>_subgraph_closed: "induced_subgraph (dom \<sigma>) \<sigma> `` U \<subseteq> U"
  proof -
    from ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran, of "dom \<sigma>"] no_opponent_escapes
         V_opponent_player_int[OF U_in_V, of ?\<alpha>]
    have "\<forall>v \<in> U. \<forall>v'. (v,v') \<in> induced_subgraph (dom \<sigma>) \<sigma> \<longrightarrow> v' \<in> U"
      using \<sigma>_dom by blast
    thus ?thesis by blast
  qed

  show "p_dominion ?\<alpha> p U"
    unfolding p_dominion_strat
    apply (rule conjI; simp add: U_in_V)
    apply (rule exI[where x="\<sigma>"]; intro conjI)
    subgoal using \<sigma>_strat by simp
    subgoal using \<sigma>_dom by simp
    subgoal using \<sigma>_ran by simp
    subgoal using no_opponent_escapes by fast
    subgoal proof (rule ballI; rule allI; rule impI)
      fix v ys
      assume v_in_U: "v \<in> U" and cycle_w_ys: "cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v ys"
      from cycle_from_node_closed_set[OF v_in_U \<sigma>_subgraph_closed cycle_w_ys]
      have ys_in_U: "set ys \<subseteq> U" .

      from cycle_w_ys ys_in_U obtain y where
          cycle_y_ys: "cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) y ys"
      and y_in_U: "y \<in> U"
        unfolding cycle_from_node_def
        using origin_in_cycle_node by fastforce

      have "induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U) \<subseteq> (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
        apply (subst \<sigma>_dom; simp; rule conjI)
        subgoal using ind_subgraph[of "U \<inter> V_player ?\<alpha>"] by blast
        subgoal apply (subst V_opponent_player_int[OF U_in_V])
          unfolding induced_subgraph_def by fast
        done
      from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
      show "player_wins_list ?\<alpha> ys" by simp
    qed
    subgoal proof (rule ccontr)
      assume not_max: "p \<noteq> Max (prio ` {x. \<exists>v xs. cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<and> x \<in> set xs})"
      hence "\<exists>v\<in>U. \<exists>xs. \<exists>x \<in> set xs. cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<and> p < prio x"
        apply auto sorry
      show "False" sorry
    qed
    done
qed

(** 2: Every p-dominion contains one or more p-tangles. *)
corollary tangle_obs_2: "p_dominion (player_wins_prio p) p D \<Longrightarrow> \<exists>U. U \<subseteq> D \<and> p_tangle p U" sorry

(** 3: Tangles may contain tangles of a lower priority *)
corollary tangle_obs_3: "p_tangle p U" oops

(** A tangle without a specified p. Useful for proofs that do not need p. *)
definition tangle :: "'v set \<Rightarrow> bool" where
  "tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
  (let \<alpha> = player_wins_prio (Max (prio ` U)) in (
    \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  ))))"

lemma tangle_iff_p_tangle: "tangle U \<longleftrightarrow> (\<exists>p. p_tangle p U)"
  unfolding tangle_def p_tangle_def by simp

(** I may want to move these definitions into a player_paritygame context like the original attractor definition *)
definition escapes :: "player \<Rightarrow> 'v set \<Rightarrow> 'v set" where
  "escapes \<alpha> t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V_opponent \<alpha> \<and> v \<in> V - t}"
end

context player_paritygame
begin
(** This would technically work for any set, but we want to use it for tangles only *)
definition opponent_escapes :: "'v set \<Rightarrow> 'v set" where
  "opponent_escapes t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V\<^sub>\<beta> \<and> v \<in> V - t}"

inductive_set player_tangle_attractor :: "'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set" for T A where
  base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor T A"
| own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y)\<in>E; y \<in> player_tangle_attractor T A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor T A"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y)\<in>E \<longrightarrow> y \<in> player_tangle_attractor T A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor T A"
| escape: "\<lbrakk>x \<in> t-A; t \<in> T; opponent_escapes t \<noteq> {}; opponent_escapes t \<subseteq> player_tangle_attractor T A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor T A"
end

end
